//! Commitment-opening + membership + nullifier — the Phase-2 spend statement (C-01/C-02/C-03).
//!
//! One Winterfell proof attests, for public `(root, nf, tx_binding)` and a private note:
//!   1. **commitment** `cm = H(recipient, value, rho, rcm)`  (block 0, one Rescue permutation)
//!   2. **membership** `cm` folds up a general-position path to `root`  (blocks 1..=DEPTH)
//!   3. **nullifier**  `nf = H(nk, rho, pos)`  (last block; `nf` public)
//!   4. **tx-binding** the proof is bound to `tx_binding` (the tx sighash) via Fiat-Shamir, so it
//!      cannot be lifted/replayed onto another transaction.
//! with the **same `rho`** in (1) and (3).
//!
//! Cross-region `rho` binding without an auxiliary grand-product segment: a **persistent `rho`
//! column** (col 13) is held constant across the whole trace, bound to the commitment's `rho`
//! input at row 0 and to the nullifier's `rho` input at its load. Per-boundary periodic selectors
//! (`is_round` / `is_merge` / `is_null` / `is_first`) gate which constraint fires on each row.
//!
//! Validated against native oracles: `cm`/`nf` match `Rp64_256::hash_elements`; the AIR trace
//! `root` and `nf` match the native fold/hash; valid-verifies; wrong `root`, wrong `nf`, a
//! tampered opening, and an **inconsistent `rho`** (commitment vs nullifier) are all rejected.
//!
//! Scope / audit note (Codex audit precedes production wiring): `recipient`/`nk`/`pos` are single
//! field elements (demo). Still TODO before production: **ownership** (recipient ↔ `nk`),
//! **value-balance + range** (bind `out_cm`), **position-consistency** (nullifier `pos` ↔ the
//! path), depth 32, canonical proof serialization, and the real `lattica_spend_verify`.

use winterfell::{
    math::{fields::f64::BaseElement, FieldElement, ToElements},
    matrix::ColMatrix,
    Air, AirContext, Assertion, AuxRandElements, BatchingMethod, CompositionPoly,
    CompositionPolyTrace, ConstraintCompositionCoefficients, DefaultConstraintCommitment,
    DefaultConstraintEvaluator, DefaultTraceLde, EvaluationFrame, FieldExtension, PartitionOptions,
    Proof, ProofOptions, Prover, StarkDomain, TraceInfo, TracePolyTable, TraceTable,
    TransitionConstraintDegree,
};
use winterfell::crypto::hashers::Rp64_256;

use crate::{inv_mds_mul, mds_mul, pow7, Coin, Hf, Vc, CYCLE, NUM_ROUNDS, STATE_WIDTH};

pub const DEPTH: usize = 6; // membership levels (production 32; needs a block-count pad decision)
pub const DIGEST: usize = 4;
pub const COMMIT_LEN: usize = 4; // [recipient, value, rho, rcm]
pub const NULL_LEN: usize = 3; // [nk, rho, pos]
const BLOCK: usize = 8;
const WIDTH: usize = STATE_WIDTH + 2; // 12 state + bit + persistent rho
const BIT: usize = STATE_WIDTH; // col 12
const RHO: usize = STATE_WIDTH + 1; // col 13 (persistent rho)
const NUM_BLOCKS: usize = DEPTH + 2; // commitment + DEPTH merges + nullifier
const TRACE_LEN: usize = BLOCK * NUM_BLOCKS;
const ROOT_ROW: usize = BLOCK * (DEPTH + 1) - 1; // last membership block output
const NF_ROW: usize = TRACE_LEN - 1; // nullifier block output
const N_CONSTRAINTS: usize = STATE_WIDTH + 2; // 12 state + rho-constancy + row-0 rho-binding

#[derive(Clone, Copy)]
pub struct Note {
    pub recipient: BaseElement,
    pub value: BaseElement,
    pub rho: BaseElement,
    pub rcm: BaseElement,
    pub nk: BaseElement,
    pub pos: BaseElement,
}

// --- native oracles ---------------------------------------------------------------------------

fn hash_n(elems: &[BaseElement]) -> [BaseElement; DIGEST] {
    let mut state = [BaseElement::ZERO; STATE_WIDTH];
    state[0] = BaseElement::new(elems.len() as u64);
    state[4..4 + elems.len()].copy_from_slice(elems);
    Rp64_256::apply_permutation(&mut state);
    state[4..8].try_into().unwrap()
}

pub fn native_commit(n: Note) -> [BaseElement; DIGEST] {
    hash_n(&[n.recipient, n.value, n.rho, n.rcm])
}
pub fn native_nullifier(n: Note) -> [BaseElement; DIGEST] {
    hash_n(&[n.nk, n.rho, n.pos])
}
fn native_merge(left: [BaseElement; DIGEST], right: [BaseElement; DIGEST]) -> [BaseElement; DIGEST] {
    let mut state = [BaseElement::ZERO; STATE_WIDTH];
    state[0] = BaseElement::new(8);
    state[4..8].copy_from_slice(&left);
    state[8..12].copy_from_slice(&right);
    Rp64_256::apply_permutation(&mut state);
    state[4..8].try_into().unwrap()
}
pub fn native_root(n: Note, siblings: &[[BaseElement; DIGEST]; DEPTH], bits: &[bool; DEPTH]) -> [BaseElement; DIGEST] {
    let mut node = native_commit(n);
    for d in 0..DEPTH {
        node = if bits[d] { native_merge(siblings[d], node) } else { native_merge(node, siblings[d]) };
    }
    node
}

// --- public inputs ----------------------------------------------------------------------------

#[derive(Clone)]
pub struct PublicInputs {
    pub root: [BaseElement; DIGEST],
    pub nf: [BaseElement; DIGEST],
    /// Transaction-binding digest (the tx sighash as field elements). It is not constrained in the
    /// trace; it is absorbed into the Fiat-Shamir transcript via `to_elements`, so a proof produced
    /// for one transaction fails to verify against any other (no proof lifting/replay across txs).
    pub tx_binding: [BaseElement; DIGEST],
}

impl ToElements<BaseElement> for PublicInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut v = self.root.to_vec();
        v.extend_from_slice(&self.nf);
        v.extend_from_slice(&self.tx_binding);
        v
    }
}

// --- AIR --------------------------------------------------------------------------------------

pub struct SpendAir {
    context: AirContext<BaseElement>,
    root: [BaseElement; DIGEST],
    nf: [BaseElement; DIGEST],
}

impl Air for SpendAir {
    type BaseField = BaseElement;
    type PublicInputs = PublicInputs;

    fn new(trace_info: TraceInfo, pub_inputs: PublicInputs, options: ProofOptions) -> Self {
        assert_eq!(WIDTH, trace_info.width());
        let mut degrees = Vec::with_capacity(N_CONSTRAINTS);
        // State slots: degree-7 round gated by the round/ARK (cycle 8) and boundary selectors (64).
        for _ in 0..STATE_WIDTH {
            degrees.push(TransitionConstraintDegree::with_cycles(7, vec![CYCLE, TRACE_LEN]));
        }
        degrees.push(TransitionConstraintDegree::new(1)); // rho constancy
        degrees.push(TransitionConstraintDegree::with_cycles(1, vec![TRACE_LEN])); // row-0 rho binding
        // Assertions: row-0 commitment capacity/pad (8) + root (4) + nf (4).
        let context = AirContext::new(trace_info, degrees, 16, options);
        SpendAir { context, root: pub_inputs.root, nf: pub_inputs.nf }
    }

    fn context(&self) -> &AirContext<BaseElement> {
        &self.context
    }

    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self,
        frame: &EvaluationFrame<E>,
        periodic: &[E],
        result: &mut [E],
    ) {
        let cur: &[E] = frame.current();
        let next: &[E] = frame.next();
        // periodic layout: [ARK1(12), ARK2(12), is_round, is_merge, is_null, is_first]
        let is_round = periodic[2 * STATE_WIDTH];
        let is_merge = periodic[2 * STATE_WIDTH + 1];
        let is_null = periodic[2 * STATE_WIDTH + 2];
        let is_first = periodic[2 * STATE_WIDTH + 3];
        let one = E::ONE;

        // Rescue round identity (degree 7).
        let mut sbox_cur = [E::ZERO; STATE_WIDTH];
        for i in 0..STATE_WIDTH {
            sbox_cur[i] = pow7(cur[i]);
        }
        let mds_sbox = mds_mul(&sbox_cur);
        let mut nm = [E::ZERO; STATE_WIDTH];
        for i in 0..STATE_WIDTH {
            nm[i] = next[i] - periodic[STATE_WIDTH + i]; // - ARK2
        }
        let pre = inv_mds_mul(&nm);

        let bit = next[BIT];
        let three = E::from(BaseElement::new(NULL_LEN as u64));
        let eight = E::from(BaseElement::new(8));

        for i in 0..STATE_WIDTH {
            let round_i = (mds_sbox[i] + periodic[i]) - pow7(pre[i]);

            // merge link: cap=8, running digest (cur[4..8]) placed left/right by bit, sibling free.
            let merge_i = if i == 0 {
                next[0] - eight
            } else if i < DIGEST {
                next[i]
            } else if i < 2 * DIGEST {
                let r = cur[i];
                (one - bit) * (next[i] - r) + bit * (next[i + DIGEST] - r)
            } else if i == 2 * DIGEST {
                bit * (one - bit)
            } else {
                E::ZERO
            };

            // nullifier load: cap=3, rate = [nk(free), rho(=persistent), pos(free)], pad 0.
            let null_i = if i == 0 {
                next[0] - three
            } else if i < DIGEST {
                next[i]
            } else if i == DIGEST + 1 {
                next[i] - cur[RHO] // rho bound to the persistent column
            } else if i == DIGEST || i == DIGEST + 2 {
                E::ZERO // nk, pos free
            } else {
                next[i] // pad slots 7..12 = 0
            };

            result[i] = is_round * round_i + is_merge * merge_i + is_null * null_i;
        }

        // rho persistence (all transitions) and the row-0 commitment-rho binding.
        result[STATE_WIDTH] = next[RHO] - cur[RHO];
        result[STATE_WIDTH + 1] = is_first * (cur[DIGEST + 2] - cur[RHO]); // cm rho at state[6] == persistent
    }

    fn get_periodic_column_values(&self) -> Vec<Vec<BaseElement>> {
        let ark1 = Rp64_256::ARK1;
        let ark2 = Rp64_256::ARK2;
        let mut cols = Vec::with_capacity(2 * STATE_WIDTH + 4);
        for j in 0..STATE_WIDTH {
            let mut c = vec![BaseElement::ZERO; CYCLE];
            for r in 0..NUM_ROUNDS {
                c[r] = ark1[r][j];
            }
            cols.push(c);
        }
        for j in 0..STATE_WIDTH {
            let mut c = vec![BaseElement::ZERO; CYCLE];
            for r in 0..NUM_ROUNDS {
                c[r] = ark2[r][j];
            }
            cols.push(c);
        }
        // is_round (period 8): 1 on the 7 round transitions, 0 on the block boundary.
        let mut is_round = vec![BaseElement::ONE; CYCLE];
        is_round[CYCLE - 1] = BaseElement::ZERO;
        cols.push(is_round);
        // boundary selectors (period = full trace).
        let mut is_merge = vec![BaseElement::ZERO; TRACE_LEN];
        let mut is_null = vec![BaseElement::ZERO; TRACE_LEN];
        let mut is_first = vec![BaseElement::ZERO; TRACE_LEN];
        for b in 0..DEPTH {
            is_merge[BLOCK * b + (BLOCK - 1)] = BaseElement::ONE; // boundaries loading merges 0..DEPTH-1
        }
        is_null[BLOCK * DEPTH + (BLOCK - 1)] = BaseElement::ONE; // boundary loading the nullifier block
        is_first[0] = BaseElement::ONE;
        cols.push(is_merge);
        cols.push(is_null);
        cols.push(is_first);
        cols
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let mut a = Vec::with_capacity(16);
        // Row-0 commitment input: state[0] = COMMIT_LEN, capacity[1..4] = 0, rate pad[8..12] = 0.
        a.push(Assertion::single(0, 0, BaseElement::new(COMMIT_LEN as u64)));
        for i in 1..DIGEST {
            a.push(Assertion::single(i, 0, BaseElement::ZERO));
        }
        for i in 2 * DIGEST..STATE_WIDTH {
            a.push(Assertion::single(i, 0, BaseElement::ZERO));
        }
        // Membership root (block DEPTH output) and nullifier (final block output).
        for i in 0..DIGEST {
            a.push(Assertion::single(DIGEST + i, ROOT_ROW, self.root[i]));
        }
        for i in 0..DIGEST {
            a.push(Assertion::single(DIGEST + i, NF_ROW, self.nf[i]));
        }
        a
    }
}

// --- Prover -----------------------------------------------------------------------------------

pub struct SpendProver {
    options: ProofOptions,
    tx_binding: [BaseElement; DIGEST],
}

impl SpendProver {
    pub fn new(options: ProofOptions, tx_binding: [BaseElement; DIGEST]) -> Self {
        Self { options, tx_binding }
    }

    /// Build the trace. `rho_in_null` lets tests inject an inconsistent nullifier `rho` to confirm
    /// the binding constraint bites; honest callers pass `note.rho`.
    fn build_trace_with(
        &self,
        note: Note,
        siblings: [[BaseElement; DIGEST]; DEPTH],
        bits: [bool; DEPTH],
        rho_in_null: BaseElement,
    ) -> TraceTable<BaseElement> {
        let mut trace = TraceTable::new(WIDTH, TRACE_LEN);

        let clear = |state: &mut [BaseElement]| {
            for s in state.iter_mut().take(STATE_WIDTH) {
                *s = BaseElement::ZERO;
            }
        };

        trace.fill(
            |state| {
                // Block 0: commitment input.
                for s in state.iter_mut() {
                    *s = BaseElement::ZERO;
                }
                state[0] = BaseElement::new(COMMIT_LEN as u64);
                state[4] = note.recipient;
                state[5] = note.value;
                state[6] = note.rho;
                state[7] = note.rcm;
                state[RHO] = note.rho; // persistent rho
            },
            |step, state| {
                let phase = step % BLOCK;
                let rho = state[RHO];
                if phase < NUM_ROUNDS {
                    let mut s: [BaseElement; STATE_WIDTH] = state[..STATE_WIDTH].try_into().unwrap();
                    Rp64_256::apply_round(&mut s, phase);
                    state[..STATE_WIDTH].copy_from_slice(&s);
                    state[RHO] = rho;
                } else {
                    let b = step / BLOCK;
                    if b < DEPTH {
                        // merge link: running digest = state[4..8]
                        let node: [BaseElement; DIGEST] = state[4..8].try_into().unwrap();
                        clear(state);
                        state[0] = BaseElement::new(8);
                        if bits[b] {
                            state[8..12].copy_from_slice(&node);
                            state[4..8].copy_from_slice(&siblings[b]);
                        } else {
                            state[4..8].copy_from_slice(&node);
                            state[8..12].copy_from_slice(&siblings[b]);
                        }
                        state[BIT] = if bits[b] { BaseElement::ONE } else { BaseElement::ZERO };
                        state[RHO] = rho;
                    } else {
                        // nullifier load
                        clear(state);
                        state[0] = BaseElement::new(NULL_LEN as u64);
                        state[4] = note.nk;
                        state[5] = rho_in_null;
                        state[6] = note.pos;
                        state[BIT] = BaseElement::ZERO;
                        state[RHO] = rho;
                    }
                }
            },
        );
        trace
    }

    pub fn build_trace(
        &self,
        note: Note,
        siblings: [[BaseElement; DIGEST]; DEPTH],
        bits: [bool; DEPTH],
    ) -> TraceTable<BaseElement> {
        self.build_trace_with(note, siblings, bits, note.rho)
    }
}

impl Prover for SpendProver {
    type BaseField = BaseElement;
    type Air = SpendAir;
    type Trace = TraceTable<BaseElement>;
    type HashFn = Hf;
    type VC = Vc;
    type RandomCoin = Coin;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Hf, Vc>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintEvaluator<'a, SpendAir, E>;
    type ConstraintCommitment<E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintCommitment<E, Hf, Vc>;

    fn get_pub_inputs(&self, trace: &Self::Trace) -> PublicInputs {
        let mut root = [BaseElement::ZERO; DIGEST];
        let mut nf = [BaseElement::ZERO; DIGEST];
        for i in 0..DIGEST {
            root[i] = trace.get(DIGEST + i, ROOT_ROW);
            nf[i] = trace.get(DIGEST + i, NF_ROW);
        }
        PublicInputs { root, nf, tx_binding: self.tx_binding }
    }

    fn options(&self) -> &ProofOptions {
        &self.options
    }

    fn new_trace_lde<E: FieldElement<BaseField = BaseElement>>(
        &self,
        trace_info: &TraceInfo,
        main_trace: &ColMatrix<BaseElement>,
        domain: &StarkDomain<BaseElement>,
        partition_option: PartitionOptions,
    ) -> (Self::TraceLde<E>, TracePolyTable<E>) {
        DefaultTraceLde::new(trace_info, main_trace, domain, partition_option)
    }

    fn new_evaluator<'a, E: FieldElement<BaseField = BaseElement>>(
        &self,
        air: &'a SpendAir,
        aux_rand_elements: Option<AuxRandElements<E>>,
        composition_coefficients: ConstraintCompositionCoefficients<E>,
    ) -> Self::ConstraintEvaluator<'a, E> {
        DefaultConstraintEvaluator::new(air, aux_rand_elements, composition_coefficients)
    }

    fn build_constraint_commitment<E: FieldElement<BaseField = BaseElement>>(
        &self,
        composition_poly_trace: CompositionPolyTrace<E>,
        num_constraint_composition_columns: usize,
        domain: &StarkDomain<BaseElement>,
        partition_options: PartitionOptions,
    ) -> (Self::ConstraintCommitment<E>, CompositionPoly<E>) {
        DefaultConstraintCommitment::new(
            composition_poly_trace,
            num_constraint_composition_columns,
            domain,
            partition_options,
        )
    }
}

// --- glue -------------------------------------------------------------------------------------

pub fn build_options() -> ProofOptions {
    ProofOptions::new(
        96,
        32,
        16,
        FieldExtension::Quadratic,
        8,
        63,
        BatchingMethod::Linear,
        BatchingMethod::Linear,
    )
}

pub fn prove_spend(
    note: Note,
    siblings: [[BaseElement; DIGEST]; DEPTH],
    bits: [bool; DEPTH],
    tx_binding: [BaseElement; DIGEST],
) -> (Proof, PublicInputs) {
    let prover = SpendProver::new(build_options(), tx_binding);
    let trace = prover.build_trace(note, siblings, bits);
    let pi = prover.get_pub_inputs(&trace);
    let proof = prover.prove(trace).expect("proving failed");
    (proof, pi)
}

pub fn verify_spend(proof: Proof, pi: PublicInputs) -> Result<(), String> {
    let acceptable = winterfell::AcceptableOptions::OptionSet(vec![build_options()]);
    winterfell::verify::<SpendAir, Hf, Coin, Vc>(proof, pi, &acceptable).map_err(|e| format!("{e}"))
}

// --- tests ------------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> (Note, [[BaseElement; DIGEST]; DEPTH], [bool; DEPTH]) {
        let note = Note {
            recipient: BaseElement::new(0xABCD),
            value: BaseElement::new(1000),
            rho: BaseElement::new(0x1111_2222),
            rcm: BaseElement::new(0x3333_4444),
            nk: BaseElement::new(0x5555_6666),
            pos: BaseElement::new(42),
        };
        let mut sib = [[BaseElement::ZERO; DIGEST]; DEPTH];
        let mut bits = [false; DEPTH];
        for d in 0..DEPTH {
            for k in 0..DIGEST {
                sib[d][k] = BaseElement::new((d * 10 + k + 1) as u64);
            }
            bits[d] = d % 2 == 1;
        }
        (note, sib, bits)
    }

    fn txb() -> [BaseElement; DIGEST] {
        [BaseElement::new(7), BaseElement::new(8), BaseElement::new(9), BaseElement::new(10)]
    }

    #[test]
    fn trace_matches_native_oracles() {
        let (note, sib, bits) = sample();
        let prover = SpendProver::new(build_options(), txb());
        let trace = prover.build_trace(note, sib, bits);
        let pi = prover.get_pub_inputs(&trace);
        assert_eq!(pi.root, native_root(note, &sib, &bits));
        assert_eq!(pi.nf, native_nullifier(note));
    }

    #[test]
    fn valid_spend_verifies() {
        let (note, sib, bits) = sample();
        let (proof, pi) = prove_spend(note, sib, bits, txb());
        assert!(verify_spend(proof, pi).is_ok());
    }

    #[test]
    fn wrong_root_rejected() {
        let (note, sib, bits) = sample();
        let (proof, mut pi) = prove_spend(note, sib, bits, txb());
        pi.root[0] += BaseElement::ONE;
        assert!(verify_spend(proof, pi).is_err());
    }

    #[test]
    fn wrong_nullifier_rejected() {
        let (note, sib, bits) = sample();
        let (proof, mut pi) = prove_spend(note, sib, bits, txb());
        pi.nf[0] += BaseElement::ONE;
        assert!(verify_spend(proof, pi).is_err());
    }

    #[test]
    fn tampered_value_changes_root() {
        let (note, sib, bits) = sample();
        let real_root = native_root(note, &sib, &bits);
        let mut bad = note;
        bad.value += BaseElement::ONE;
        let (proof, pi) = prove_spend(bad, sib, bits, txb());
        assert_ne!(pi.root, real_root);
        let claim = PublicInputs { root: real_root, nf: pi.nf.clone(), tx_binding: pi.tx_binding };
        assert!(verify_spend(proof, claim).is_err());
    }

    #[test]
    fn inconsistent_rho_rejected() {
        // Build a trace where the nullifier uses a different rho than the commitment; the
        // persistent-rho binding must reject it.
        let (note, sib, bits) = sample();
        let prover = SpendProver::new(build_options(), txb());
        let trace = prover.build_trace_with(note, sib, bits, note.rho + BaseElement::ONE);
        let pi = prover.get_pub_inputs(&trace);
        // Proving may still succeed (prover doesn't check), but verification must fail.
        match prover.prove(trace) {
            Ok(proof) => assert!(verify_spend(proof, pi).is_err()),
            Err(_) => {} // a fail-stop in proving is also acceptable
        }
    }

    #[test]
    fn wrong_tx_binding_rejected() {
        // A proof produced for one tx-binding must not verify against another (no proof lifting).
        let (note, sib, bits) = sample();
        let (proof, mut pi) = prove_spend(note, sib, bits, txb());
        pi.tx_binding[0] += BaseElement::ONE;
        assert!(verify_spend(proof, pi).is_err());
    }
}
