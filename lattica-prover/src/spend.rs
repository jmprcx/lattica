//! Commitment + membership + nullifier + value-balance + range + **ownership** — the Phase-2
//! spend statement.
//!
//! One Winterfell proof attests, for public `(root, nf, out_cm, tx_binding, fee)` and a private
//! note + output:
//!   0. **ownership**  `recipient = H(nk)[0]`                          (block 0)
//!   1. **commitment** `cm = H(recipient, value, rho, rcm)`            (block 1)
//!   2. **membership** `cm` folds up a general-position path to `root` (blocks 2..=DEPTH+1)
//!   3. **nullifier**  `nf = H(nk, rho, pos)`                          (block DEPTH+2)
//!   4. **output commitment** `out_cm = H(out_recipient, out_value, out_rho, out_rcm)`
//!   5. **value-balance** `value = out_value + fee`
//!   6. **range** `value, out_value < 2^BITS`
//!   7. **tx-binding** via Fiat-Shamir.
//! The input note's `recipient` is derived from the spender's key `nk`, and the **same `nk`** drives
//! the nullifier — so only the owner of `nk` can spend the note, and the nullifier is bound to that
//! owner. The **same `rho`** is used in (1) and (3).
//!
//! Cross-region binding uses **persistent columns** (constant across the trace): `rho`, `value`,
//! `out_value`, `nk`; `recipient` flows ownership→commitment by adjacency. Two parallel `rem`
//! columns carry the range decompositions. Per-boundary periodic selectors gate
//! round / commit-load / merge-link / nullifier-load / output-load / row-0 / range.
//!
//! Validated against native oracles: `recipient`/`cm`/`nf`/`out_cm` match the native hashes; the
//! AIR `root`/`nf`/`out_cm` match; valid-verifies; wrong root/nf/out_cm, tampered opening,
//! inconsistent `rho`, **wrong `nk`** (ownership), unbalanced, out-of-range, and wrong tx-binding
//! are all rejected.
//!
//! Scope (Codex audit precedes production): `recipient = H(nk)[0]` is a single field element (a
//! demo-strength owner binding; production uses the full 4-element digest). `nk`/`pos` are single
//! elements; `BITS=31`, `DEPTH=4`. Remaining: position-consistency (nullifier `pos` ↔ path),
//! `mint`/`burn` issuance, depth 32, production parameters.

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

pub const DEPTH: usize = 4; // membership levels (production 32; needs a block-count pad decision)
pub const DIGEST: usize = 4;
pub const COMMIT_LEN: usize = 4; // [recipient, value, rho, rcm]
pub const NULL_LEN: usize = 3; // [nk, rho, pos]
pub const OWN_LEN: usize = 1; // [nk]
const BLOCK: usize = 8;
// columns: 0..12 state, 12 bit, 13 rho, 14 value, 15 out_value, 16 nk, 17 rem_in, 18 rem_out
const WIDTH: usize = STATE_WIDTH + 7; // 19
const BIT: usize = STATE_WIDTH; // 12
const RHO: usize = STATE_WIDTH + 1; // 13
const VAL: usize = STATE_WIDTH + 2; // 14
const OUTVAL: usize = STATE_WIDTH + 3; // 15
const NK: usize = STATE_WIDTH + 4; // 16
const REM_IN: usize = STATE_WIDTH + 5; // 17
const REM_OUT: usize = STATE_WIDTH + 6; // 18
const BITS: usize = 31;
const NUM_BLOCKS: usize = DEPTH + 4; // ownership + commitment + DEPTH merges + nullifier + output
const TRACE_LEN: usize = BLOCK * NUM_BLOCKS;
const ROOT_ROW: usize = BLOCK * (DEPTH + 2) - 1; // last membership block output
const NF_ROW: usize = BLOCK * (DEPTH + 3) - 1; // nullifier block output
const OUT_CM_ROW: usize = TRACE_LEN - 1; // output-commitment block output
const RECIP_SLOT: usize = 4;
const VALUE_SLOT: usize = 5;
const RHO_SLOT: usize = 6;
const N_CONSTRAINTS: usize = STATE_WIDTH + 10; // 12 state + 4 constancy + 4 row-0 + 2 range

#[derive(Clone, Copy)]
pub struct Note {
    pub value: BaseElement,
    pub rho: BaseElement,
    pub rcm: BaseElement,
    pub nk: BaseElement, // input note's recipient is derived as H(nk)[0]
    pub pos: BaseElement,
    pub out_recipient: BaseElement,
    pub out_value: BaseElement,
    pub out_rho: BaseElement,
    pub out_rcm: BaseElement,
}

// --- native oracles ---------------------------------------------------------------------------

fn hash_n(elems: &[BaseElement]) -> [BaseElement; DIGEST] {
    let mut state = [BaseElement::ZERO; STATE_WIDTH];
    state[0] = BaseElement::new(elems.len() as u64);
    state[4..4 + elems.len()].copy_from_slice(elems);
    Rp64_256::apply_permutation(&mut state);
    state[4..8].try_into().unwrap()
}
/// Owner binding: recipient = first element of H(nk).
pub fn native_owner(nk: BaseElement) -> BaseElement {
    hash_n(&[nk])[0]
}
pub fn native_commit(n: Note) -> [BaseElement; DIGEST] {
    hash_n(&[native_owner(n.nk), n.value, n.rho, n.rcm])
}
pub fn native_out_commit(n: Note) -> [BaseElement; DIGEST] {
    hash_n(&[n.out_recipient, n.out_value, n.out_rho, n.out_rcm])
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
    pub out_cm: [BaseElement; DIGEST],
    pub tx_binding: [BaseElement; DIGEST],
    pub fee: BaseElement,
}

impl ToElements<BaseElement> for PublicInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut v = self.root.to_vec();
        v.extend_from_slice(&self.nf);
        v.extend_from_slice(&self.out_cm);
        v.extend_from_slice(&self.tx_binding);
        v.push(self.fee);
        v
    }
}

// --- AIR --------------------------------------------------------------------------------------

pub struct SpendAir {
    context: AirContext<BaseElement>,
    root: [BaseElement; DIGEST],
    nf: [BaseElement; DIGEST],
    out_cm: [BaseElement; DIGEST],
    fee: BaseElement,
}

impl Air for SpendAir {
    type BaseField = BaseElement;
    type PublicInputs = PublicInputs;

    fn new(trace_info: TraceInfo, pub_inputs: PublicInputs, options: ProofOptions) -> Self {
        assert_eq!(WIDTH, trace_info.width());
        let mut degrees = Vec::with_capacity(N_CONSTRAINTS);
        for _ in 0..STATE_WIDTH {
            degrees.push(TransitionConstraintDegree::with_cycles(7, vec![CYCLE, TRACE_LEN]));
        }
        for _ in 0..4 {
            degrees.push(TransitionConstraintDegree::new(1)); // rho/value/out_value/nk persistence
        }
        for _ in 0..4 {
            degrees.push(TransitionConstraintDegree::with_cycles(1, vec![TRACE_LEN])); // row-0 binds
        }
        for _ in 0..2 {
            degrees.push(TransitionConstraintDegree::with_cycles(2, vec![TRACE_LEN])); // range bits
        }
        // Assertions: row-0 ownership cap/pad (11) + root (4) + nf (4) + out_cm (4) + rem tails (2) = 25.
        let context = AirContext::new(trace_info, degrees, 25, options);
        SpendAir {
            context,
            root: pub_inputs.root,
            nf: pub_inputs.nf,
            out_cm: pub_inputs.out_cm,
            fee: pub_inputs.fee,
        }
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
        // periodic: [ARK1(12), ARK2(12), is_round, is_commitload, is_merge, is_null, is_out, is_first, is_range]
        let is_round = periodic[2 * STATE_WIDTH];
        let is_commit = periodic[2 * STATE_WIDTH + 1];
        let is_merge = periodic[2 * STATE_WIDTH + 2];
        let is_null = periodic[2 * STATE_WIDTH + 3];
        let is_out = periodic[2 * STATE_WIDTH + 4];
        let is_first = periodic[2 * STATE_WIDTH + 5];
        let is_range = periodic[2 * STATE_WIDTH + 6];
        let one = E::ONE;

        let mut sbox_cur = [E::ZERO; STATE_WIDTH];
        for i in 0..STATE_WIDTH {
            sbox_cur[i] = pow7(cur[i]);
        }
        let mds_sbox = mds_mul(&sbox_cur);
        let mut nm = [E::ZERO; STATE_WIDTH];
        for i in 0..STATE_WIDTH {
            nm[i] = next[i] - periodic[STATE_WIDTH + i];
        }
        let pre = inv_mds_mul(&nm);

        let bit = next[BIT];
        let eight = E::from(BaseElement::new(8));
        let three = E::from(BaseElement::new(NULL_LEN as u64));
        let four = E::from(BaseElement::new(COMMIT_LEN as u64));

        for i in 0..STATE_WIDTH {
            let round_i = (mds_sbox[i] + periodic[i]) - pow7(pre[i]);

            // commit-load (ownership→commitment): cap=4, recipient = ownership output[4] (adjacency),
            // value/rho bound to persistent columns, rcm free, pad 0.
            let commit_i = if i == 0 {
                next[0] - four
            } else if i < DIGEST {
                next[i]
            } else if i == RECIP_SLOT {
                next[RECIP_SLOT] - cur[RECIP_SLOT]
            } else if i == VALUE_SLOT {
                next[VALUE_SLOT] - cur[VAL]
            } else if i == RHO_SLOT {
                next[RHO_SLOT] - cur[RHO]
            } else if i == 7 {
                E::ZERO // rcm free
            } else {
                next[i] // pad 8..12
            };

            // merge link: cap=8, running digest cur[4..8] placed by bit, sibling free.
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

            // nullifier load: cap=3, [nk(=persistent), rho(=persistent), pos(free)], pad 0.
            let null_i = if i == 0 {
                next[0] - three
            } else if i < DIGEST {
                next[i]
            } else if i == DIGEST {
                next[DIGEST] - cur[NK] // nk bound to the same owner key
            } else if i == DIGEST + 1 {
                next[DIGEST + 1] - cur[RHO] // rho bound
            } else if i == DIGEST + 2 {
                E::ZERO // pos free
            } else {
                next[i]
            };

            // output-commitment load: cap=4, [out_recipient(free), out_value(=persistent),
            // out_rho(free), out_rcm(free)], pad 0.
            let out_i = if i == 0 {
                next[0] - four
            } else if i < DIGEST {
                next[i]
            } else if i == DIGEST + 1 {
                next[DIGEST + 1] - cur[OUTVAL]
            } else if i == DIGEST || i == DIGEST + 2 || i == DIGEST + 3 {
                E::ZERO
            } else {
                next[i]
            };

            result[i] = is_round * round_i
                + is_commit * commit_i
                + is_merge * merge_i
                + is_null * null_i
                + is_out * out_i;
        }

        // Persistence of the witness-carrying columns.
        result[STATE_WIDTH] = next[RHO] - cur[RHO];
        result[STATE_WIDTH + 1] = next[VAL] - cur[VAL];
        result[STATE_WIDTH + 2] = next[OUTVAL] - cur[OUTVAL];
        result[STATE_WIDTH + 3] = next[NK] - cur[NK];

        // Row-0 bindings (is_first): ownership nk pinned to its persistent column, value-balance,
        // and the range seeds.
        let fee = E::from(self.fee);
        result[STATE_WIDTH + 4] = is_first * (cur[RECIP_SLOT] - cur[NK]); // ownership input nk == nk col
        result[STATE_WIDTH + 5] = is_first * (cur[VAL] - cur[OUTVAL] - fee);
        result[STATE_WIDTH + 6] = is_first * (cur[REM_IN] - cur[VAL]);
        result[STATE_WIDTH + 7] = is_first * (cur[REM_OUT] - cur[OUTVAL]);

        // Range bit-booleans.
        let bit_in = cur[REM_IN] - E::from(BaseElement::new(2)) * next[REM_IN];
        let bit_out = cur[REM_OUT] - E::from(BaseElement::new(2)) * next[REM_OUT];
        result[STATE_WIDTH + 8] = is_range * (bit_in * (bit_in - one));
        result[STATE_WIDTH + 9] = is_range * (bit_out * (bit_out - one));
    }

    fn get_periodic_column_values(&self) -> Vec<Vec<BaseElement>> {
        let ark1 = Rp64_256::ARK1;
        let ark2 = Rp64_256::ARK2;
        let mut cols = Vec::with_capacity(2 * STATE_WIDTH + 7);
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
        let mut is_round = vec![BaseElement::ONE; CYCLE];
        is_round[CYCLE - 1] = BaseElement::ZERO;
        cols.push(is_round);

        let mut is_commit = vec![BaseElement::ZERO; TRACE_LEN];
        let mut is_merge = vec![BaseElement::ZERO; TRACE_LEN];
        let mut is_null = vec![BaseElement::ZERO; TRACE_LEN];
        let mut is_out = vec![BaseElement::ZERO; TRACE_LEN];
        let mut is_first = vec![BaseElement::ZERO; TRACE_LEN];
        let mut is_range = vec![BaseElement::ZERO; TRACE_LEN];
        // boundary b -> row BLOCK*b + (BLOCK-1)
        is_commit[BLOCK - 1] = BaseElement::ONE; // b=0: ownership -> commitment
        for b in 1..=DEPTH {
            is_merge[BLOCK * b + (BLOCK - 1)] = BaseElement::ONE; // b=1..DEPTH: load membership blocks
        }
        is_null[BLOCK * (DEPTH + 1) + (BLOCK - 1)] = BaseElement::ONE; // load nullifier
        is_out[BLOCK * (DEPTH + 2) + (BLOCK - 1)] = BaseElement::ONE; // load output commitment
        is_first[0] = BaseElement::ONE;
        for r in 0..BITS {
            is_range[r] = BaseElement::ONE;
        }
        cols.push(is_commit);
        cols.push(is_merge);
        cols.push(is_null);
        cols.push(is_out);
        cols.push(is_first);
        cols.push(is_range);
        cols
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let mut a = Vec::with_capacity(25);
        // Row-0 ownership input: cap=1, capacity[1..4]=0, rate pad[5..12]=0 (only state[4]=nk free).
        a.push(Assertion::single(0, 0, BaseElement::new(OWN_LEN as u64)));
        for i in 1..DIGEST {
            a.push(Assertion::single(i, 0, BaseElement::ZERO));
        }
        for i in (DIGEST + 1)..STATE_WIDTH {
            a.push(Assertion::single(i, 0, BaseElement::ZERO));
        }
        for i in 0..DIGEST {
            a.push(Assertion::single(DIGEST + i, ROOT_ROW, self.root[i]));
        }
        for i in 0..DIGEST {
            a.push(Assertion::single(DIGEST + i, NF_ROW, self.nf[i]));
        }
        for i in 0..DIGEST {
            a.push(Assertion::single(DIGEST + i, OUT_CM_ROW, self.out_cm[i]));
        }
        a.push(Assertion::single(REM_IN, BITS, BaseElement::ZERO));
        a.push(Assertion::single(REM_OUT, BITS, BaseElement::ZERO));
        a
    }
}

// --- Prover -----------------------------------------------------------------------------------

pub struct SpendProver {
    options: ProofOptions,
    tx_binding: [BaseElement; DIGEST],
    fee: BaseElement,
}

impl SpendProver {
    pub fn new(options: ProofOptions, tx_binding: [BaseElement; DIGEST], fee: BaseElement) -> Self {
        Self { options, tx_binding, fee }
    }

    fn build_trace_with(
        &self,
        note: Note,
        siblings: [[BaseElement; DIGEST]; DEPTH],
        bits: [bool; DEPTH],
        rho_in_null: BaseElement,
    ) -> TraceTable<BaseElement> {
        let mut trace = TraceTable::new(WIDTH, TRACE_LEN);
        let value_u64 = note.value.as_int();
        let out_value_u64 = note.out_value.as_int();
        let clear = |state: &mut [BaseElement]| {
            for s in state.iter_mut().take(STATE_WIDTH) {
                *s = BaseElement::ZERO;
            }
        };
        trace.fill(
            |state| {
                for s in state.iter_mut() {
                    *s = BaseElement::ZERO;
                }
                // ownership input: hash_elements([nk])
                state[0] = BaseElement::new(OWN_LEN as u64);
                state[4] = note.nk;
                // persistent columns + range seeds
                state[RHO] = note.rho;
                state[VAL] = note.value;
                state[OUTVAL] = note.out_value;
                state[NK] = note.nk;
                state[REM_IN] = note.value;
                state[REM_OUT] = note.out_value;
            },
            |step, state| {
                let phase = step % BLOCK;
                let (rho, val, outv, nk) = (state[RHO], state[VAL], state[OUTVAL], state[NK]);
                if phase < NUM_ROUNDS {
                    let mut s: [BaseElement; STATE_WIDTH] = state[..STATE_WIDTH].try_into().unwrap();
                    Rp64_256::apply_round(&mut s, phase);
                    state[..STATE_WIDTH].copy_from_slice(&s);
                } else {
                    let b = step / BLOCK;
                    if b == 0 {
                        // commit-load: recipient = ownership output[4]; value/rho/rcm.
                        let recipient = state[4];
                        clear(state);
                        state[0] = BaseElement::new(COMMIT_LEN as u64);
                        state[RECIP_SLOT] = recipient;
                        state[VALUE_SLOT] = val;
                        state[RHO_SLOT] = rho;
                        state[7] = note.rcm;
                    } else if b <= DEPTH {
                        // merge link (load membership level b-1).
                        let level = b - 1;
                        let node: [BaseElement; DIGEST] = state[4..8].try_into().unwrap();
                        clear(state);
                        state[0] = BaseElement::new(8);
                        if bits[level] {
                            state[8..12].copy_from_slice(&node);
                            state[4..8].copy_from_slice(&siblings[level]);
                        } else {
                            state[4..8].copy_from_slice(&node);
                            state[8..12].copy_from_slice(&siblings[level]);
                        }
                        state[BIT] = if bits[level] { BaseElement::ONE } else { BaseElement::ZERO };
                    } else if b == DEPTH + 1 {
                        // nullifier load
                        clear(state);
                        state[0] = BaseElement::new(NULL_LEN as u64);
                        state[4] = nk;
                        state[5] = rho_in_null;
                        state[6] = note.pos;
                    } else {
                        // output-commitment load
                        clear(state);
                        state[0] = BaseElement::new(COMMIT_LEN as u64);
                        state[4] = note.out_recipient;
                        state[5] = note.out_value;
                        state[6] = note.out_rho;
                        state[7] = note.out_rcm;
                    }
                }
                state[RHO] = rho;
                state[VAL] = val;
                state[OUTVAL] = outv;
                state[NK] = nk;
                let row = step + 1;
                state[REM_IN] = BaseElement::new(value_u64 >> row);
                state[REM_OUT] = BaseElement::new(out_value_u64 >> row);
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
        let mut out_cm = [BaseElement::ZERO; DIGEST];
        for i in 0..DIGEST {
            root[i] = trace.get(DIGEST + i, ROOT_ROW);
            nf[i] = trace.get(DIGEST + i, NF_ROW);
            out_cm[i] = trace.get(DIGEST + i, OUT_CM_ROW);
        }
        PublicInputs { root, nf, out_cm, tx_binding: self.tx_binding, fee: self.fee }
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
    fee: BaseElement,
) -> (Proof, PublicInputs) {
    let prover = SpendProver::new(build_options(), tx_binding, fee);
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
            value: BaseElement::new(1000),
            rho: BaseElement::new(0x1111_2222),
            rcm: BaseElement::new(0x3333_4444),
            nk: BaseElement::new(0x5555_6666),
            pos: BaseElement::new(42),
            out_recipient: BaseElement::new(0xBEEF),
            out_value: BaseElement::new(900),
            out_rho: BaseElement::new(0x7777),
            out_rcm: BaseElement::new(0x8888),
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

    fn fee() -> BaseElement {
        BaseElement::new(100)
    }

    #[test]
    fn trace_matches_native_oracles() {
        let (note, sib, bits) = sample();
        let prover = SpendProver::new(build_options(), txb(), fee());
        let trace = prover.build_trace(note, sib, bits);
        let pi = prover.get_pub_inputs(&trace);
        assert_eq!(pi.root, native_root(note, &sib, &bits));
        assert_eq!(pi.nf, native_nullifier(note));
        assert_eq!(pi.out_cm, native_out_commit(note));
    }

    #[test]
    fn valid_spend_verifies() {
        let (note, sib, bits) = sample();
        let (proof, pi) = prove_spend(note, sib, bits, txb(), fee());
        assert!(verify_spend(proof, pi).is_ok());
    }

    #[test]
    fn wrong_root_rejected() {
        let (note, sib, bits) = sample();
        let (proof, mut pi) = prove_spend(note, sib, bits, txb(), fee());
        pi.root[0] += BaseElement::ONE;
        assert!(verify_spend(proof, pi).is_err());
    }

    #[test]
    fn wrong_out_cm_rejected() {
        let (note, sib, bits) = sample();
        let (proof, mut pi) = prove_spend(note, sib, bits, txb(), fee());
        pi.out_cm[0] += BaseElement::ONE;
        assert!(verify_spend(proof, pi).is_err());
    }

    #[test]
    fn unbalanced_rejected() {
        let (mut note, sib, bits) = sample();
        note.value = BaseElement::new(1001); // 900 + 100 != 1001
        let prover = SpendProver::new(build_options(), txb(), fee());
        let trace = prover.build_trace(note, sib, bits);
        let pi = prover.get_pub_inputs(&trace);
        match prover.prove(trace) {
            Ok(proof) => assert!(verify_spend(proof, pi).is_err()),
            Err(_) => {}
        }
    }

    #[test]
    fn inconsistent_rho_rejected() {
        let (note, sib, bits) = sample();
        let prover = SpendProver::new(build_options(), txb(), fee());
        let trace = prover.build_trace_with(note, sib, bits, note.rho + BaseElement::ONE);
        let pi = prover.get_pub_inputs(&trace);
        match prover.prove(trace) {
            Ok(proof) => assert!(verify_spend(proof, pi).is_err()),
            Err(_) => {}
        }
    }

    #[test]
    fn wrong_nk_breaks_membership() {
        // The recipient is H(nk)[0]; the tree was built (native_root) with the true nk, so the
        // public root encodes a commitment to recipient = H(nk)[0]. Proving with a different nk
        // changes recipient -> cm -> root, so the proof no longer attests membership under the
        // claimed root. (Ownership is bound into the commitment.)
        let (note, sib, bits) = sample();
        let real_root = native_root(note, &sib, &bits);
        let mut other = note;
        other.nk = note.nk + BaseElement::ONE;
        let (proof, pi) = prove_spend(other, sib, bits, txb(), fee());
        assert_ne!(pi.root, real_root);
        let claim = PublicInputs { root: real_root, ..pi.clone() };
        assert!(verify_spend(proof, claim).is_err());
    }

    #[test]
    fn wrong_tx_binding_rejected() {
        let (note, sib, bits) = sample();
        let (proof, mut pi) = prove_spend(note, sib, bits, txb(), fee());
        pi.tx_binding[0] += BaseElement::ONE;
        assert!(verify_spend(proof, pi).is_err());
    }

    #[test]
    fn out_of_range_value_rejected() {
        let (mut note, sib, bits) = sample();
        note.value = BaseElement::new(1u64 << 31);
        note.out_value = BaseElement::new((1u64 << 31) - 100);
        let prover = SpendProver::new(build_options(), txb(), fee());
        let trace = prover.build_trace(note, sib, bits);
        let pi = prover.get_pub_inputs(&trace);
        match prover.prove(trace) {
            Ok(proof) => assert!(verify_spend(proof, pi).is_err()),
            Err(_) => {}
        }
    }
}
