//! Commitment-opening + membership — Phase 2 spend core (audit C-01/C-03 foundation).
//!
//! Proves, for a public `root`, knowledge of a **private note opening** whose Rescue-Prime
//! commitment `cm = H(recipient, value, rho, rcm)` is a member of the tree under `root`. The
//! opening and path stay private. This binds the *committed* note to the *membership leaf*: the
//! committed value is the one in the tree (not an unrelated leaf).
//!
//! Layout: block 0 is the commitment permutation (`hash_elements` of the 4-element opening:
//! `state[0]=4`, rate = opening, pad 0, permute, `cm = state[4..8]`). Blocks 1..=DEPTH are the
//! membership merges, with the running leaf for block 1 being block-0's output `cm` — so the
//! commitment→leaf binding reuses the same link constraint as the membership chain.
//!
//! Validated against native oracles: `native_commit` equals `Rp64_256::hash_elements`; the AIR
//! trace root equals the native fold of `cm`; valid-verifies; wrong-root and a tampered opening
//! (different `cm` ⇒ different root) rejected.
//!
//! Audit note: `recipient` is one field element here (a demo binding; production uses a 4-element
//! recipient digest — still ≤ rate, one permutation). `DEPTH=7` gives 8 blocks (a power-of-two
//! trace); production depth 32 needs a block-count padding decision. The opening is unconstrained
//! beyond the commitment (ownership / value-balance / nullifier are the next Phase-2 items). Codex
//! audit precedes production wiring.

use winterfell::{
    math::{fields::f64::BaseElement, FieldElement, ToElements},
    matrix::ColMatrix,
    Air, AirContext, Assertion, AuxRandElements, BatchingMethod, CompositionPoly,
    CompositionPolyTrace, ConstraintCompositionCoefficients, DefaultConstraintCommitment,
    DefaultConstraintEvaluator, DefaultTraceLde, EvaluationFrame, FieldExtension, PartitionOptions,
    Proof, ProofOptions, Prover, StarkDomain, Trace, TraceInfo, TracePolyTable, TraceTable,
    TransitionConstraintDegree,
};
use winterfell::crypto::hashers::Rp64_256;

use crate::{inv_mds_mul, mds_mul, pow7, Coin, Hf, Vc, CYCLE, NUM_ROUNDS, STATE_WIDTH};

pub const DEPTH: usize = 7; // membership levels (production 32; see header on block-count padding)
pub const DIGEST: usize = 4;
pub const OPENING_LEN: usize = 4; // [recipient, value, rho, rcm]
const BLOCK: usize = 8;
const WIDTH: usize = STATE_WIDTH + 1; // 12 state + 1 position bit
const BIT: usize = STATE_WIDTH;
const NUM_BLOCKS: usize = DEPTH + 1; // block 0 = commitment, 1..=DEPTH = merges
const TRACE_LEN: usize = BLOCK * NUM_BLOCKS;

/// The full note opening (each element a field element; `recipient` is one element here).
#[derive(Clone, Copy)]
pub struct Opening {
    pub recipient: BaseElement,
    pub value: BaseElement,
    pub rho: BaseElement,
    pub rcm: BaseElement,
}

impl Opening {
    fn elems(&self) -> [BaseElement; OPENING_LEN] {
        [self.recipient, self.value, self.rho, self.rcm]
    }
}

// --- native oracles ---------------------------------------------------------------------------

/// `cm = H(opening)` exactly as `Rp64_256::hash_elements` does it for a 4-element input.
pub fn native_commit(opening: Opening) -> [BaseElement; DIGEST] {
    let mut state = [BaseElement::ZERO; STATE_WIDTH];
    state[0] = BaseElement::new(OPENING_LEN as u64);
    state[4..4 + OPENING_LEN].copy_from_slice(&opening.elems());
    Rp64_256::apply_permutation(&mut state);
    state[4..8].try_into().unwrap()
}

fn native_merge(left: [BaseElement; DIGEST], right: [BaseElement; DIGEST]) -> [BaseElement; DIGEST] {
    let mut state = [BaseElement::ZERO; STATE_WIDTH];
    state[0] = BaseElement::new(8);
    state[4..8].copy_from_slice(&left);
    state[8..12].copy_from_slice(&right);
    Rp64_256::apply_permutation(&mut state);
    state[4..8].try_into().unwrap()
}

pub fn native_root(opening: Opening, siblings: &[[BaseElement; DIGEST]; DEPTH], bits: &[bool; DEPTH]) -> [BaseElement; DIGEST] {
    let mut node = native_commit(opening);
    for d in 0..DEPTH {
        node = if bits[d] { native_merge(siblings[d], node) } else { native_merge(node, siblings[d]) };
    }
    node
}

// --- public inputs ----------------------------------------------------------------------------

#[derive(Clone)]
pub struct PublicInputs {
    pub root: [BaseElement; DIGEST],
}

impl ToElements<BaseElement> for PublicInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        self.root.to_vec()
    }
}

// --- AIR --------------------------------------------------------------------------------------

pub struct SpendAir {
    context: AirContext<BaseElement>,
    root: [BaseElement; DIGEST],
}

impl Air for SpendAir {
    type BaseField = BaseElement;
    type PublicInputs = PublicInputs;

    fn new(trace_info: TraceInfo, pub_inputs: PublicInputs, options: ProofOptions) -> Self {
        assert_eq!(WIDTH, trace_info.width());
        let degrees =
            vec![TransitionConstraintDegree::with_cycles(7, vec![CYCLE, CYCLE]); STATE_WIDTH];
        // Assertions: row-0 commitment capacity/pad (8) + final-row digest = root (4).
        let context = AirContext::new(trace_info, degrees, 12, options);
        SpendAir { context, root: pub_inputs.root }
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
        let is_round = periodic[2 * STATE_WIDTH];
        let is_link = E::ONE - is_round;

        // Rescue round identity.
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

        // Link load (block boundary): reset capacity to 8, place running digest left/right by the
        // bit, sibling free, bit boolean. (Block-0 output cm is the running leaf for block 1.)
        let bit = next[BIT];
        let one = E::ONE;
        for i in 0..STATE_WIDTH {
            let round_i = (mds_sbox[i] + periodic[i]) - pow7(pre[i]);
            let link_i = if i == 0 {
                next[0] - E::from(BaseElement::new(8))
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
            result[i] = is_round * round_i + is_link * link_i;
        }
    }

    fn get_periodic_column_values(&self) -> Vec<Vec<BaseElement>> {
        let ark1 = Rp64_256::ARK1;
        let ark2 = Rp64_256::ARK2;
        let mut cols = Vec::with_capacity(2 * STATE_WIDTH + 1);
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
        let mut sel = vec![BaseElement::ONE; CYCLE];
        sel[CYCLE - 1] = BaseElement::ZERO;
        cols.push(sel);
        cols
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let last = self.trace_length() - 1;
        let mut a = Vec::with_capacity(12);
        // Block-0 commitment input: state[0] = OPENING_LEN, capacity[1..4] = 0, rate pad[8..12] = 0.
        a.push(Assertion::single(0, 0, BaseElement::new(OPENING_LEN as u64)));
        for i in 1..DIGEST {
            a.push(Assertion::single(i, 0, BaseElement::ZERO));
        }
        for i in 2 * DIGEST..STATE_WIDTH {
            a.push(Assertion::single(i, 0, BaseElement::ZERO));
        }
        // Final digest = public root.
        for i in 0..DIGEST {
            a.push(Assertion::single(DIGEST + i, last, self.root[i]));
        }
        a
    }
}

// --- Prover -----------------------------------------------------------------------------------

pub struct SpendProver {
    options: ProofOptions,
}

impl SpendProver {
    pub fn new(options: ProofOptions) -> Self {
        Self { options }
    }

    pub fn build_trace(
        &self,
        opening: Opening,
        siblings: [[BaseElement; DIGEST]; DEPTH],
        bits: [bool; DEPTH],
    ) -> TraceTable<BaseElement> {
        let mut trace = TraceTable::new(WIDTH, TRACE_LEN);

        let load_merge = |state: &mut [BaseElement], node: [BaseElement; DIGEST], level: usize| {
            for s in state.iter_mut().take(STATE_WIDTH) {
                *s = BaseElement::ZERO;
            }
            state[0] = BaseElement::new(8);
            if bits[level] {
                state[8..12].copy_from_slice(&node);
                state[4..8].copy_from_slice(&siblings[level]);
            } else {
                state[4..8].copy_from_slice(&node);
                state[8..12].copy_from_slice(&siblings[level]);
            }
            state[BIT] = if bits[level] { BaseElement::ONE } else { BaseElement::ZERO };
        };

        trace.fill(
            |state| {
                // Block 0: commitment input (hash_elements layout for OPENING_LEN elements).
                for s in state.iter_mut() {
                    *s = BaseElement::ZERO;
                }
                state[0] = BaseElement::new(OPENING_LEN as u64);
                state[4..4 + OPENING_LEN].copy_from_slice(&opening.elems());
            },
            |step, state| {
                let phase = step % BLOCK;
                if phase < NUM_ROUNDS {
                    let mut s: [BaseElement; STATE_WIDTH] = state[..STATE_WIDTH].try_into().unwrap();
                    Rp64_256::apply_round(&mut s, phase);
                    state[..STATE_WIDTH].copy_from_slice(&s);
                } else {
                    // Link: running digest = state[4..8]; load the next merge (level = block-1).
                    let node: [BaseElement; DIGEST] = state[4..8].try_into().unwrap();
                    let level = (step + 1) / BLOCK - 1;
                    load_merge(state, node, level);
                }
            },
        );
        trace
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
        let last = trace.length() - 1;
        let mut root = [BaseElement::ZERO; DIGEST];
        for i in 0..DIGEST {
            root[i] = trace.get(DIGEST + i, last);
        }
        PublicInputs { root }
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
    opening: Opening,
    siblings: [[BaseElement; DIGEST]; DEPTH],
    bits: [bool; DEPTH],
) -> (Proof, PublicInputs) {
    let prover = SpendProver::new(build_options());
    let trace = prover.build_trace(opening, siblings, bits);
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

    fn sample() -> (Opening, [[BaseElement; DIGEST]; DEPTH], [bool; DEPTH]) {
        let opening = Opening {
            recipient: BaseElement::new(0xABCD),
            value: BaseElement::new(1000),
            rho: BaseElement::new(0x1111_2222),
            rcm: BaseElement::new(0x3333_4444),
        };
        let mut sib = [[BaseElement::ZERO; DIGEST]; DEPTH];
        let mut bits = [false; DEPTH];
        for d in 0..DEPTH {
            for k in 0..DIGEST {
                sib[d][k] = BaseElement::new((d * 10 + k + 1) as u64);
            }
            bits[d] = d % 2 == 1;
        }
        (opening, sib, bits)
    }

    #[test]
    fn native_commit_matches_winterfell_hash_elements() {
        use winterfell::crypto::ElementHasher;
        let (opening, _, _) = sample();
        let mine = native_commit(opening);
        let theirs = <Rp64_256 as ElementHasher>::hash_elements(&opening.elems());
        assert_eq!(&mine[..], theirs.as_elements());
    }

    #[test]
    fn trace_root_matches_native_oracle() {
        let (opening, sib, bits) = sample();
        let prover = SpendProver::new(build_options());
        let trace = prover.build_trace(opening, sib, bits);
        let pi = prover.get_pub_inputs(&trace);
        assert_eq!(pi.root, native_root(opening, &sib, &bits));
    }

    #[test]
    fn valid_spend_verifies() {
        let (opening, sib, bits) = sample();
        let (proof, pi) = prove_spend(opening, sib, bits);
        assert!(verify_spend(proof, pi).is_ok());
    }

    #[test]
    fn wrong_root_rejected() {
        let (opening, sib, bits) = sample();
        let (proof, mut pi) = prove_spend(opening, sib, bits);
        pi.root[0] += BaseElement::ONE;
        assert!(verify_spend(proof, pi).is_err());
    }

    #[test]
    fn tampered_opening_changes_commitment_and_root() {
        // A different note value yields a different commitment, hence a different root: the proof
        // no longer attests membership of the original committed note. (Commitment binds the leaf.)
        let (opening, sib, bits) = sample();
        let real_root = native_root(opening, &sib, &bits);
        let mut bad = opening;
        bad.value += BaseElement::ONE;
        let (proof, pi) = prove_spend(bad, sib, bits);
        assert_ne!(pi.root, real_root);
        let claim = PublicInputs { root: real_root };
        assert!(verify_spend(proof, claim).is_err());
    }
}
