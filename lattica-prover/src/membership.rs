//! Merkle membership AIR — the heart of audit finding C-02.
//!
//! Proves, for a public `root`, knowledge of a leaf and an authentication path (siblings +
//! position bits) such that folding the leaf up the path with the vetted Rescue-Prime 2-to-1
//! compression yields `root`. The leaf and path stay private. Each level is one `Rp64_256`
//! permutation (the `merge` convention: `state[0]=8`, `state[4..8]=left`, `state[8..12]=right`,
//! permute, digest = `state[4..8]`), so the trace is `DEPTH` permutation blocks chained together.
//!
//! Trace width 13: the 12-element Rescue state plus one **position-bit** column. A periodic
//! selector splits each 8-row block into 7 round transitions (the Rescue identity) and 1 link
//! transition (load the next block: capacity reset, the running digest placed left/right by the
//! bit, the sibling free). Correctness is guarded by a differential test against a native
//! `Rp64_256::merge` tree, plus valid-verifies and tamper-rejected (root and sibling).
//!
//! Audit note: `DEPTH` is a constant (8 here for fast tests; production is 32 — a one-line change
//! and a longer trace). The leaf is unconstrained here (pure membership); in the full spend it is
//! tied to the commitment region. Codex audit precedes production wiring.

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

pub const DEPTH: usize = 8; // production: 32 (const change + longer trace)
pub const DIGEST: usize = 4; // Rp64_256 digest size
const BLOCK: usize = 8; // rows per merge (one permutation)
const WIDTH: usize = STATE_WIDTH + 1; // 12 state + 1 position bit
const BIT: usize = STATE_WIDTH; // position-bit column index (12)
const MEM_LEN: usize = BLOCK * DEPTH;

// --- native oracle ----------------------------------------------------------------------------

/// The Rescue-Prime 2-to-1 compression, written exactly as `Rp64_256::merge` does it.
pub fn native_merge(left: [BaseElement; DIGEST], right: [BaseElement; DIGEST]) -> [BaseElement; DIGEST] {
    let mut state = [BaseElement::ZERO; STATE_WIDTH];
    state[0] = BaseElement::new(8); // RATE_WIDTH
    state[4..8].copy_from_slice(&left);
    state[8..12].copy_from_slice(&right);
    Rp64_256::apply_permutation(&mut state);
    state[4..8].try_into().unwrap()
}

/// Fold a leaf up an authentication path to the root (native).
pub fn native_root(
    leaf: [BaseElement; DIGEST],
    siblings: &[[BaseElement; DIGEST]; DEPTH],
    bits: &[bool; DEPTH],
) -> [BaseElement; DIGEST] {
    let mut node = leaf;
    for d in 0..DEPTH {
        node = if bits[d] {
            native_merge(siblings[d], node) // running on the right
        } else {
            native_merge(node, siblings[d]) // running on the left
        };
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

pub struct MembershipAir {
    context: AirContext<BaseElement>,
    root: [BaseElement; DIGEST],
}

impl Air for MembershipAir {
    type BaseField = BaseElement;
    type PublicInputs = PublicInputs;

    fn new(trace_info: TraceInfo, pub_inputs: PublicInputs, options: ProofOptions) -> Self {
        assert_eq!(WIDTH, trace_info.width());
        // Each of the 12 state constraints is, on round rows, a degree-7 Rescue identity gated by
        // the periodic round selector (and the periodic round constants).
        let degrees =
            vec![TransitionConstraintDegree::with_cycles(7, vec![CYCLE, CYCLE]); STATE_WIDTH];
        // Assertions: row-0 capacity [8,0,0,0] (4) + final-row digest = root (4).
        let context = AirContext::new(trace_info, degrees, 8, options);
        MembershipAir { context, root: pub_inputs.root }
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
        let is_round = periodic[2 * STATE_WIDTH]; // round selector (1 on rounds, 0 on link rows)
        let is_link = E::ONE - is_round;

        // --- round identity: MDS·sbox(cur) + ARK1 == sbox(INV_MDS·(next - ARK2)) ---
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

        // --- link load (block boundary): next = [8,0,0,0, ordered(running, sibling)], bit bool ---
        let bit = next[BIT];
        let one = E::ONE;
        for i in 0..STATE_WIDTH {
            let round_i = (mds_sbox[i] + periodic[i]) - pow7(pre[i]);

            let link_i = if i == 0 {
                next[0] - E::from(BaseElement::new(8))
            } else if i < DIGEST {
                next[i] // capacity 1..4 == 0
            } else if i < 2 * DIGEST {
                // i in 4..8: the running digest element R = cur[4 + (i-4)] = cur[i] must occupy the
                // bit-selected slot; left slot = next[i], right slot = next[i + DIGEST].
                let r = cur[i];
                (one - bit) * (next[i] - r) + bit * (next[i + DIGEST] - r)
            } else if i == 2 * DIGEST {
                // i == 8: position bit is boolean.
                bit * (one - bit)
            } else {
                E::ZERO // i in 9..12: no link constraint
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
        // round selector: 1 on the 7 round transitions, 0 on the link transition (row 7).
        let mut sel = vec![BaseElement::ONE; CYCLE];
        sel[CYCLE - 1] = BaseElement::ZERO;
        cols.push(sel);
        cols
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let last = self.trace_length() - 1;
        let mut a = Vec::with_capacity(8);
        // Row-0 capacity = [8, 0, 0, 0].
        a.push(Assertion::single(0, 0, BaseElement::new(8)));
        a.push(Assertion::single(1, 0, BaseElement::ZERO));
        a.push(Assertion::single(2, 0, BaseElement::ZERO));
        a.push(Assertion::single(3, 0, BaseElement::ZERO));
        // Final digest (state[4..8] of the last row) = public root.
        for i in 0..DIGEST {
            a.push(Assertion::single(DIGEST + i, last, self.root[i]));
        }
        a
    }
}

// --- Prover -----------------------------------------------------------------------------------

pub struct MembershipProver {
    options: ProofOptions,
}

impl MembershipProver {
    pub fn new(options: ProofOptions) -> Self {
        Self { options }
    }

    pub fn build_trace(
        &self,
        leaf: [BaseElement; DIGEST],
        siblings: [[BaseElement; DIGEST]; DEPTH],
        bits: [bool; DEPTH],
    ) -> TraceTable<BaseElement> {
        let mut trace = TraceTable::new(WIDTH, MEM_LEN);

        let load = |state: &mut [BaseElement], node: [BaseElement; DIGEST], d: usize| {
            for s in state.iter_mut().take(STATE_WIDTH) {
                *s = BaseElement::ZERO;
            }
            state[0] = BaseElement::new(8);
            if bits[d] {
                state[8..12].copy_from_slice(&node); // running on the right
                state[4..8].copy_from_slice(&siblings[d]);
            } else {
                state[4..8].copy_from_slice(&node); // running on the left
                state[8..12].copy_from_slice(&siblings[d]);
            }
            state[BIT] = if bits[d] { BaseElement::ONE } else { BaseElement::ZERO };
        };

        trace.fill(
            |state| load(state, leaf, 0),
            |step, state| {
                let phase = step % BLOCK;
                if phase < NUM_ROUNDS {
                    // round transition within the current block
                    let mut s: [BaseElement; STATE_WIDTH] = state[..STATE_WIDTH].try_into().unwrap();
                    Rp64_256::apply_round(&mut s, phase);
                    state[..STATE_WIDTH].copy_from_slice(&s);
                    // position bit carries unchanged within a block
                } else {
                    // link transition: load the next block from the running digest (state[4..8])
                    let node: [BaseElement; DIGEST] = state[4..8].try_into().unwrap();
                    let d_next = (step + 1) / BLOCK;
                    load(state, node, d_next);
                }
            },
        );
        trace
    }
}

impl Prover for MembershipProver {
    type BaseField = BaseElement;
    type Air = MembershipAir;
    type Trace = TraceTable<BaseElement>;
    type HashFn = Hf;
    type VC = Vc;
    type RandomCoin = Coin;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Hf, Vc>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintEvaluator<'a, MembershipAir, E>;
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
        air: &'a MembershipAir,
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
        32, // blowup: degree-7 round gated by periodic selector
        16,
        FieldExtension::Quadratic,
        8,
        63,
        BatchingMethod::Linear,
        BatchingMethod::Linear,
    )
}

pub fn prove_membership(
    leaf: [BaseElement; DIGEST],
    siblings: [[BaseElement; DIGEST]; DEPTH],
    bits: [bool; DEPTH],
) -> (Proof, PublicInputs) {
    let prover = MembershipProver::new(build_options());
    let trace = prover.build_trace(leaf, siblings, bits);
    let pi = prover.get_pub_inputs(&trace);
    let proof = prover.prove(trace).expect("proving failed");
    (proof, pi)
}

pub fn verify_membership(proof: Proof, pi: PublicInputs) -> Result<(), String> {
    let acceptable = winterfell::AcceptableOptions::OptionSet(vec![build_options()]);
    winterfell::verify::<MembershipAir, Hf, Coin, Vc>(proof, pi, &acceptable).map_err(|e| format!("{e}"))
}

// --- tests ------------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn digest(seed: u64) -> [BaseElement; DIGEST] {
        let mut d = [BaseElement::ZERO; DIGEST];
        for i in 0..DIGEST {
            d[i] = BaseElement::new(seed.wrapping_mul(0x9e37_79b9).wrapping_add(i as u64 + 1));
        }
        d
    }

    fn sample() -> ([BaseElement; DIGEST], [[BaseElement; DIGEST]; DEPTH], [bool; DEPTH]) {
        let leaf = digest(1);
        let mut sib = [[BaseElement::ZERO; DIGEST]; DEPTH];
        let mut bits = [false; DEPTH];
        for d in 0..DEPTH {
            sib[d] = digest(100 + d as u64);
            bits[d] = d % 3 == 0; // a mixed left/right path
        }
        (leaf, sib, bits)
    }

    #[test]
    fn trace_root_matches_native_oracle() {
        let (leaf, sib, bits) = sample();
        let prover = MembershipProver::new(build_options());
        let trace = prover.build_trace(leaf, sib, bits);
        let pi = prover.get_pub_inputs(&trace);
        assert_eq!(pi.root, native_root(leaf, &sib, &bits));
    }

    #[test]
    fn native_merge_matches_winterfell_merge() {
        use winterfell::crypto::Hasher;
        let a = digest(7);
        let b = digest(8);
        let mine = native_merge(a, b);
        let theirs = <Rp64_256 as Hasher>::merge(&[
            <Rp64_256 as Hasher>::Digest::new(a),
            <Rp64_256 as Hasher>::Digest::new(b),
        ]);
        assert_eq!(&mine[..], theirs.as_elements());
    }

    #[test]
    fn valid_membership_verifies() {
        let (leaf, sib, bits) = sample();
        let (proof, pi) = prove_membership(leaf, sib, bits);
        assert!(verify_membership(proof, pi).is_ok());
    }

    #[test]
    fn wrong_root_rejected() {
        let (leaf, sib, bits) = sample();
        let (proof, mut pi) = prove_membership(leaf, sib, bits);
        pi.root[0] += BaseElement::ONE;
        assert!(verify_membership(proof, pi).is_err());
    }

    #[test]
    fn tampered_sibling_changes_root() {
        // Proving with a different sibling yields a different root, so the proof no longer attests
        // membership under the original root.
        let (leaf, sib, bits) = sample();
        let real_root = native_root(leaf, &sib, &bits);
        let mut bad = sib;
        bad[2] = digest(999);
        let (proof, pi) = prove_membership(leaf, bad, bits);
        assert_ne!(pi.root, real_root);
        // The proof is valid for ITS root, but not for the real one.
        let claim = PublicInputs { root: real_root };
        assert!(verify_membership(proof, claim).is_err());
    }
}
