//! `lattica-prover` — the production proof backend (Phase 2).
//!
//! Built on **Winterfell** (transparent, post-quantum FRI-STARK). This module implements the
//! foundational in-circuit primitive the whole spend statement is built from: an AIR for the
//! **Rescue-Prime `Rp64_256` permutation** — the *vetted* arithmetization-friendly hash
//! (closing audit C-05 in-circuit), using Winterfell's own MDS/round constants. Commitment,
//! nullifier, and Merkle membership are repeated applications of this permutation; they layer on
//! top (the spend statement is grown incrementally and audited in Phase 3).
//!
//! Correctness is guarded three ways: the AIR trace is cross-checked against the native
//! `Rp64_256::apply_permutation` oracle, a valid proof must verify, and a tampered output must be
//! rejected. The C ABI (`lattica_spend_verify`) matches the Zig `src/ffi.zig` boundary.

use winterfell::{
    crypto::{hashers::Rp64_256, DefaultRandomCoin, MerkleTree},
    math::{fields::f64::BaseElement, FieldElement, ToElements},
    matrix::ColMatrix,
    Air, AirContext, Assertion, AuxRandElements, BatchingMethod, CompositionPoly,
    CompositionPolyTrace, ConstraintCompositionCoefficients, DefaultConstraintCommitment,
    DefaultConstraintEvaluator, DefaultTraceLde, EvaluationFrame, FieldExtension, PartitionOptions,
    Proof, ProofOptions, Prover, StarkDomain, Trace, TraceInfo, TracePolyTable, TraceTable,
    TransitionConstraintDegree,
};

pub mod membership;

pub(crate) type Hf = Rp64_256;
pub(crate) type Vc = MerkleTree<Hf>;
pub(crate) type Coin = DefaultRandomCoin<Hf>;

pub(crate) const STATE_WIDTH: usize = 12; // Rp64_256::STATE_WIDTH
pub(crate) const NUM_ROUNDS: usize = 7; // Rp64_256::NUM_ROUNDS
const TRACE_LEN: usize = 8; // next power of two >= NUM_ROUNDS + 1
pub(crate) const CYCLE: usize = 8; // periodic round-constant cycle

// --- field helpers ----------------------------------------------------------------------------

#[inline]
pub(crate) fn pow7<E: FieldElement>(x: E) -> E {
    let x2 = x * x;
    let x4 = x2 * x2;
    x4 * x2 * x
}

/// `MDS · v` with the (BaseElement) MDS matrix lifted into the working field `E`.
pub(crate) fn mds_mul<E: FieldElement<BaseField = BaseElement>>(v: &[E; STATE_WIDTH]) -> [E; STATE_WIDTH] {
    let mds = Rp64_256::MDS;
    let mut out = [E::ZERO; STATE_WIDTH];
    for i in 0..STATE_WIDTH {
        let mut acc = E::ZERO;
        for j in 0..STATE_WIDTH {
            acc += E::from(mds[i][j]) * v[j];
        }
        out[i] = acc;
    }
    out
}

pub(crate) fn inv_mds_mul<E: FieldElement<BaseField = BaseElement>>(v: &[E; STATE_WIDTH]) -> [E; STATE_WIDTH] {
    let inv = Rp64_256::INV_MDS;
    let mut out = [E::ZERO; STATE_WIDTH];
    for i in 0..STATE_WIDTH {
        let mut acc = E::ZERO;
        for j in 0..STATE_WIDTH {
            acc += E::from(inv[i][j]) * v[j];
        }
        out[i] = acc;
    }
    out
}

// --- public inputs ----------------------------------------------------------------------------

#[derive(Clone)]
pub struct PublicInputs {
    pub output: [BaseElement; STATE_WIDTH],
}

impl ToElements<BaseElement> for PublicInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        self.output.to_vec()
    }
}

// --- AIR --------------------------------------------------------------------------------------

pub struct RescueAir {
    context: AirContext<BaseElement>,
    output: [BaseElement; STATE_WIDTH],
}

impl Air for RescueAir {
    type BaseField = BaseElement;
    type PublicInputs = PublicInputs;

    fn new(trace_info: TraceInfo, pub_inputs: PublicInputs, options: ProofOptions) -> Self {
        assert_eq!(STATE_WIDTH, trace_info.width());
        // One degree-7 constraint per state element; the round constants are periodic (cycle 8).
        let degrees =
            vec![TransitionConstraintDegree::with_cycles(7, vec![CYCLE]); STATE_WIDTH];
        let context = AirContext::new(trace_info, degrees, STATE_WIDTH, options);
        RescueAir { context, output: pub_inputs.output }
    }

    fn context(&self) -> &AirContext<BaseElement> {
        &self.context
    }

    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self,
        frame: &EvaluationFrame<E>,
        periodic_values: &[E],
        result: &mut [E],
    ) {
        let current: &[E] = frame.current();
        let next: &[E] = frame.next();

        // Rescue-Prime round (Rp64_256::apply_round), enforced as a degree-7 identity:
        //   step1 = MDS · sbox(current) + ARK1
        //   step2 = sbox( MDS^{-1} · (next - ARK2) )
        //   step1 == step2
        // (the inverse S-box is never evaluated; both sides are degree-7).
        let mut sbox_cur = [E::ZERO; STATE_WIDTH];
        for i in 0..STATE_WIDTH {
            sbox_cur[i] = pow7(current[i]);
        }
        let mds_sbox = mds_mul(&sbox_cur);

        let mut next_minus_ark2 = [E::ZERO; STATE_WIDTH];
        for i in 0..STATE_WIDTH {
            next_minus_ark2[i] = next[i] - periodic_values[STATE_WIDTH + i]; // ARK2
        }
        let pre = inv_mds_mul(&next_minus_ark2);

        for i in 0..STATE_WIDTH {
            let step1 = mds_sbox[i] + periodic_values[i]; // + ARK1
            let step2 = pow7(pre[i]);
            result[i] = step1 - step2;
        }
    }

    fn get_periodic_column_values(&self) -> Vec<Vec<BaseElement>> {
        // 24 columns: ARK1[*][j] then ARK2[*][j], each padded to the cycle length.
        let ark1 = Rp64_256::ARK1;
        let ark2 = Rp64_256::ARK2;
        let mut cols = Vec::with_capacity(2 * STATE_WIDTH);
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
        cols
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        // The permutation output is the final trace row.
        let last = self.trace_length() - 1;
        (0..STATE_WIDTH)
            .map(|i| Assertion::single(i, last, self.output[i]))
            .collect()
    }
}

// --- Prover -----------------------------------------------------------------------------------

pub struct RescueProver {
    options: ProofOptions,
}

impl RescueProver {
    pub fn new(options: ProofOptions) -> Self {
        Self { options }
    }

    /// Build the execution trace: row 0 = input, row i+1 = apply_round(row i, i), row 7 = output.
    pub fn build_trace(&self, input: [BaseElement; STATE_WIDTH]) -> TraceTable<BaseElement> {
        let mut trace = TraceTable::new(STATE_WIDTH, TRACE_LEN);
        trace.fill(
            |state| {
                state[..STATE_WIDTH].copy_from_slice(&input);
            },
            |step, state| {
                let mut s: [BaseElement; STATE_WIDTH] = state.try_into().unwrap();
                if step < NUM_ROUNDS {
                    Rp64_256::apply_round(&mut s, step);
                }
                state.copy_from_slice(&s);
            },
        );
        trace
    }
}

impl Prover for RescueProver {
    type BaseField = BaseElement;
    type Air = RescueAir;
    type Trace = TraceTable<BaseElement>;
    type HashFn = Hf;
    type VC = Vc;
    type RandomCoin = Coin;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Hf, Vc>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintEvaluator<'a, RescueAir, E>;
    type ConstraintCommitment<E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintCommitment<E, Hf, Vc>;

    fn get_pub_inputs(&self, trace: &Self::Trace) -> PublicInputs {
        let last = trace.length() - 1;
        let mut output = [BaseElement::ZERO; STATE_WIDTH];
        for i in 0..STATE_WIDTH {
            output[i] = trace.get(i, last);
        }
        PublicInputs { output }
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
        air: &'a RescueAir,
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

/// Production-leaning options: extension-field challenges (C-04), healthy query count.
pub fn build_options() -> ProofOptions {
    ProofOptions::new(
        96,
        16, // blowup (degree-7 + periodic constants)
        16,
        FieldExtension::Quadratic,
        8,
        63,
        BatchingMethod::Linear,
        BatchingMethod::Linear,
    )
}

/// Prove knowledge of a secret input whose Rp64_256 permutation equals the public output.
pub fn prove_permutation(input: [BaseElement; STATE_WIDTH]) -> (Proof, PublicInputs) {
    let prover = RescueProver::new(build_options());
    let trace = prover.build_trace(input);
    let pub_inputs = prover.get_pub_inputs(&trace);
    let proof = prover.prove(trace).expect("proving failed");
    (proof, pub_inputs)
}

pub fn verify_permutation(proof: Proof, pub_inputs: PublicInputs) -> Result<(), String> {
    let acceptable = winterfell::AcceptableOptions::OptionSet(vec![build_options()]);
    winterfell::verify::<RescueAir, Hf, Coin, Vc>(proof, pub_inputs, &acceptable)
        .map_err(|e| format!("{e}"))
}

/// Native oracle: the Rp64_256 permutation, used to cross-check the AIR.
pub fn native_permutation(mut state: [BaseElement; STATE_WIDTH]) -> [BaseElement; STATE_WIDTH] {
    Rp64_256::apply_permutation(&mut state);
    state
}

// --- C ABI (matches src/ffi.zig) --------------------------------------------------------------

/// `lattica_spend_verify` — the production spend verifier the Zig node calls.
///
/// NOTE: the full spend statement (commitment opening + membership + nullifier + balance + range
/// + tx-binding) is built up incrementally on top of the Rescue-Prime AIR above. Until that is
/// complete and audited, this returns a non-zero "unimplemented" code so the node fails closed —
/// it never accepts a spend against a stub verifier.
#[no_mangle]
pub extern "C" fn lattica_spend_verify(
    _proof_ptr: *const u8,
    _proof_len: usize,
    _pi_ptr: *const u8,
    _pi_len: usize,
) -> i32 {
    -1 // unimplemented; fail closed
}

// --- tests ------------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_input(seed: u64) -> [BaseElement; STATE_WIDTH] {
        let mut s = [BaseElement::ZERO; STATE_WIDTH];
        for i in 0..STATE_WIDTH {
            s[i] = BaseElement::new(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(i as u64));
        }
        s
    }

    #[test]
    fn trace_output_matches_native_oracle() {
        // The AIR trace's final row must equal the native Rp64_256 permutation.
        let input = sample_input(1);
        let prover = RescueProver::new(build_options());
        let trace = prover.build_trace(input);
        let pi = prover.get_pub_inputs(&trace);
        assert_eq!(pi.output, native_permutation(input));
    }

    #[test]
    fn valid_proof_verifies() {
        let input = sample_input(2);
        let (proof, pi) = prove_permutation(input);
        assert!(verify_permutation(proof, pi).is_ok());
    }

    #[test]
    fn tampered_output_rejected() {
        let input = sample_input(3);
        let (proof, mut pi) = prove_permutation(input);
        pi.output[0] += BaseElement::ONE;
        assert!(verify_permutation(proof, pi).is_err());
    }

    #[test]
    fn spend_verify_abi_fails_closed() {
        let pi = [0u8; 136];
        assert_eq!(lattica_spend_verify(pi.as_ptr(), 4, pi.as_ptr(), pi.len()), -1);
    }
}
