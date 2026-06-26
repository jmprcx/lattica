//! Phase-0 framework spike — Winterfell (transparent, post-quantum FRI-STARK).
//!
//! This re-expresses the *core* of the hand-rolled authorization proof (`stark.zig`) — knowledge
//! of a secret preimage under the degree-7 power map, which is exactly the S-box nonlinearity of
//! our arithmetization-friendly hash — in a vetted framework, to de-risk the framework decision.
//!
//! What it demonstrates against the audit:
//!   * **C-04 (soundness):** challenges drawn from a field *extension* (`FieldExtension::Quadratic`)
//!     over the same Goldilocks field (`f64`) we prototyped on — no longer capped at the ~50-bit
//!     base-field bound.
//!   * **C-05 (hash):** commitments/Fiat-Shamir use the vetted `Rp64_256` Rescue-Prime instance
//!     shipped by `winter-crypto`, not project-local constants.
//!   * **transparent + post-quantum:** FRI/hash-based, no trusted setup, no elliptic curves.
//!
//! The statement: public `result`; the prover knows a secret `seed` with
//! `seed^(7^(N-1)) = result`, enforced step-by-step by the degree-7 transition `next = cur^7`.
//! The full Rescue *sponge* AIR + the four-constraint spend (commitment/membership/nullifier/
//! balance/tx-binding) is Phase-2 work; this spike validates the mechanics and the framework.

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

type Blake = Rp64_256; // the vetted Rescue-Prime hash used for the transcript & commitments
type Vc = MerkleTree<Blake>;
type Coin = DefaultRandomCoin<Blake>;

// --- public inputs ----------------------------------------------------------------------------

#[derive(Clone)]
pub struct PublicInputs {
    pub result: BaseElement,
}

impl ToElements<BaseElement> for PublicInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        vec![self.result]
    }
}

// --- AIR --------------------------------------------------------------------------------------

pub struct PowChainAir {
    context: AirContext<BaseElement>,
    result: BaseElement,
}

impl Air for PowChainAir {
    type BaseField = BaseElement;
    type PublicInputs = PublicInputs;

    fn new(trace_info: TraceInfo, pub_inputs: PublicInputs, options: ProofOptions) -> Self {
        assert_eq!(1, trace_info.width());
        // Transition is degree 7 (the x^7 S-box).
        let degrees = vec![TransitionConstraintDegree::new(7)];
        let context = AirContext::new(trace_info, degrees, 1, options);
        PowChainAir { context, result: pub_inputs.result }
    }

    fn context(&self) -> &AirContext<BaseElement> {
        &self.context
    }

    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self,
        frame: &EvaluationFrame<E>,
        _periodic_values: &[E],
        result: &mut [E],
    ) {
        let current = frame.current()[0];
        let next = frame.next()[0];
        // next - current^7 = 0
        let c2 = current * current;
        let c4 = c2 * c2;
        let c7 = c4 * c2 * current;
        result[0] = next - c7;
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        // Only the public result (last step) is pinned; the seed (step 0) stays secret.
        let last = self.trace_length() - 1;
        vec![Assertion::single(0, last, self.result)]
    }
}

// --- Prover -----------------------------------------------------------------------------------

pub struct PowChainProver {
    options: ProofOptions,
}

impl PowChainProver {
    pub fn new(options: ProofOptions) -> Self {
        Self { options }
    }

    /// Build the execution trace: column 0 is seed, seed^7, seed^(7^2), ...
    pub fn build_trace(&self, seed: BaseElement, n: usize) -> TraceTable<BaseElement> {
        let mut trace = TraceTable::new(1, n);
        trace.fill(
            |state| {
                state[0] = seed;
            },
            |_, state| {
                let x = state[0];
                let x2 = x * x;
                let x4 = x2 * x2;
                state[0] = x4 * x2 * x; // x^7
            },
        );
        trace
    }
}

impl Prover for PowChainProver {
    type BaseField = BaseElement;
    type Air = PowChainAir;
    type Trace = TraceTable<BaseElement>;
    type HashFn = Blake;
    type VC = Vc;
    type RandomCoin = Coin;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Blake, Vc>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintEvaluator<'a, PowChainAir, E>;
    type ConstraintCommitment<E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintCommitment<E, Blake, Vc>;

    fn get_pub_inputs(&self, trace: &Self::Trace) -> PublicInputs {
        let last = trace.length() - 1;
        PublicInputs { result: trace.get(0, last) }
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
        air: &'a PowChainAir,
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

/// Production-leaning options: extension-field challenges (the C-04 fix) + healthy query count.
pub fn build_options() -> ProofOptions {
    ProofOptions::new(
        96,                       // num_queries
        8,                        // blowup_factor (>= degree-7 composition needs)
        16,                       // grinding_factor (proof-of-work bits)
        FieldExtension::Quadratic, // <-- challenges from F_p^2, not the 64-bit base field
        8,                        // fri_folding_factor
        63,                       // fri_remainder_max_degree
        BatchingMethod::Linear,
        BatchingMethod::Linear,
    )
}

#[allow(dead_code)] // used by tests as a native oracle
fn pow7_iter(seed: BaseElement, n: usize) -> BaseElement {
    let mut x = seed;
    for _ in 0..(n - 1) {
        let x2 = x * x;
        let x4 = x2 * x2;
        x = x4 * x2 * x;
    }
    x
}

pub fn prove_pow_chain(seed: BaseElement, n: usize) -> (Proof, PublicInputs) {
    let prover = PowChainProver::new(build_options());
    let trace = prover.build_trace(seed, n);
    let pub_inputs = prover.get_pub_inputs(&trace);
    let proof = prover.prove(trace).expect("proving failed");
    (proof, pub_inputs)
}

pub fn verify_pow_chain(proof: Proof, pub_inputs: PublicInputs) -> Result<(), String> {
    let acceptable = winterfell::AcceptableOptions::OptionSet(vec![build_options()]);
    winterfell::verify::<PowChainAir, Blake, Coin, Vc>(proof, pub_inputs, &acceptable)
        .map_err(|e| format!("{e}"))
}

fn main() {
    let n = 1024usize;
    let seed = BaseElement::new(0x1234_5678_9abc_def0);

    let (proof, pub_inputs) = prove_pow_chain(seed, n);
    let size = proof.to_bytes().len();
    let sec = proof.conjectured_security::<Blake>().bits();

    println!("Winterfell spike: x^7 chain over Goldilocks f64, Rp64_256 hash, F_p^2 challenges");
    println!("  trace length     : {n}");
    println!("  proof size       : {size} bytes");
    println!("  conjectured sec  : {sec} bits");
    println!("  public result    : {}", pub_inputs.result.as_int());

    match verify_pow_chain(proof, pub_inputs) {
        Ok(()) => println!("  verify           : ACCEPTED"),
        Err(e) => {
            println!("  verify           : REJECTED ({e})");
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_proof_verifies() {
        let n = 256;
        let seed = BaseElement::new(42);
        let (proof, pi) = prove_pow_chain(seed, n);
        assert!(verify_pow_chain(proof, pi).is_ok());
    }

    #[test]
    fn wrong_public_result_rejected() {
        let n = 256;
        let seed = BaseElement::new(42);
        let (proof, mut pi) = prove_pow_chain(seed, n);
        pi.result += BaseElement::ONE; // tamper the public output
        assert!(verify_pow_chain(proof, pi).is_err());
    }

    #[test]
    fn public_result_matches_native() {
        let n = 256;
        let seed = BaseElement::new(7);
        let (_proof, pi) = prove_pow_chain(seed, n);
        assert_eq!(pi.result, pow7_iter(seed, n));
    }
}
