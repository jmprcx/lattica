//! Range check AIR — proves a value lies in `[0, 2^BITS)` (no field wraparound).
//!
//! This is the soundness companion to value-balance: over Goldilocks (`p ≈ 2^64`), a balance
//! constraint `in = out + fee` alone is satisfiable with a wrapped `out = in - fee + p`, which
//! would mint value. A range proof on the hidden values forbids that.
//!
//! Construction (remainder decomposition, LSB-first): a single `rem` column with
//!   `rem[0] = value`,  `bit_i = rem[i] - 2·rem[i+1]`,  `rem[BITS] = 0`,
//! and each `bit_i` constrained boolean. Then `value = Σ bit_i·2^i` with all bits boolean ⇒
//! `value < 2^BITS`. No periodic columns, one degree-2 transition constraint, two boundary
//! assertions, and — crucially — no unconstrained final bit (the `rem[BITS]=0` boundary closes it).
//!
//! Validated: an in-range value verifies; an out-of-range value cannot satisfy `rem[BITS]=0` with
//! boolean bits and is rejected. `BITS=31` here (values < 2^31, trace length 32); production
//! widens `BITS` (and keeps `2^(BITS+1) < p` so balanced sums never wrap). Codex audit precedes
//! production wiring; integration ties `value` to the hidden note value via a persistent column.

use winterfell::{
    math::{fields::f64::BaseElement, FieldElement, ToElements},
    matrix::ColMatrix,
    Air, AirContext, Assertion, AuxRandElements, BatchingMethod, CompositionPoly,
    CompositionPolyTrace, ConstraintCompositionCoefficients, DefaultConstraintCommitment,
    DefaultConstraintEvaluator, DefaultTraceLde, EvaluationFrame, FieldExtension, PartitionOptions,
    Proof, ProofOptions, Prover, StarkDomain, TraceInfo, TracePolyTable, TraceTable,
    TransitionConstraintDegree,
};

use crate::{Coin, Hf, Vc};

pub const BITS: usize = 31; // values < 2^31; trace length = BITS + 1 = 32 (power of two)
const TRACE_LEN: usize = BITS + 1;

#[derive(Clone)]
pub struct PublicInputs {
    pub value: BaseElement,
}

impl ToElements<BaseElement> for PublicInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        vec![self.value]
    }
}

pub struct RangeAir {
    context: AirContext<BaseElement>,
    value: BaseElement,
}

impl Air for RangeAir {
    type BaseField = BaseElement;
    type PublicInputs = PublicInputs;

    fn new(trace_info: TraceInfo, pub_inputs: PublicInputs, options: ProofOptions) -> Self {
        assert_eq!(2, trace_info.width());
        // col0: bit = rem_cur - 2*rem_next ; bit*(bit-1) = 0  (degree 2)
        // col1: a 0,1,2,... counter (counter_next - counter_cur - 1 = 0) — keeps the trace at full
        //       degree so even value=0 (an all-zero rem column) is not a degenerate trace.
        let degrees = vec![TransitionConstraintDegree::new(2), TransitionConstraintDegree::new(1)];
        let context = AirContext::new(trace_info, degrees, 3, options);
        RangeAir { context, value: pub_inputs.value }
    }

    fn context(&self) -> &AirContext<BaseElement> {
        &self.context
    }

    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self,
        frame: &EvaluationFrame<E>,
        _periodic: &[E],
        result: &mut [E],
    ) {
        let rem = frame.current()[0];
        let rem_next = frame.next()[0];
        let two = E::from(BaseElement::new(2));
        let bit = rem - two * rem_next;
        result[0] = bit * (bit - E::ONE); // boolean
        result[1] = frame.next()[1] - frame.current()[1] - E::ONE; // counter increments
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        vec![
            Assertion::single(0, 0, self.value),                    // rem[0] = value
            Assertion::single(0, TRACE_LEN - 1, BaseElement::ZERO), // rem[BITS] = 0
            Assertion::single(1, 0, BaseElement::ZERO),             // counter[0] = 0
        ]
    }
}

pub struct RangeProver {
    options: ProofOptions,
}

impl RangeProver {
    pub fn new(options: ProofOptions) -> Self {
        Self { options }
    }

    /// Trace: `rem[0]=value`, peel one bit per row, `rem[BITS]=0` for in-range values.
    pub fn build_trace(&self, value: u64) -> TraceTable<BaseElement> {
        let mut trace = TraceTable::new(2, TRACE_LEN);
        trace.fill(
            |state| {
                state[0] = BaseElement::new(value);
                state[1] = BaseElement::ZERO; // counter
            },
            |step, state| {
                // rem_{i+1} = floor(rem_i / 2) = value >> (i+1); bit_i = (value >> i) & 1.
                state[0] = BaseElement::new(value >> (step + 1));
                state[1] = BaseElement::new((step + 1) as u64);
            },
        );
        trace
    }
}

impl Prover for RangeProver {
    type BaseField = BaseElement;
    type Air = RangeAir;
    type Trace = TraceTable<BaseElement>;
    type HashFn = Hf;
    type VC = Vc;
    type RandomCoin = Coin;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Hf, Vc>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintEvaluator<'a, RangeAir, E>;
    type ConstraintCommitment<E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintCommitment<E, Hf, Vc>;

    fn get_pub_inputs(&self, trace: &Self::Trace) -> PublicInputs {
        PublicInputs { value: trace.get(0, 0) }
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
        air: &'a RangeAir,
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

pub fn build_options() -> ProofOptions {
    ProofOptions::new(
        96,
        4, // blowup (degree-2 constraint)
        16,
        FieldExtension::Quadratic,
        8,
        31,
        BatchingMethod::Linear,
        BatchingMethod::Linear,
    )
}

pub fn prove_range(value: u64) -> (Proof, PublicInputs) {
    let prover = RangeProver::new(build_options());
    let trace = prover.build_trace(value);
    let pi = prover.get_pub_inputs(&trace);
    let proof = prover.prove(trace).expect("proving failed");
    (proof, pi)
}

pub fn verify_range(proof: Proof, pi: PublicInputs) -> Result<(), String> {
    let acceptable = winterfell::AcceptableOptions::OptionSet(vec![build_options()]);
    winterfell::verify::<RangeAir, Hf, Coin, Vc>(proof, pi, &acceptable).map_err(|e| format!("{e}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn in_range_values_verify() {
        for v in [0u64, 1, 42, 1000, (1u64 << 31) - 1] {
            let (proof, pi) = prove_range(v);
            assert!(verify_range(proof, pi).is_ok(), "value {v} should verify");
        }
    }

    #[test]
    fn out_of_range_value_rejected() {
        // 2^31 cannot be represented in BITS=31 boolean bits with rem[BITS]=0.
        let v = 1u64 << 31;
        let prover = RangeProver::new(build_options());
        let trace = prover.build_trace(v);
        let pi = prover.get_pub_inputs(&trace);
        match prover.prove(trace) {
            Ok(proof) => assert!(verify_range(proof, pi).is_err()),
            Err(_) => {} // fail-stop in proving is also acceptable
        }
    }

    #[test]
    fn wrong_public_value_rejected() {
        let (proof, mut pi) = prove_range(1234);
        pi.value += BaseElement::ONE;
        assert!(verify_range(proof, pi).is_err());
    }
}
