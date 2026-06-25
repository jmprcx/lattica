//! # lattica-circuit
//!
//! The zero-knowledge proving system for Lattica spends — built on a **transparent,
//! hash-based FRI-STARK** (Winterfell). This is the single most important component for
//! quantum safety: it replaces Zcash's Halo 2 proof (whose soundness rests on the discrete
//! log of the Pasta curves, and is broken by Shor) with a proof whose soundness rests only
//! on the collision resistance of a hash function. There is **no trusted setup** and **no
//! elliptic curve** anywhere in the proof.
//!
//! ## The full shielded statement
//!
//! A complete Lattica spend proves, in zero knowledge, the conjunction:
//!
//! 1. **Membership** — the spent note's commitment `cm` is a leaf under the public anchor
//!    (an authentication path hashes up to the root). See [`lattica_tree::verify_path`].
//! 2. **Nullifier correctness** — the revealed nullifier equals `PRF(nk, rho, position)`
//!    for the same note, so double-spends are detectable but unlinkable.
//! 3. **Spend authorization** — the prover knows the secret authorizing the spend
//!    (knowledge of a preimage under a one-way hash), folded *into the proof* rather than
//!    carried as a separate re-randomizable signature (no standardized PQ scheme exists for
//!    that yet).
//! 4. **Balance** — `sum(input values) == sum(output values) + fee`, checked over the
//!    cleartext values inside the proof (Lattica has no homomorphic value commitment to
//!    lean on, by design).
//!
//! In a production build all four are constraints of a single AIR over an arithmetization-
//! friendly hash (Poseidon2/Rescue). **This PoC implements constraint (3) as a real,
//! end-to-end FRI-STARK** (below), and enforces (1), (2), (4) natively in `lattica-node`
//! so the whole transfer verifies. The framing (commitments, nullifiers, Merkle hashing) is
//! identical across both, so moving them inside the AIR is additive, not a redesign.
//!
//! ## Honest limitations of this PoC
//!
//! * **Zero-knowledge masking.** Winterfell STARKs are sound and transparent but not yet
//!   zero-knowledge (the trace LDE can leak). A production shielded build adds the standard
//!   ZK randomization (masked trace / random columns). We prove soundness + transparency +
//!   post-quantum here; ZK masking is the remaining, well-understood step.
//! * **One-way hash.** The authorization chain below uses an algebraic transition for
//!   clarity; production substitutes a vetted one-way arithmetization-friendly hash so the
//!   relation is genuinely hard to invert.

use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin, MerkleTree},
    math::{fields::f128::BaseElement, FieldElement, StarkField, ToElements},
    matrix::ColMatrix,
    verify, AcceptableOptions, Air, AirContext, Assertion, AuxRandElements, BatchingMethod,
    CompositionPoly, CompositionPolyTrace, ConstraintCompositionCoefficients,
    DefaultConstraintCommitment, DefaultConstraintEvaluator, DefaultTraceLde, EvaluationFrame,
    FieldExtension, PartitionOptions, Proof, ProofOptions, Prover, StarkDomain, Trace, TraceInfo,
    TracePolyTable, TraceTable, TransitionConstraintDegree,
};

use lattica_primitives::Hash32;

/// Number of steps in the authorization chain (must be a power of two).
const NUM_STEPS: usize = 1024;
/// Round constant in the chain transition `x -> x^3 + C`.
const C: u128 = 42;

type Blake3 = Blake3_256<BaseElement>;

// ---------------------------------------------------------------------------------------
// AIR: prove knowledge of a secret `s` whose chain image `T^NUM_STEPS(s)` equals a public
// value. Stands in for the spend-authorization relation (knowledge of the spend secret).
// ---------------------------------------------------------------------------------------

#[derive(Clone)]
pub struct AuthPublicInputs {
    /// The public authorization image; the prover must know a preimage chain ending here.
    pub image: BaseElement,
}

impl ToElements<BaseElement> for AuthPublicInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        vec![self.image]
    }
}

pub struct AuthAir {
    context: AirContext<BaseElement>,
    image: BaseElement,
}

impl Air for AuthAir {
    type BaseField = BaseElement;
    type PublicInputs = AuthPublicInputs;

    fn new(trace_info: TraceInfo, pub_inputs: AuthPublicInputs, options: ProofOptions) -> Self {
        assert_eq!(1, trace_info.width());
        let degrees = vec![TransitionConstraintDegree::new(3)];
        AuthAir {
            context: AirContext::new(trace_info, degrees, 1, options),
            image: pub_inputs.image,
        }
    }

    fn evaluate_transition<E: FieldElement + From<Self::BaseField>>(
        &self,
        frame: &EvaluationFrame<E>,
        _periodic_values: &[E],
        result: &mut [E],
    ) {
        let current = frame.current()[0];
        let next = current.exp(3u32.into()) + E::from(BaseElement::new(C));
        result[0] = frame.next()[0] - next;
    }

    fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
        // Only the *final* state is public. The starting secret is never asserted, so the
        // proof attests to knowledge of a preimage without revealing it.
        let last_step = self.trace_length() - 1;
        vec![Assertion::single(0, last_step, self.image)]
    }

    fn context(&self) -> &AirContext<Self::BaseField> {
        &self.context
    }
}

// ---------------------------------------------------------------------------------------
// Prover
// ---------------------------------------------------------------------------------------

struct AuthProver {
    options: ProofOptions,
}

impl Prover for AuthProver {
    type BaseField = BaseElement;
    type Air = AuthAir;
    type Trace = TraceTable<BaseElement>;
    type HashFn = Blake3;
    type VC = MerkleTree<Blake3>;
    type RandomCoin = DefaultRandomCoin<Blake3>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Blake3, Self::VC>;
    type ConstraintCommitment<E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintCommitment<E, Blake3, Self::VC>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintEvaluator<'a, AuthAir, E>;

    fn get_pub_inputs(&self, trace: &Self::Trace) -> AuthPublicInputs {
        let last_step = trace.length() - 1;
        AuthPublicInputs { image: trace.get(0, last_step) }
    }

    fn new_trace_lde<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        trace_info: &TraceInfo,
        main_trace: &ColMatrix<Self::BaseField>,
        domain: &StarkDomain<Self::BaseField>,
        partition_options: PartitionOptions,
    ) -> (Self::TraceLde<E>, TracePolyTable<E>) {
        DefaultTraceLde::new(trace_info, main_trace, domain, partition_options)
    }

    fn build_constraint_commitment<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        composition_poly_trace: CompositionPolyTrace<E>,
        num_constraint_composition_columns: usize,
        domain: &StarkDomain<Self::BaseField>,
        partition_options: PartitionOptions,
    ) -> (Self::ConstraintCommitment<E>, CompositionPoly<E>) {
        DefaultConstraintCommitment::new(
            composition_poly_trace,
            num_constraint_composition_columns,
            domain,
            partition_options,
        )
    }

    fn new_evaluator<'a, E: FieldElement<BaseField = BaseElement>>(
        &self,
        air: &'a AuthAir,
        aux_rand_elements: Option<AuxRandElements<E>>,
        composition_coefficients: ConstraintCompositionCoefficients<E>,
    ) -> Self::ConstraintEvaluator<'a, E> {
        DefaultConstraintEvaluator::new(air, aux_rand_elements, composition_coefficients)
    }

    fn options(&self) -> &ProofOptions {
        &self.options
    }
}

// ---------------------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------------------

/// A spend-authorization proof: the public image plus the serialized FRI-STARK proof.
#[derive(Clone, Debug)]
pub struct AuthProof {
    pub image: [u8; 16],
    pub proof: Vec<u8>,
}

fn proof_options() -> ProofOptions {
    // 32 queries, blowup 8, no grinding, no field extension, FRI folding 8, remainder 127.
    // ~ conjectured 100+ bit security; tune for production.
    ProofOptions::new(
        32,
        8,
        0,
        FieldExtension::None,
        8,
        127,
        BatchingMethod::Linear,
        BatchingMethod::Linear,
    )
}

fn secret_to_field(secret: &Hash32) -> BaseElement {
    let mut bytes = [0u8; 16];
    bytes.copy_from_slice(&secret[..16]);
    BaseElement::new(u128::from_le_bytes(bytes))
}

fn build_trace(secret: BaseElement) -> TraceTable<BaseElement> {
    let mut trace = TraceTable::new(1, NUM_STEPS);
    trace.fill(
        |state| {
            state[0] = secret;
        },
        |_, state| {
            state[0] = state[0].exp(3u32.into()) + BaseElement::new(C);
        },
    );
    trace
}

/// Prove knowledge of the spend secret. Returns the public image and a FRI-STARK proof.
pub fn prove_authorization(secret: &Hash32) -> Result<AuthProof, &'static str> {
    let s = secret_to_field(secret);
    let trace = build_trace(s);
    let image = trace.get(0, NUM_STEPS - 1);
    let prover = AuthProver { options: proof_options() };
    let proof = prover.prove(trace).map_err(|_| "proving failed")?;
    Ok(AuthProof {
        image: image.as_int().to_le_bytes(),
        proof: proof.to_bytes(),
    })
}

/// Verify a spend-authorization proof.
pub fn verify_authorization(auth: &AuthProof) -> bool {
    let image = BaseElement::new(u128::from_le_bytes(auth.image));
    let proof = match Proof::from_bytes(&auth.proof) {
        Ok(p) => p,
        Err(_) => return false,
    };
    let pub_inputs = AuthPublicInputs { image };
    let acceptable = AcceptableOptions::MinConjecturedSecurity(95);
    verify::<AuthAir, Blake3, DefaultRandomCoin<Blake3>, MerkleTree<Blake3>>(
        proof, pub_inputs, &acceptable,
    )
    .is_ok()
}

/// Recompute the public authorization image for a secret (what the address would commit to).
pub fn authorization_image(secret: &Hash32) -> [u8; 16] {
    let mut s = secret_to_field(secret);
    for _ in 0..(NUM_STEPS - 1) {
        s = s.exp(3u32.into()) + BaseElement::new(C);
    }
    s.as_int().to_le_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_proof_verifies() {
        let secret = [7u8; 32];
        let auth = prove_authorization(&secret).unwrap();
        assert!(verify_authorization(&auth));
    }

    #[test]
    fn image_matches_independent_recomputation() {
        let secret = [9u8; 32];
        let auth = prove_authorization(&secret).unwrap();
        assert_eq!(auth.image, authorization_image(&secret));
    }

    #[test]
    fn tampered_image_rejected() {
        let secret = [7u8; 32];
        let mut auth = prove_authorization(&secret).unwrap();
        auth.image[0] ^= 0xff;
        assert!(!verify_authorization(&auth), "proof must not verify against a different image");
    }

    #[test]
    fn corrupted_proof_rejected() {
        let secret = [7u8; 32];
        let mut auth = prove_authorization(&secret).unwrap();
        let n = auth.proof.len();
        auth.proof[n / 2] ^= 0xff;
        assert!(!verify_authorization(&auth));
    }
}
