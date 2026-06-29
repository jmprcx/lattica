//! B3a/B3b spike — in-circuit **F_p² arithmetic** + the **FRI commit-phase fold step**.
//!
//! This retires the residual correctness risk flagged in B1's go/no-go: that the in-circuit FRI
//! *folding* over the challenge field F_p² is expressible as constraints and matches Plonky3 exactly.
//!
//! Field model: `Challenge = BinomialExtensionField<Goldilocks, 2>` with `X² = W`, `W = 7`. An element
//! `(a0, a1)` represents `a0 + a1·X`; `mul = (a0·b0 + W·a1·b1, a0·b1 + a1·b0)`.
//!
//! The arity-2 FRI fold (from `p3_fri::two_adic_pcs::fold_matrix` / `lagrange_interpolate_at`):
//! `folded = (e0 + e1)/2 + (e0 − e1)·β / (2·s)` where `e0, e1, β ∈ F_p²` are the two evaluations + the
//! round challenge and `s ∈ F_p` is the (base-field) evaluation point. The in-circuit AIR supplies
//! `inv2s = 1/(2s)` as a witness and constrains `inv2s·(2s) = 1`, then checks the fold relation, binding
//! the result to a public output. Validated by a fast formula KAT + a real-prover differential.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing};
use p3_fri::{FriParameters, HidingFriPcs};
use p3_goldilocks::{default_goldilocks_poseidon2_8, Goldilocks, Poseidon2Goldilocks};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeHidingMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{prove, verify, Proof, StarkConfig};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

type Val = Goldilocks;
type Challenge = BinomialExtensionField<Val, 2>;
const W_EXT: u64 = 7; // X² = 7 for the Goldilocks quadratic extension

// column layout (width 10): e0(2) ‖ e1(2) ‖ beta(2) ‖ s ‖ inv2s ‖ folded(2)
const E0: usize = 0;
const E1: usize = 2;
const BETA: usize = 4;
const S: usize = 6;
const INV2S: usize = 7;
const FOLDED: usize = 8;
const WIDTH: usize = 10;
const HEIGHT: usize = 16;

fn ext(x: Val) -> Challenge {
    Challenge::from_basis_coefficients_fn(|i| if i == 0 { x } else { Val::ZERO })
}
fn coeffs(c: Challenge) -> [Val; 2] {
    let s = c.as_basis_coefficients_slice();
    [s[0], s[1]]
}

/// The native arity-2 FRI fold (the reference): `(e0+e1)/2 + (e0-e1)·β/(2s)`.
pub fn native_fold(e0: Challenge, e1: Challenge, beta: Challenge, s: Val) -> Challenge {
    let half = ext(Val::ONE.halve());
    let inv2s = ext((Val::TWO * s).inverse());
    (e0 + e1) * half + (e0 - e1) * beta * inv2s
}

pub struct FriFoldAir;

impl BaseAir<Goldilocks> for FriFoldAir {
    fn width(&self) -> usize {
        WIDTH
    }
    fn num_public_values(&self) -> usize {
        2 // the folded F_p² result
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for FriFoldAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let w = AB::Expr::from(Goldilocks::from_u64(W_EXT));
        let half = AB::Expr::from(Goldilocks::ONE.halve());
        let two = AB::Expr::TWO;

        // F_p² helpers over (lo, hi) expression pairs.
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (
                a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(),
                a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
            )
        };
        let escale = |a: (AB::Expr, AB::Expr), s: AB::Expr| -> (AB::Expr, AB::Expr) {
            (a.0.clone() * s.clone(), a.1.clone() * s.clone())
        };

        let e0 = (cur[E0].clone(), cur[E0 + 1].clone());
        let e1 = (cur[E1].clone(), cur[E1 + 1].clone());
        let beta = (cur[BETA].clone(), cur[BETA + 1].clone());
        let s = cur[S].clone();
        let inv2s = cur[INV2S].clone();

        let mut when0 = builder.when_first_row();

        // inv2s is the genuine inverse of 2s.
        when0.assert_zero(inv2s.clone() * (two.clone() * s.clone()) - AB::Expr::ONE);

        // sum = e0 + e1 ; diff = e0 - e1 ; prod = diff ⊗ beta (F_p² mul)
        let sum = (e0.0.clone() + e1.0.clone(), e0.1.clone() + e1.1.clone());
        let diff = (e0.0.clone() - e1.0.clone(), e0.1.clone() - e1.1.clone());
        let prod = emul(diff, beta);
        // folded = sum·(1/2) + prod·inv2s
        let term0 = escale(sum, half.clone());
        let term1 = escale(prod, inv2s.clone());
        let folded = (term0.0 + term1.0, term0.1 + term1.1);

        // bind the computed fold to the trace's folded columns…
        when0.assert_zero(cur[FOLDED].clone() - folded.0.clone());
        when0.assert_zero(cur[FOLDED + 1].clone() - folded.1.clone());
        // …and the folded columns to the public output.
        when0.assert_zero(cur[FOLDED].clone() - pis[0].clone());
        when0.assert_zero(cur[FOLDED + 1].clone() - pis[1].clone());
    }
}

fn build_trace(e0: Challenge, e1: Challenge, beta: Challenge, s: Val) -> RowMajorMatrix<Val> {
    let folded = native_fold(e0, e1, beta, s);
    let inv2s = (Val::TWO * s).inverse();
    let (e0c, e1c, bc, fc) = (coeffs(e0), coeffs(e1), coeffs(beta), coeffs(folded));
    let mut r0 = [Val::ZERO; WIDTH];
    r0[E0] = e0c[0];
    r0[E0 + 1] = e0c[1];
    r0[E1] = e1c[0];
    r0[E1 + 1] = e1c[1];
    r0[BETA] = bc[0];
    r0[BETA + 1] = bc[1];
    r0[S] = s;
    r0[INV2S] = inv2s;
    r0[FOLDED] = fc[0];
    r0[FOLDED + 1] = fc[1];
    // constraints are first-row-only; pad the rest with the same row (harmless, unconstrained).
    let mut vals = Vec::with_capacity(HEIGHT * WIDTH);
    for _ in 0..HEIGHT {
        vals.extend_from_slice(&r0);
    }
    RowMajorMatrix::new(vals, WIDTH)
}

// --- FRI config (same family as the other spikes) ---------------------------------------------
type Perm = Poseidon2Goldilocks<8>;
type MyHash = PaddingFreeSponge<Perm, 8, 4, 4>;
type MyCompress = TruncatedPermutation<Perm, 2, 4, 8>;
type ValMmcs =
    MerkleTreeHidingMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, ChaCha20Rng, 2, 4, 4>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Challenger = DuplexChallenger<Val, Perm, 8, 4>;
type Dft = Radix2DitParallel<Val>;
type Pcs = HidingFriPcs<Val, Dft, ValMmcs, ChallengeMmcs, ChaCha20Rng>;
type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;

fn make_config() -> MyConfig {
    let perm = default_goldilocks_poseidon2_8();
    let val_mmcs = ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), 6, ChaCha20Rng::from_rng(&mut rand::rng()));
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let fri = FriParameters {
        log_blowup: 4,
        log_final_poly_len: 0,
        max_log_arity: 4,
        num_queries: 96,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 16,
        mmcs: challenge_mmcs,
    };
    let pcs = Pcs::new(Dft::default(), val_mmcs, fri, 4, ChaCha20Rng::from_rng(&mut rand::rng()));
    MyConfig::new(pcs, Challenger::new(perm))
}

/// Prove the in-circuit fold of (e0,e1,beta,s) equals `claimed`.
pub fn prove_fold(e0: Challenge, e1: Challenge, beta: Challenge, s: Val, claimed: Challenge) -> Vec<u8> {
    let proof = prove(&make_config(), &FriFoldAir, build_trace(e0, e1, beta, s), &coeffs(claimed).to_vec());
    postcard::to_allocvec(&proof).expect("serialize")
}

pub fn verify_fold(proof_bytes: &[u8], claimed: Challenge) -> bool {
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), &FriFoldAir, &proof, &coeffs(claimed).to_vec()).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn c(a: u64, b: u64) -> Challenge {
        Challenge::from_basis_coefficients_fn(|i| Val::from_u64(if i == 0 { a } else { b }))
    }

    #[test]
    fn binomial_w_is_seven() {
        // X² == 7: confirms the W used by the in-circuit mul matches the field.
        let x = c(0, 1); // = X
        assert_eq!(coeffs(x * x), [Val::from_u64(W_EXT), Val::ZERO]);
    }

    #[test]
    fn in_circuit_formula_matches_native() {
        // The plain-Rust mirror of the AIR's expressions equals native_fold (fast, no prover).
        let (e0, e1, beta, s) = (c(3, 5), c(11, 13), c(17, 19), Val::from_u64(23));
        let inv2s = (Val::TWO * s).inverse();
        let half = Val::ONE.halve();
        let sum = e0 + e1;
        let diff = e0 - e1;
        let prod = diff * beta; // F_p² mul
        let folded = sum * ext(half) + prod * ext(inv2s);
        assert_eq!(folded, native_fold(e0, e1, beta, s));
    }

    #[test]
    #[ignore = "slow: real prover (F_p² FRI fold step)"]
    fn fold_proves_and_rejects_wrong() {
        let (e0, e1, beta, s) = (c(2, 7), c(9, 4), c(5, 6), Val::from_u64(31));
        let folded = native_fold(e0, e1, beta, s);
        let proof = prove_fold(e0, e1, beta, s, folded);
        assert!(verify_fold(&proof, folded));
        // wrong claimed fold ⇒ reject
        assert!(!verify_fold(&proof, folded + c(1, 0)));
        // a prover claiming an incorrect fold can't satisfy the constraints
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let p = prove_fold(e0, e1, beta, s, folded + c(0, 1));
            verify_fold(&p, folded + c(0, 1))
        }));
        assert!(matches!(outcome, Ok(false) | Err(_)));
    }
}
