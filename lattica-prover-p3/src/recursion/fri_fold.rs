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

// =================================================================================================
// Multi-round commit-phase fold CHAIN — the running eval folded round by round, with the FRI squaring
// point map x → x². This is the verifier's per-query commit-phase loop (each round folds the running
// eval with that round's sibling at the round challenge β_r), reusing the validated single-fold formula.
// =================================================================================================

// row layout (width 8): running eval E(2) ‖ sibling S(2) ‖ beta B(2) ‖ point X ‖ inv2x
const C_E: usize = 0;
const C_S: usize = 2;
const C_B: usize = 4;
const C_X: usize = 6;
const C_I2X: usize = 7;
const CHAIN_WIDTH: usize = 8;

pub struct FoldChainAir;

impl BaseAir<Goldilocks> for FoldChainAir {
    fn width(&self) -> usize {
        CHAIN_WIDTH
    }
    fn num_public_values(&self) -> usize {
        4 // initial E ‖ final E
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for FoldChainAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let w = AB::Expr::from(Goldilocks::from_u64(W_EXT));
        let half = AB::Expr::from(Goldilocks::ONE.halve());
        let two = AB::Expr::TWO;

        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (
                a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(),
                a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
            )
        };

        // first row: running eval == public initial
        {
            let mut fr = builder.when_first_row();
            fr.assert_zero(cur[C_E].clone() - pis[0].clone());
            fr.assert_zero(cur[C_E + 1].clone() - pis[1].clone());
        }

        // per round (transition): inv2x correct, next.E = fold(cur), next.X = cur.X² (squaring map)
        let x = cur[C_X].clone();
        let i2x = cur[C_I2X].clone();
        builder.when_transition().assert_zero(i2x.clone() * (two.clone() * x.clone()) - AB::Expr::ONE);

        let e = (cur[C_E].clone(), cur[C_E + 1].clone());
        let s = (cur[C_S].clone(), cur[C_S + 1].clone());
        let b = (cur[C_B].clone(), cur[C_B + 1].clone());
        let sum = (e.0.clone() + s.0.clone(), e.1.clone() + s.1.clone());
        let diff = (e.0.clone() - s.0.clone(), e.1.clone() - s.1.clone());
        let prod = emul(diff, b);
        let folded0 = sum.0 * half.clone() + prod.0 * i2x.clone();
        let folded1 = sum.1 * half.clone() + prod.1 * i2x.clone();
        builder.when_transition().assert_zero(nxt[C_E].clone() - folded0);
        builder.when_transition().assert_zero(nxt[C_E + 1].clone() - folded1);
        builder.when_transition().assert_zero(nxt[C_X].clone() - x.clone() * x.clone());

        // last row: running eval == public final (the final_poly value)
        {
            let mut lr = builder.when_last_row();
            lr.assert_zero(cur[C_E].clone() - pis[2].clone());
            lr.assert_zero(cur[C_E + 1].clone() - pis[3].clone());
        }
    }
}

/// Native commit-phase fold chain: returns the per-round running evals (`evals[0]` = initial,
/// `evals[rounds]` = final) and the squaring point sequence.
pub fn native_fold_chain(e0: Challenge, sibs: &[Challenge], betas: &[Challenge], x0: Val) -> Vec<Challenge> {
    assert_eq!(sibs.len(), betas.len());
    let mut e = e0;
    let mut x = x0;
    let mut evals = vec![e0];
    for r in 0..sibs.len() {
        e = native_fold(e, sibs[r], betas[r], x);
        x = x * x;
        evals.push(e);
    }
    evals
}

fn build_chain_trace(e0: Challenge, sibs: &[Challenge], betas: &[Challenge], x0: Val) -> RowMajorMatrix<Val> {
    let rounds = sibs.len();
    let height = (rounds + 1).next_power_of_two().max(2);
    let evals = native_fold_chain(e0, sibs, betas, x0);
    let mut x = x0;
    let mut vals = vec![Val::ZERO; height * CHAIN_WIDTH];
    for r in 0..height {
        let base = r * CHAIN_WIDTH;
        let e = if r < evals.len() { evals[r] } else { *evals.last().unwrap() };
        let ec = coeffs(e);
        vals[base + C_E] = ec[0];
        vals[base + C_E + 1] = ec[1];
        // X must satisfy nxt.X = cur.X² on every transition, so fill the squaring chain through ALL rows.
        vals[base + C_X] = x;
        vals[base + C_I2X] = (Val::TWO * x).inverse();
        if r < rounds {
            let sc = coeffs(sibs[r]);
            let bc = coeffs(betas[r]);
            vals[base + C_S] = sc[0];
            vals[base + C_S + 1] = sc[1];
            vals[base + C_B] = bc[0];
            vals[base + C_B + 1] = bc[1];
        } else {
            // padding rows: sibling = running eval, beta = 0 ⇒ the fold is the identity, so the running
            // eval (= final) carries unchanged through the remaining transitions to the last row.
            vals[base + C_S] = ec[0];
            vals[base + C_S + 1] = ec[1];
        }
        x = x * x;
    }
    RowMajorMatrix::new(vals, CHAIN_WIDTH)
}

/// Prove the commit-phase fold chain takes `e0` to `final_eval` under the given siblings/betas/point.
pub fn prove_fold_chain(e0: Challenge, sibs: &[Challenge], betas: &[Challenge], x0: Val, final_eval: Challenge) -> Vec<u8> {
    let mut pis = coeffs(e0).to_vec();
    pis.extend_from_slice(&coeffs(final_eval));
    let proof = prove(&make_config(), &FoldChainAir, build_chain_trace(e0, sibs, betas, x0), &pis);
    postcard::to_allocvec(&proof).expect("serialize")
}

pub fn verify_fold_chain(proof_bytes: &[u8], e0: Challenge, final_eval: Challenge) -> bool {
    let mut pis = coeffs(e0).to_vec();
    pis.extend_from_slice(&coeffs(final_eval));
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), &FoldChainAir, &proof, &pis).is_ok()
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
    fn native_fold_matches_p3_fold_row() {
        // Bulletproof differential: native_fold (the formula the in-circuit AIR + chain implement) equals
        // p3's ACTUAL TwoAdicFriFolding::fold_row for arity 2, using p3's own point derivation
        // (s = two_adic_generator(log_height+1)^reverse_bits(index, log_height)).
        use core::marker::PhantomData;
        use p3_field::TwoAdicField;
        use p3_fri::{FriFoldingStrategy, TwoAdicFriFolding};

        fn reverse_bits(mut x: usize, bits: usize) -> usize {
            let mut r = 0;
            for _ in 0..bits {
                r = (r << 1) | (x & 1);
                x >>= 1;
            }
            r
        }

        let folding = TwoAdicFriFolding::<(), ()>(PhantomData);
        let e0 = c(2, 7);
        let e1 = c(9, 4);
        let beta = c(5, 6);
        for (index, log_height) in [(0usize, 3usize), (3, 3), (5, 4), (1, 2), (13, 4)] {
            let g = Goldilocks::two_adic_generator(log_height + 1);
            let s = g.exp_u64(reverse_bits(index, log_height) as u64);
            let mine = native_fold(e0, e1, beta, s);
            let p3: Challenge = <TwoAdicFriFolding<(), ()> as FriFoldingStrategy<Goldilocks, Challenge>>::fold_row(
                &folding,
                index,
                log_height,
                1,
                beta,
                [e0, e1].into_iter(),
            );
            assert_eq!(mine, p3, "index={index} log_height={log_height}");
        }
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

    #[test]
    #[ignore = "slow: real prover (commit-phase fold chain)"]
    fn fold_chain_proves_and_rejects() {
        let e0 = c(2, 3);
        let sibs: Vec<Challenge> = (0..6).map(|i| c(10 + i, 20 + i)).collect();
        let betas: Vec<Challenge> = (0..6).map(|i| c(100 + i, 200 + i)).collect();
        let x0 = Val::from_u64(7); // a 2-adic point; squares each round
        let evals = native_fold_chain(e0, &sibs, &betas, x0);
        let final_eval = *evals.last().unwrap();
        let proof = prove_fold_chain(e0, &sibs, &betas, x0, final_eval);
        assert!(verify_fold_chain(&proof, e0, final_eval));
        // wrong final ⇒ reject
        assert!(!verify_fold_chain(&proof, e0, final_eval + c(1, 0)));
        // tampered sibling ⇒ the chain no longer reaches `final_eval` ⇒ reject
        let mut tsibs = sibs.clone();
        tsibs[2] = tsibs[2] + c(0, 1);
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let p = prove_fold_chain(e0, &tsibs, &betas, x0, final_eval);
            verify_fold_chain(&p, e0, final_eval)
        }));
        assert!(matches!(outcome, Ok(false) | Err(_)));
    }
}
