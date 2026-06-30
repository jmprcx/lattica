//! The in-circuit recursive verifier — **under construction** (the multi-week B3-wire build).
//!
//! This is assembled component-by-component, each validated against the native skeleton
//! (`native_verify.rs`) / the validated primitives, then wired together. It is NOT a complete verifier
//! yet. Status: component 1 of N.
//!
//! ## Component 1 — in-circuit Fiat–Shamir transcript (`TranscriptAir`)
//! The verifier's entry: replay `p3-uni-stark::verify`'s two-phase transcript as a Poseidon2 duplex
//! sponge AIR — absorb the instance (degree bits ‖ trace commitment ‖ public values), squeeze the
//! constraint-combination challenge **α**, absorb the quotient + random commitments, squeeze the
//! out-of-domain point **ζ** — and bind α, ζ as public outputs. The sponge mechanics (overwrite rate,
//! carry capacity, prefix-free `state[RATE] += RATE`, permute) reuse `poseidon2_air`; the squeeze order
//! matches `sample` (the F_p² challenge = `(rate[3], rate[2])`). Validated to produce the same α, ζ as
//! the native `ModelChallenger` (which agrees with the real `DuplexChallenger`).
//!
//! Modeled with the absorb stream chunked into `RATE`-sized blocks (α after the instance blocks, ζ after
//! the commitment blocks). For the worked example here: 8 instance felts (2 blocks) → α, then 8
//! commitment felts (2 blocks) → ζ, i.e. 4 sponge blocks.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{FriParameters, HidingFriPcs};
use p3_goldilocks::{default_goldilocks_poseidon2_8, Goldilocks, Poseidon2Goldilocks};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeHidingMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{prove, verify, Proof, StarkConfig};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use crate::poseidon2_air::{ext_linear, int_linear, native_permute, native_steps, periodic_table, pow7, BLOCK, W};

type Val = Goldilocks;
type Challenge = BinomialExtensionField<Val, 2>;

const RATE: usize = 4;
const CAP_LANE: usize = RATE;
const N_BLOCKS: usize = 4; // 2 instance blocks (→ α) + 2 commitment blocks (→ ζ)
const HEIGHT: usize = N_BLOCKS * BLOCK;
const ALPHA_ROW: usize = 2 * BLOCK - 1; // output row of the 2nd block (the α squeeze)

// periodic: poseidon2's 11 round columns (period BLOCK) + P_BLOCK_LAST (period BLOCK, row 31)
// + P_ALPHA (period HEIGHT, 1 at ALPHA_ROW only).
const P_BLOCK_LAST: usize = 11;
const P_ALPHA: usize = 12;
const N_PERIODIC: usize = 13;

fn periodic() -> Vec<Vec<Val>> {
    let mut cols = periodic_table(); // 11 round cols, length BLOCK
    let mut block_last = vec![Val::ZERO; BLOCK];
    block_last[BLOCK - 1] = Val::ONE;
    cols.push(block_last);
    let mut alpha = vec![Val::ZERO; HEIGHT]; // full-height period ⇒ fires once, at ALPHA_ROW
    alpha[ALPHA_ROW] = Val::ONE;
    cols.push(alpha);
    cols
}

/// The native two-phase transcript reference (uses the validated `ModelChallenger`): absorb the
/// instance felts → α, absorb the commitment felts → ζ. Returns (α, ζ) as `[Val; 2]` coefficient pairs.
pub fn native_alpha_zeta(instance: &[Val], commitments: &[Val]) -> ([Val; 2], [Val; 2]) {
    let mut ch = crate::recursion::transcript::ModelChallenger::new();
    ch.observe_slice(instance);
    let alpha = ch.sample_ext();
    ch.observe_slice(commitments);
    let zeta = ch.sample_ext();
    (alpha, zeta)
}

pub struct TranscriptAir;

impl BaseAir<Goldilocks> for TranscriptAir {
    fn width(&self) -> usize {
        W
    }
    fn num_public_values(&self) -> usize {
        4 // α(2) ‖ ζ(2)
    }
    fn num_periodic_columns(&self) -> usize {
        N_PERIODIC
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        periodic()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for TranscriptAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let rate = AB::Expr::from(Goldilocks::from_u64(RATE as u64));

        // ---- Poseidon2 round constraints per block (reused) ----
        let is_init = p[0].clone();
        let is_full = p[1].clone();
        let is_partial = p[2].clone();
        let rc: Vec<AB::Expr> = (0..W).map(|i| p[3 + i].clone()).collect();
        let mut init_s: [AB::Expr; W] = core::array::from_fn(|i| cur[i].clone());
        ext_linear(&mut init_s);
        let mut full_s: [AB::Expr; W] = core::array::from_fn(|i| pow7(cur[i].clone() + rc[i].clone()));
        ext_linear(&mut full_s);
        let mut part_s: [AB::Expr; W] =
            core::array::from_fn(|i| if i == 0 { pow7(cur[0].clone() + rc[0].clone()) } else { cur[i].clone() });
        int_linear(&mut part_s);
        for i in 0..W {
            let c = is_init.clone() * (nxt[i].clone() - init_s[i].clone())
                + is_full.clone() * (nxt[i].clone() - full_s[i].clone())
                + is_partial.clone() * (nxt[i].clone() - part_s[i].clone());
            builder.when_transition().assert_zero(c);
        }

        // ---- block 0 starts from the zero capacity with the prefix-free count folded in ----
        {
            let mut fr = builder.when_first_row();
            fr.assert_zero(cur[CAP_LANE].clone() - rate.clone());
            for i in (CAP_LANE + 1)..W {
                fr.assert_zero(cur[i].clone());
            }
        }

        // ---- capacity carries across blocks (+RATE), rate lanes free (the next absorbed felts) ----
        {
            let bl = p[P_BLOCK_LAST].clone();
            builder
                .when_transition()
                .assert_zero(bl.clone() * (nxt[CAP_LANE].clone() - (cur[CAP_LANE].clone() + rate.clone())));
            for i in (CAP_LANE + 1)..W {
                builder.when_transition().assert_zero(bl.clone() * (nxt[i].clone() - cur[i].clone()));
            }
        }

        // ---- α squeeze: at the 2nd block's output row, α = (rate[3], rate[2]) ----
        {
            let a = p[P_ALPHA].clone();
            builder.assert_zero(a.clone() * (cur[3].clone() - pis[0].clone()));
            builder.assert_zero(a.clone() * (cur[2].clone() - pis[1].clone()));
        }

        // ---- ζ squeeze: at the last block's output (last row), ζ = (rate[3], rate[2]) ----
        {
            let mut lr = builder.when_last_row();
            lr.assert_zero(cur[3].clone() - pis[2].clone());
            lr.assert_zero(cur[2].clone() - pis[3].clone());
        }
    }
}

fn build_trace(instance: &[Val], commitments: &[Val]) -> RowMajorMatrix<Val> {
    assert_eq!(instance.len(), 2 * RATE);
    assert_eq!(commitments.len(), 2 * RATE);
    let mut felts = instance.to_vec();
    felts.extend_from_slice(commitments);
    let mut t = vec![Val::ZERO; HEIGHT * W];
    let mut cap = [Val::ZERO; W - RATE];
    for blk in 0..N_BLOCKS {
        let mut input = [Val::ZERO; W];
        input[..RATE].copy_from_slice(&felts[blk * RATE..blk * RATE + RATE]);
        input[RATE..].copy_from_slice(&cap);
        input[CAP_LANE] += Val::from_u64(RATE as u64);
        let rows = native_steps(input);
        for r in 0..BLOCK {
            let base = (blk * BLOCK + r) * W;
            t[base..base + W].copy_from_slice(&rows[r]);
        }
        let out = native_permute(input);
        cap.copy_from_slice(&out[RATE..]);
    }
    RowMajorMatrix::new(t, W)
}

// --- hiding (ZK) config (matches the production family) ----------------------------------------
type Perm = Poseidon2Goldilocks<8>;
type MyHash = PaddingFreeSponge<Perm, 8, 4, 4>;
type MyCompress = TruncatedPermutation<Perm, 2, 4, 8>;
type ValMmcs =
    MerkleTreeHidingMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, ChaCha20Rng, 2, 4, 4>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Challenger = DuplexChallenger<Val, Perm, 8, 4>;
type Dft = Radix2DitParallel<Val>;
type MyPcs = HidingFriPcs<Val, Dft, ValMmcs, ChallengeMmcs, ChaCha20Rng>;
type MyConfig = StarkConfig<MyPcs, Challenge, Challenger>;

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
    let pcs = MyPcs::new(Dft::default(), val_mmcs, fri, 4, ChaCha20Rng::from_rng(&mut rand::rng()));
    MyConfig::new(pcs, Challenger::new(perm))
}

/// Prove that absorbing (instance ‖ commitments) squeezes the public (α, ζ).
pub fn prove_transcript(instance: &[Val], commitments: &[Val], alpha: [Val; 2], zeta: [Val; 2]) -> Vec<u8> {
    let pis = vec![alpha[0], alpha[1], zeta[0], zeta[1]];
    let proof = prove(&make_config(), &TranscriptAir, build_trace(instance, commitments), &pis);
    postcard::to_allocvec(&proof).expect("serialize")
}

pub fn verify_transcript(proof_bytes: &[u8], alpha: [Val; 2], zeta: [Val; 2]) -> bool {
    let pis = vec![alpha[0], alpha[1], zeta[0], zeta[1]];
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), &TranscriptAir, &proof, &pis).is_ok()
}

// =================================================================================================
// Component 2 — in-circuit OOD / constraint check (the "constraint folder as constraints").
// Evaluates the INNER AIR's constraints at ζ in-circuit, combined with α (Horner), and checks
// folded(ζ) == Z_H(ζ)·quotient (i.e. folded·inv_vanishing == quotient) — the verifier's exit step.
// Inner AIR = ConstAir (2 constraints: is_first·(local−pub), is_transition·(next−local)). The domain
// selectors at ζ (is_first, is_transition, inv_vanishing) are computed natively and fed as witness for
// this component; computing them in-circuit is a separate sub-component. All arithmetic is over F_p².
// =================================================================================================

const W_EXT: u64 = 7; // X² = 7

// column layout (width 15): local(2) ‖ next(2) ‖ alpha(2) ‖ is_first(2) ‖ is_transition(2) ‖
//                            inv_vanishing(2) ‖ quotient(2) ‖ pub(1, base)
const CC_LOCAL: usize = 0;
const CC_NEXT: usize = 2;
const CC_ALPHA: usize = 4;
const CC_ISFIRST: usize = 6;
const CC_ISTRANS: usize = 8;
const CC_INVVAN: usize = 10;
const CC_QUOT: usize = 12;
const CC_PUB: usize = 14;
const CC_WIDTH: usize = 15;

pub struct ConstraintCheckAir;

impl BaseAir<Goldilocks> for ConstraintCheckAir {
    fn width(&self) -> usize {
        CC_WIDTH
    }
    fn num_public_values(&self) -> usize {
        2 // the quotient (bound)
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for ConstraintCheckAir {
    fn eval(&self, builder: &mut AB) {
        let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let w = AB::Expr::from(Goldilocks::from_u64(W_EXT));
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (
                a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(),
                a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
            )
        };
        let g = |o: usize| (cur[o].clone(), cur[o + 1].clone());

        let mut fr = builder.when_first_row();
        // c0 = is_first ⊗ (local − pub)   [pub is base, lifted to (pub, 0)]
        let local_m_pub = (cur[CC_LOCAL].clone() - cur[CC_PUB].clone(), cur[CC_LOCAL + 1].clone());
        let c0 = emul(g(CC_ISFIRST), local_m_pub);
        // c1 = is_transition ⊗ (next − local)
        let next_m_local = (cur[CC_NEXT].clone() - cur[CC_LOCAL].clone(), cur[CC_NEXT + 1].clone() - cur[CC_LOCAL + 1].clone());
        let c1 = emul(g(CC_ISTRANS), next_m_local);
        // folded = c0·α + c1   (Horner, matching the VerifierConstraintFolder accumulation order)
        let c0a = emul(c0, g(CC_ALPHA));
        let folded = (c0a.0 + c1.0, c0a.1 + c1.1);
        // check folded · inv_vanishing == quotient
        let lhs = emul(folded, g(CC_INVVAN));
        fr.assert_zero(lhs.0 - cur[CC_QUOT].clone());
        fr.assert_zero(lhs.1 - cur[CC_QUOT + 1].clone());
        // bind quotient to the public output
        fr.assert_zero(cur[CC_QUOT].clone() - pis[0].clone());
        fr.assert_zero(cur[CC_QUOT + 1].clone() - pis[1].clone());
    }
}

fn cc_build_trace(
    local: Challenge,
    next: Challenge,
    alpha: Challenge,
    is_first: Challenge,
    is_trans: Challenge,
    inv_van: Challenge,
    quotient: Challenge,
    pub_val: Val,
) -> RowMajorMatrix<Val> {
    use p3_field::BasedVectorSpace;
    let c = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
    let mut r = [Val::ZERO; CC_WIDTH];
    for (off, v) in [
        (CC_LOCAL, local),
        (CC_NEXT, next),
        (CC_ALPHA, alpha),
        (CC_ISFIRST, is_first),
        (CC_ISTRANS, is_trans),
        (CC_INVVAN, inv_van),
        (CC_QUOT, quotient),
    ] {
        let cc = c(v);
        r[off] = cc[0];
        r[off + 1] = cc[1];
    }
    r[CC_PUB] = pub_val;
    let mut vals = Vec::with_capacity(8 * CC_WIDTH);
    for _ in 0..8 {
        vals.extend_from_slice(&r);
    }
    RowMajorMatrix::new(vals, CC_WIDTH)
}

/// Prove the in-circuit constraint/OOD check for the given (opened values, challenges, selectors,
/// quotient); the quotient is the public output.
#[allow(clippy::too_many_arguments)]
pub fn prove_constraint_check(
    local: Challenge,
    next: Challenge,
    alpha: Challenge,
    is_first: Challenge,
    is_trans: Challenge,
    inv_van: Challenge,
    quotient: Challenge,
    pub_val: Val,
) -> Vec<u8> {
    use p3_field::BasedVectorSpace;
    let pis: Vec<Val> = quotient.as_basis_coefficients_slice().to_vec();
    let trace = cc_build_trace(local, next, alpha, is_first, is_trans, inv_van, quotient, pub_val);
    postcard::to_allocvec(&prove(&make_config(), &ConstraintCheckAir, trace, &pis)).expect("serialize")
}

pub fn verify_constraint_check(proof_bytes: &[u8], quotient: Challenge) -> bool {
    use p3_field::BasedVectorSpace;
    let pis: Vec<Val> = quotient.as_basis_coefficients_slice().to_vec();
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), &ConstraintCheckAir, &proof, &pis).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn felts(start: u64, n: usize) -> Vec<Val> {
        (0..n as u64).map(|i| Val::from_u64(start + i)).collect()
    }

    #[test]
    #[ignore = "slow: in-circuit transcript (α, ζ) vs ModelChallenger"]
    fn transcript_binds_alpha_zeta() {
        let instance = felts(1, 8);
        let commitments = felts(100, 8);
        let (alpha, zeta) = native_alpha_zeta(&instance, &commitments);
        let proof = prove_transcript(&instance, &commitments, alpha, zeta);
        assert!(verify_transcript(&proof, alpha, zeta), "in-circuit α/ζ must match the native challenger");
        // wrong α ⇒ reject
        let mut bad = alpha;
        bad[0] += Val::ONE;
        assert!(!verify_transcript(&proof, bad, zeta));
        // a tampered absorb ⇒ different α/ζ ⇒ unsatisfiable against the original public (α, ζ)
        let mut tinstance = instance.clone();
        tinstance[0] += Val::ONE;
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let p = prove_transcript(&tinstance, &commitments, alpha, zeta);
            verify_transcript(&p, alpha, zeta)
        }));
        assert!(matches!(outcome, Ok(false) | Err(_)));
    }

    #[test]
    #[ignore = "slow: in-circuit constraint check vs native verify_constraints"]
    fn constraint_check_matches_native() {
        use crate::recursion::native_verify::ConstAir;
        use p3_commit::{Pcs, PolynomialSpace};
        use p3_field::BasedVectorSpace;
        use p3_uni_stark::{verify_constraints, StarkGenericConfig};

        let ext = |x: Val| Challenge::from_basis_coefficients_fn(|i| if i == 0 { x } else { Val::ZERO });
        let ch = |a: u64, b: u64| Challenge::from_basis_coefficients_fn(|i| Val::from_u64(if i == 0 { a } else { b }));

        let config = make_config();
        let pcs = config.pcs();
        let domain = <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, 1 << 4);

        let local = ch(5, 6);
        let next = ch(7, 8);
        let alpha = ch(9, 10);
        let pub_val = Val::from_u64(5);
        let zeta = ch(1234567, 7654321); // not in the domain
        let sels = domain.selectors_at_point(zeta);

        // native ConstAir folder: c0 = is_first·(local−pub), c1 = is_transition·(next−local),
        // folded = c0·α + c1 (Horner order matching the eval: when_first_row then when_transition).
        let c0 = sels.is_first_row * (local - ext(pub_val));
        let c1 = sels.is_transition * (next - local);
        let folded = c0 * alpha + c1;
        let quotient = folded * sels.inv_vanishing;

        type PErr = <MyPcs as Pcs<Challenge, Challenger>>::Error;
        // native verify_constraints accepts this quotient…
        assert!(verify_constraints::<MyConfig, ConstAir, PErr>(
            &ConstAir, &[local], &[next], None, None, &[], &[pub_val], domain, zeta, alpha, quotient
        )
        .is_ok());
        // …and the in-circuit check agrees (real prover).
        let proof = prove_constraint_check(local, next, alpha, sels.is_first_row, sels.is_transition, sels.inv_vanishing, quotient, pub_val);
        assert!(verify_constraint_check(&proof, quotient), "in-circuit constraint check must accept the correct quotient");

        // a wrong quotient ⇒ both native and in-circuit reject.
        let bad = quotient + ext(Val::ONE);
        assert!(verify_constraints::<MyConfig, ConstAir, PErr>(
            &ConstAir, &[local], &[next], None, None, &[], &[pub_val], domain, zeta, alpha, bad
        )
        .is_err());
        assert!(!verify_constraint_check(&proof, bad));
    }
}
