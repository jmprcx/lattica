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
// Component 3b-iii — in-circuit `sample_bits` (the FRI query index).
// `sample_bits(bits)` = the low `bits` of the squeezed challenge's CANONICAL u64. In-circuit: decompose
// x into 64 boolean bits, reconstruct x = Σ b_i·2^i, prove the value is CANONICAL (< Goldilocks p =
// 2^64 − 2^32 + 1 ⇔ NOT(high 32 bits all 1 AND low 32 bits ≠ 0), enforced soundly by q₃₁·lo == 0 where
// q₃₁ = Π of the high 32 bits and lo = Σ_{i<32} b_i·2^i), and output the low `bits` as the index.
// Validated vs the native challenger's `sample_bits`.
// =================================================================================================

const SB_BITS: usize = 16; // index width (a representative log_height)
const SB_X: usize = 0;
const SB_B: usize = 1; // b_0..b_63
const SB_Q: usize = SB_B + 64; // q_1..q_31 (product chain over the high 32 bits)
const SB_WIDTH: usize = SB_Q + 31;

pub struct SampleBitsAir;

impl BaseAir<Goldilocks> for SampleBitsAir {
    fn width(&self) -> usize {
        SB_WIDTH
    }
    fn num_public_values(&self) -> usize {
        1 // the query index
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for SampleBitsAir {
    fn eval(&self, builder: &mut AB) {
        let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let pow2 = |i: usize| AB::Expr::from(Goldilocks::from_u64(1u64 << i));
        let mut fr = builder.when_first_row();

        // each bit is boolean
        for i in 0..64 {
            let b = cur[SB_B + i].clone();
            fr.assert_zero(b.clone() * (one.clone() - b));
        }
        // reconstruction: x = Σ_{i=0}^{63} b_i·2^i
        let mut recon = AB::Expr::ZERO;
        for i in 0..64 {
            recon = recon + cur[SB_B + i].clone() * pow2(i);
        }
        fr.assert_zero(cur[SB_X].clone() - recon);

        // product chain over the high 32 bits: q_1 = b_32·b_33, q_k = q_{k-1}·b_{32+k}; q_31 = Π high bits
        fr.assert_zero(cur[SB_Q].clone() - cur[SB_B + 32].clone() * cur[SB_B + 33].clone());
        for k in 2..=31 {
            fr.assert_zero(cur[SB_Q + k - 1].clone() - cur[SB_Q + k - 2].clone() * cur[SB_B + 32 + k].clone());
        }
        // canonical: q_31 · lo == 0  (lo = Σ_{i<32} b_i·2^i) ⇒ value < p
        let mut lo = AB::Expr::ZERO;
        for i in 0..32 {
            lo = lo + cur[SB_B + i].clone() * pow2(i);
        }
        fr.assert_zero(cur[SB_Q + 30].clone() * lo);

        // index = low SB_BITS bits, bound to the public output
        let mut idx = AB::Expr::ZERO;
        for i in 0..SB_BITS {
            idx = idx + cur[SB_B + i].clone() * pow2(i);
        }
        fr.assert_zero(idx - pis[0].clone());
    }
}

fn sb_build_trace(x: Val) -> RowMajorMatrix<Val> {
    use p3_field::PrimeField64;
    let v = x.as_canonical_u64();
    let mut r = [Val::ZERO; SB_WIDTH];
    r[SB_X] = x;
    for i in 0..64 {
        r[SB_B + i] = Val::from_u64((v >> i) & 1);
    }
    // product chain q_1..q_31 over the high 32 bits
    let mut q = (v >> 32) & 1; // = b_32
    for k in 1..=31 {
        q &= (v >> (32 + k)) & 1;
        r[SB_Q + k - 1] = Val::from_u64(q);
    }
    let mut vals = Vec::with_capacity(8 * SB_WIDTH);
    for _ in 0..8 {
        vals.extend_from_slice(&r);
    }
    RowMajorMatrix::new(vals, SB_WIDTH)
}

/// Native reference: the low `SB_BITS` bits of x's canonical u64.
pub fn native_sample_bits(x: Val) -> u64 {
    use p3_field::PrimeField64;
    x.as_canonical_u64() & ((1u64 << SB_BITS) - 1)
}

pub fn prove_sample_bits(x: Val, index: u64) -> Vec<u8> {
    postcard::to_allocvec(&prove(&make_config(), &SampleBitsAir, sb_build_trace(x), &vec![Val::from_u64(index)])).expect("serialize")
}

pub fn verify_sample_bits(proof_bytes: &[u8], index: u64) -> bool {
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), &SampleBitsAir, &proof, &vec![Val::from_u64(index)]).is_ok()
}

// =================================================================================================
// Component 3b-ii — in-circuit reduced opening (the FRI DEEP combination), single matrix / single point.
// p3 reduces a query's matrix openings to: reduced[X] = inv_denom[X] · Σ_i α^i·(p_i[X] − y_i), where
// p_i[X] is the opened row value of column i at the query point X, y_i is the claimed evaluation at ζ,
// and inv_denom[X] = 1/(X − ζ) (the DEEP denominator). Built in-circuit (F_p², in-circuit inverse,
// Horner over α), validated vs a native computation of the same. (The multi-matrix α-power offset +
// multi-point {ζ, ζ·g} accumulation is the wiring.)
// =================================================================================================

const RO_NCOLS: usize = 4;
const RO_P: usize = 0; // p_0..p_3 (base row values), 1 each
const RO_Y: usize = RO_NCOLS; // y_0..y_3 (F_p² openings at ζ), 2 each
const RO_ALPHA: usize = RO_Y + 2 * RO_NCOLS;
const RO_X: usize = RO_ALPHA + 2; // query point (base)
const RO_ZETA: usize = RO_X + 1;
const RO_INV_DENOM: usize = RO_ZETA + 2;
const RO_WIDTH: usize = RO_INV_DENOM + 2;

pub struct ReducedOpeningAir;

impl BaseAir<Goldilocks> for ReducedOpeningAir {
    fn width(&self) -> usize {
        RO_WIDTH
    }
    fn num_public_values(&self) -> usize {
        2 // the reduced opening
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for ReducedOpeningAir {
    fn eval(&self, builder: &mut AB) {
        let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let zero = AB::Expr::ZERO;
        let w = AB::Expr::from(Goldilocks::from_u64(W_EXT));
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (
                a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(),
                a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
            )
        };

        let mut fr = builder.when_first_row();
        let alpha = (cur[RO_ALPHA].clone(), cur[RO_ALPHA + 1].clone());
        let zeta = (cur[RO_ZETA].clone(), cur[RO_ZETA + 1].clone());
        let inv_denom = (cur[RO_INV_DENOM].clone(), cur[RO_INV_DENOM + 1].clone());

        // inv_denom · (X − ζ) == 1  [X − ζ = (X − ζ_0, −ζ_1)]
        let x_m_zeta = (cur[RO_X].clone() - zeta.0.clone(), zero.clone() - zeta.1.clone());
        let chk = emul(inv_denom.clone(), x_m_zeta);
        fr.assert_zero(chk.0 - one.clone());
        fr.assert_zero(chk.1);

        // num = Σ_i α^i·(p_i − y_i)  via Horner (i high → low)
        let mut acc = (zero.clone(), zero.clone());
        for i in (0..RO_NCOLS).rev() {
            let d = (cur[RO_P + i].clone() - cur[RO_Y + 2 * i].clone(), zero.clone() - cur[RO_Y + 2 * i + 1].clone());
            let t = emul(acc, alpha.clone());
            acc = (t.0 + d.0, t.1 + d.1);
        }
        // reduced = inv_denom · num
        let reduced = emul(inv_denom, acc);
        fr.assert_zero(reduced.0 - pis[0].clone());
        fr.assert_zero(reduced.1 - pis[1].clone());
    }
}

fn ro_build_trace(p: [Val; RO_NCOLS], y: [Challenge; RO_NCOLS], alpha: Challenge, x: Val, zeta: Challenge, reduced: Challenge) -> RowMajorMatrix<Val> {
    use p3_field::BasedVectorSpace;
    let c = |v: Challenge| -> [Val; 2] { v.as_basis_coefficients_slice().try_into().unwrap() };
    let inv_denom = (Challenge::from(x) - zeta).inverse();
    let mut r = [Val::ZERO; RO_WIDTH];
    for i in 0..RO_NCOLS {
        r[RO_P + i] = p[i];
        let yc = c(y[i]);
        r[RO_Y + 2 * i] = yc[0];
        r[RO_Y + 2 * i + 1] = yc[1];
    }
    let (ac, zc, idc, _rc) = (c(alpha), c(zeta), c(inv_denom), c(reduced));
    r[RO_ALPHA] = ac[0];
    r[RO_ALPHA + 1] = ac[1];
    r[RO_X] = x;
    r[RO_ZETA] = zc[0];
    r[RO_ZETA + 1] = zc[1];
    r[RO_INV_DENOM] = idc[0];
    r[RO_INV_DENOM + 1] = idc[1];
    let mut vals = Vec::with_capacity(8 * RO_WIDTH);
    for _ in 0..8 {
        vals.extend_from_slice(&r);
    }
    RowMajorMatrix::new(vals, RO_WIDTH)
}

/// Native reduced opening: `(X − ζ)⁻¹ · Σ_i α^i·(p_i − y_i)`.
pub fn native_reduced_opening(p: [Val; RO_NCOLS], y: [Challenge; RO_NCOLS], alpha: Challenge, x: Val, zeta: Challenge) -> Challenge {
    let mut num = Challenge::ZERO;
    for i in (0..RO_NCOLS).rev() {
        num = num * alpha + (Challenge::from(p[i]) - y[i]);
    }
    (Challenge::from(x) - zeta).inverse() * num
}

pub fn prove_reduced_opening(p: [Val; RO_NCOLS], y: [Challenge; RO_NCOLS], alpha: Challenge, x: Val, zeta: Challenge, reduced: Challenge) -> Vec<u8> {
    use p3_field::BasedVectorSpace;
    let pis = reduced.as_basis_coefficients_slice().to_vec();
    postcard::to_allocvec(&prove(&make_config(), &ReducedOpeningAir, ro_build_trace(p, y, alpha, x, zeta, reduced), &pis)).expect("serialize")
}

pub fn verify_reduced_opening(proof_bytes: &[u8], reduced: Challenge) -> bool {
    use p3_field::BasedVectorSpace;
    let pis = reduced.as_basis_coefficients_slice().to_vec();
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), &ReducedOpeningAir, &proof, &pis).is_ok()
}

// =================================================================================================
// Component 3b-i — in-circuit MMCS leaf hash (PaddingFreeSponge).
// A FRI query opens a committed matrix ROW; the MMCS hashes that row to a 4-felt leaf digest via
// `MyHash = PaddingFreeSponge<Perm,8,4,4>`, then merges up the path (the validated `fri_merkle` gadget).
// This builds the leaf hash in-circuit: a Poseidon2 sponge that OVERWRITES the rate lanes, CARRIES the
// capacity, and (unlike the challenger) folds in NO prefix-free count. Validated vs native `MyHash`.
// Worked example: a length-8 row → 2 sponge blocks → the 4-felt leaf digest.
// =================================================================================================

const LH_LEN: usize = 8; // row length (a multiple of RATE)
const LH_BLOCKS: usize = LH_LEN / RATE; // 2
const LH_HEIGHT: usize = LH_BLOCKS * BLOCK;
const LH_P_BLOCK_LAST: usize = 11;
const LH_N_PERIODIC: usize = 12;

fn lh_periodic() -> Vec<Vec<Val>> {
    let mut cols = periodic_table();
    let mut block_last = vec![Val::ZERO; BLOCK];
    block_last[BLOCK - 1] = Val::ONE;
    cols.push(block_last);
    cols
}

pub struct LeafHashAir;

impl BaseAir<Goldilocks> for LeafHashAir {
    fn width(&self) -> usize {
        W
    }
    fn num_public_values(&self) -> usize {
        4 // the leaf digest
    }
    fn num_periodic_columns(&self) -> usize {
        LH_N_PERIODIC
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        lh_periodic()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for LeafHashAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();

        // Poseidon2 rounds (reused).
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

        // block 0 starts from the all-zero capacity (NO prefix-free count) ...
        {
            let mut fr = builder.when_first_row();
            for i in RATE..W {
                fr.assert_zero(cur[i].clone());
            }
        }
        // ... capacity carries unchanged across blocks (rate lanes free = the next row chunk) ...
        {
            let bl = p[LH_P_BLOCK_LAST].clone();
            for i in RATE..W {
                builder.when_transition().assert_zero(bl.clone() * (nxt[i].clone() - cur[i].clone()));
            }
        }
        // ... the final block's rate lanes are the leaf digest.
        {
            let mut lr = builder.when_last_row();
            for k in 0..4 {
                lr.assert_zero(cur[k].clone() - pis[k].clone());
            }
        }
    }
}

fn lh_build_trace(row: &[Val]) -> RowMajorMatrix<Val> {
    assert_eq!(row.len(), LH_LEN);
    let mut t = vec![Val::ZERO; LH_HEIGHT * W];
    let mut cap = [Val::ZERO; W - RATE];
    for blk in 0..LH_BLOCKS {
        let mut input = [Val::ZERO; W];
        input[..RATE].copy_from_slice(&row[blk * RATE..blk * RATE + RATE]);
        input[RATE..].copy_from_slice(&cap); // capacity carries; no count
        let rows = native_steps(input);
        for r in 0..BLOCK {
            let base = (blk * BLOCK + r) * W;
            t[base..base + W].copy_from_slice(&rows[r]);
        }
        cap.copy_from_slice(&native_permute(input)[RATE..]);
    }
    RowMajorMatrix::new(t, W)
}

/// Prove that `MyHash(row) == digest` (the leaf hash), with the digest as public output.
pub fn prove_leaf_hash(row: &[Val], digest: [Val; 4]) -> Vec<u8> {
    postcard::to_allocvec(&prove(&make_config(), &LeafHashAir, lh_build_trace(row), &digest.to_vec())).expect("serialize")
}

pub fn verify_leaf_hash(proof_bytes: &[u8], digest: [Val; 4]) -> bool {
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), &LeafHashAir, &proof, &digest.to_vec()).is_ok()
}

// =================================================================================================
// Component 4 — in-circuit domain selectors at ζ.
// Computes the LagrangeSelectors p3 uses in verify_constraints, in-circuit, from ζ + the domain
// parameters: for the trace domain (shift = 1 ⇒ u = ζ),
//   z_h = ζ^(2^log_size) − 1,  is_first = z_h/(ζ−1),  is_last = z_h/(ζ−g⁻¹),
//   is_transition = ζ − g⁻¹,   inv_vanishing = z_h⁻¹,   g = two_adic_generator(log_size).
// Validated against the real `domain.selectors_at_point(ζ)`. This is the sub-component that feeds
// component 2's selectors in-circuit (instead of as witness). All arithmetic over F_p².
// =================================================================================================

const DS_LOG_SIZE: usize = 4; // domain size 2^4 = 16 (the squaring-chain length)
const DS_ZETA: usize = 0;
// squaring chain S_1..S_{LOG_SIZE} at offsets 2*i (S_0 = ζ at offset 0)
const DS_INV_UM1: usize = 2 * (DS_LOG_SIZE + 1); // inv(ζ − 1)
const DS_INV_UMG: usize = DS_INV_UM1 + 2; // inv(ζ − g⁻¹)
const DS_INV_ZH: usize = DS_INV_UMG + 2; // inv(z_h)
const DS_WIDTH: usize = DS_INV_ZH + 2;

fn ds_g_inv() -> Val {
    use p3_field::TwoAdicField;
    Goldilocks::two_adic_generator(DS_LOG_SIZE).inverse()
}

/// Native reference for the squaring chain + inverses (shift = 1). Returns
/// (chain[1..=LOG_SIZE], inv_um1, inv_umg, inv_zh) so the trace can be filled.
fn ds_native(zeta: Challenge) -> (Vec<Challenge>, Challenge, Challenge, Challenge) {
    let mut chain = Vec::with_capacity(DS_LOG_SIZE);
    let mut s = zeta;
    for _ in 0..DS_LOG_SIZE {
        s = s * s;
        chain.push(s);
    }
    let z_h = *chain.last().unwrap() - Challenge::ONE;
    let g_inv = Challenge::from(ds_g_inv());
    let inv_um1 = (zeta - Challenge::ONE).inverse();
    let inv_umg = (zeta - g_inv).inverse();
    let inv_zh = z_h.inverse();
    (chain, inv_um1, inv_umg, inv_zh)
}

pub struct DomainSelectorsAir;

impl BaseAir<Goldilocks> for DomainSelectorsAir {
    fn width(&self) -> usize {
        DS_WIDTH
    }
    fn num_public_values(&self) -> usize {
        8 // is_first(2) ‖ is_last(2) ‖ is_transition(2) ‖ inv_vanishing(2)
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for DomainSelectorsAir {
    fn eval(&self, builder: &mut AB) {
        let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let g_inv = AB::Expr::from(ds_g_inv());
        let w = AB::Expr::from(Goldilocks::from_u64(W_EXT));
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (
                a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(),
                a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
            )
        };
        let g = |o: usize| (cur[o].clone(), cur[o + 1].clone());

        let mut fr = builder.when_first_row();
        // squaring chain: S_i == (S_{i-1})², S_0 = ζ
        for i in 1..=DS_LOG_SIZE {
            let sq = emul(g(2 * (i - 1)), g(2 * (i - 1)));
            fr.assert_zero(cur[2 * i].clone() - sq.0);
            fr.assert_zero(cur[2 * i + 1].clone() - sq.1);
        }
        let u = g(DS_ZETA);
        let z_h = (cur[2 * DS_LOG_SIZE].clone() - one.clone(), cur[2 * DS_LOG_SIZE + 1].clone());
        let u_m1 = (u.0.clone() - one.clone(), u.1.clone());
        let u_mg = (u.0.clone() - g_inv, u.1.clone());

        // inverse witnesses are genuine inverses (⊗ == (1, 0))
        let p1 = emul(g(DS_INV_UM1), u_m1.clone());
        fr.assert_zero(p1.0 - one.clone());
        fr.assert_zero(p1.1);
        let p2 = emul(g(DS_INV_UMG), u_mg.clone());
        fr.assert_zero(p2.0 - one.clone());
        fr.assert_zero(p2.1);
        let p3 = emul(g(DS_INV_ZH), z_h.clone());
        fr.assert_zero(p3.0 - one.clone());
        fr.assert_zero(p3.1);

        // selectors → public
        let is_first = emul(z_h.clone(), g(DS_INV_UM1));
        let is_last = emul(z_h, g(DS_INV_UMG));
        fr.assert_zero(is_first.0 - pis[0].clone());
        fr.assert_zero(is_first.1 - pis[1].clone());
        fr.assert_zero(is_last.0 - pis[2].clone());
        fr.assert_zero(is_last.1 - pis[3].clone());
        fr.assert_zero(u_mg.0 - pis[4].clone()); // is_transition = ζ − g⁻¹
        fr.assert_zero(u_mg.1 - pis[5].clone());
        fr.assert_zero(cur[DS_INV_ZH].clone() - pis[6].clone()); // inv_vanishing = z_h⁻¹
        fr.assert_zero(cur[DS_INV_ZH + 1].clone() - pis[7].clone());
    }
}

fn ds_build_trace(zeta: Challenge) -> RowMajorMatrix<Val> {
    use p3_field::BasedVectorSpace;
    let c = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
    let (chain, inv_um1, inv_umg, inv_zh) = ds_native(zeta);
    let mut r = [Val::ZERO; DS_WIDTH];
    let zc = c(zeta);
    r[DS_ZETA] = zc[0];
    r[DS_ZETA + 1] = zc[1];
    for (i, s) in chain.iter().enumerate() {
        let sc = c(*s);
        r[2 * (i + 1)] = sc[0];
        r[2 * (i + 1) + 1] = sc[1];
    }
    for (off, v) in [(DS_INV_UM1, inv_um1), (DS_INV_UMG, inv_umg), (DS_INV_ZH, inv_zh)] {
        let vc = c(v);
        r[off] = vc[0];
        r[off + 1] = vc[1];
    }
    let mut vals = Vec::with_capacity(8 * DS_WIDTH);
    for _ in 0..8 {
        vals.extend_from_slice(&r);
    }
    RowMajorMatrix::new(vals, DS_WIDTH)
}

/// Prove the in-circuit domain selectors at ζ; the 4 selectors are the public output.
pub fn prove_domain_selectors(zeta: Challenge, selectors: [Challenge; 4]) -> Vec<u8> {
    use p3_field::BasedVectorSpace;
    let pis: Vec<Val> = selectors.iter().flat_map(|s| s.as_basis_coefficients_slice().to_vec()).collect();
    postcard::to_allocvec(&prove(&make_config(), &DomainSelectorsAir, ds_build_trace(zeta), &pis)).expect("serialize")
}

pub fn verify_domain_selectors(proof_bytes: &[u8], selectors: [Challenge; 4]) -> bool {
    use p3_field::BasedVectorSpace;
    let pis: Vec<Val> = selectors.iter().flat_map(|s| s.as_basis_coefficients_slice().to_vec()).collect();
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), &DomainSelectorsAir, &proof, &pis).is_ok()
}

// =================================================================================================
// Component 3a — in-circuit FRI commit-phase challenge derivation.
// The first slice of the FRI query loop's prerequisites: extend the transcript past ζ to observe each
// FRI round commitment and squeeze every round challenge β_r (alongside α, ζ). Validated against the
// native ModelChallenger. (The query loop proper — per-query Merkle openings + folds + reduced openings
// — is the remaining bulk of component 3.) Worked with R = 4 FRI rounds: 2 instance blocks → α,
// 2 commitment blocks → ζ, then 4 round blocks → β_0..β_3 = 8 sponge blocks (256 rows).
// =================================================================================================

const FRI_ROUNDS: usize = 4;
const FT_BLOCKS: usize = 4 + FRI_ROUNDS; // 8
const FT_HEIGHT: usize = FT_BLOCKS * BLOCK; // 256

// periodic: rounds (11) + P_BLOCK_LAST (12) + one-hots binding α, ζ, β_0, β_1, β_2 at their block-output
// rows (β_3 is bound at the last row). Each one-hot is a full-height (256) period ⇒ fires once.
const FT_P_BLOCK_LAST: usize = 11;
const FT_P_FIRST_BIND: usize = 12; // 5 binding one-hots: α, ζ, β_0, β_1, β_2
const FT_N_PERIODIC: usize = FT_P_FIRST_BIND + 5;

/// Output rows of the blocks whose squeeze is bound by a periodic one-hot: α@block1, ζ@block3,
/// β_0@block4, β_1@block5, β_2@block6 (β_3@block7 = the last row).
const FT_BIND_BLOCKS: [usize; 5] = [1, 3, 4, 5, 6];

fn ft_periodic() -> Vec<Vec<Val>> {
    let mut cols = periodic_table();
    let mut block_last = vec![Val::ZERO; BLOCK];
    block_last[BLOCK - 1] = Val::ONE;
    cols.push(block_last);
    for blk in FT_BIND_BLOCKS {
        let mut sel = vec![Val::ZERO; FT_HEIGHT];
        sel[(blk + 1) * BLOCK - 1] = Val::ONE; // that block's output row
        cols.push(sel);
    }
    cols
}

/// Native reference: α, ζ, then β_0..β_{R-1}, via the validated ModelChallenger.
pub fn native_fri_challenges(instance: &[Val], zeta_commits: &[Val], round_commits: &[[Val; RATE]]) -> Vec<[Val; 2]> {
    let mut ch = crate::recursion::transcript::ModelChallenger::new();
    ch.observe_slice(instance);
    let mut out = vec![ch.sample_ext()]; // α
    ch.observe_slice(zeta_commits);
    out.push(ch.sample_ext()); // ζ
    for rc in round_commits {
        ch.observe_slice(rc);
        out.push(ch.sample_ext()); // β_r
    }
    out
}

pub struct FriTranscriptAir;

impl BaseAir<Goldilocks> for FriTranscriptAir {
    fn width(&self) -> usize {
        W
    }
    fn num_public_values(&self) -> usize {
        2 * (2 + FRI_ROUNDS) // α, ζ, β_0..β_{R-1}
    }
    fn num_periodic_columns(&self) -> usize {
        FT_N_PERIODIC
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        ft_periodic()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for FriTranscriptAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let rate = AB::Expr::from(Goldilocks::from_u64(RATE as u64));

        // Poseidon2 rounds per block (reused).
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

        // capacity init + carry (+RATE), same sponge mechanics as TranscriptAir.
        {
            let mut fr = builder.when_first_row();
            fr.assert_zero(cur[CAP_LANE].clone() - rate.clone());
            for i in (CAP_LANE + 1)..W {
                fr.assert_zero(cur[i].clone());
            }
        }
        {
            let bl = p[FT_P_BLOCK_LAST].clone();
            builder
                .when_transition()
                .assert_zero(bl.clone() * (nxt[CAP_LANE].clone() - (cur[CAP_LANE].clone() + rate.clone())));
            for i in (CAP_LANE + 1)..W {
                builder.when_transition().assert_zero(bl.clone() * (nxt[i].clone() - cur[i].clone()));
            }
        }

        // squeeze bindings: α, ζ, β_0, β_1, β_2 at their block-output rows; β_3 at the last row.
        // each challenge = (rate[3], rate[2]).
        for (k, _blk) in FT_BIND_BLOCKS.iter().enumerate() {
            let sel = p[FT_P_FIRST_BIND + k].clone();
            builder.assert_zero(sel.clone() * (cur[3].clone() - pis[2 * k].clone()));
            builder.assert_zero(sel.clone() * (cur[2].clone() - pis[2 * k + 1].clone()));
        }
        {
            let last = 2 + FRI_ROUNDS - 1; // index of β_{R-1}
            let mut lr = builder.when_last_row();
            lr.assert_zero(cur[3].clone() - pis[2 * last].clone());
            lr.assert_zero(cur[2].clone() - pis[2 * last + 1].clone());
        }
    }
}

fn ft_build_trace(felts: &[Val]) -> RowMajorMatrix<Val> {
    assert_eq!(felts.len(), FT_BLOCKS * RATE);
    let mut t = vec![Val::ZERO; FT_HEIGHT * W];
    let mut cap = [Val::ZERO; W - RATE];
    for blk in 0..FT_BLOCKS {
        let mut input = [Val::ZERO; W];
        input[..RATE].copy_from_slice(&felts[blk * RATE..blk * RATE + RATE]);
        input[RATE..].copy_from_slice(&cap);
        input[CAP_LANE] += Val::from_u64(RATE as u64);
        let rows = native_steps(input);
        for r in 0..BLOCK {
            let base = (blk * BLOCK + r) * W;
            t[base..base + W].copy_from_slice(&rows[r]);
        }
        cap.copy_from_slice(&native_permute(input)[RATE..]);
    }
    RowMajorMatrix::new(t, W)
}

/// Prove that the transcript over (instance ‖ ζ-commits ‖ round-commits) squeezes the public challenges
/// (α, ζ, β_0..β_{R-1}), each a 2-coefficient F_p² value.
pub fn prove_fri_transcript(felts: &[Val], challenges: &[[Val; 2]]) -> Vec<u8> {
    let pis: Vec<Val> = challenges.iter().flat_map(|c| [c[0], c[1]]).collect();
    postcard::to_allocvec(&prove(&make_config(), &FriTranscriptAir, ft_build_trace(felts), &pis)).expect("serialize")
}

pub fn verify_fri_transcript(proof_bytes: &[u8], challenges: &[[Val; 2]]) -> bool {
    let pis: Vec<Val> = challenges.iter().flat_map(|c| [c[0], c[1]]).collect();
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), &FriTranscriptAir, &proof, &pis).is_ok()
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

// =================================================================================================
// AIR PORT (step 1) — compose component 4 (in-circuit domain selectors) INTO component 2 (constraint
// check). The verifier's constraint/OOD region now DERIVES is_first/is_transition/inv_vanishing from ζ
// in-circuit (the squaring chain + selector formulas + in-circuit inverses) instead of taking them as
// witness, then folds the constraints with α and checks folded·inv_van == quotient. Validated end-to-end
// vs the real `domain.selectors_at_point(ζ)` + the folded relation — the first wired multi-gadget
// fragment of the verifier AIR. (Both sub-gadgets are individually validated; this validates they
// compose: the AIR accepts iff the selectors-at-ζ are correct AND the constraint relation holds.)
// =================================================================================================

const CCS_ZETA: usize = 0; // squaring chain S_1..S_{DS_LOG_SIZE} follows at offset 2*i (S_0 = ζ)
const CCS_INV_UM1: usize = 2 * (DS_LOG_SIZE + 1);
const CCS_INV_UMG: usize = CCS_INV_UM1 + 2;
const CCS_INV_ZH: usize = CCS_INV_UMG + 2;
const CCS_LOCAL: usize = CCS_INV_ZH + 2;
const CCS_NEXT: usize = CCS_LOCAL + 2;
const CCS_ALPHA: usize = CCS_NEXT + 2;
const CCS_PUB: usize = CCS_ALPHA + 2; // base
const CCS_QUOT: usize = CCS_PUB + 1;
const CCS_WIDTH: usize = CCS_QUOT + 2;

pub struct ConstraintCheckWithSelectorsAir;

impl BaseAir<Goldilocks> for ConstraintCheckWithSelectorsAir {
    fn width(&self) -> usize {
        CCS_WIDTH
    }
    fn num_public_values(&self) -> usize {
        2 // the quotient (bound)
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for ConstraintCheckWithSelectorsAir {
    fn eval(&self, builder: &mut AB) {
        let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let w = AB::Expr::from(Goldilocks::from_u64(W_EXT));
        let g_inv = AB::Expr::from(ds_g_inv());
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (
                a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(),
                a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
            )
        };
        let g = |o: usize| (cur[o].clone(), cur[o + 1].clone());
        let mut fr = builder.when_first_row();

        // --- component 4: derive the selectors from ζ ---
        for i in 1..=DS_LOG_SIZE {
            let sq = emul(g(2 * (i - 1)), g(2 * (i - 1)));
            fr.assert_zero(cur[2 * i].clone() - sq.0);
            fr.assert_zero(cur[2 * i + 1].clone() - sq.1);
        }
        let u = g(CCS_ZETA);
        let z_h = (cur[2 * DS_LOG_SIZE].clone() - one.clone(), cur[2 * DS_LOG_SIZE + 1].clone());
        let u_m1 = (u.0.clone() - one.clone(), u.1.clone());
        let u_mg = (u.0.clone() - g_inv, u.1.clone());
        let p1 = emul(g(CCS_INV_UM1), u_m1);
        fr.assert_zero(p1.0 - one.clone());
        fr.assert_zero(p1.1);
        let p2 = emul(g(CCS_INV_UMG), u_mg.clone());
        fr.assert_zero(p2.0 - one.clone());
        fr.assert_zero(p2.1);
        let p3 = emul(g(CCS_INV_ZH), z_h.clone());
        fr.assert_zero(p3.0 - one.clone());
        fr.assert_zero(p3.1);
        let is_first = emul(z_h, g(CCS_INV_UM1));
        let is_trans = u_mg; // is_transition = ζ − g⁻¹
        let inv_van = g(CCS_INV_ZH);

        // --- component 2: fold the constraints with the derived selectors ---
        let local_m_pub = (cur[CCS_LOCAL].clone() - cur[CCS_PUB].clone(), cur[CCS_LOCAL + 1].clone());
        let c0 = emul(is_first, local_m_pub);
        let next_m_local = (cur[CCS_NEXT].clone() - cur[CCS_LOCAL].clone(), cur[CCS_NEXT + 1].clone() - cur[CCS_LOCAL + 1].clone());
        let c1 = emul(is_trans, next_m_local);
        let c0a = emul(c0, g(CCS_ALPHA));
        let folded = (c0a.0 + c1.0, c0a.1 + c1.1);
        let lhs = emul(folded, inv_van);
        fr.assert_zero(lhs.0 - cur[CCS_QUOT].clone());
        fr.assert_zero(lhs.1 - cur[CCS_QUOT + 1].clone());
        fr.assert_zero(cur[CCS_QUOT].clone() - pis[0].clone());
        fr.assert_zero(cur[CCS_QUOT + 1].clone() - pis[1].clone());
    }
}

/// Native reference for the composed fragment: the quotient implied by deriving the selectors at ζ and
/// folding the (ConstAir-shaped) constraints with α. Uses the same selector formula as component 4.
pub fn ccs_native_quotient(zeta: Challenge, alpha: Challenge, local: Challenge, next: Challenge, pub_val: Val) -> Challenge {
    let (chain, inv_um1, _inv_umg, inv_zh) = ds_native(zeta);
    let z_h = *chain.last().unwrap() - Challenge::ONE;
    let is_first = z_h * inv_um1;
    let is_trans = zeta - Challenge::from(ds_g_inv());
    let c0 = is_first * (local - Challenge::from(pub_val));
    let c1 = is_trans * (next - local);
    (c0 * alpha + c1) * inv_zh
}

fn ccs_build_trace(zeta: Challenge, alpha: Challenge, local: Challenge, next: Challenge, pub_val: Val, quotient: Challenge) -> RowMajorMatrix<Val> {
    use p3_field::BasedVectorSpace;
    let c = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
    let (chain, inv_um1, inv_umg, inv_zh) = ds_native(zeta);
    let mut r = [Val::ZERO; CCS_WIDTH];
    let zc = c(zeta);
    r[CCS_ZETA] = zc[0];
    r[CCS_ZETA + 1] = zc[1];
    for (i, s) in chain.iter().enumerate() {
        let sc = c(*s);
        r[2 * (i + 1)] = sc[0];
        r[2 * (i + 1) + 1] = sc[1];
    }
    for (off, v) in [(CCS_INV_UM1, inv_um1), (CCS_INV_UMG, inv_umg), (CCS_INV_ZH, inv_zh), (CCS_LOCAL, local), (CCS_NEXT, next), (CCS_ALPHA, alpha), (CCS_QUOT, quotient)] {
        let vc = c(v);
        r[off] = vc[0];
        r[off + 1] = vc[1];
    }
    r[CCS_PUB] = pub_val;
    let mut vals = Vec::with_capacity(8 * CCS_WIDTH);
    for _ in 0..8 {
        vals.extend_from_slice(&r);
    }
    RowMajorMatrix::new(vals, CCS_WIDTH)
}

pub fn prove_ccs(zeta: Challenge, alpha: Challenge, local: Challenge, next: Challenge, pub_val: Val, quotient: Challenge) -> Vec<u8> {
    use p3_field::BasedVectorSpace;
    let pis = quotient.as_basis_coefficients_slice().to_vec();
    postcard::to_allocvec(&prove(&make_config(), &ConstraintCheckWithSelectorsAir, ccs_build_trace(zeta, alpha, local, next, pub_val, quotient), &pis)).expect("serialize")
}

pub fn verify_ccs(proof_bytes: &[u8], quotient: Challenge) -> bool {
    use p3_field::BasedVectorSpace;
    let pis = quotient.as_basis_coefficients_slice().to_vec();
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), &ConstraintCheckWithSelectorsAir, &proof, &pis).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn felts(start: u64, n: usize) -> Vec<Val> {
        (0..n as u64).map(|i| Val::from_u64(start + i)).collect()
    }

    #[test]
    #[ignore = "slow: composed constraint-check w/ in-circuit selectors vs native selectors_at_point + fold"]
    fn ccs_matches_native() {
        use p3_commit::{Pcs, PolynomialSpace};
        use p3_field::BasedVectorSpace;
        use p3_uni_stark::StarkGenericConfig;
        let config = make_config();
        let domain = <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(config.pcs(), 1 << DS_LOG_SIZE);
        let ch = |a: u64, b: u64| Challenge::from_basis_coefficients_fn(|i| Val::from_u64(if i == 0 { a } else { b }));
        let zeta = ch(7_777, 5_555);
        let sels = domain.selectors_at_point(zeta);
        let (alpha, local, next, pub_val) = (ch(31, 37), ch(11, 13), ch(17, 19), Val::from_u64(23));

        // expected quotient via the REAL `selectors_at_point` + the folded relation.
        let c0 = sels.is_first_row * (local - Challenge::from(pub_val));
        let c1 = sels.is_transition * (next - local);
        let quotient = (c0 * alpha + c1) * sels.inv_vanishing;
        // the in-circuit selectors (component 4 formula) must agree with the real selectors_at_point.
        assert_eq!(ccs_native_quotient(zeta, alpha, local, next, pub_val), quotient);

        let proof = prove_ccs(zeta, alpha, local, next, pub_val, quotient);
        assert!(verify_ccs(&proof, quotient), "composed selectors+constraint must match native");
        assert!(!verify_ccs(&proof, quotient + Challenge::ONE));
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
    #[ignore = "slow: in-circuit sample_bits (query index, canonical) vs native"]
    fn sample_bits_matches_native() {
        // includes the canonical boundary 0xFFFF_FFFF_0000_0000 (high 32 bits all 1, lo = 0 ⇒ < p).
        for x in [
            Val::from_u64(0xDEAD_BEEF_1234_5678),
            Val::from_u64(42),
            Val::from_u64(0xFFFF_FFFF_0000_0000),
        ] {
            let index = native_sample_bits(x);
            let proof = prove_sample_bits(x, index);
            assert!(verify_sample_bits(&proof, index), "in-circuit index must match native sample_bits");
            assert!(!verify_sample_bits(&proof, index ^ 1));
        }
    }

    #[test]
    #[ignore = "slow: in-circuit reduced opening (DEEP) vs native"]
    fn reduced_opening_matches_native() {
        use p3_field::BasedVectorSpace;
        let ch = |a: u64, b: u64| Challenge::from_basis_coefficients_fn(|i| Val::from_u64(if i == 0 { a } else { b }));
        let p = [Val::from_u64(3), Val::from_u64(5), Val::from_u64(7), Val::from_u64(11)];
        let y = [ch(2, 1), ch(4, 3), ch(6, 5), ch(8, 7)];
        let alpha = ch(13, 17);
        let x = Val::from_u64(19);
        let zeta = ch(23, 29);
        let reduced = native_reduced_opening(p, y, alpha, x, zeta);
        let proof = prove_reduced_opening(p, y, alpha, x, zeta, reduced);
        assert!(verify_reduced_opening(&proof, reduced), "in-circuit reduced opening must match native");
        assert!(!verify_reduced_opening(&proof, reduced + ch(1, 0)));
    }

    #[test]
    #[ignore = "slow: in-circuit MMCS leaf hash vs native MyHash"]
    fn leaf_hash_matches_native() {
        use p3_symmetric::CryptographicHasher;
        let row = felts(7, LH_LEN);
        let digest: [Val; 4] = MyHash::new(default_goldilocks_poseidon2_8()).hash_iter(row.iter().copied());
        let proof = prove_leaf_hash(&row, digest);
        assert!(verify_leaf_hash(&proof, digest), "in-circuit leaf hash must match native MyHash");
        let mut bad = digest;
        bad[0] += Val::ONE;
        assert!(!verify_leaf_hash(&proof, bad));
    }

    #[test]
    #[ignore = "slow: in-circuit domain selectors vs native selectors_at_point"]
    fn domain_selectors_match_native() {
        use p3_commit::{Pcs, PolynomialSpace};
        use p3_field::BasedVectorSpace;
        use p3_uni_stark::StarkGenericConfig;
        let config = make_config();
        let domain = <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(config.pcs(), 1 << DS_LOG_SIZE);
        let zeta = Challenge::from_basis_coefficients_fn(|i| Val::from_u64(if i == 0 { 9_999 } else { 12_345 }));
        let sels = domain.selectors_at_point(zeta);
        let selectors = [sels.is_first_row, sels.is_last_row, sels.is_transition, sels.inv_vanishing];

        let proof = prove_domain_selectors(zeta, selectors);
        assert!(verify_domain_selectors(&proof, selectors), "in-circuit selectors must match native selectors_at_point");
        // a wrong selector ⇒ reject
        let mut bad = selectors;
        bad[0] += Challenge::ONE;
        assert!(!verify_domain_selectors(&proof, bad));
    }

    #[test]
    #[ignore = "slow: in-circuit FRI commit-phase challenge derivation vs native challenger"]
    fn fri_transcript_binds_all_challenges() {
        let felts = felts(1, FT_BLOCKS * RATE); // 32 felts
        let instance = &felts[0..8];
        let zeta_commits = &felts[8..16];
        let round_commits: Vec<[Val; RATE]> =
            (0..FRI_ROUNDS).map(|r| felts[16 + 4 * r..20 + 4 * r].try_into().unwrap()).collect();
        let challenges = native_fri_challenges(instance, zeta_commits, &round_commits);
        assert_eq!(challenges.len(), 2 + FRI_ROUNDS); // α, ζ, β_0..β_3

        let proof = prove_fri_transcript(&felts, &challenges);
        assert!(verify_fri_transcript(&proof, &challenges), "in-circuit α/ζ/β_r must match the native challenger");

        // a tampered absorb ⇒ different challenges ⇒ unsatisfiable against the original public set.
        let mut tfelts = felts.clone();
        tfelts[20] += Val::ONE; // perturb a β-round commitment felt
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let p = prove_fri_transcript(&tfelts, &challenges);
            verify_fri_transcript(&p, &challenges)
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
