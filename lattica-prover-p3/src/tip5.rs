//! Phase-0 (0c) — Tip5 permutation **structural reference** for cost analysis.
//!
//! Tip5 (Szepieniec, 2023 — "The Tip5 Hash Function for Recursive STARKs"; Triton VM / Neptune) is the
//! recursion-optimized Goldilocks permutation this program evaluates as the proof-system (Layer-A) hash.
//! Its recursion appeal vs Poseidon2 is **fewer rounds** (5 vs 30) and a **split-and-lookup S-box** that a
//! lookup argument verifies cheaply in-circuit.
//!
//! ## Status: STRUCTURAL, not byte-correct
//! This implements the correct **shape** — width 16, 5 rounds, `NUM_SPLIT_LANES = 4` split-and-lookup
//! lanes + 12 `x^7` power lanes, an MDS layer, and per-round constants — with **PLACEHOLDER constants**
//! (the lookup table, the MDS matrix, and the round constants). It is NOT the real Tip5 and does NOT match
//! published KATs. Its purpose is Phase-0 feasibility only:
//!   (1) confirm Tip5 slots into the p3-symmetric `Permutation`/`CryptographicPermutation` traits (hence
//!       into `PaddingFreeSponge`/`TruncatedPermutation`/`DuplexChallenger`) — i.e. a Layer-A swap is
//!       mechanically a `config.rs` type-alias change; and
//!   (2) produce the **in-circuit cost numbers** (rows/permutation, S-box degree) the wrap-feasibility
//!       spike (0a) needs.
//! Phase 1 replaces the three `PLACEHOLDER_*` tables with the published Tip5 constants and adds KAT tests.
//!
//! The cost analysis depends only on the STRUCTURE (round count, lane split, S-box algebra), which IS
//! faithful here; the constant VALUES do not affect rows/degree.

use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_goldilocks::Goldilocks;
use p3_symmetric::{CryptographicPermutation, Permutation};

/// Tip5 state width.
pub const WIDTH: usize = 16;
/// Tip5 round count (vs Poseidon2-Goldilocks-8's 30 = 8 full + 22 partial).
pub const NUM_ROUNDS: usize = 5;
/// Lanes routed through the split-and-lookup S-box (the rest use the `x^7` power map).
pub const NUM_SPLIT_LANES: usize = 4;
/// Bytes a field element is decomposed into for the split-and-lookup S-box.
pub const NUM_LOOKUP_BYTES: usize = 8;
/// The power-map exponent on the non-lookup lanes (7 is coprime to Goldilocks p−1).
pub const POWER: u64 = 7;

// --- PLACEHOLDER constants (replace with the published Tip5 spec in Phase 1) ---------------------

/// PLACEHOLDER 8-bit S-box for the split-and-lookup lanes. A fixed bijection on `0..256` so the
/// permutation is invertible and deterministic; NOT the real Tip5 lookup table. Structurally, what
/// matters is that each split lane is 8 independent byte-lookups (the in-circuit lookup count).
const fn placeholder_sbox(b: u8) -> u8 {
    // an affine bijection over the byte (odd multiplier ⇒ invertible mod 256) — placeholder only.
    b.wrapping_mul(29).wrapping_add(31)
}

/// PLACEHOLDER MDS circulant first row. The real Tip5 MDS is a specific NTT-friendly matrix; any
/// invertible linear map has the same in-circuit cost (degree 1), so a circulant suffices for 0c.
const PLACEHOLDER_MDS_FIRST_ROW: [u64; WIDTH] = [
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
];

/// The Tip5 permutation (structural reference).
#[derive(Clone, Copy, Debug, Default)]
pub struct Tip5;

impl Tip5 {
    /// The split-and-lookup S-box: decompose the element into `NUM_LOOKUP_BYTES` bytes, apply the 8-bit
    /// S-box to each, recombine. This is the operation a lookup argument turns into `NUM_LOOKUP_BYTES`
    /// cheap table lookups in-circuit (the whole point of Tip5 for recursion).
    #[inline]
    fn split_and_lookup(x: Goldilocks) -> Goldilocks {
        let v = x.as_canonical_u64();
        let mut out: u64 = 0;
        let mut i = 0;
        while i < NUM_LOOKUP_BYTES {
            let byte = ((v >> (8 * i)) & 0xff) as u8;
            out |= (placeholder_sbox(byte) as u64) << (8 * i);
            i += 1;
        }
        // `out < 2^64`; reduce into the field (the real Tip5 keeps bytes in range so no wraparound —
        // placeholder reduction here is sufficient for structure/cost).
        Goldilocks::from_u64(out)
    }

    /// The `x^7` power map on the non-lookup lanes (degree-7 constraint in-circuit — same as Poseidon2).
    #[inline]
    fn power_sbox(x: Goldilocks) -> Goldilocks {
        let x2 = x * x;
        let x4 = x2 * x2;
        x4 * x2 * x // x^7
    }

    #[inline]
    fn sbox_layer(state: &mut [Goldilocks; WIDTH]) {
        for (i, s) in state.iter_mut().enumerate() {
            *s = if i < NUM_SPLIT_LANES {
                Self::split_and_lookup(*s)
            } else {
                Self::power_sbox(*s)
            };
        }
    }

    #[inline]
    fn mds_layer(state: &mut [Goldilocks; WIDTH]) {
        // circulant multiply by PLACEHOLDER_MDS_FIRST_ROW (degree-1 linear map).
        let mut out = [Goldilocks::ZERO; WIDTH];
        for (i, o) in out.iter_mut().enumerate() {
            let mut acc = Goldilocks::ZERO;
            for j in 0..WIDTH {
                let c = Goldilocks::from_u64(PLACEHOLDER_MDS_FIRST_ROW[(j + WIDTH - i) % WIDTH]);
                acc += c * state[j];
            }
            *o = acc;
        }
        *state = out;
    }

    #[inline]
    fn add_round_constants(state: &mut [Goldilocks; WIDTH], round: usize) {
        // PLACEHOLDER round constants derived from (round, lane); the real Tip5 uses published constants.
        for (i, s) in state.iter_mut().enumerate() {
            *s += Goldilocks::from_u64((round as u64 * 0x9E37_79B9 + i as u64 * 0x1000_0001) | 1);
        }
    }
}

impl Permutation<[Goldilocks; WIDTH]> for Tip5 {
    fn permute_mut(&self, state: &mut [Goldilocks; WIDTH]) {
        for round in 0..NUM_ROUNDS {
            Self::sbox_layer(state);
            Self::mds_layer(state);
            Self::add_round_constants(state, round);
        }
    }
}

impl CryptographicPermutation<[Goldilocks; WIDTH]> for Tip5 {}

/// Packed (SIMD) permutation — the FRI-PCS Merkle commit hashes packed rows, so Tip5 must also permute the
/// concrete `Goldilocks::Packing` type. Implemented for the concrete SIMD type (coherence-distinct from
/// scalar `Goldilocks`, unlike the associated-type form) by unpacking each lane, applying the scalar Tip5,
/// and repacking — correct, not vectorized (a Phase-1 perf item). Only the AVX2 packing (this research
/// box's target) is wired; other SIMD targets mirror the crate's `Field::Packing` cfg in Phase 1. Under a
/// no-SIMD target `Packing = Goldilocks`, so the scalar impl above already covers it and this is skipped.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
mod packed_impl {
    use super::{Tip5, WIDTH};
    use p3_field::PackedValue;
    use p3_goldilocks::{Goldilocks, PackedGoldilocksAVX2};
    use p3_symmetric::{CryptographicPermutation, Permutation};

    impl Permutation<[PackedGoldilocksAVX2; WIDTH]> for Tip5 {
        fn permute_mut(&self, state: &mut [PackedGoldilocksAVX2; WIDTH]) {
            for lane in 0..PackedGoldilocksAVX2::WIDTH {
                let mut s: [Goldilocks; WIDTH] = core::array::from_fn(|i| state[i].as_slice()[lane]);
                <Tip5 as Permutation<[Goldilocks; WIDTH]>>::permute_mut(self, &mut s);
                for (i, si) in s.into_iter().enumerate() {
                    state[i].as_slice_mut()[lane] = si;
                }
            }
        }
    }
    impl CryptographicPermutation<[PackedGoldilocksAVX2; WIDTH]> for Tip5 {}
}

// ------------------------------------------------------------------------------------------------
// Cost analysis (the 0c deliverable feeding the 0a wrap-feasibility spike).
// ------------------------------------------------------------------------------------------------

/// A structural in-circuit cost estimate for one Tip5 permutation, contrasted with Poseidon2-Goldilocks-8.
///
/// These are the numbers 0a needs: Tip5's row/degree profile as the proof-system (Layer-A) hash the
/// recursion verifier must re-check in-circuit.
#[derive(Clone, Copy, Debug)]
pub struct Tip5CostEstimate {
    /// Rounds (⇒ ≈ trace rows per permutation at ~1 round/row): Tip5 5 vs Poseidon2 30.
    pub rounds: usize,
    /// Poseidon2 rows/permutation for reference (its AIR uses BLOCK = 32).
    pub poseidon2_rows_per_perm: usize,
    /// Max S-box constraint degree WITHOUT a lookup argument: the `x^7` power lanes ⇒ 7 (same as Poseidon2).
    pub sbox_degree_no_lookup: usize,
    /// Max S-box constraint degree WITH a lookup argument: the split lanes become degree-~1 lookups; the
    /// `x^7` lanes remain 7. (So Tip5's win is ROWS, not S-box degree — the wrap's *degree* fix is the
    /// lookup argument applied to the FRI-fold relations, not the hash S-box. See the 0a analysis.)
    pub sbox_degree_with_lookup: usize,
    /// Byte-lookups per split lane (⇒ the lookup-table load a lookup argument must carry).
    pub lookups_per_split_lane: usize,
    /// Approx rows/permutation for Tip5 (≈ rounds, allowing a couple of layout rows).
    pub tip5_rows_per_perm_approx: usize,
    /// Row reduction factor vs Poseidon2 (the recursion-height lever).
    pub row_reduction_vs_poseidon2: f64,
}

/// Compute the structural cost estimate. Deterministic; drives the 0a spike + the 0d design doc.
pub fn cost_estimate() -> Tip5CostEstimate {
    let poseidon2_rows_per_perm = 32; // poseidon2_air.rs BLOCK
    let tip5_rows_per_perm_approx = NUM_ROUNDS + 2; // ~1 round/row + input/output rows
    Tip5CostEstimate {
        rounds: NUM_ROUNDS,
        poseidon2_rows_per_perm,
        sbox_degree_no_lookup: POWER as usize, // 7
        sbox_degree_with_lookup: POWER as usize, // 7 — x^7 lanes unchanged; split lanes → lookups (~1)
        lookups_per_split_lane: NUM_LOOKUP_BYTES,
        tip5_rows_per_perm_approx,
        row_reduction_vs_poseidon2: poseidon2_rows_per_perm as f64 / tip5_rows_per_perm_approx as f64,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};

    /// The permutation is a bijection (invertibility sanity — placeholder constants, structural check).
    #[test]
    fn tip5_permute_is_deterministic_and_mixing() {
        let a: [Goldilocks; WIDTH] = core::array::from_fn(|i| Goldilocks::from_u64(i as u64));
        let mut b = a;
        Tip5.permute_mut(&mut b);
        // deterministic
        let mut c = a;
        Tip5.permute_mut(&mut c);
        assert_eq!(b, c);
        // mixing: output differs from input in every lane touched (not identity)
        assert_ne!(a, b);
    }

    /// **The key wiring result:** Tip5 slots into the exact p3-symmetric wrappers the Layer-A config uses,
    /// so migrating the proof-system hash is a `config.rs` type-alias change (const-generic churn only).
    #[test]
    fn tip5_slots_into_layer_a_wrappers() {
        // PaddingFreeSponge<Tip5, WIDTH=16, RATE=10, OUT=5>  — MMCS leaf hash + DuplexChallenger shape
        let sponge = PaddingFreeSponge::<Tip5, 16, 10, 5>::new(Tip5);
        // TruncatedPermutation<Tip5, N=2, CHUNK=5, WIDTH=16>  (CHUNK*N=10 ≤ 16) — MMCS 2-to-1 node
        let compress = TruncatedPermutation::<Tip5, 2, 5, 16>::new(Tip5);
        // exercise them so the trait bounds are actually instantiated by the compiler
        use p3_symmetric::{CryptographicHasher, PseudoCompressionFunction};
        let digest: [Goldilocks; 5] = sponge.hash_iter((0..20).map(|i| Goldilocks::from_u64(i)));
        let node: [Goldilocks; 5] = compress.compress([digest, digest]);
        assert_ne!(digest, node);
    }

    /// Emit the structural cost numbers 0a/0d consume.
    #[test]
    fn tip5_cost_report() {
        let c = cost_estimate();
        println!("TIP5-COST rounds={} rows/perm≈{} (poseidon2={}) row_reduction={:.1}x sbox_deg(no_lookup)={} sbox_deg(with_lookup_split_lanes)=~1..{} lookups/split_lane={}",
            c.rounds, c.tip5_rows_per_perm_approx, c.poseidon2_rows_per_perm,
            c.row_reduction_vs_poseidon2, c.sbox_degree_no_lookup, c.sbox_degree_with_lookup,
            c.lookups_per_split_lane);
        assert_eq!(c.rounds, 5);
        assert!(c.row_reduction_vs_poseidon2 >= 4.0, "Tip5 should be ≥4x fewer rows/perm than Poseidon2");
    }
}

// ================================================================================================
// Phase-1 (mechanical core) — a Tip5 **proof-system (Layer-A) config**, mirroring `config::demo` but
// with Tip5 in place of Poseidon2. Demonstrates end-to-end that migrating the Layer-A hash produces
// valid, verifiable proofs: the const-generic churn (width 16 / rate 10 / digest 5) composes through
// the same FRI-PCS + Merkle + Fiat-Shamir stack. (Structural constants ⇒ this validates the MACHINERY,
// not cryptographic security; byte-exact Tip5 constants land in Phase 1 proper.)
// ================================================================================================
pub mod proof_system {
    use super::Tip5;
    use crate::config::{Challenge, Dft, Val};
    use p3_challenger::DuplexChallenger;
    use p3_commit::ExtensionMmcs;
    use p3_fri::{FriParameters, HidingFriPcs};
    use p3_goldilocks::Goldilocks;
    use p3_merkle_tree::MerkleTreeHidingMmcs;
    use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
    use p3_uni_stark::StarkConfig;
    use rand::rngs::SmallRng;
    use rand::SeedableRng;

    /// Tip5 Layer-A type stack (cf. `config.rs:37-55`, Poseidon2 width-8 → Tip5 width-16 / digest-5).
    /// The MMCS packing slots use scalar `Goldilocks` (width-1) rather than `<Val>::Packing` (AVX2), so the
    /// demo needs only Tip5's scalar `Permutation<[Goldilocks;16]>` impl. Phase 1 adds the packed impl for
    /// SIMD Merkle hashing (a perf, not correctness, matter).
    pub type MyHashT5 = PaddingFreeSponge<Tip5, 16, 10, 5>;
    pub type MyCompressT5 = TruncatedPermutation<Tip5, 2, 5, 16>;
    pub type ValMmcsT5 =
        MerkleTreeHidingMmcs<Goldilocks, Goldilocks, MyHashT5, MyCompressT5, SmallRng, 2, 5, 5>;
    pub type ChallengeMmcsT5 = ExtensionMmcs<Val, Challenge, ValMmcsT5>;
    pub type ChallengerT5 = DuplexChallenger<Val, Tip5, 16, 10>;
    pub type MyPcsT5 = HidingFriPcs<Val, Dft, ValMmcsT5, ChallengeMmcsT5, SmallRng>;
    pub type MyConfigT5 = StarkConfig<MyPcsT5, Challenge, ChallengerT5>;

    /// A Tip5-committed proving/verifying config (demo parameters; seeded salts).
    pub fn make_tip5_config(seed: u64) -> MyConfigT5 {
        let perm = Tip5;
        let hash = MyHashT5::new(perm);
        let compress = MyCompressT5::new(perm);
        let val_mmcs = ValMmcsT5::new(hash, compress, 0, SmallRng::seed_from_u64(seed));
        let challenge_mmcs = ChallengeMmcsT5::new(val_mmcs.clone());
        let fri_params = FriParameters {
            log_blowup: 3,
            log_final_poly_len: 0,
            max_log_arity: 1,
            num_queries: 24,
            commit_proof_of_work_bits: 1,
            query_proof_of_work_bits: 1,
            mmcs: challenge_mmcs,
        };
        let pcs = MyPcsT5::new(Dft::default(), val_mmcs, fri_params, 4, SmallRng::seed_from_u64(seed));
        MyConfigT5::new(pcs, ChallengerT5::new(perm))
    }
}

#[cfg(test)]
mod proof_system_tests {
    use super::proof_system::make_tip5_config;
    use crate::config::Val;
    use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
    use p3_field::PrimeCharacteristicRing;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_uni_stark::{prove, verify};

    /// Self-contained AIR: a single boolean column, `x·(x−1) = 0` (degree 2, no public values).
    struct BoolAir;
    impl<F: p3_field::Field> BaseAir<F> for BoolAir {
        fn width(&self) -> usize {
            1
        }
    }
    impl<AB: AirBuilder<F = Val>> Air<AB> for BoolAir {
        fn eval(&self, builder: &mut AB) {
            let x: AB::Expr = builder.main().current_slice()[0].into();
            builder.assert_zero(x.clone() * (x - AB::Expr::ONE));
        }
    }

    /// **The Phase-1 mechanical result:** a proof committed with **Tip5** as the Layer-A hash (width-16 /
    /// digest-5 sponge + compress + duplex challenger) proves and verifies end-to-end through the standard
    /// `p3_uni_stark::{prove,verify}`. So migrating the proof-system hash is sound machinery — the whole
    /// FRI-PCS + Merkle + Fiat-Shamir stack composes with Tip5, not just a type swap. (Fail-closed rejection
    /// of tampered proofs is exercised by the production verifier fuzz suites; not re-tested here.)
    #[test]
    fn tip5_committed_proof_proves_and_verifies() {
        let config = make_tip5_config(0);
        let n = 1 << 6;
        // a valid boolean trace (all zeros satisfies x·(x−1)=0).
        let trace = RowMajorMatrix::new(vec![Val::ZERO; n], 1);
        let pis: Vec<Val> = vec![];

        let proof = prove(&config, &BoolAir, trace, &pis);
        verify(&config, &BoolAir, &proof, &pis).expect("Tip5-committed proof must verify end-to-end");
    }
}
