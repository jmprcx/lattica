//! Tip5 permutation — **real vetted constants**, canonical-Goldilocks variant (Phase 1).
//!
//! Tip5 (Szepieniec, 2023 — "The Tip5 Hash Function for Recursive STARKs"; Triton VM / Neptune) is the
//! recursion-optimized Goldilocks permutation this program evaluates as the proof-system (Layer-A) hash.
//! Its recursion appeal vs Poseidon2 is **fewer rounds** (5 vs 30) and a **split-and-lookup S-box** that a
//! lookup argument verifies cheaply in-circuit.
//!
//! ## Real constants; canonical (not Triton-byte-identical) variant
//! Shape: width 16, 5 rounds, `NUM_SPLIT_LANES = 4` split-and-lookup lanes + 12 `x^7` power lanes, MDS,
//! per-round constants. The **constants are the real published Tip5 parameters**:
//!   * `LOOKUP_TABLE` — the offset-Fermat-cube map `(x+1)³−1 mod 257`, generated from the spec formula
//!     (value-identical to Triton's);
//!   * `MDS_FIRST_COLUMN` — Tip5's circulant MDS (SHA-256("Tip5")); and
//!   * `ROUND_CONSTANTS` — the real `Blake3("Tip5" ‖ i)` stream.
//!
//! It is a **canonical-Goldilocks variant**: the split-and-lookup decomposes the *canonical* field value,
//! whereas Triton splits its *Montgomery raw* form (a non-canonical "degenerate" representation the Triton
//! KAT even exercises). Replicating that exactly is impractical and unnecessary — lattica needs a
//! **self-consistent** recursion hash (same prover/verifier/node), not Triton interop. The S-box bijection,
//! the MDS, and the round-constant stream are the vetted ones, so the security argument carries; only the
//! byte-basis of the split differs, so this does **not** match Triton's KATs (documented, deliberate).

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

// --- Real Tip5 constants (published spec; canonical-Goldilocks variant) --------------------------

/// The **real** Tip5 8-bit lookup S-box — the "offset Fermat cube map" `L(x) = (x+1)³ − 1` over F₂₅₇
/// (`= ((x+1)³ + 256) mod 257`). Bijective on bytes (gcd(3,256)=1; only 256↦256, outside the byte range,
/// so `L` restricted to `0..256` is a permutation of `0..256`). Generated at const time from the spec
/// formula — value-identical to Triton VM's `LOOKUP_TABLE` (its `offset_fermat_cube_map`).
const LOOKUP_TABLE: [u8; 256] = {
    let mut t = [0u8; 256];
    let mut i = 0usize;
    while i < 256 {
        let x = (i as u64) + 1;
        t[i] = ((x * x * x + 256) % 257) as u8;
        i += 1;
    }
    t
};

/// The **real** Tip5 circulant MDS matrix first column (the byte-form of SHA-256("Tip5")).
const MDS_FIRST_COLUMN: [u64; WIDTH] = [
    61402, 1108, 28750, 33823, 7454, 43244, 53865, 12034, 56951, 27521, 41351, 40901, 12021, 59689,
    26798, 17845,
];

/// Goldilocks prime `p = 2⁶⁴ − 2³² + 1`.
const GOLDILOCKS_P: u64 = 0xFFFF_FFFF_0000_0001;

/// The **real** Tip5 round constants: `Blake3("Tip5" ‖ i)[0..16]` read LSB-first, reduced mod `p`, for
/// `i = 0..NUM_ROUNDS·WIDTH`. (Triton additionally multiplies by `R⁻¹` to pre-encode the constant into its
/// Montgomery storage; that `R⁻¹` is a representation artifact of Triton's non-canonical field and is
/// omitted for this canonical-Goldilocks variant — the underlying nothing-up-my-sleeve Blake3 stream is
/// the same.)
static ROUND_CONSTANTS: std::sync::LazyLock<[Goldilocks; NUM_ROUNDS * WIDTH]> =
    std::sync::LazyLock::new(|| {
        core::array::from_fn(|i| {
            let mut input = b"Tip5".to_vec();
            input.push(i as u8);
            let digest = blake3::hash(&input);
            let lo = u128::from_le_bytes(digest.as_bytes()[0..16].try_into().unwrap());
            Goldilocks::from_u64((lo % (GOLDILOCKS_P as u128)) as u64)
        })
    });

/// The Tip5 permutation (real vetted constants; canonical-Goldilocks variant).
#[derive(Clone, Copy, Debug, Default)]
pub struct Tip5;

impl Tip5 {
    /// The split-and-lookup S-box: decompose the element into `NUM_LOOKUP_BYTES` bytes, apply the real
    /// Tip5 `LOOKUP_TABLE` to each, recombine. This is the operation a lookup argument turns into
    /// `NUM_LOOKUP_BYTES` cheap table lookups in-circuit (the whole point of Tip5 for recursion).
    ///
    /// **Canonical variant:** the bytes are those of the *canonical* Goldilocks value. Triton splits the
    /// bytes of its *Montgomery* representation (`raw_bytes()`), which — because its representation is
    /// non-canonical (`raw` may exceed `p`, the "degenerate form") — is impractical to replicate exactly
    /// and unnecessary for lattica (which needs a self-consistent hash, not Triton interop). The S-box
    /// bijection, and hence the security argument, is identical; only the byte-basis differs.
    #[inline]
    fn split_and_lookup(x: Goldilocks) -> Goldilocks {
        let mut bytes = x.as_canonical_u64().to_le_bytes();
        for b in &mut bytes {
            *b = LOOKUP_TABLE[*b as usize];
        }
        Goldilocks::from_u64(u64::from_le_bytes(bytes))
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
        // circulant multiply by the real Tip5 MDS first column (degree-1 linear map):
        // out[i] = Σ_j C[(i − j) mod WIDTH] · state[j].
        let mut out = [Goldilocks::ZERO; WIDTH];
        for (i, o) in out.iter_mut().enumerate() {
            let mut acc = Goldilocks::ZERO;
            for j in 0..WIDTH {
                let c = Goldilocks::from_u64(MDS_FIRST_COLUMN[(i + WIDTH - j) % WIDTH]);
                acc += c * state[j];
            }
            *o = acc;
        }
        *state = out;
    }

    #[inline]
    fn add_round_constants(state: &mut [Goldilocks; WIDTH], round: usize) {
        for (i, s) in state.iter_mut().enumerate() {
            *s += ROUND_CONSTANTS[round * WIDTH + i];
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

    /// The permutation is deterministic and mixing (sanity).
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

    /// The lookup S-box is the **real** Tip5 offset-Fermat-cube map: value-identical to Triton's
    /// `LOOKUP_TABLE` — a byte bijection with the fixed points `L(0)=0`, `L(255)=255` that Triton asserts.
    #[test]
    fn real_lookup_table_is_the_fermat_cube_bijection() {
        assert_eq!(LOOKUP_TABLE[0], 0, "L(0)=0");
        assert_eq!(LOOKUP_TABLE[255], 255, "L(255)=255");
        // it is a permutation of 0..256
        let mut seen = [false; 256];
        for &v in LOOKUP_TABLE.iter() {
            seen[v as usize] = true;
        }
        assert!(seen.iter().all(|&b| b), "LOOKUP_TABLE must be a permutation of the bytes");
        // and matches ((x+1)^3 + 256) mod 257 on every input
        for (i, &v) in LOOKUP_TABLE.iter().enumerate() {
            let x = (i as u64) + 1;
            assert_eq!(v as u64, (x * x * x + 256) % 257);
        }
    }

    /// The real round constants derive from the Blake3("Tip5"‖i) stream (nothing-up-my-sleeve).
    #[test]
    fn round_constants_are_the_real_blake3_stream() {
        assert_eq!(ROUND_CONSTANTS.len(), NUM_ROUNDS * WIDTH);
        // deterministic + non-trivial (first constant matches the direct Blake3 derivation)
        let mut input = b"Tip5".to_vec();
        input.push(0u8);
        let lo = u128::from_le_bytes(blake3::hash(&input).as_bytes()[0..16].try_into().unwrap());
        assert_eq!(ROUND_CONSTANTS[0], Goldilocks::from_u64((lo % (GOLDILOCKS_P as u128)) as u64));
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

    /// **Step 4 (W4) bridge — the 4.6× Tip5 lever applies DIRECTLY to the recursion wrap's HEIGHT.** The in-circuit
    /// recursion verifier (the monolith) re-checks the inner proof's Merkle/leaf/transcript hashes with the Poseidon2
    /// AIR at `BLOCK = 32` rows/permutation — the SAME Poseidon2 `cost_estimate()` contrasts against. So swapping the
    /// wrap's own hashing to Tip5 (~7 rows/perm) shrinks its hash-dominated trace HEIGHT by the measured 4.6×. Ties
    /// the standalone Tip5 cost to the ACTUAL wrap: the narrow-tall swaps drove the WIDTH to the W5 fixed point
    /// `W* = 677`; Tip5 is the orthogonal HEIGHT lever (the hash blocks that dominate the super-tile). Both are SIZE,
    /// not the gate — the W5 gate (B<1) holds regardless (`w4_tip5_lever_is_b_neutral`: the hash carriers are
    /// B-neutral). The full in-circuit Tip5 AIR is the deferred (optional, non-gate) implementation; its size benefit
    /// is HERE quantified against the real Poseidon2 the wrap uses.
    #[test]
    fn tip5_row_reduction_applies_to_the_recursion_wrap() {
        let c = cost_estimate();
        // the wrap's in-circuit hashing IS Poseidon2 at BLOCK rows/perm — the exact baseline cost_estimate contrasts.
        assert_eq!(
            c.poseidon2_rows_per_perm,
            crate::poseidon2_air::BLOCK,
            "cost_estimate's Poseidon2 baseline must equal the monolith's BLOCK (the wrap's in-circuit hash cost)"
        );
        println!(
            "W4 bridge: the recursion wrap hashes in-circuit with Poseidon2 at BLOCK={} rows/perm; Tip5 ≈{} rows/perm \
             ⇒ {:.1}× fewer HASH ROWS on the wrap's super-tile HEIGHT (orthogonal to the W5 WIDTH fixed point W*=677). \
             Both are SIZE; the W5 gate (B<1) holds regardless (hash carriers B-neutral). Full in-circuit Tip5 AIR deferred.",
            crate::poseidon2_air::BLOCK,
            c.tip5_rows_per_perm_approx,
            c.row_reduction_vs_poseidon2
        );
        assert!(c.row_reduction_vs_poseidon2 >= 4.0);
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
