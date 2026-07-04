//! CRATE-WIDE STARK CONFIGURATION — the single source of the proof-system parameter families.
//!
//! Two families:
//!  - **production** (module top level): the hiding (zero-knowledge) Goldilocks config every production
//!    circuit proves under (C-04): Poseidon2-8 sponge/compress, salted `MerkleTreeHidingMmcs` (ChaCha20
//!    CSPRNG salts), F_p² challenges, and the production FRI parameters — `log_blowup=4`,
//!    `num_queries=96`, `query_pow=16` bits, cap height 6, 4 random codewords ⇒ ≈103-bit proven /
//!    ~127-bit conjectured security at the single-tx height. These values are WIRE-PINNED: the proof
//!    bytes are `postcard(Proof<MyConfig>)`, so changing any type or parameter here breaks the Zig node
//!    seam (see lib.rs) and consensus. They are also mirrored by `docs/soundness-budget.md`.
//!  - **demo** (submodule): the small non-consensus config used by dev tools / reference AIRs
//!    (`main.rs`, `poseidon2_air::Poseidon2RowsAir`) — deterministic `SmallRng` salts, `log_blowup=3`,
//!    24 queries. NEVER use for production proofs: the salt RNG is seeded, so blinding is predictable.
//!
//! The previous layout duplicated the 10-type alias stanza + the FRI literal in SIX files (each circuit
//! + the two dev tools) and the security recomputation in FOUR; this module is the audit point for all
//! of them.

use p3_air::symbolic::SymbolicAirBuilder;
use p3_air::{Air, DebugConstraintBuilder};
use p3_matrix::dense::RowMajorMatrix;
use p3_uni_stark::{prove, verify, Proof, ProverConstraintFolder, VerifierConstraintFolder};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::Field;
use p3_fri::{FriParameters, HidingFriPcs};
use p3_goldilocks::{default_goldilocks_poseidon2_8, Goldilocks, Poseidon2Goldilocks};
use p3_merkle_tree::MerkleTreeHidingMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{AirLayout, ProvenSecurity, StarkConfig, StarkSecurityParams};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

pub type Val = Goldilocks;
pub type Perm = Poseidon2Goldilocks<8>;
pub type MyHash = PaddingFreeSponge<Perm, 8, 4, 4>;
pub type MyCompress = TruncatedPermutation<Perm, 2, 4, 8>;
pub type ValMmcs =
    MerkleTreeHidingMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, ChaCha20Rng, 2, 4, 4>;
pub type Challenge = BinomialExtensionField<Val, 2>;
pub type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
pub type Challenger = DuplexChallenger<Val, Perm, 8, 4>;
pub type Dft = Radix2DitParallel<Val>;
pub type MyPcs = HidingFriPcs<Val, Dft, ValMmcs, ChallengeMmcs, ChaCha20Rng>;
pub type MyConfig = StarkConfig<MyPcs, Challenge, Challenger>;

// --- production parameters (C-04; consensus + wire pinned) --------------------------------------
/// FRI rate: LDE blowup 2^4 (supports formal constraint degree ≤ 16 + 1 hiding).
pub const LOG_BLOWUP: usize = 4;
/// FRI query count (with the blowup + PoW: ≈103-bit proven / ~127-bit conjectured).
pub const NUM_QUERIES: usize = 96;
/// Query-phase proof-of-work grinding bits.
pub const QUERY_POW_BITS: usize = 16;
/// Merkle cap height (2^6 = 64-entry caps).
pub const CAP_HEIGHT: usize = 6;
/// HidingFriPcs random codewords appended to each committed matrix (the ZK masking width).
pub const NUM_RANDOM_CODEWORDS: usize = 4;

/// The production FRI parameter block. The ONLY place these literals live.
pub fn production_fri(mmcs: ChallengeMmcs) -> FriParameters<ChallengeMmcs> {
    FriParameters {
        log_blowup: LOG_BLOWUP,
        log_final_poly_len: 0,
        max_log_arity: 4,
        num_queries: NUM_QUERIES,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: QUERY_POW_BITS,
        mmcs,
    }
}

/// The production proving/verifying config.
///
/// The hiding-PCS / Merkle-salt RNG must be a CSPRNG seeded from fresh OS entropy **per proof** —
/// otherwise the zero-knowledge blinding is predictable/identical across proofs and the witness is
/// not actually hidden. ChaCha20Rng is ChaCha-based; `from_rng(&mut rand::rng())` reseeds each call.
pub fn make_config() -> MyConfig {
    let perm = default_goldilocks_poseidon2_8();
    let val_mmcs =
        ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), CAP_HEIGHT, ChaCha20Rng::from_rng(&mut rand::rng()));
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let fri = production_fri(challenge_mmcs);
    let pcs = MyPcs::new(Dft::default(), val_mmcs, fri, NUM_RANDOM_CODEWORDS, ChaCha20Rng::from_rng(&mut rand::rng()));
    MyConfig::new(pcs, Challenger::new(perm))
}

/// Proven (UDR) security bits for `air` proven at `trace_height` rows under the production parameters.
///
/// `trailing_zeros + 1`: the hiding PCS commits the trace at DOUBLE the degree (`is_zk` randomization),
/// so the security is evaluated at 2^(log_height + 1). Conjectured/field/extension parameters
/// (127, 128, 2) mirror `docs/soundness-budget.md`. Deterministic (seeded MMCS — parameters only, no
/// proving), so `#[test]`s can pin production floors against parameter edits.
pub fn proven_security_bits<A>(air: &A, trace_height: usize) -> usize
where
    A: Air<SymbolicAirBuilder<Val, Challenge>>,
{
    let perm = default_goldilocks_poseidon2_8();
    let vm = ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm), CAP_HEIGHT, ChaCha20Rng::seed_from_u64(1));
    let fri = production_fri(ChallengeMmcs::new(vm));
    let layout = AirLayout::from_air::<Val>(air);
    let params = StarkSecurityParams::from_air::<Val, Challenge, A, ChallengeMmcs>(&fri, air, layout, 127, 128, 2);
    ProvenSecurity::compute(&params, 1usize << (trace_height.trailing_zeros() as usize + 1)).security_bits()
}

/// Prove `air` over `trace` with public inputs `pis` under the production config, returning the
/// canonical `postcard(Proof<MyConfig>)` bytes. The ONE audited prove-and-serialize path behind the
/// circuits' `prove_to_bytes` / `prove_batch_to_bytes` shims (their per-circuit AIR + trace + pis are
/// the only difference).
pub fn proof_to_bytes<A>(air: &A, trace: RowMajorMatrix<Val>, pis: &[Val]) -> Vec<u8>
where
    A: Air<SymbolicAirBuilder<Val>>
        + for<'a> Air<ProverConstraintFolder<'a, MyConfig>>
        + for<'a> Air<DebugConstraintBuilder<'a, Val>>,
{
    // Streaming builds (`--features stream`) spill the LDE/quotient/Merkle buffers to an mmap'd file for
    // the duration of this prove — bounding peak RSS. No-op (and zero cost) in the default build. Prove
    // is the only path armed; the verifier + the 10 frozen externs never spill. Byte-transparent.
    #[cfg(feature = "stream")]
    let _spill = crate::spill_alloc::SpillScope::arm();
    let proof = prove(&make_config(), air, trace, pis);
    postcard::to_allocvec(&proof).expect("proof serialization is infallible")
}

/// Deserialize a `postcard(Proof<MyConfig>)` and verify it against `pis` under the production config.
/// **Fail-closed**: a public-input count ≠ `n_expected_pis`, malformed proof bytes, or a verify error
/// all return `false`. The ONE audited deserialize-bound verify gate behind the circuits'
/// `verify_bytes` / `verify_batch_bytes` shims.
pub fn verify_proof_bytes<A>(air: &A, n_expected_pis: usize, proof_bytes: &[u8], pis: &[Val]) -> bool
where
    A: Air<SymbolicAirBuilder<Val>> + for<'a> Air<VerifierConstraintFolder<'a, MyConfig>>,
{
    if pis.len() != n_expected_pis {
        return false;
    }
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), air, &proof, pis).is_ok()
}

/// GPU-accelerated proving config (opt-in via `--features gpu`). IDENTICAL to the production config
/// except the LDE runs on the GPU (`crate::gpu::GpuDft` in the PCS `Dft` slot). **Prove-only +
/// wire-compatible**: the `Dft` appears neither in `verify` nor in the serialized `Proof`, so a
/// GPU-produced proof deserializes and verifies under the standard `MyConfig` / `verify_bytes`
/// unchanged. Same hiding PCS, same FRI params, same salts (still a fresh CSPRNG per proof).
#[cfg(feature = "gpu")]
pub mod gpu {
    use super::*;
    use crate::gpu::GpuDft;

    pub type MyPcsGpu = HidingFriPcs<Val, GpuDft, ValMmcs, ChallengeMmcs, ChaCha20Rng>;
    pub type MyConfigGpu = StarkConfig<MyPcsGpu, Challenge, Challenger>;

    /// The production config with GPU LDE. See `super::make_config` — only the `Dft` differs.
    pub fn make_config() -> MyConfigGpu {
        let perm = default_goldilocks_poseidon2_8();
        let val_mmcs =
            ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), CAP_HEIGHT, ChaCha20Rng::from_rng(&mut rand::rng()));
        let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
        let fri = production_fri(challenge_mmcs);
        let pcs = MyPcsGpu::new(GpuDft, val_mmcs, fri, NUM_RANDOM_CODEWORDS, ChaCha20Rng::from_rng(&mut rand::rng()));
        MyConfigGpu::new(pcs, Challenger::new(perm))
    }

    /// Prove `air` over `trace` with `pis`, GPU-accelerated LDE. Returns wire-compatible postcard bytes
    /// — verify with the standard `<circuit>::verify_bytes` / the C-ABI verifier, unchanged.
    pub fn proof_to_bytes<A>(air: &A, trace: RowMajorMatrix<Val>, pis: &[Val]) -> Vec<u8>
    where
        A: Air<SymbolicAirBuilder<Val>>
            + for<'a> Air<ProverConstraintFolder<'a, MyConfigGpu>>
            + for<'a> Air<DebugConstraintBuilder<'a, Val>>,
    {
        let proof = prove(&make_config(), air, trace, pis);
        postcard::to_allocvec(&proof).expect("proof serialization is infallible")
    }

    // --- GPU HIDING config: production-identical, with BOTH heavy steps on the GPU -------------------
    // `HidingFriPcs` + `is_zk` + `NUM_RANDOM_CODEWORDS` + `CAP_HEIGHT` + FRI params all match production;
    // only `GpuDft` (LDE) and `GpuHidingMerkleMmcs` (Merkle) differ. `GpuHidingMerkleMmcs`'s
    // `Commitment`/`Proof` are byte-identical to `MerkleTreeHidingMmcs`, so a proof made here serializes
    // exactly like `Proof<MyConfig>` and **verifies under the standard production verifier**
    // (`<circuit>::verify_bytes` / the C-ABI / the node), unchanged — see `gpu_*_proof_verifies_hiding`.
    use crate::gpu::GpuHidingMerkleMmcs;
    use crate::gpu_pcs::GpuHidingPcs;

    pub use crate::gpu_pcs::ChallengeMmcsGpuHiding;
    /// The GPU-hiding PCS: `HidingFriPcs` (GPU LDE + GPU Merkle) wrapped so the quotient-chunk
    /// randomization pipeline also runs device-side (`gpu_pcs::GpuHidingPcs`). Associated types —
    /// and therefore the serialized `Proof` — are identical to the plain `HidingFriPcs` stack.
    pub type MyPcsGpuHiding = GpuHidingPcs;
    pub type MyConfigGpuHiding = StarkConfig<MyPcsGpuHiding, Challenge, Challenger>;

    /// The production config with LDE + Merkle + quotient randomization on the GPU. Mirror of
    /// `super::make_config` — only the `Dft` (`GpuDft`), the inner MMCS (`GpuHidingMerkleMmcs`), and
    /// the quotient-LDE pipeline differ; identical `CAP_HEIGHT`, `NUM_RANDOM_CODEWORDS`, FRI params,
    /// and fresh per-proof ChaCha20 randomness.
    pub fn make_config_hiding() -> MyConfigGpuHiding {
        let perm = default_goldilocks_poseidon2_8();
        let val_mmcs = GpuHidingMerkleMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), CAP_HEIGHT, ChaCha20Rng::from_rng(&mut rand::rng()));
        let challenge_mmcs = ChallengeMmcsGpuHiding::new(val_mmcs.clone());
        let fri = gpu_fri_params(challenge_mmcs);
        let pcs = GpuHidingPcs::new(
            GpuDft,
            val_mmcs,
            fri,
            NUM_RANDOM_CODEWORDS,
            ChaCha20Rng::from_rng(&mut rand::rng()),
            ChaCha20Rng::from_rng(&mut rand::rng()),
        );
        MyConfigGpuHiding::new(pcs, Challenger::new(perm))
    }

    /// Prove `air` with GPU LDE + GPU Merkle. **Wire-compatible**: verify with the standard
    /// `<circuit>::verify_bytes`, unchanged. The ONE GPU-hiding prove-and-serialize path.
    ///
    /// The quotient stays on the CPU here (p3's `prove`): the GPU quotient offload
    /// (`crate::quotient_gpu::prove_gpu` with `QuotientMode::Gpu`) is correct and production-compatible but
    /// currently net-neutral — the kernel is fast, but marshalling the trace to the GPU offsets it — so it
    /// is kept as validated infrastructure, not wired into the default path. See `docs/gpu-acceleration.md`.
    pub fn proof_to_bytes_hiding<A>(air: &A, trace: RowMajorMatrix<Val>, pis: &[Val]) -> Vec<u8>
    where
        A: Air<SymbolicAirBuilder<Val>>
            + for<'a> Air<ProverConstraintFolder<'a, MyConfigGpuHiding>>
            + for<'a> Air<DebugConstraintBuilder<'a, Val>>,
    {
        let proof = prove(&make_config_hiding(), air, trace, pis);
        postcard::to_allocvec(&proof).expect("proof serialization is infallible")
    }

    // --- Non-hiding BENCHMARK configs (NOT production): isolate the GPU LDE + Merkle speedup against an
    // apples-to-apples CPU baseline with identical FRI parameters. No ZK, no salts. `GpuMerkleMmcs`
    // commits equal-height matrices with `cap_height = 0`, so the CPU baseline mirrors that exactly
    // (`MerkleTreeMmcs`, cap 0). Proofs are self-consistent (proved+verified under the same config) — the
    // point is a clean wall-clock comparison of the accelerated commit path, not a wire/consensus proof.
    use crate::gpu::GpuMerkleMmcs;
    use p3_fri::TwoAdicFriPcs;
    use p3_merkle_tree::MerkleTreeMmcs;

    pub type BenchValMmcsCpu = MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, 2, 4>;
    pub type BenchChMmcsCpu = ExtensionMmcs<Val, Challenge, BenchValMmcsCpu>;
    pub type BenchPcsCpu = TwoAdicFriPcs<Val, Dft, BenchValMmcsCpu, BenchChMmcsCpu>;
    pub type BenchConfigCpu = StarkConfig<BenchPcsCpu, Challenge, Challenger>;

    pub type BenchChMmcsGpu = ExtensionMmcs<Val, Challenge, GpuMerkleMmcs>;
    pub type BenchPcsGpu = TwoAdicFriPcs<Val, GpuDft, GpuMerkleMmcs, BenchChMmcsGpu>;
    pub type BenchConfigGpu = StarkConfig<BenchPcsGpu, Challenge, Challenger>;

    /// The production FRI literals (`LOG_BLOWUP` / `NUM_QUERIES` / `QUERY_POW_BITS` / …), generic over the
    /// challenge MMCS — identical to `super::production_fri`, shared by the GPU-module configs.
    fn gpu_fri_params<M>(mmcs: M) -> FriParameters<M> {
        FriParameters {
            log_blowup: LOG_BLOWUP,
            log_final_poly_len: 0,
            max_log_arity: 4,
            num_queries: NUM_QUERIES,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: QUERY_POW_BITS,
            mmcs,
        }
    }

    /// Apples-to-apples CPU baseline: `Radix2DitParallel` LDE + plain `MerkleTreeMmcs`, non-hiding.
    pub fn make_bench_config_cpu() -> BenchConfigCpu {
        let perm = default_goldilocks_poseidon2_8();
        let vm = BenchValMmcsCpu::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), 0);
        let pcs = BenchPcsCpu::new(Dft::default(), vm.clone(), gpu_fri_params(BenchChMmcsCpu::new(vm)));
        BenchConfigCpu::new(pcs, Challenger::new(perm))
    }

    /// The same config with BOTH heavy steps on the GPU: `GpuDft` LDE + `GpuMerkleMmcs` tree build.
    pub fn make_bench_config_gpu() -> BenchConfigGpu {
        let perm = default_goldilocks_poseidon2_8();
        let vm = GpuMerkleMmcs::new();
        let pcs = BenchPcsGpu::new(GpuDft, vm.clone(), gpu_fri_params(BenchChMmcsGpu::new(vm)));
        BenchConfigGpu::new(pcs, Challenger::new(perm))
    }
}

/// Dev/demo config family — deterministic salts, reduced parameters. NOT for production proofs.
pub mod demo {
    use super::{Challenge, Dft, MyCompress, MyHash, Val};
    use p3_fri::{FriParameters, HidingFriPcs};
    use p3_goldilocks::default_goldilocks_poseidon2_8;
    use p3_merkle_tree::MerkleTreeHidingMmcs;
    use p3_commit::ExtensionMmcs;
    use p3_challenger::DuplexChallenger;
    use p3_field::Field;
    use p3_uni_stark::StarkConfig;
    use rand::rngs::SmallRng;
    use rand::SeedableRng;

    pub const LOG_BLOWUP: usize = 3; // supports the degree-7 S-box
    pub type Perm = super::Perm;
    pub type ValMmcs =
        MerkleTreeHidingMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, SmallRng, 2, 4, 4>;
    pub type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
    pub type Challenger = DuplexChallenger<Val, Perm, 8, 4>;
    pub type MyPcs = HidingFriPcs<Val, Dft, ValMmcs, ChallengeMmcs, SmallRng>;
    pub type MyConfig = StarkConfig<MyPcs, Challenge, Challenger>;

    /// Deterministic demo config (seeded SmallRng salts — blinding is PREDICTABLE; dev tools only).
    pub fn make_config(seed: u64) -> MyConfig {
        let perm = default_goldilocks_poseidon2_8();
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm.clone());
        let val_mmcs = ValMmcs::new(hash, compress, 0, SmallRng::seed_from_u64(seed));
        let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
        let fri_params = FriParameters {
            log_blowup: LOG_BLOWUP,
            log_final_poly_len: 0,
            max_log_arity: 1,
            num_queries: 24,
            commit_proof_of_work_bits: 1,
            query_proof_of_work_bits: 1,
            mmcs: challenge_mmcs,
        };
        let pcs = MyPcs::new(Dft::default(), val_mmcs, fri_params, 4, SmallRng::seed_from_u64(seed));
        MyConfig::new(pcs, Challenger::new(perm))
    }
}
