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
use p3_air::Air;
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
