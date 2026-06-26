//! Field comparison: proof size of the *same logical work* (N Poseidon2 compressions) on
//! **Goldilocks** vs **BabyBear**, using the vetted `p3-poseidon2-air` and matched FRI parameters.
//!
//! Run: `cargo run --release --bin field_compare`. This isolates the field-size effect on proof
//! bytes without porting the whole spend circuit. Each field uses its *native* Poseidon2 (Goldilocks
//! width 8, BabyBear width 16 — BabyBear needs the wider state to hold a ~256-bit digest), an
//! algebraic (Poseidon2) hiding Merkle commitment, and a `DuplexChallenger`, so the only differences
//! are the field and its natural extension/width. The ratio (not the absolute size) is the takeaway.

use p3_baby_bear::{
    default_babybear_poseidon2_16, BabyBear, GenericPoseidon2LinearLayersBabyBear,
    BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS, BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16,
};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::Field;
use p3_fri::{FriParameters, HidingFriPcs};
use p3_goldilocks::{
    default_goldilocks_poseidon2_8, GenericPoseidon2LinearLayersGoldilocks, Goldilocks,
    GOLDILOCKS_POSEIDON2_HALF_FULL_ROUNDS, GOLDILOCKS_POSEIDON2_PARTIAL_ROUNDS_8,
};
use p3_air::BaseAir;
use p3_poseidon2_air::{Poseidon2Air, RoundConstants};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{prove, verify, StarkConfig};
use rand::rngs::SmallRng;
use rand::SeedableRng;
use std::time::Instant;

const LOG_BLOWUP: usize = 4;
const NUM_QUERIES: usize = 96;
const QUERY_POW: usize = 16;

struct Row {
    field: &'static str,
    width: usize,
    proof_kb: f64,
    prove_ms: u128,
    verify_ms: u128,
}

fn goldilocks_measure(n: usize) -> Row {
    type Val = Goldilocks;
    type Challenge = BinomialExtensionField<Val, 2>; // F_p^2 ≈ 127-bit
    type Perm = p3_goldilocks::Poseidon2Goldilocks<8>;
    type MyHash = PaddingFreeSponge<Perm, 8, 4, 4>;
    type MyCompress = TruncatedPermutation<Perm, 2, 4, 8>;
    type ValMmcs =
        MerkleHiding<Val, MyHash, MyCompress, 4>;
    type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
    type Challenger = DuplexChallenger<Val, Perm, 8, 4>;
    type Dft = Radix2DitParallel<Val>;
    type Pcs = HidingFriPcs<Val, Dft, ValMmcs, ChallengeMmcs, SmallRng>;
    type Cfg = StarkConfig<Pcs, Challenge, Challenger>;
    type Air = Poseidon2Air<
        Val,
        GenericPoseidon2LinearLayersGoldilocks,
        8,
        7,
        1,
        GOLDILOCKS_POSEIDON2_HALF_FULL_ROUNDS,
        GOLDILOCKS_POSEIDON2_PARTIAL_ROUNDS_8,
    >;

    let perm = default_goldilocks_poseidon2_8();
    let mut rng = SmallRng::seed_from_u64(1);
    let air: Air = Poseidon2Air::new(RoundConstants::from_rng(&mut rng));
    let val_mmcs = ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), 0, SmallRng::seed_from_u64(1));
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let fri = FriParameters {
        log_blowup: LOG_BLOWUP,
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: NUM_QUERIES,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: QUERY_POW,
        mmcs: challenge_mmcs,
    };
    let pcs = Pcs::new(Dft::default(), val_mmcs, fri, 4, SmallRng::seed_from_u64(1));
    let config = Cfg::new(pcs, Challenger::new(perm));
    let width = <Air as BaseAir<Val>>::width(&air);
    let trace = air.generate_trace_rows(n, LOG_BLOWUP);
    let t0 = Instant::now();
    let proof = prove(&config, &air, trace, &[]);
    let prove_ms = t0.elapsed().as_millis();
    let bytes = postcard::to_allocvec(&proof).unwrap();
    let t1 = Instant::now();
    verify(&config, &air, &proof, &[]).unwrap();
    let verify_ms = t1.elapsed().as_millis();
    Row { field: "Goldilocks w8", width, proof_kb: bytes.len() as f64 / 1024.0, prove_ms, verify_ms }
}

fn babybear_measure(n: usize) -> Row {
    type Val = BabyBear;
    type Challenge = BinomialExtensionField<Val, 4>; // F_p^4 ≈ 124-bit
    type Perm = p3_baby_bear::Poseidon2BabyBear<16>;
    type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
    type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
    type ValMmcs = MerkleHiding<Val, MyHash, MyCompress, 8>;
    type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
    type Challenger = DuplexChallenger<Val, Perm, 16, 8>;
    type Dft = Radix2DitParallel<Val>;
    type Pcs = HidingFriPcs<Val, Dft, ValMmcs, ChallengeMmcs, SmallRng>;
    type Cfg = StarkConfig<Pcs, Challenge, Challenger>;
    type Air = Poseidon2Air<
        Val,
        GenericPoseidon2LinearLayersBabyBear,
        16,
        7,
        1,
        BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS,
        BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16,
    >;

    let perm = default_babybear_poseidon2_16();
    let mut rng = SmallRng::seed_from_u64(1);
    let air: Air = Poseidon2Air::new(RoundConstants::from_rng(&mut rng));
    let val_mmcs = ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), 0, SmallRng::seed_from_u64(1));
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let fri = FriParameters {
        log_blowup: LOG_BLOWUP,
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: NUM_QUERIES,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: QUERY_POW,
        mmcs: challenge_mmcs,
    };
    let pcs = Pcs::new(Dft::default(), val_mmcs, fri, 4, SmallRng::seed_from_u64(1));
    let config = Cfg::new(pcs, Challenger::new(perm));
    let width = <Air as BaseAir<Val>>::width(&air);
    let trace = air.generate_trace_rows(n, LOG_BLOWUP);
    let t0 = Instant::now();
    let proof = prove(&config, &air, trace, &[]);
    let prove_ms = t0.elapsed().as_millis();
    let bytes = postcard::to_allocvec(&proof).unwrap();
    let t1 = Instant::now();
    verify(&config, &air, &proof, &[]).unwrap();
    let verify_ms = t1.elapsed().as_millis();
    Row { field: "BabyBear w16", width, proof_kb: bytes.len() as f64 / 1024.0, prove_ms, verify_ms }
}

// Shared hiding-Mmcs alias to keep the per-field type lines short.
type MerkleHiding<Val, H, C, const D: usize> = p3_merkle_tree::MerkleTreeHidingMmcs<
    <Val as Field>::Packing,
    <Val as Field>::Packing,
    H,
    C,
    SmallRng,
    2,
    D,
    D,
>;

fn main() {
    let n = 128; // compressions (≈ the spend's ~36 hashes, padded); ratio is N-independent
    println!("Field comparison: {n} Poseidon2 compressions, matched FRI (lb{LOG_BLOWUP} q{NUM_QUERIES} pow{QUERY_POW} ar1 cap0), ZK");
    println!("{:<16} {:>6} {:>10} {:>10} {:>11}", "field", "width", "proof(KB)", "prove(ms)", "verify(ms)");
    println!("{}", "-".repeat(58));
    for r in [goldilocks_measure(n), babybear_measure(n)] {
        println!("{:<16} {:>6} {:>10.1} {:>10} {:>11}", r.field, r.width, r.proof_kb, r.prove_ms, r.verify_ms);
    }
}
