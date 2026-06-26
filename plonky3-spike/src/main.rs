//! ZK-01 spike — the degree-7 power-map core on **Plonky3** with the **hiding (zero-knowledge)**
//! FRI PCS, on **stable** Rust.
//!
//! Statement (same as the original Winterfell Phase-0 spike, for a direct comparison): public
//! `result`; the prover knows a secret `seed` with `seed^(7^(N-1)) = result`, enforced by the
//! degree-7 transition `next = cur^7`. Here it is proven in **zero-knowledge** via Plonky3's
//! `HidingFriPcs` + `MerkleTreeHidingMmcs` (salted commitments) — which Winterfell cannot do.
//!
//! Confirms: ZK prove→verify works end-to-end on stable; two proofs of the same statement differ
//! (blinding); a tampered public output is rejected.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_challenger::{HashChallenger, SerializingChallenger32};
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::PrimeCharacteristicRing;
use p3_fri::{FriParameters, HidingFriPcs};
use p3_keccak::{Keccak256Hash, KeccakF};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeHidingMmcs;
use p3_symmetric::{CompressionFunctionFromHasher, PaddingFreeSponge, SerializingHasher};
use p3_uni_stark::{prove, verify, StarkConfig};
use rand::rngs::SmallRng;
use rand::SeedableRng;

// --- the AIR: a single column where next = cur^7 (degree 7) ---------------------------------

struct Pow7Air;

impl<F> BaseAir<F> for Pow7Air {
    fn width(&self) -> usize {
        1
    }
    fn num_public_values(&self) -> usize {
        1
    }
    fn max_constraint_degree(&self) -> Option<usize> {
        Some(7)
    }
}

impl<AB: AirBuilder> Air<AB> for Pow7Air {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let l0 = main.current_slice()[0];
        let n0 = main.next_slice()[0];
        let result = builder.public_values()[0];

        // next = cur^7
        let x: AB::Expr = l0.into();
        let x2 = x.clone() * x.clone();
        let x4 = x2.clone() * x2.clone();
        let x6 = x4 * x2;
        let x7 = x6 * x;
        builder.when_transition().assert_eq(n0, x7);

        // the public result is the last row
        builder.when_last_row().assert_eq(l0, result);
    }
}

fn pow7(x: BabyBear) -> BabyBear {
    let x2 = x * x;
    let x4 = x2 * x2;
    x4 * x2 * x
}

fn generate_trace(seed: BabyBear, n: usize) -> RowMajorMatrix<BabyBear> {
    let mut vals = Vec::with_capacity(n);
    let mut cur = seed;
    for _ in 0..n {
        vals.push(cur);
        cur = pow7(cur);
    }
    RowMajorMatrix::new(vals, 1)
}

fn native_result(seed: BabyBear, n: usize) -> BabyBear {
    let mut cur = seed;
    for _ in 0..(n - 1) {
        cur = pow7(cur);
    }
    cur
}

// --- the zero-knowledge config (BabyBear + Keccak hiding Merkle PCS) -------------------------
// Field/hash are config choices: p3-goldilocks + Poseidon2 are also available; this mirrors the
// framework's own ZK test setup (the hiding commitment is what provides zero-knowledge).

type Val = BabyBear;
type Challenge = BinomialExtensionField<Val, 4>;
type Dft = Radix2DitParallel<Val>;

type ByteHash = Keccak256Hash;
type U64Hash = PaddingFreeSponge<KeccakF, 25, 17, 4>;
type FieldHash = SerializingHasher<U64Hash>;
type Compress = CompressionFunctionFromHasher<U64Hash, 2, 4>;
type ValHidingMmcs = MerkleTreeHidingMmcs<
    [Val; p3_keccak::VECTOR_LEN],
    [u64; p3_keccak::VECTOR_LEN],
    FieldHash,
    Compress,
    SmallRng,
    2,
    4,
    4,
>;
type Challenger = SerializingChallenger32<Val, HashChallenger<u8, ByteHash, 32>>;
type ChallengeHidingMmcs = ExtensionMmcs<Val, Challenge, ValHidingMmcs>;
type HidingPcs = HidingFriPcs<Val, Dft, ValHidingMmcs, ChallengeHidingMmcs, SmallRng>;
type ZkConfig = StarkConfig<HidingPcs, Challenge, Challenger>;

fn make_zk_config(rng_seed: u64) -> ZkConfig {
    let byte_hash = ByteHash {};
    let u64_hash = U64Hash::new(KeccakF {});
    let field_hash = FieldHash::new(u64_hash);
    let compress = Compress::new(u64_hash);
    let val_mmcs = ValHidingMmcs::new(field_hash, compress, 0, SmallRng::seed_from_u64(rng_seed));
    let challenge_mmcs = ChallengeHidingMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    // log_blowup = 3 supports the degree-7 constraint (blowup 8).
    let fri_params = FriParameters {
        log_blowup: 3,
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 24,
        commit_proof_of_work_bits: 1,
        query_proof_of_work_bits: 1,
        mmcs: challenge_mmcs,
    };
    let pcs = HidingPcs::new(dft, val_mmcs, fri_params, 4, SmallRng::seed_from_u64(rng_seed));
    let challenger = Challenger::from_hasher(vec![], byte_hash);
    ZkConfig::new(pcs, challenger)
}

fn main() {
    use std::time::Instant;
    let n = 1usize << 6; // 64-row trace
    let seed = BabyBear::from_u64(0x1234_5678);
    let result = native_result(seed, n);
    let pis = vec![result];

    let config = make_zk_config(1);
    let trace = generate_trace(seed, n);

    let t1 = Instant::now();
    let proof = prove(&config, &Pow7Air, trace.clone(), &pis);
    let prove_ms = t1.elapsed().as_millis();

    let size = postcard::to_allocvec(&proof).map(|v| v.len()).unwrap_or(0);

    let t2 = Instant::now();
    verify(&config, &Pow7Air, &proof, &pis).expect("verification failed");
    let verify_ms = t2.elapsed().as_millis();

    // ZK evidence: a second proof (independent blinding rng) differs from the first.
    let config2 = make_zk_config(2);
    let proof2 = prove(&config2, &Pow7Air, trace, &pis);
    verify(&config2, &Pow7Air, &proof2, &pis).expect("verification failed (proof2)");
    let b1 = postcard::to_allocvec(&proof).unwrap_or_default();
    let b2 = postcard::to_allocvec(&proof2).unwrap_or_default();
    let randomized = b1 != b2;

    println!("plonky3 ZK spike (HidingFriPcs, stable toolchain)");
    println!("  field            : BabyBear (Goldilocks/Poseidon2 also available)");
    println!("  PCS              : hiding FRI (zero-knowledge), transparent, PQ");
    println!("  statement        : seed^(7^(N-1)) = result, N={n} (degree-7 transition)");
    println!("  toolchain        : stable");
    println!("  prove time       : {prove_ms} ms");
    println!("  verify time      : {verify_ms} ms");
    println!("  proof size       : {size} bytes");
    println!("  ZK re-randomized : {randomized}");
    println!("  verify           : ACCEPTED");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_zk_proof_verifies() {
        let n = 1usize << 6;
        let seed = BabyBear::from_u64(42);
        let pis = vec![native_result(seed, n)];
        let config = make_zk_config(7);
        let proof = prove(&config, &Pow7Air, generate_trace(seed, n), &pis);
        verify(&config, &Pow7Air, &proof, &pis).expect("should verify");
    }

    #[test]
    fn wrong_public_result_rejected() {
        let n = 1usize << 6;
        let seed = BabyBear::from_u64(42);
        let bad_pis = vec![native_result(seed, n) + BabyBear::ONE];
        let config = make_zk_config(7);
        let proof = prove(&config, &Pow7Air, generate_trace(seed, n), &bad_pis);
        assert!(verify(&config, &Pow7Air, &proof, &bad_pis).is_err());
    }

    #[test]
    fn zero_knowledge_proofs_are_randomized() {
        let n = 1usize << 6;
        let seed = BabyBear::from_u64(42);
        let pis = vec![native_result(seed, n)];
        let p1 = prove(&make_zk_config(11), &Pow7Air, generate_trace(seed, n), &pis);
        let p2 = prove(&make_zk_config(22), &Pow7Air, generate_trace(seed, n), &pis);
        let b1 = postcard::to_allocvec(&p1).unwrap();
        let b2 = postcard::to_allocvec(&p2).unwrap();
        assert_ne!(b1, b2, "hiding PCS should re-randomize proofs");
    }
}
