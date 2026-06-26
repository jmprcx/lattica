//! Production spend circuit on **Plonky3** — milestone 1: the vetted **Poseidon2-Goldilocks**
//! hash as an AIR, proving + verifying in-repo, on stable Rust.
//!
//! This stands up the production path chosen in `docs/framework-decision.md`:
//!   * field    = Goldilocks (64-bit — holds `u64` note values directly, clean value-balance/range);
//!   * hash     = Poseidon2 with the **vetted** `GOLDILOCKS_POSEIDON2_RC_8_*` constants, via the
//!                vetted `p3-poseidon2-air` AIR (so the in-circuit hash equals the protocol's
//!                native `Poseidon2Goldilocks` — no circuit/protocol hash mismatch, cf. C-03);
//!   * proof    = FRI STARK (transparent, post-quantum), **zero-knowledge** (M2) via the hiding
//!                Merkle PCS (`HidingFriPcs` + salted `MerkleTreeHidingMmcs`) and a Goldilocks-native
//!                `DuplexChallenger`.
//!
//! Remaining (see `docs/plonky3-port-plan.md`): compose the full spend statement (commitment +
//! membership + nullifier + ownership + balance + range + tx-binding) over the Poseidon2 chip via a
//! lookup argument (`p3-lookup`/LogUp). The Winterfell `lattica-prover` stays as a differential oracle.

use lattica_prover_p3::{full_spend_air, poseidon2_air, spend_air};

use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::Field;
use p3_fri::{FriParameters, HidingFriPcs};
use p3_goldilocks::{
    default_goldilocks_poseidon2_8, GenericPoseidon2LinearLayersGoldilocks, Goldilocks,
    Poseidon2Goldilocks, GOLDILOCKS_POSEIDON2_HALF_FULL_ROUNDS,
    GOLDILOCKS_POSEIDON2_PARTIAL_ROUNDS_8, GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_FINAL,
    GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_INITIAL, GOLDILOCKS_POSEIDON2_RC_8_INTERNAL,
};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeHidingMmcs;
use p3_poseidon2_air::{Poseidon2Air, RoundConstants};
use p3_symmetric::{PaddingFreeSponge, Permutation, TruncatedPermutation};
use p3_uni_stark::{prove, verify, StarkConfig};
use rand::rngs::SmallRng;
use rand::SeedableRng;

const WIDTH: usize = 8;
const SBOX_DEGREE: u64 = 7;
const SBOX_REGISTERS: usize = 1;
const HALF_FULL_ROUNDS: usize = GOLDILOCKS_POSEIDON2_HALF_FULL_ROUNDS; // 4
const PARTIAL_ROUNDS: usize = GOLDILOCKS_POSEIDON2_PARTIAL_ROUNDS_8; // 22

type Val = Goldilocks;
type Perm = Poseidon2Goldilocks<8>;

type SpendPoseidon2Air = Poseidon2Air<
    Val,
    GenericPoseidon2LinearLayersGoldilocks,
    WIDTH,
    SBOX_DEGREE,
    SBOX_REGISTERS,
    HALF_FULL_ROUNDS,
    PARTIAL_ROUNDS,
>;

/// The vetted Goldilocks Poseidon2 round constants, as the AIR's `RoundConstants` — identical to
/// the constants the native `Poseidon2Goldilocks` permutation uses.
fn vetted_constants() -> RoundConstants<Val, WIDTH, HALF_FULL_ROUNDS, PARTIAL_ROUNDS> {
    RoundConstants::new(
        GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_INITIAL,
        GOLDILOCKS_POSEIDON2_RC_8_INTERNAL,
        GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_FINAL,
    )
}

/// The protocol's native hash: one Goldilocks Poseidon2 permutation (vetted constants). The AIR
/// computes exactly this, so on-chain commitments/nullifiers and the in-circuit hash agree.
fn native_permute(input: [Val; WIDTH]) -> [Val; WIDTH] {
    let perm = default_goldilocks_poseidon2_8();
    let mut s = input;
    perm.permute_mut(&mut s);
    s
}

// --- STARK config (zero-knowledge: hiding Merkle PCS + DuplexChallenger, Goldilocks-native) ------

const LOG_BLOWUP: usize = 3; // supports the degree-7 S-box
type MyHash = PaddingFreeSponge<Perm, 8, 4, 4>;
type MyCompress = TruncatedPermutation<Perm, 2, 4, 8>;
// Hiding (salted) Merkle commitment ⇒ zero-knowledge.
type ValMmcs = MerkleTreeHidingMmcs<
    <Val as Field>::Packing,
    <Val as Field>::Packing,
    MyHash,
    MyCompress,
    SmallRng,
    2,
    4,
    4,
>;
type Challenge = BinomialExtensionField<Val, 2>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Challenger = DuplexChallenger<Val, Perm, 8, 4>;
type Dft = Radix2DitParallel<Val>;
type Pcs = HidingFriPcs<Val, Dft, ValMmcs, ChallengeMmcs, SmallRng>;
type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;

fn make_config(seed: u64) -> MyConfig {
    let perm = default_goldilocks_poseidon2_8();
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress, 0, SmallRng::seed_from_u64(seed));
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = FriParameters {
        log_blowup: LOG_BLOWUP,
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 24,
        commit_proof_of_work_bits: 1,
        query_proof_of_work_bits: 1,
        mmcs: challenge_mmcs,
    };
    let pcs = Pcs::new(dft, val_mmcs, fri_params, 4, SmallRng::seed_from_u64(seed));
    let challenger = Challenger::new(perm);
    MyConfig::new(pcs, challenger)
}

fn prove_perms(seed: u64) -> (MyConfig, p3_uni_stark::Proof<MyConfig>) {
    let air: SpendPoseidon2Air = Poseidon2Air::new(vetted_constants());
    let config = make_config(seed);
    let num_perms = 1 << 6;
    let trace: RowMajorMatrix<Val> = air.generate_trace_rows(num_perms, LOG_BLOWUP);
    let proof = prove(&config, &air, trace, &[]);
    (config, proof)
}

fn run() -> Result<(), impl core::fmt::Debug> {
    let air: SpendPoseidon2Air = Poseidon2Air::new(vetted_constants());
    let (config, proof) = prove_perms(1);
    verify(&config, &air, &proof, &[])
}

fn main() {
    let input = [
        Val::new(1),
        Val::new(2),
        Val::new(3),
        Val::new(4),
        Val::new(5),
        Val::new(6),
        Val::new(7),
        Val::new(8),
    ];
    let out = native_permute(input);
    println!("plonky3 production M1+M2: vetted Poseidon2-Goldilocks AIR, zero-knowledge");
    println!("  field   : Goldilocks (64-bit)");
    println!("  hash    : Poseidon2, vetted GOLDILOCKS_POSEIDON2_RC_8_* constants");
    println!("  proof   : hiding FRI PCS (zero-knowledge), transparent, PQ, stable toolchain");
    println!("  native H(1..8)[0] = {}", out[0]);
    match run() {
        Ok(()) => println!("  ZK AIR prove -> verify: ACCEPTED"),
        Err(e) => {
            println!("  AIR prove -> verify: FAILED ({e:?})");
            std::process::exit(1);
        }
    }

    // M4a: the across-rows Poseidon2 AIR (the spend statement's hash building block).
    let p2_in: [Val; 8] = core::array::from_fn(|i| Val::new(i as u64 * 11 + 1));
    match poseidon2_air::prove_verify(p2_in) {
        Ok(()) => println!("  M4a across-rows Poseidon2 AIR (ZK): ACCEPTED"),
        Err(e) => {
            println!("  M4a across-rows Poseidon2 AIR: FAILED ({e})");
            std::process::exit(1);
        }
    }

    // M4b: commitment + general-position Merkle membership.
    let opening: [Val; 4] = core::array::from_fn(|i| Val::new(i as u64 + 1));
    let sib: [[Val; 4]; spend_air::DEPTH] =
        core::array::from_fn(|d| core::array::from_fn(|k| Val::new((d * 10 + k + 100) as u64)));
    let bits: [bool; spend_air::DEPTH] = core::array::from_fn(|d| d % 2 == 1);
    let root = spend_air::native_root(opening, &sib, &bits);
    match spend_air::prove_verify(opening, sib, bits, root) {
        Ok(()) => println!("  M4b commitment + membership (ZK): ACCEPTED"),
        Err(e) => {
            println!("  M4b commitment + membership: FAILED ({e})");
            std::process::exit(1);
        }
    }

    // M4c: the full spend statement (ownership, commitment, membership, nullifier, output,
    // value-balance, range, tx-binding) in zero-knowledge.
    let w = full_spend_air::Witness {
        nk: 12345,
        value: 1000,
        rho: Val::new(7),
        rcm: Val::new(9),
        pos: Val::new(3),
        sib: core::array::from_fn(|d| core::array::from_fn(|k| Val::new((d * 4 + k + 50) as u64))),
        bits: [false, true, true, false],
        out_recipient: Val::new(77),
        out_value: 600,
        out_rho: Val::new(11),
        out_rcm: Val::new(13),
        fee: 400,
        tx_binding: core::array::from_fn(|i| Val::new(0xABCDEF + i as u64)),
    };
    match full_spend_air::prove_verify(&w) {
        Ok(()) => println!("  M4c full spend statement (ZK): ACCEPTED"),
        Err(e) => {
            println!("  M4c full spend statement: FAILED ({e})");
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;

    #[test]
    fn native_hash_is_deterministic() {
        let input = core::array::from_fn(|i| Val::from_u64(i as u64 + 1));
        assert_eq!(native_permute(input), native_permute(input));
    }

    #[test]
    fn vetted_poseidon2_air_proves_and_verifies() {
        run().expect("prove/verify should succeed");
    }
}
