//! Dev demo / smoke binary for the production prover crate. NOT shipped to the node — the node
//! consumes the C ABI in `lib.rs` (`liblattica_prover_p3.a`).
//!
//! Runs, end to end: the protocol's native Poseidon2 hash, the reference across-rows Poseidon2 AIR
//! (`poseidon2_air::Poseidon2RowsAir`, demo config), and the production join-split circuit
//! (`joinsplit_air::measure`: prove + verify + proven-security recompute under the production config
//! from `crate::config`).
//!
//! History: this file originally carried the M1 milestone — the vendored `p3-poseidon2-air`
//! permutation AIR under a local config stanza. That path was superseded by
//! `poseidon2_air::Poseidon2RowsAir` (the in-repo reference AIR) and the fused production circuits;
//! see git history and `docs/framework-decision.md`.

use lattica_prover_p3::poseidon2_air::native_permute;
use lattica_prover_p3::{joinsplit_air, poseidon2_air};
use p3_goldilocks::Goldilocks;

type Val = Goldilocks;

fn main() {
    let input: [Val; 8] = core::array::from_fn(|i| Val::new(i as u64 + 1));
    let out = native_permute(input);
    println!("lattica-prover-p3 demo: Poseidon2-Goldilocks, zero-knowledge FRI STARK");
    println!("  field   : Goldilocks (64-bit)");
    println!("  hash    : Poseidon2, vetted GOLDILOCKS_POSEIDON2_RC_8_* constants");
    println!("  proof   : hiding FRI PCS (zero-knowledge), transparent, PQ, stable toolchain");
    println!("  native H(1..8)[0] = {}", out[0]);

    // The reference across-rows Poseidon2 AIR (validation lineage for the fused circuits' hash regions).
    let p2_in: [Val; 8] = core::array::from_fn(|i| Val::new(i as u64 * 11 + 1));
    match poseidon2_air::prove_verify(p2_in) {
        Ok(()) => println!("  across-rows Poseidon2 AIR (ZK, demo config): ACCEPTED"),
        Err(e) => {
            println!("  across-rows Poseidon2 AIR: FAILED ({e})");
            std::process::exit(1);
        }
    }

    // Join-split (N-in/M-out) — the production circuit, under the production config.
    let (jbytes, jprove, jverify, jproven) = joinsplit_air::measure(&joinsplit_air::demo_witness());
    println!(
        "  join-split {}-in/{}-out (DEPTH={}, ZK): proof {} bytes, prove {} ms, verify {} ms, proven {} bits",
        joinsplit_air::N_IN,
        joinsplit_air::M_OUT,
        joinsplit_air::DEPTH,
        jbytes,
        jprove,
        jverify,
        jproven
    );
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
}
