//! v3 audit round 3 — executable verifier-robustness fuzzing for the HTLC C ABI.
//!
//! Prior rounds *reasoned* that `lattica_htlc_verify` is fail-closed + panic-isolated and that the
//! public inputs are non-malleable. This harness *demonstrates* it: it mutates a real proof and real
//! public-input bytes thousands of ways and asserts the verifier always rejects (never accepts a
//! forgery, never panics / UBs across the C ABI). Deterministic LCG — no `rand`, reproducible.

use lattica_prover_p3::{encode_htlc_public_inputs, htlc_air, lattica_htlc_verify};

fn lcg(s: &mut u64) -> u64 {
    *s = s
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *s
}

fn verify(proof: &[u8], pib: &[u8]) -> i32 {
    unsafe { lattica_htlc_verify(proof.as_ptr(), proof.len(), pib.as_ptr(), pib.len()) }
}

#[test]
fn fuzz_htlc_verify_is_fail_closed_and_non_malleable() {
    let w = htlc_air::demo_htlc_witness();
    let proof = htlc_air::prove_to_bytes(&w);
    let pib = encode_htlc_public_inputs(&htlc_air::public_values(&w)).unwrap();

    // baseline: the honest proof verifies.
    assert_eq!(verify(&proof, &pib), 0, "the honest demo proof must verify");

    let mut s: u64 = 0x0123_4567_89ab_cdef;
    let iters = 3000;

    // (1) mutate 1–4 bytes of the proof: every mutation must be REJECTED (a mutated proof that still
    //     verified would be a malleability/forgery break).
    let mut accepted = 0usize;
    for _ in 0..iters {
        let mut p = proof.clone();
        let k = 1 + (lcg(&mut s) % 4) as usize;
        for _ in 0..k {
            let idx = (lcg(&mut s) as usize) % p.len();
            p[idx] ^= (1 + (lcg(&mut s) % 255)) as u8;
        }
        if verify(&p, &pib) == 0 {
            accepted += 1;
        }
    }
    assert_eq!(
        accepted, 0,
        "{accepted} mutated proofs verified — malleability/forgery risk"
    );

    // (2) flip a single byte of the public inputs: every field byte is bound, so each must REJECT
    //     (either a non-canonical limb → parse reject, or a changed bound value → verify reject).
    for _ in 0..iters {
        let mut b = pib.clone();
        let idx = (lcg(&mut s) as usize) % b.len();
        b[idx] ^= (1 + (lcg(&mut s) % 255)) as u8;
        assert_ne!(
            verify(&proof, &b),
            0,
            "verify accepted tampered public inputs at byte {idx}"
        );
    }

    // (3) garbage / wrong-length proof bytes: must reject and must NOT panic across the C ABI
    //     (reaching the end of the loop is the no-panic assertion).
    for len in [
        0usize,
        1,
        16,
        31,
        64,
        1000,
        100_000,
        proof.len() - 1,
        proof.len() + 1,
    ] {
        let g: Vec<u8> = (0..len)
            .map(|i| (i as u8).wrapping_mul(31).wrapping_add(7))
            .collect();
        assert_ne!(
            verify(&g, &pib),
            0,
            "garbage proof of len {len} must be rejected"
        );
    }

    // (4) wrong-length public inputs: must reject (the parser length-checks before indexing).
    for delta in [-1i64, 1, -8, 8, 100] {
        let n = (pib.len() as i64 + delta).max(0) as usize;
        let b: Vec<u8> = (0..n).map(|i| pib.get(i).copied().unwrap_or(0)).collect();
        assert_ne!(
            verify(&proof, &b),
            0,
            "wrong-length public inputs ({n}) must be rejected"
        );
    }
}
