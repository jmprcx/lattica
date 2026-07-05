//! W2 (v3 batch-delta audit) — executable verifier-robustness fuzzing for the BATCH C ABI.
//!
//! Companion to `fuzz_htlc.rs`, for the four batch externs (`lattica_batch_{prove,verify}` and
//! `lattica_htlc_batch_{prove,verify}`). A batch proof ("one proof per block") binds ONE 32-byte block
//! tx-root — the Merkle–Damgård fold of the per-tile statement digests. The batch verifier must be
//! fail-closed, panic-isolated, and non-malleable in exactly the same way as the single-tx verifiers.
//!
//! This harness proves a real 2-tile block through the C ABI, then mutates the proof bytes and the
//! tx-root bytes thousands of ways and asserts the verifier ALWAYS rejects: it never accepts a mutated
//! proof (malleability/forgery), never accepts a tampered tx-root (a proof binds exactly one block
//! root), and never panics / UBs across the C ABI (reaching the end of a loop is the no-panic
//! assertion). Deterministic LCG — reproducible, no `rand`.

use lattica_prover_p3::{
    encode_htlc_witness, encode_joinsplit_witness, htlc_air, joinsplit_air, lattica_batch_prove,
    lattica_batch_verify, lattica_htlc_batch_prove, lattica_htlc_batch_verify,
};

fn lcg(s: &mut u64) -> u64 {
    *s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    *s
}

const ITERS: usize = 2000;

/// Prototype of the two batch verify externs: `verify(proof, proof_len, root, root_len) -> 0 iff accept`.
type BatchVerify = unsafe extern "C" fn(*const u8, usize, *const u8, usize) -> i32;
/// Prototype of the two batch prove externs.
type BatchProve =
    unsafe extern "C" fn(*const u8, usize, usize, *mut u8, usize, *mut usize, *mut u8, usize, *mut usize) -> i32;

/// Build a real batch proof + its 32-byte block tx-root through the C-ABI prover (as `batch_c_abi_roundtrip`).
fn prove_batch_abi(witness_bytes: &[u8], n_tx: usize, prove: BatchProve) -> (Vec<u8>, [u8; 32]) {
    let mut proof = vec![0u8; 1 << 21];
    let mut root = [0u8; 32];
    let (mut pl, mut rl) = (0usize, 0usize);
    let rc = unsafe {
        prove(
            witness_bytes.as_ptr(), witness_bytes.len(), n_tx,
            proof.as_mut_ptr(), proof.len(), &mut pl,
            root.as_mut_ptr(), root.len(), &mut rl,
        )
    };
    assert_eq!(rc, 0, "C-ABI batch prove must succeed");
    assert_eq!(rl, 32, "the block tx-root is a 32-byte digest");
    proof.truncate(pl);
    (proof, root)
}

/// The shared fuzz body: proof-byte mutations, tx-root-byte mutations, and garbage/wrong-length inputs.
fn fuzz_batch(label: &str, proof: &[u8], root: &[u8; 32], verify: BatchVerify) {
    let v = |p: &[u8], r: &[u8]| unsafe { verify(p.as_ptr(), p.len(), r.as_ptr(), r.len()) };

    // baseline: the honest block proof verifies against its own tx-root.
    assert_eq!(v(proof, root), 0, "{label}: the honest batch proof must verify");

    let mut s: u64 = 0x0123_4567_89ab_cdef;

    // (1) mutate 1–4 proof bytes: every mutation must be REJECTED. A mutated proof that still verifies
    //     against the same root would be a malleability/forgery break.
    let mut accepted = 0usize;
    for _ in 0..ITERS {
        let mut p = proof.to_vec();
        let k = 1 + (lcg(&mut s) % 4) as usize;
        for _ in 0..k {
            let idx = (lcg(&mut s) as usize) % p.len();
            p[idx] ^= (1 + (lcg(&mut s) % 255)) as u8;
        }
        if v(&p, root) == 0 {
            accepted += 1;
        }
    }
    assert_eq!(accepted, 0, "{label}: {accepted} mutated batch proofs verified — malleability/forgery risk");

    // (2) flip a single tx-root byte: a proof binds exactly one block root, so EVERY root byte is bound
    //     ⇒ each flip must REJECT (the proof no longer matches the claimed block).
    for _ in 0..ITERS {
        let mut r = *root;
        let idx = (lcg(&mut s) as usize) % 32;
        r[idx] ^= (1 + (lcg(&mut s) % 255)) as u8;
        assert_ne!(v(proof, &r), 0, "{label}: verify accepted a tampered tx-root at byte {idx}");
    }

    // (3) garbage / wrong-length proof bytes: reject + must NOT panic across the C ABI.
    for len in [0usize, 1, 16, 31, 64, 1000, 100_000, proof.len() - 1, proof.len() + 1] {
        let g: Vec<u8> = (0..len).map(|i| (i as u8).wrapping_mul(31).wrapping_add(7)).collect();
        assert_ne!(v(&g, root), 0, "{label}: garbage proof of len {len} must be rejected");
    }

    // (4) wrong-length root: the parser length-checks the digest before indexing ⇒ reject (never a panic).
    for n in [0usize, 1, 16, 31, 33, 64] {
        let r: Vec<u8> = (0..n).map(|i| root.get(i).copied().unwrap_or(0)).collect();
        assert_ne!(v(proof, &r), 0, "{label}: wrong-length root ({n}) must be rejected");
    }
}

#[test]
#[ignore = "slow: batch prove (2 tiles) + fuzz — part of the --ignored audit suite"]
fn fuzz_batch_join_split_verify_is_fail_closed_and_non_malleable() {
    // a real 2-tile block: two demo join-split tiles (each independently a valid spend).
    let w = joinsplit_air::demo_witness();
    let mut wb = encode_joinsplit_witness(&w);
    wb.extend_from_slice(&encode_joinsplit_witness(&w));
    let (proof, root) = prove_batch_abi(&wb, 2, lattica_batch_prove);
    fuzz_batch("join-split batch", &proof, &root, lattica_batch_verify);
}

#[test]
#[ignore = "slow: HTLC batch prove (2 tiles) + fuzz — part of the --ignored audit suite"]
fn fuzz_htlc_batch_verify_is_fail_closed_and_non_malleable() {
    let w = htlc_air::demo_htlc_witness();
    let mut wb = encode_htlc_witness(&w);
    wb.extend_from_slice(&encode_htlc_witness(&w));
    let (proof, root) = prove_batch_abi(&wb, 2, lattica_htlc_batch_prove);
    fuzz_batch("HTLC batch", &proof, &root, lattica_htlc_batch_verify);
}
