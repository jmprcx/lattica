//! Production spend prover/verifier on Plonky3 (zero-knowledge, transparent, post-quantum, stable).
//!
//! Modules build the statement incrementally: `poseidon2_air` (M4a, the vetted Poseidon2-Goldilocks
//! permutation AIR), `spend_air` (M4b, commitment + general-position membership), `full_spend_air`
//! (M4c, the full spend statement, ZK). This top level (M5) adds the canonical proof serialization
//! and the `lattica_spend_verify` **C ABI** the Zig node calls — matching `src/ffi.zig`.

pub mod full_spend_air;
pub mod joinsplit_air;
pub mod poseidon2_air;
pub mod spend_air;

use core::slice;
use p3_field::PrimeField64;
use p3_goldilocks::Goldilocks;

/// Goldilocks modulus `p = 2^64 − 2^32 + 1`; field-element bytes are rejected if `≥ p` (canonical).
const GOLDILOCKS_ORDER: u64 = 0xFFFF_FFFF_0000_0001;
const DIGEST_BYTES: usize = 32; // a 4-element Goldilocks digest, little-endian
/// `SpendPublicInputs` length from `src/ffi.zig`: anchor‖nullifier‖out_cm‖tx_binding (4×32) ‖ fee (8).
const SPEND_PUBLIC_INPUTS_LEN: usize = DIGEST_BYTES * 4 + 8; // 136

fn parse_felt(b: &[u8]) -> Option<Goldilocks> {
    let v = u64::from_le_bytes(b.try_into().ok()?);
    if v >= GOLDILOCKS_ORDER {
        return None; // non-canonical ⇒ fail-closed
    }
    Some(Goldilocks::new(v))
}

fn push_digest(b: &[u8], out: &mut Vec<Goldilocks>) -> Option<()> {
    for k in 0..4 {
        out.push(parse_felt(&b[k * 8..k * 8 + 8])?);
    }
    Some(())
}

/// Canonical encoding of the circuit's public inputs into the `src/ffi.zig` `SpendPublicInputs`
/// byte layout (the inverse of `parse_spend_public_inputs`). Used by tests and the wallet/node glue.
pub fn encode_spend_public_inputs(pis: &[Goldilocks]) -> Option<Vec<u8>> {
    if pis.len() != full_spend_air::NUM_PUBLIC_INPUTS {
        return None;
    }
    // circuit order: root(4), nf(4), out_cm(4), fee(1), tx_binding(4)
    let mut out = vec![0u8; SPEND_PUBLIC_INPUTS_LEN];
    let put = |dst: &mut [u8], felts: &[Goldilocks]| {
        for (k, f) in felts.iter().enumerate() {
            dst[k * 8..k * 8 + 8].copy_from_slice(&f.as_canonical_u64().to_le_bytes());
        }
    };
    put(&mut out[0..32], &pis[0..4]); // anchor = root
    put(&mut out[32..64], &pis[4..8]); // nullifier
    put(&mut out[64..96], &pis[8..12]); // out_cm
    put(&mut out[96..128], &pis[13..17]); // tx_binding
    out[128..136].copy_from_slice(&pis[12].as_canonical_u64().to_le_bytes()); // fee
    Some(out)
}

/// Parse the `SpendPublicInputs` byte layout from `src/ffi.zig` into the circuit's public-input
/// vector `[root(4), nf(4), out_cm(4), fee(1), tx_binding(4)]`. Fail-closed on wrong length or any
/// non-canonical field element.
fn parse_spend_public_inputs(b: &[u8]) -> Option<Vec<Goldilocks>> {
    if b.len() != SPEND_PUBLIC_INPUTS_LEN {
        return None;
    }
    let mut pis = Vec::with_capacity(full_spend_air::NUM_PUBLIC_INPUTS);
    push_digest(&b[0..32], &mut pis)?; // root
    push_digest(&b[32..64], &mut pis)?; // nf
    push_digest(&b[64..96], &mut pis)?; // out_cm
    let mut txb = Vec::with_capacity(4);
    push_digest(&b[96..128], &mut txb)?; // tx_binding (parsed, appended after fee)
    pis.push(parse_felt(&b[128..136])?); // fee
    pis.extend_from_slice(&txb);
    Some(pis)
}

/// C ABI: verify a serialized spend proof against `SpendPublicInputs` bytes.
///
/// Returns `0` on accept, nonzero on reject. **Fail-closed** on null pointers, wrong public-input
/// length, non-canonical field elements, or malformed proof bytes. Matches `src/ffi.zig`'s
/// `VerifyFn` so the node can install it via `ffi.setBackend`.
///
/// # Safety
/// `proof_ptr`/`pi_ptr` must point to `proof_len`/`pi_len` readable bytes (or be null).
#[no_mangle]
pub unsafe extern "C" fn lattica_spend_verify(
    proof_ptr: *const u8,
    proof_len: usize,
    pi_ptr: *const u8,
    pi_len: usize,
) -> i32 {
    if proof_ptr.is_null() || pi_ptr.is_null() {
        return 1;
    }
    let proof = slice::from_raw_parts(proof_ptr, proof_len);
    let pib = slice::from_raw_parts(pi_ptr, pi_len);
    let pis = match parse_spend_public_inputs(pib) {
        Some(p) => p,
        None => return 1,
    };
    if full_spend_air::verify_bytes(proof, &pis) {
        0
    } else {
        1
    }
}

// --- join-split (N-in/M-out) C ABI -------------------------------------------------------------

/// `JoinSplitPublicInputs` byte layout: anchor(32) ‖ N·nullifier(32) ‖ M·out_cm(32) ‖
/// tx_binding(32) ‖ fee(8 LE). Each 32-byte field is a 4-element Goldilocks digest.
const JS_PUBLIC_INPUTS_LEN: usize =
    DIGEST_BYTES * (2 + joinsplit_air::N_IN + joinsplit_air::M_OUT) + 8;

/// Parse the join-split public-input bytes into the circuit's vector
/// `anchor ‖ nf_i ‖ out_cm_j ‖ fee ‖ tx_binding`. Fail-closed on length / non-canonical limbs.
fn parse_joinsplit_public_inputs(b: &[u8]) -> Option<Vec<Goldilocks>> {
    if b.len() != JS_PUBLIC_INPUTS_LEN {
        return None;
    }
    let mut pis = Vec::with_capacity(joinsplit_air::NUM_PUBLIC_INPUTS);
    let mut off = 0;
    push_digest(&b[off..off + 32], &mut pis)?; // anchor
    off += 32;
    for _ in 0..joinsplit_air::N_IN {
        push_digest(&b[off..off + 32], &mut pis)?; // nf_i
        off += 32;
    }
    for _ in 0..joinsplit_air::M_OUT {
        push_digest(&b[off..off + 32], &mut pis)?; // out_cm_j
        off += 32;
    }
    let mut txb = Vec::with_capacity(4);
    push_digest(&b[off..off + 32], &mut txb)?; // tx_binding (appended after fee, circuit order)
    off += 32;
    pis.push(parse_felt(&b[off..off + 8])?); // fee
    pis.extend_from_slice(&txb);
    Some(pis)
}

/// C ABI: verify a serialized **join-split** proof against `JoinSplitPublicInputs` bytes.
/// `0` accept / nonzero reject; fail-closed. See `lattica_spend_verify` for the conventions.
///
/// # Safety
/// `proof_ptr`/`pi_ptr` must point to `proof_len`/`pi_len` readable bytes (or be null).
#[no_mangle]
pub unsafe extern "C" fn lattica_joinsplit_verify(
    proof_ptr: *const u8,
    proof_len: usize,
    pi_ptr: *const u8,
    pi_len: usize,
) -> i32 {
    if proof_ptr.is_null() || pi_ptr.is_null() {
        return 1;
    }
    let proof = slice::from_raw_parts(proof_ptr, proof_len);
    let pib = slice::from_raw_parts(pi_ptr, pi_len);
    let pis = match parse_joinsplit_public_inputs(pib) {
        Some(p) => p,
        None => return 1,
    };
    if joinsplit_air::verify_bytes(proof, &pis) {
        0
    } else {
        1
    }
}

/// C ABI: prove the fixed demo join-split witness and write the proof + the `JoinSplitPublicInputs`
/// bytes into the caller's buffers. For the end-to-end FFI integration test (prove in Rust, verify
/// across the ABI). Returns 0 on success, 1 on encode failure, 2 if a buffer is too small.
///
/// # Safety
/// The four pointers must be valid; `*_out` must point to `*_cap` writable bytes; the `len` pointers
/// must be writable.
#[no_mangle]
pub unsafe extern "C" fn lattica_joinsplit_prove_demo(
    proof_out: *mut u8,
    proof_cap: usize,
    proof_len: *mut usize,
    pi_out: *mut u8,
    pi_cap: usize,
    pi_len: *mut usize,
) -> i32 {
    let w = joinsplit_air::demo_witness();
    let proof = joinsplit_air::prove_to_bytes(&w);
    let pib = match encode_joinsplit_public_inputs(&joinsplit_air::public_values(&w)) {
        Some(b) => b,
        None => return 1,
    };
    if proof.len() > proof_cap || pib.len() > pi_cap {
        return 2;
    }
    core::ptr::copy_nonoverlapping(proof.as_ptr(), proof_out, proof.len());
    *proof_len = proof.len();
    core::ptr::copy_nonoverlapping(pib.as_ptr(), pi_out, pib.len());
    *pi_len = pib.len();
    0
}

/// Encode the circuit's join-split public-input vector into the `JoinSplitPublicInputs` byte layout
/// (inverse of `parse_joinsplit_public_inputs`). Used by tests and the node/wallet glue.
pub fn encode_joinsplit_public_inputs(pis: &[Goldilocks]) -> Option<Vec<u8>> {
    if pis.len() != joinsplit_air::NUM_PUBLIC_INPUTS {
        return None;
    }
    let d = joinsplit_air::DIGEST;
    let n = joinsplit_air::N_IN;
    let m = joinsplit_air::M_OUT;
    let mut out = vec![0u8; JS_PUBLIC_INPUTS_LEN];
    let put = |dst: &mut [u8], felts: &[Goldilocks]| {
        for (k, f) in felts.iter().enumerate() {
            dst[k * 8..k * 8 + 8].copy_from_slice(&f.as_canonical_u64().to_le_bytes());
        }
    };
    let mut off = 0;
    put(&mut out[off..off + 32], &pis[0..d]); // anchor
    off += 32;
    for i in 0..n {
        put(&mut out[off..off + 32], &pis[d + i * d..d + (i + 1) * d]); // nf_i
        off += 32;
    }
    let oc = d + n * d;
    for j in 0..m {
        put(&mut out[off..off + 32], &pis[oc + j * d..oc + (j + 1) * d]); // out_cm_j
        off += 32;
    }
    let fee_idx = oc + m * d;
    put(&mut out[off..off + 32], &pis[fee_idx + 1..fee_idx + 1 + d]); // tx_binding
    off += 32;
    out[off..off + 8].copy_from_slice(&pis[fee_idx].as_canonical_u64().to_le_bytes()); // fee
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::full_spend_air::{prove_to_bytes, public_values, Witness};
    use p3_field::PrimeCharacteristicRing;

    fn sample() -> Witness {
        Witness {
            nk: 12345,
            value: 1000,
            rho: Goldilocks::from_u64(7),
            rcm: Goldilocks::from_u64(9),
            pos: Goldilocks::from_u64(3),
            sib: core::array::from_fn(|d| core::array::from_fn(|k| Goldilocks::from_u64((d * 4 + k + 50) as u64))),
            bits: core::array::from_fn(|d| d % 3 == 0),
            out_recipient: core::array::from_fn(|i| Goldilocks::from_u64(77 + i as u64)),
            out_value: 600,
            out_rho: Goldilocks::from_u64(11),
            out_rcm: Goldilocks::from_u64(13),
            fee: 400,
            tx_binding: core::array::from_fn(|i| Goldilocks::from_u64(0xABCDEF + i as u64)),
        }
    }

    #[test]
    fn public_input_byte_roundtrip() {
        let pis = public_values(&sample());
        let bytes = encode_spend_public_inputs(&pis).unwrap();
        assert_eq!(bytes.len(), SPEND_PUBLIC_INPUTS_LEN);
        assert_eq!(parse_spend_public_inputs(&bytes).unwrap(), pis);
    }

    #[test]
    fn c_abi_accepts_valid_and_fails_closed() {
        let w = sample();
        let proof = prove_to_bytes(&w);
        let pib = encode_spend_public_inputs(&public_values(&w)).unwrap();

        // accept
        assert_eq!(
            unsafe { lattica_spend_verify(proof.as_ptr(), proof.len(), pib.as_ptr(), pib.len()) },
            0
        );
        // tampered public inputs (wrong root) → reject
        let mut bad = public_values(&w);
        bad[0] += Goldilocks::ONE;
        let bad_pib = encode_spend_public_inputs(&bad).unwrap();
        assert_ne!(
            unsafe { lattica_spend_verify(proof.as_ptr(), proof.len(), bad_pib.as_ptr(), bad_pib.len()) },
            0
        );
        // wrong public-input length → fail-closed
        assert_ne!(
            unsafe { lattica_spend_verify(proof.as_ptr(), proof.len(), pib.as_ptr(), pib.len() - 1) },
            0
        );
        // null pointer → fail-closed
        assert_ne!(
            unsafe { lattica_spend_verify(core::ptr::null(), 0, pib.as_ptr(), pib.len()) },
            0
        );
        // malformed proof bytes → fail-closed
        assert_ne!(
            unsafe { lattica_spend_verify(proof[..proof.len() - 1].as_ptr(), proof.len() - 1, pib.as_ptr(), pib.len()) },
            0
        );
    }

    #[test]
    fn non_canonical_field_element_rejected() {
        // a digest limb of exactly p is non-canonical ⇒ parse fails ⇒ verify fails-closed
        let mut pib = encode_spend_public_inputs(&public_values(&sample())).unwrap();
        pib[0..8].copy_from_slice(&GOLDILOCKS_ORDER.to_le_bytes());
        assert!(parse_spend_public_inputs(&pib).is_none());
    }

    #[test]
    fn joinsplit_c_abi_roundtrip() {
        let w = crate::joinsplit_air::demo_witness();
        let proof = crate::joinsplit_air::prove_to_bytes(&w);
        let pis = crate::joinsplit_air::public_values(&w);
        let pib = encode_joinsplit_public_inputs(&pis).unwrap();
        assert_eq!(pib.len(), JS_PUBLIC_INPUTS_LEN);
        assert_eq!(parse_joinsplit_public_inputs(&pib).unwrap(), pis);
        // accept
        assert_eq!(
            unsafe { lattica_joinsplit_verify(proof.as_ptr(), proof.len(), pib.as_ptr(), pib.len()) },
            0
        );
        // tampered anchor → reject
        let mut bad = pis.clone();
        bad[0] += Goldilocks::ONE;
        let badb = encode_joinsplit_public_inputs(&bad).unwrap();
        assert_ne!(
            unsafe { lattica_joinsplit_verify(proof.as_ptr(), proof.len(), badb.as_ptr(), badb.len()) },
            0
        );
        // wrong length / null → fail-closed
        assert_ne!(
            unsafe { lattica_joinsplit_verify(proof.as_ptr(), proof.len(), pib.as_ptr(), pib.len() - 1) },
            0
        );
        assert_ne!(
            unsafe { lattica_joinsplit_verify(core::ptr::null(), 0, pib.as_ptr(), pib.len()) },
            0
        );
    }
}
