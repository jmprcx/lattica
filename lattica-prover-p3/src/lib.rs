//! Production prover/verifier on Plonky3 (zero-knowledge, transparent, post-quantum, stable). The two
//! production circuits are `joinsplit_air` (v1 N-in/M-out join-split) and `htlc_air` (v3 shielded HTLC
//! spend); both build on `poseidon2_air` (the Poseidon2 permutation AIR). This top level adds the
//! canonical proof serialization + the `lattica_joinsplit_*` / `lattica_htlc_*` **C ABI** the Zig node
//! calls (matching `src/ffi.zig`).

pub mod config; // crate-wide STARK config: the production (wire-pinned) + demo parameter families
pub mod domains; // consensus-frozen domain-separation tags (the normative table; mirrored by the Zig node)
pub mod spend_common; // shared native spend primitives (hashes/commit/nullifier/merge/fold) for both circuits
pub mod joinsplit_air;
pub mod htlc_air; // v3: shielded HTLC spend (redeem/refund) — clone of joinsplit_air, extended
pub mod batch_common; // shared batch machinery: MAX_BATCH_TILES, tile padding, the fold-block writer
pub mod batch_joinsplit_air; // batch aggregation: one proof per block (join-split tiling + tx-root fold)
pub mod batch_htlc_air; // batch aggregation for the v3 shielded-HTLC spend (mirrors batch_joinsplit_air)
pub mod poseidon2_air;
pub mod recursion; // Phase B: recursive STARK verifier (B1 spike = in-circuit FRI Merkle-opening verifier)
#[cfg(test)]
mod constraint_fingerprint; // refactor/audit oracle: pinned constraint-set fingerprints for every production AIR

use core::slice;
use p3_field::PrimeField64;
use p3_goldilocks::Goldilocks;

/// Goldilocks modulus `p = 2^64 − 2^32 + 1`; field-element bytes are rejected if `≥ p` (canonical).
const GOLDILOCKS_ORDER: u64 = 0xFFFF_FFFF_0000_0001;
const DIGEST_BYTES: usize = 32; // a 4-element Goldilocks digest, little-endian

/// Upper bound on an accepted proof, in bytes (real proofs are ~0.5 MB). The verifier C ABI rejects
/// anything larger before deserialization so untrusted callers can't force huge parse work (audit
/// M-08). Must match `src/ffi.zig`'s `MAX_PROOF_LEN`.
const MAX_PROOF_LEN: usize = 1 << 21;

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

// --- join-split (N-in/M-out) C ABI -------------------------------------------------------------

/// `JoinSplitPublicInputs` byte layout: anchor(32) ‖ N·nullifier(32) ‖ M·out_cm(32) ‖
/// tx_binding(32) ‖ fee(8 LE) ‖ mint(8 LE). Each 32-byte field is a 4-element Goldilocks digest.
const JS_PUBLIC_INPUTS_LEN: usize =
    DIGEST_BYTES * (2 + joinsplit_air::N_IN + joinsplit_air::M_OUT) + 8 + 8; // … ‖ fee(8) ‖ mint(8)

/// Parse the join-split public-input bytes into the circuit's vector
/// `anchor ‖ nf_i ‖ out_cm_j ‖ fee ‖ tx_binding`. Fail-closed on length / non-canonical limbs.
fn parse_joinsplit_public_inputs(b: &[u8]) -> Option<Vec<Goldilocks>> {
    if b.len() != JS_PUBLIC_INPUTS_LEN {
        return None;
    }
    let mut pis = Vec::with_capacity(joinsplit_air::N_PUBLIC);
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
    push_digest(&b[off..off + 32], &mut txb)?; // tx_binding (appended after fee/mint, circuit order)
    off += 32;
    pis.push(parse_felt(&b[off..off + 8])?); // fee
    off += 8;
    pis.push(parse_felt(&b[off..off + 8])?); // mint
    pis.extend_from_slice(&txb);
    Some(pis)
}

// --- shared ABI core ---------------------------------------------------------------------------
// The 10 #[no_mangle] entry points stay concrete (the frozen node seam), delegating their common
// sequences here so every fail-closed property — null checks, the M-08 size bound, canonical
// statement parsing, panic isolation, cap-before-store — is ONE audited implementation instead of
// ten mirrored copies.

/// Verify-side core: null → M-08 size bound → parse the statement bytes → panic-isolated verify.
/// `0` accept / `1` reject, fail-closed at every step.
///
/// # Safety
/// `proof_ptr`/`stmt_ptr` must point to `proof_len`/`stmt_len` readable bytes (or be null).
unsafe fn verify_abi(
    proof_ptr: *const u8,
    proof_len: usize,
    stmt_ptr: *const u8,
    stmt_len: usize,
    parse: impl Fn(&[u8]) -> Option<Vec<Goldilocks>>,
    verify: impl Fn(&[u8], &[Goldilocks]) -> bool,
) -> i32 {
    if proof_ptr.is_null() || stmt_ptr.is_null() {
        return 1;
    }
    // Bound the proof size before building/deserializing the slice, so C callers get fail-closed
    // behaviour even if a Zig-side cap is bypassed (audit M-08). Must match `ffi.MAX_PROOF_LEN`.
    if proof_len > MAX_PROOF_LEN {
        return 1;
    }
    let proof = slice::from_raw_parts(proof_ptr, proof_len);
    let sb = slice::from_raw_parts(stmt_ptr, stmt_len);
    let pis = match parse(sb) {
        Some(p) => p,
        None => return 1,
    };
    // Isolate any panic in deserialization / the STARK verifier (malformed-but-deserializable proofs
    // from the network must not unwind across `extern "C"`).
    let ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| verify(proof, &pis)));
    if matches!(ok, Ok(true)) {
        0
    } else {
        1
    }
}

/// The batch statement parser: a 32-byte block tx-root digest → 4 canonical limbs.
fn parse_root_digest(rb: &[u8]) -> Option<Vec<Goldilocks>> {
    if rb.len() != DIGEST_BYTES {
        return None;
    }
    let mut root = Vec::with_capacity(4);
    push_digest(rb, &mut root)?;
    Some(root)
}

/// Prove-side output writer: cap-checks BOTH buffers before ANY store (on `2` the `*_len` outputs
/// are untouched — the documented header contract), then copies and sets the lengths.
///
/// # Safety
/// The out pointers must be non-null with `*_cap` writable bytes; the len pointers writable.
#[allow(clippy::too_many_arguments)]
unsafe fn write_out2(
    a: &[u8],
    a_out: *mut u8,
    a_cap: usize,
    a_len: *mut usize,
    b: &[u8],
    b_out: *mut u8,
    b_cap: usize,
    b_len: *mut usize,
) -> i32 {
    if a.len() > a_cap || b.len() > b_cap {
        return 2;
    }
    core::ptr::copy_nonoverlapping(a.as_ptr(), a_out, a.len());
    *a_len = a.len();
    core::ptr::copy_nonoverlapping(b.as_ptr(), b_out, b.len());
    *b_len = b.len();
    0
}

/// C ABI: verify a serialized **join-split** proof against `JoinSplitPublicInputs` bytes.
/// `0` accept / nonzero reject; **fail-closed**: returns nonzero on null pointers, wrong public-input
/// length, non-canonical limbs, malformed proof bytes, or any panic inside the proof system (a node
/// accepts proofs from untrusted peers, so a panic must become a clean reject, never UB across the
/// C boundary).
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
    verify_abi(proof_ptr, proof_len, pi_ptr, pi_len, parse_joinsplit_public_inputs, joinsplit_air::verify_bytes)
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
    if proof_out.is_null() || pi_out.is_null() || proof_len.is_null() || pi_len.is_null() {
        return 1; // fail-closed on any null pointer (audit M-01)
    }
    let w = joinsplit_air::demo_witness();
    let proof = joinsplit_air::prove_to_bytes(&w);
    let pib = match encode_joinsplit_public_inputs(&joinsplit_air::public_values(&w)) {
        Some(b) => b,
        None => return 1,
    };
    write_out2(&proof, proof_out, proof_cap, proof_len, &pib, pi_out, pi_cap, pi_len)
}

/// Encode the circuit's join-split public-input vector into the `JoinSplitPublicInputs` byte layout
/// (inverse of `parse_joinsplit_public_inputs`). Used by tests and the node/wallet glue.
pub fn encode_joinsplit_public_inputs(pis: &[Goldilocks]) -> Option<Vec<u8>> {
    if pis.len() != joinsplit_air::N_PUBLIC {
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
    put(&mut out[off..off + 32], &pis[fee_idx + 2..fee_idx + 2 + d]); // tx_binding
    off += 32;
    out[off..off + 8].copy_from_slice(&pis[fee_idx].as_canonical_u64().to_le_bytes()); // fee
    off += 8;
    out[off..off + 8].copy_from_slice(&pis[fee_idx + 1].as_canonical_u64().to_le_bytes()); // mint
    Some(out)
}

// --- HTLC (v3 shielded HTLC spend) C ABI ------------------------------------------------------

/// `HtlcPublicInputs` byte layout: anchor(32) ‖ N·nullifier(32) ‖ M·out_cm(32) ‖ tx_binding(32) ‖
/// fee(8 LE) ‖ mint(8 LE) ‖ current_height(8 LE) ‖ redeem_hashlock(32). Parsed into the htlc_air
/// public-input vector (circuit order: …, fee, mint, tx_binding, current_height, redeem_hashlock).
const HTLC_PUBLIC_INPUTS_LEN: usize =
    DIGEST_BYTES * (2 + htlc_air::N_IN + htlc_air::M_OUT) + 8 + 8 + 8 + DIGEST_BYTES;

fn parse_htlc_public_inputs(b: &[u8]) -> Option<Vec<Goldilocks>> {
    if b.len() != HTLC_PUBLIC_INPUTS_LEN {
        return None;
    }
    let mut pis = Vec::with_capacity(htlc_air::N_PUBLIC);
    let mut off = 0;
    push_digest(&b[off..off + 32], &mut pis)?; // anchor
    off += 32;
    for _ in 0..htlc_air::N_IN {
        push_digest(&b[off..off + 32], &mut pis)?; // nf_i
        off += 32;
    }
    for _ in 0..htlc_air::M_OUT {
        push_digest(&b[off..off + 32], &mut pis)?; // out_cm_j
        off += 32;
    }
    let mut txb = Vec::with_capacity(4);
    push_digest(&b[off..off + 32], &mut txb)?; // tx_binding (bytes order: before fee/mint)
    off += 32;
    pis.push(parse_felt(&b[off..off + 8])?); // fee
    off += 8;
    pis.push(parse_felt(&b[off..off + 8])?); // mint
    off += 8;
    pis.extend_from_slice(&txb); // tx_binding (circuit order: after fee/mint)
    pis.push(parse_felt(&b[off..off + 8])?); // current_height
    off += 8;
    push_digest(&b[off..off + 32], &mut pis)?; // redeem_hashlock
    Some(pis)
}

/// Encode the htlc_air public-input vector into the byte layout (inverse of `parse_htlc_public_inputs`).
pub fn encode_htlc_public_inputs(pis: &[Goldilocks]) -> Option<Vec<u8>> {
    if pis.len() != htlc_air::N_PUBLIC {
        return None;
    }
    let d = htlc_air::DIGEST;
    let n = htlc_air::N_IN;
    let m = htlc_air::M_OUT;
    let mut out = vec![0u8; HTLC_PUBLIC_INPUTS_LEN];
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
    // circuit order from fee_idx: fee, mint, tx_binding(d), current_height, redeem_hashlock(d)
    let fee_idx = oc + m * d;
    put(&mut out[off..off + 32], &pis[fee_idx + 2..fee_idx + 2 + d]); // tx_binding
    off += 32;
    out[off..off + 8].copy_from_slice(&pis[fee_idx].as_canonical_u64().to_le_bytes()); // fee
    off += 8;
    out[off..off + 8].copy_from_slice(&pis[fee_idx + 1].as_canonical_u64().to_le_bytes()); // mint
    off += 8;
    out[off..off + 8].copy_from_slice(&pis[fee_idx + 2 + d].as_canonical_u64().to_le_bytes()); // current_height
    off += 8;
    put(&mut out[off..off + 32], &pis[fee_idx + 2 + d + 1..fee_idx + 2 + d + 1 + d]); // redeem_hashlock
    Some(out)
}

/// C ABI: verify a serialized **HTLC** proof against `HtlcPublicInputs` bytes. `0` accept / nonzero
/// reject; fail-closed + panic-isolated + proof-size-bounded, exactly like `lattica_joinsplit_verify`.
///
/// # Safety
/// `proof_ptr`/`pi_ptr` must point to `proof_len`/`pi_len` readable bytes (or be null).
#[no_mangle]
pub unsafe extern "C" fn lattica_htlc_verify(
    proof_ptr: *const u8,
    proof_len: usize,
    pi_ptr: *const u8,
    pi_len: usize,
) -> i32 {
    verify_abi(proof_ptr, proof_len, pi_ptr, pi_len, parse_htlc_public_inputs, htlc_air::verify_bytes)
}

/// C ABI: prove the fixed demo HTLC-redeem witness, writing the proof + `HtlcPublicInputs` bytes.
/// For the end-to-end FFI integration test. Returns 0 ok, 1 encode failure, 2 if a buffer is too small.
///
/// # Safety
/// The four pointers must be valid; `*_out` to `*_cap` writable bytes; the `len` pointers writable.
#[no_mangle]
pub unsafe extern "C" fn lattica_htlc_prove_demo(
    proof_out: *mut u8,
    proof_cap: usize,
    proof_len: *mut usize,
    pi_out: *mut u8,
    pi_cap: usize,
    pi_len: *mut usize,
) -> i32 {
    if proof_out.is_null() || pi_out.is_null() || proof_len.is_null() || pi_len.is_null() {
        return 1;
    }
    let w = htlc_air::demo_htlc_witness();
    let proof = htlc_air::prove_to_bytes(&w);
    let pib = match encode_htlc_public_inputs(&htlc_air::public_values(&w)) {
        Some(b) => b,
        None => return 1,
    };
    write_out2(&proof, proof_out, proof_cap, proof_len, &pib, pi_out, pi_cap, pi_len)
}

// --- wallet-side prover ABI -------------------------------------------------------------------

/// Canonical wallet→prover witness byte layout. Per input: nk0,nk1 (u64 LE) ‖ div (felt) ‖ value
/// (u64) ‖ rho0,rho1 (felt) ‖ rcm0,rcm1 (felt) ‖ sib[DEPTH]·digest(32) ‖ bits[DEPTH] (1 byte each).
/// Per output: recipient(32) ‖ value (u64) ‖ rho0,rho1 (felt) ‖ rcm0,rcm1 (felt). Tail: fee,mint
/// (u64) ‖ tx_binding(32). `div` is the diversifier; rho/rcm are 128-bit; felts are canonical 8-byte LE.
const fn js_witness_len() -> usize {
    let per_in = 8 + 8 + 8 + 8 + 8 + 16 + 16 + joinsplit_air::DEPTH * 32 + joinsplit_air::DEPTH; // nk0,nk1,div,asset,value,rho,rcm
    let per_out = 32 + 8 + 8 + 16 + 16; // recipient,asset,value,rho,rcm
    joinsplit_air::N_IN * per_in + joinsplit_air::M_OUT * per_out + 8 + 8 + 32
}
const JS_WITNESS_LEN: usize = js_witness_len();

fn rd_u64(b: &[u8], off: &mut usize) -> u64 {
    let v = u64::from_le_bytes(b[*off..*off + 8].try_into().unwrap());
    *off += 8;
    v
}
fn rd_felt(b: &[u8], off: &mut usize) -> Option<Goldilocks> {
    let f = parse_felt(&b[*off..*off + 8])?;
    *off += 8;
    Some(f)
}
fn rd_digest(b: &[u8], off: &mut usize) -> Option<[Goldilocks; 4]> {
    let mut d = Vec::with_capacity(4);
    for _ in 0..4 {
        d.push(rd_felt(b, off)?);
    }
    d.try_into().ok()
}
fn rd_felt2(b: &[u8], off: &mut usize) -> Option<[Goldilocks; 2]> {
    Some([rd_felt(b, off)?, rd_felt(b, off)?])
}

/// Parse the witness byte layout into a circuit witness. Fail-closed on wrong length / non-canonical.
fn parse_joinsplit_witness(b: &[u8]) -> Option<joinsplit_air::Witness> {
    use joinsplit_air::{Input, Output, Witness, DEPTH, M_OUT, N_IN};
    if b.len() != JS_WITNESS_LEN {
        return None;
    }
    let mut off = 0usize;
    let mut inputs = Vec::with_capacity(N_IN);
    for _ in 0..N_IN {
        let nk = [rd_u64(b, &mut off), rd_u64(b, &mut off)];
        let div = rd_felt(b, &mut off)?;
        let asset = rd_felt(b, &mut off)?;
        let value = rd_u64(b, &mut off);
        let rho = rd_felt2(b, &mut off)?;
        let rcm = rd_felt2(b, &mut off)?;
        let mut sib = Vec::with_capacity(DEPTH);
        for _ in 0..DEPTH {
            sib.push(rd_digest(b, &mut off)?);
        }
        let sib: [[Goldilocks; 4]; DEPTH] = sib.try_into().ok()?;
        let mut bits = [false; DEPTH];
        for bit in bits.iter_mut() {
            *bit = match b[off] {
                0 => false,
                1 => true,
                _ => return None, // path bits must be canonical 0/1 (audit M-03)
            };
            off += 1;
        }
        inputs.push(Input { nk, div, asset, value, rho, rcm, sib, bits });
    }
    let inputs: [Input; N_IN] = inputs.try_into().ok()?;
    let mut outputs = Vec::with_capacity(M_OUT);
    for _ in 0..M_OUT {
        let recipient = rd_digest(b, &mut off)?;
        let asset = rd_felt(b, &mut off)?;
        let value = rd_u64(b, &mut off);
        let rho = rd_felt2(b, &mut off)?;
        let rcm = rd_felt2(b, &mut off)?;
        outputs.push(Output { recipient, asset, value, rho, rcm });
    }
    let outputs: [Output; M_OUT] = outputs.try_into().ok()?;
    let fee = rd_u64(b, &mut off);
    let mint = rd_u64(b, &mut off);
    let tx_binding = rd_digest(b, &mut off)?;
    Some(Witness { inputs, outputs, fee, mint, tx_binding })
}

/// Encode a circuit witness into the canonical wallet→prover byte layout (inverse of
/// `parse_joinsplit_witness`). Used by tests and the wallet glue.
pub fn encode_joinsplit_witness(w: &joinsplit_air::Witness) -> Vec<u8> {
    let mut out = Vec::with_capacity(JS_WITNESS_LEN);
    let put_felt = |o: &mut Vec<u8>, f: Goldilocks| o.extend_from_slice(&f.as_canonical_u64().to_le_bytes());
    let put_u64 = |o: &mut Vec<u8>, v: u64| o.extend_from_slice(&v.to_le_bytes());
    for inp in &w.inputs {
        put_u64(&mut out, inp.nk[0]);
        put_u64(&mut out, inp.nk[1]);
        put_felt(&mut out, inp.div);
        put_felt(&mut out, inp.asset);
        put_u64(&mut out, inp.value);
        put_felt(&mut out, inp.rho[0]);
        put_felt(&mut out, inp.rho[1]);
        put_felt(&mut out, inp.rcm[0]);
        put_felt(&mut out, inp.rcm[1]);
        for row in &inp.sib {
            for &f in row {
                put_felt(&mut out, f);
            }
        }
        for &bit in &inp.bits {
            out.push(bit as u8);
        }
    }
    for o in &w.outputs {
        for &f in &o.recipient {
            put_felt(&mut out, f);
        }
        put_felt(&mut out, o.asset);
        put_u64(&mut out, o.value);
        put_felt(&mut out, o.rho[0]);
        put_felt(&mut out, o.rho[1]);
        put_felt(&mut out, o.rcm[0]);
        put_felt(&mut out, o.rcm[1]);
    }
    put_u64(&mut out, w.fee);
    put_u64(&mut out, w.mint);
    for &f in &w.tx_binding {
        put_felt(&mut out, f);
    }
    out
}

/// C ABI: prove a join-split from a serialized witness (wallet→prover), writing the proof + the
/// `JoinSplitPublicInputs` bytes. Returns 0 ok, 1 malformed/invalid witness or encode failure, 2 if a
/// buffer is too small. Fail-closed on null pointers; a witness that fails the circuit's relation
/// (e.g. unbalanced) is caught and returns 1 rather than unwinding across the ABI.
///
/// # Safety
/// `witness_ptr` must point to `witness_len` readable bytes; `*_out` to `*_cap` writable bytes; the
/// `len` pointers writable.
#[no_mangle]
pub unsafe extern "C" fn lattica_joinsplit_prove(
    witness_ptr: *const u8,
    witness_len: usize,
    proof_out: *mut u8,
    proof_cap: usize,
    proof_len: *mut usize,
    pi_out: *mut u8,
    pi_cap: usize,
    pi_len: *mut usize,
) -> i32 {
    if witness_ptr.is_null()
        || proof_out.is_null()
        || pi_out.is_null()
        || proof_len.is_null()
        || pi_len.is_null()
    {
        return 1; // fail-closed on any null pointer, incl. the output length pointers (audit M-01)
    }
    let wb = slice::from_raw_parts(witness_ptr, witness_len);
    let w = match parse_joinsplit_witness(wb) {
        Some(w) => w,
        None => return 1,
    };
    // public_values / trace-building assert the witness satisfies the relation; catch any panic so an
    // invalid witness returns an error instead of unwinding across the C boundary (UB).
    let built = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let pib = encode_joinsplit_public_inputs(&joinsplit_air::public_values(&w))?;
        let proof = joinsplit_air::prove_to_bytes(&w);
        Some((proof, pib))
    }));
    let (proof, pib) = match built {
        Ok(Some(x)) => x,
        _ => return 1,
    };
    write_out2(&proof, proof_out, proof_cap, proof_len, &pib, pi_out, pi_cap, pi_len)
}

// --- batch aggregation (one proof per block) C ABI --------------------------------------------

/// Encode a 4-element digest as 32 little-endian bytes (the block tx-root wire form).
fn encode_digest(d: &[Goldilocks]) -> Vec<u8> {
    let mut out = vec![0u8; DIGEST_BYTES];
    for (k, f) in d.iter().enumerate() {
        out[k * 8..k * 8 + 8].copy_from_slice(&f.as_canonical_u64().to_le_bytes());
    }
    out
}

/// C ABI: verify a serialized **batch** proof against the 32-byte block tx-root. `0` accept / nonzero
/// reject; **fail-closed** (null pointers, oversize proof, wrong root length, non-canonical limbs,
/// malformed proof, or any panic in the verifier).
///
/// # Safety
/// `proof_ptr`/`root_ptr` must point to `proof_len`/`root_len` readable bytes (or be null).
#[no_mangle]
pub unsafe extern "C" fn lattica_batch_verify(
    proof_ptr: *const u8,
    proof_len: usize,
    root_ptr: *const u8,
    root_len: usize,
) -> i32 {
    verify_abi(proof_ptr, proof_len, root_ptr, root_len, parse_root_digest, batch_joinsplit_air::verify_batch_bytes)
}

/// C ABI: prove `n_tx` concatenated join-split witnesses (each `JS_WITNESS_LEN` bytes) as ONE batch
/// proof. Writes the proof bytes and the 32-byte block tx-root into the caller's buffers. Returns 0 on
/// success, 1 on bad input / oversize batch (> `MAX_BATCH_TILES`) / panic, 2 if a buffer is too small.
///
/// # Safety
/// `witness_ptr` must point to `witness_len` readable bytes; `*_out` must point to `*_cap` writable
/// bytes; the `len` pointers must be writable (or all may be null ⇒ fail-closed).
#[no_mangle]
pub unsafe extern "C" fn lattica_batch_prove(
    witness_ptr: *const u8,
    witness_len: usize,
    n_tx: usize,
    proof_out: *mut u8,
    proof_cap: usize,
    proof_len: *mut usize,
    root_out: *mut u8,
    root_cap: usize,
    root_len: *mut usize,
) -> i32 {
    if witness_ptr.is_null() || proof_out.is_null() || root_out.is_null() || proof_len.is_null() || root_len.is_null() {
        return 1; // fail-closed on any null pointer (audit M-01)
    }
    if n_tx == 0 || witness_len != n_tx.checked_mul(JS_WITNESS_LEN).unwrap_or(usize::MAX) {
        return 1; // exactly n_tx concatenated join-split witness records
    }
    if batch_common::padded_tiles(n_tx) > batch_common::MAX_BATCH_TILES {
        return 1; // beyond the proven-soundness floor — split into multiple batch proofs
    }
    let wb = slice::from_raw_parts(witness_ptr, witness_len);
    let mut ws = Vec::with_capacity(n_tx);
    for i in 0..n_tx {
        match parse_joinsplit_witness(&wb[i * JS_WITNESS_LEN..(i + 1) * JS_WITNESS_LEN]) {
            Some(w) => ws.push(w),
            None => return 1,
        }
    }
    // build_trace / public_values assert the relation per tile; isolate any panic as a clean error.
    let built = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let root = batch_joinsplit_air::batch_root(&ws);
        let proof = batch_joinsplit_air::prove_batch_to_bytes(&ws);
        (proof, root)
    }));
    let (proof, root) = match built {
        Ok(x) => x,
        Err(_) => return 1,
    };
    let rb = encode_digest(&root);
    write_out2(&proof, proof_out, proof_cap, proof_len, &rb, root_out, root_cap, root_len)
}

// --- HTLC batch aggregation C ABI (mirrors the join-split batch; HTLC witnesses + tx-root) ----

/// C ABI: verify a serialized **HTLC batch** proof against the 32-byte block tx-root. Fail-closed +
/// size-bounded + panic-isolated, exactly like `lattica_batch_verify`.
///
/// # Safety
/// `proof_ptr`/`root_ptr` must point to `proof_len`/`root_len` readable bytes (or be null).
#[no_mangle]
pub unsafe extern "C" fn lattica_htlc_batch_verify(
    proof_ptr: *const u8,
    proof_len: usize,
    root_ptr: *const u8,
    root_len: usize,
) -> i32 {
    verify_abi(proof_ptr, proof_len, root_ptr, root_len, parse_root_digest, batch_htlc_air::verify_batch_bytes)
}

/// C ABI: prove `n_tx` concatenated **HTLC** witnesses (each `HTLC_WITNESS_LEN` bytes) as ONE batch
/// proof; writes the proof + the 32-byte block tx-root. Returns 0 ok, 1 on bad input / oversize batch /
/// panic, 2 if a buffer is too small.
///
/// # Safety
/// As `lattica_batch_prove`.
#[no_mangle]
pub unsafe extern "C" fn lattica_htlc_batch_prove(
    witness_ptr: *const u8,
    witness_len: usize,
    n_tx: usize,
    proof_out: *mut u8,
    proof_cap: usize,
    proof_len: *mut usize,
    root_out: *mut u8,
    root_cap: usize,
    root_len: *mut usize,
) -> i32 {
    if witness_ptr.is_null() || proof_out.is_null() || root_out.is_null() || proof_len.is_null() || root_len.is_null() {
        return 1;
    }
    if n_tx == 0 || witness_len != n_tx.checked_mul(HTLC_WITNESS_LEN).unwrap_or(usize::MAX) {
        return 1;
    }
    if batch_common::padded_tiles(n_tx) > batch_common::MAX_BATCH_TILES {
        return 1;
    }
    let wb = slice::from_raw_parts(witness_ptr, witness_len);
    let mut ws = Vec::with_capacity(n_tx);
    for i in 0..n_tx {
        match parse_htlc_witness(&wb[i * HTLC_WITNESS_LEN..(i + 1) * HTLC_WITNESS_LEN]) {
            Some(w) => ws.push(w),
            None => return 1,
        }
    }
    let built = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let root = batch_htlc_air::batch_root(&ws);
        let proof = batch_htlc_air::prove_batch_to_bytes(&ws);
        (proof, root)
    }));
    let (proof, root) = match built {
        Ok(x) => x,
        Err(_) => return 1,
    };
    let rb = encode_digest(&root);
    write_out2(&proof, proof_out, proof_cap, proof_len, &rb, root_out, root_cap, root_len)
}

// --- HTLC wallet-side prover ABI --------------------------------------------------------------

/// Canonical wallet→prover **HTLC** witness layout = the join-split layout plus the HTLC fields.
/// Per input: nk0,nk1 (u64) ‖ div ‖ asset ‖ note_type ‖ value (u64) ‖ rho0,rho1 ‖ rcm0,rcm1 ‖
/// sib[DEPTH]·digest ‖ bits[DEPTH] ‖ mode ‖ redeem_tag(32) ‖ refund_tag(32) ‖ hashlock(32) ‖
/// timeout (u64). Per output: recipient(32) ‖ asset ‖ note_type ‖ value (u64) ‖ rho ‖ rcm. Tail:
/// fee,mint (u64) ‖ tx_binding(32) ‖ current_height (u64).
const fn htlc_witness_len() -> usize {
    let d = htlc_air::DEPTH;
    let per_in = 16 + 8 + 8 + 8 + 8 + 16 + 16 + d * 32 + d + 8 + 32 + 32 + 32 + 8;
    let per_out = 32 + 8 + 8 + 8 + 16 + 16;
    htlc_air::N_IN * per_in + htlc_air::M_OUT * per_out + 8 + 8 + 32 + 8
}
const HTLC_WITNESS_LEN: usize = htlc_witness_len();

fn parse_htlc_witness(b: &[u8]) -> Option<htlc_air::Witness> {
    use htlc_air::{Input, Output, Witness, DEPTH, M_OUT, N_IN};
    if b.len() != HTLC_WITNESS_LEN {
        return None;
    }
    let mut off = 0usize;
    let mut inputs = Vec::with_capacity(N_IN);
    for _ in 0..N_IN {
        let nk = [rd_u64(b, &mut off), rd_u64(b, &mut off)];
        let div = rd_felt(b, &mut off)?;
        let asset = rd_felt(b, &mut off)?;
        let note_type = rd_felt(b, &mut off)?;
        let value = rd_u64(b, &mut off);
        let rho = rd_felt2(b, &mut off)?;
        let rcm = rd_felt2(b, &mut off)?;
        let mut sib = Vec::with_capacity(DEPTH);
        for _ in 0..DEPTH {
            sib.push(rd_digest(b, &mut off)?);
        }
        let sib: [[Goldilocks; 4]; DEPTH] = sib.try_into().ok()?;
        let mut bits = [false; DEPTH];
        for bit in bits.iter_mut() {
            *bit = match b[off] {
                0 => false,
                1 => true,
                _ => return None, // canonical path bits (audit M-03)
            };
            off += 1;
        }
        let mode = rd_felt(b, &mut off)?;
        let redeem_tag = rd_digest(b, &mut off)?;
        let refund_tag = rd_digest(b, &mut off)?;
        let hashlock = rd_digest(b, &mut off)?;
        let timeout = rd_u64(b, &mut off);
        inputs.push(Input {
            nk, div, asset, note_type, value, rho, rcm, sib, bits, mode, redeem_tag, refund_tag, hashlock, timeout,
        });
    }
    let inputs: [Input; N_IN] = inputs.try_into().ok()?;
    let mut outputs = Vec::with_capacity(M_OUT);
    for _ in 0..M_OUT {
        let recipient = rd_digest(b, &mut off)?;
        let asset = rd_felt(b, &mut off)?;
        let note_type = rd_felt(b, &mut off)?;
        let value = rd_u64(b, &mut off);
        let rho = rd_felt2(b, &mut off)?;
        let rcm = rd_felt2(b, &mut off)?;
        outputs.push(Output { recipient, asset, note_type, value, rho, rcm });
    }
    let outputs: [Output; M_OUT] = outputs.try_into().ok()?;
    let fee = rd_u64(b, &mut off);
    let mint = rd_u64(b, &mut off);
    let tx_binding = rd_digest(b, &mut off)?;
    let current_height = rd_u64(b, &mut off);
    Some(Witness { inputs, outputs, fee, mint, tx_binding, current_height })
}

/// Encode an HTLC witness into the canonical byte layout (inverse of `parse_htlc_witness`).
pub fn encode_htlc_witness(w: &htlc_air::Witness) -> Vec<u8> {
    let mut out = Vec::with_capacity(HTLC_WITNESS_LEN);
    let put_felt = |o: &mut Vec<u8>, f: Goldilocks| o.extend_from_slice(&f.as_canonical_u64().to_le_bytes());
    let put_u64 = |o: &mut Vec<u8>, v: u64| o.extend_from_slice(&v.to_le_bytes());
    let put_digest = |o: &mut Vec<u8>, d: &[Goldilocks; 4]| {
        for &f in d {
            o.extend_from_slice(&f.as_canonical_u64().to_le_bytes());
        }
    };
    for inp in &w.inputs {
        put_u64(&mut out, inp.nk[0]);
        put_u64(&mut out, inp.nk[1]);
        put_felt(&mut out, inp.div);
        put_felt(&mut out, inp.asset);
        put_felt(&mut out, inp.note_type);
        put_u64(&mut out, inp.value);
        put_felt(&mut out, inp.rho[0]);
        put_felt(&mut out, inp.rho[1]);
        put_felt(&mut out, inp.rcm[0]);
        put_felt(&mut out, inp.rcm[1]);
        for row in &inp.sib {
            for &f in row {
                put_felt(&mut out, f);
            }
        }
        for &bit in &inp.bits {
            out.push(bit as u8);
        }
        put_felt(&mut out, inp.mode);
        put_digest(&mut out, &inp.redeem_tag);
        put_digest(&mut out, &inp.refund_tag);
        put_digest(&mut out, &inp.hashlock);
        put_u64(&mut out, inp.timeout);
    }
    for o in &w.outputs {
        put_digest(&mut out, &o.recipient);
        put_felt(&mut out, o.asset);
        put_felt(&mut out, o.note_type);
        put_u64(&mut out, o.value);
        put_felt(&mut out, o.rho[0]);
        put_felt(&mut out, o.rho[1]);
        put_felt(&mut out, o.rcm[0]);
        put_felt(&mut out, o.rcm[1]);
    }
    put_u64(&mut out, w.fee);
    put_u64(&mut out, w.mint);
    put_digest(&mut out, &w.tx_binding);
    put_u64(&mut out, w.current_height);
    out
}

/// C ABI: prove an HTLC spend from a serialized witness, writing the proof + `HtlcPublicInputs` bytes.
/// Same fail-closed / panic-isolated / buffer-checked contract as `lattica_joinsplit_prove`.
///
/// # Safety
/// `witness_ptr` must point to `witness_len` readable bytes; `*_out` to `*_cap` writable bytes; the
/// `len` pointers writable.
#[no_mangle]
pub unsafe extern "C" fn lattica_htlc_prove(
    witness_ptr: *const u8,
    witness_len: usize,
    proof_out: *mut u8,
    proof_cap: usize,
    proof_len: *mut usize,
    pi_out: *mut u8,
    pi_cap: usize,
    pi_len: *mut usize,
) -> i32 {
    if witness_ptr.is_null()
        || proof_out.is_null()
        || pi_out.is_null()
        || proof_len.is_null()
        || pi_len.is_null()
    {
        return 1;
    }
    let wb = slice::from_raw_parts(witness_ptr, witness_len);
    let w = match parse_htlc_witness(wb) {
        Some(w) => w,
        None => return 1,
    };
    let built = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let pib = encode_htlc_public_inputs(&htlc_air::public_values(&w))?;
        let proof = htlc_air::prove_to_bytes(&w);
        Some((proof, pib))
    }));
    let (proof, pib) = match built {
        Ok(Some(x)) => x,
        _ => return 1,
    };
    write_out2(&proof, proof_out, proof_cap, proof_len, &pib, pi_out, pi_cap, pi_len)
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;

    #[test]
    fn wire_format_kats() {
        // EXACT-BYTE golden vectors for the frozen prover↔node wire (docs/wire-format.md), harvested
        // at HEAD c7e54b1 from the fixed demo witnesses (deterministic — no proving). The round-trip
        // tests below miss a SYMMETRIC parse+encode drift; these do not. A mismatch is a node-seam
        // break (and, for the batch tx-root fold, a consensus break). Re-pin only with a deliberate,
        // documented wire change — mirror it into src/poseidon2.zig + the Zig KATs.
        let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
        let jw = crate::joinsplit_air::demo_witness();
        let hw = crate::htlc_air::demo_htlc_witness();

        assert_eq!(JS_PUBLIC_INPUTS_LEN, 208);
        assert_eq!(HTLC_PUBLIC_INPUTS_LEN, 248);
        assert_eq!(JS_WITNESS_LEN, 2464);
        assert_eq!(HTLC_WITNESS_LEN, 2728);

        assert_eq!(
            hex(&encode_joinsplit_public_inputs(&crate::joinsplit_air::public_values(&jw)).unwrap()),
            "b6a82a86be39f45723dc1db5520136a815e0061a118d13407ebc56854ecf9092b74ee2743b9898568a11a57f7000766a5c702879ae61b4a3046c789b9e8d2ed7c548378e7ac07bad4be17e494352717927e6e8cc7153cbbd40aa757e9b077ef7f63bdab15aef196d6ce13e3f9e33678d42fbf7332f466abeedfc619dcec4b90aa9ed86e630fb8f5b0d091fa1f761508e7c2282de4109ccf81cccd7ae6cd27d96cdab000000000000ceab000000000000cfab000000000000d0ab00000000000064000000000000000000000000000000",
            "join-split public inputs (208 B) wire drift"
        );
        assert_eq!(
            hex(&encode_htlc_public_inputs(&crate::htlc_air::public_values(&hw)).unwrap()),
            "2ca3f793fd6f518d9e9491a7e12389358833484983098e7508cfa99691a97ff4c685b5d08292df19f1e6ded4d5031e73871f2b428aa17351274f123be0e9fc645f5473de5b1dc9fe98a32d11d9dbe559c6cac7c77605f30af273e47838fc2a65f182e204aaa849cdff92f789899df5726ca10bbed5d3423e6651f928077121c664f02c12fcbf9784cf7d44f40c56fab177cea616ff718fa51ef33d1aa57a948dcdab000000000000ceab000000000000cfab000000000000d0ab0000000000000000000000000000000000000000000005000000000000005100000000000000520000000000000053000000000000005400000000000000",
            "HTLC public inputs (248 B) wire drift"
        );
        assert_eq!(
            hex(&encode_joinsplit_witness(&jw)),
            "0700000000000000bc02000000000000f4010000000000002a00000000000000e8030000000000000b00000000000000d30000000000000064000000000000002c01000000000000680488735de920fc62843962ce8b4ea2e496364eab27a0ea4cc164a48b50035ff54541c457ec11447bf4a2ba965bf55f02286635aee2e0de1d98072cb3963c02006c16f5bfaf698e6a424e1f534d8fb153e2b1f752602a15acc4c18dbd73ae4482c230ab05a2ca56474c1764dc93e60ff8bea246a420ffd0da89cdb213a6e14aab4117fbe42169315dea4644391136b623a052543e899ce50f801a17137f839449f9999e1858bfb2496b34ca94d91b56633dda9712ec17ee59e9d32bf4e80be302c9ccb2366b046780e064abd50cc34e164b44a3617d18ab570372fbcfbb1bc36adbc5b224a767223c33484f4b0a720a25b75483df7ff2e5a4648a5df43e7ec09434c0d036e50426a947a676cbd3375f5cc416145ccabe9d6052a6ae7f6123039054c156832aecd6d6126ae8f2fc53bbffd9e13d005adfeaa918894170eddacc09f9db58d2023cdfc5e85e12cd15d71a5b0dc5eeacf091c44ca170bc96e56913e7f172e6dea8da337d4db28d9f8cf5059fe83731e07e4245a57138b9e07b34baad1cca7b29bd7d728b5b515e6a114e8f0827084e850af14143edd8b29dabb60afc10bc65d866bb0805a90a59bdc9155a4b7a7ce8499718752139f0534472137b0440da45146077952a43e372b2da1e20285f31dadcabf320ddd264b3ebe498189b458de0e10929e9c20e5c1706b72f56dfccff6b03946e1e6d5649f9a25b00a080606c3baaa99cf596c92b78586c2974bc058a1e0b80d1ce60e9130721841ee2d0dd3d35ec7df58d457d4467b7c2037c9f82056d8eacfdba76f1fcc7cf8e0e9a391fbf446b51251c1c4def0ab7e0508fe5819da972bc8b600606a771464b6f868a2b57d2846aaddaf5fe1b9f9d20c95a92d407768cbda80b4c561d062b0ab7adcf4cd33ddb7032a606a36f3e042770adcb7aa2f3acdf0bb5a2342945d39d29da8f9993474c456d7ab9fd3d7ab635fc0a0639ecb89767bb721fd267dc0fa0300511befa3312efc51d1caa0e99cad2dc7edb1a4228527b464ad7a65ebf1aa03c02f07f5faa26f35fe087e0a3ac0205651a47a4deac2a65202e26e0461063ff8883cf19fcb1d8e80c06abac154d34618ed9f3d63348406072824e8be577024edffceedfc65457069b5c834e249e5301a091d4d8479434b0d4dcb86212e7c3471847511222ccec03d5342600354af4f62b024a4412b90014ccf6739979924d97200a979a6a84d540b9fe2d6b31e6f65c3639033c78536fea230d100e2d9132f1c9e04c4be0c58e44eb979b507d28212844ce0d237e7bafc3664bb37ef74dfbfca0d0d81d90c3e4a0af3ce552daf711a0dd92433b0bf89890e513adb17af3014f6ac9e14e00c82014e2bafd8533a1fb8cbb4e1246779dd34ad74d69bfca38d0244e0f4882d6b8325f19add23b8c84e9a4845878769fd11b9952d5b1d979f36db0c15a00000000000000000000000000000000000000000000000000000000000000000800000000000000bd02000000000000f5010000000000002a00000000000000f4010000000000000c00000000000000d40000000000000065000000000000002d010000000000003f3b519092e587548363374d0e95be606fc70011f75c80ba76090bd2cc6318e0f54541c457ec11447bf4a2ba965bf55f02286635aee2e0de1d98072cb3963c02006c16f5bfaf698e6a424e1f534d8fb153e2b1f752602a15acc4c18dbd73ae4482c230ab05a2ca56474c1764dc93e60ff8bea246a420ffd0da89cdb213a6e14aab4117fbe42169315dea4644391136b623a052543e899ce50f801a17137f839449f9999e1858bfb2496b34ca94d91b56633dda9712ec17ee59e9d32bf4e80be302c9ccb2366b046780e064abd50cc34e164b44a3617d18ab570372fbcfbb1bc36adbc5b224a767223c33484f4b0a720a25b75483df7ff2e5a4648a5df43e7ec09434c0d036e50426a947a676cbd3375f5cc416145ccabe9d6052a6ae7f6123039054c156832aecd6d6126ae8f2fc53bbffd9e13d005adfeaa918894170eddacc09f9db58d2023cdfc5e85e12cd15d71a5b0dc5eeacf091c44ca170bc96e56913e7f172e6dea8da337d4db28d9f8cf5059fe83731e07e4245a57138b9e07b34baad1cca7b29bd7d728b5b515e6a114e8f0827084e850af14143edd8b29dabb60afc10bc65d866bb0805a90a59bdc9155a4b7a7ce8499718752139f0534472137b0440da45146077952a43e372b2da1e20285f31dadcabf320ddd264b3ebe498189b458de0e10929e9c20e5c1706b72f56dfccff6b03946e1e6d5649f9a25b00a080606c3baaa99cf596c92b78586c2974bc058a1e0b80d1ce60e9130721841ee2d0dd3d35ec7df58d457d4467b7c2037c9f82056d8eacfdba76f1fcc7cf8e0e9a391fbf446b51251c1c4def0ab7e0508fe5819da972bc8b600606a771464b6f868a2b57d2846aaddaf5fe1b9f9d20c95a92d407768cbda80b4c561d062b0ab7adcf4cd33ddb7032a606a36f3e042770adcb7aa2f3acdf0bb5a2342945d39d29da8f9993474c456d7ab9fd3d7ab635fc0a0639ecb89767bb721fd267dc0fa0300511befa3312efc51d1caa0e99cad2dc7edb1a4228527b464ad7a65ebf1aa03c02f07f5faa26f35fe087e0a3ac0205651a47a4deac2a65202e26e0461063ff8883cf19fcb1d8e80c06abac154d34618ed9f3d63348406072824e8be577024edffceedfc65457069b5c834e249e5301a091d4d8479434b0d4dcb86212e7c3471847511222ccec03d5342600354af4f62b024a4412b90014ccf6739979924d97200a979a6a84d540b9fe2d6b31e6f65c3639033c78536fea230d100e2d9132f1c9e04c4be0c58e44eb979b507d28212844ce0d237e7bafc3664bb37ef74dfbfca0d0d81d90c3e4a0af3ce552daf711a0dd92433b0bf89890e513adb17af3014f6ac9e14e00c82014e2bafd8533a1fb8cbb4e1246779dd34ad74d69bfca38d0244e0f4882d6b8325f19add23b8c84e9a4845878769fd11b9952d5b1d979f36db0c15a01000000000000000000000000000000000000000000000000000000000000008945a55369692270320a1d6967f7dcd063696317e87ef406de009c1249cd8b742a0000000000000084030000000000001500000000000000dd000000000000001600000000000000de000000000000007c031708c176ae5c31b1f0130bfd2a63d6a3a9d9fe9c2dafdb522757c1d1b0e42a00000000000000f4010000000000001600000000000000de000000000000001700000000000000df0000000000000064000000000000000000000000000000cdab000000000000ceab000000000000cfab000000000000d0ab000000000000",
            "join-split witness (2464 B) wire drift"
        );
        assert_eq!(
            hex(&encode_htlc_witness(&hw)),
            "0700000000000000460000000000000001000000000000002a000000000000000100000000000000e8030000000000000b00000000000000d30000000000000064000000000000002c0100000000000058e6c50408acc10fa7cb7ceeba066d7aa309dfc5230ae309feae0f669aafa509f54541c457ec11447bf4a2ba965bf55f02286635aee2e0de1d98072cb3963c02006c16f5bfaf698e6a424e1f534d8fb153e2b1f752602a15acc4c18dbd73ae4482c230ab05a2ca56474c1764dc93e60ff8bea246a420ffd0da89cdb213a6e14aab4117fbe42169315dea4644391136b623a052543e899ce50f801a17137f839449f9999e1858bfb2496b34ca94d91b56633dda9712ec17ee59e9d32bf4e80be302c9ccb2366b046780e064abd50cc34e164b44a3617d18ab570372fbcfbb1bc36adbc5b224a767223c33484f4b0a720a25b75483df7ff2e5a4648a5df43e7ec09434c0d036e50426a947a676cbd3375f5cc416145ccabe9d6052a6ae7f6123039054c156832aecd6d6126ae8f2fc53bbffd9e13d005adfeaa918894170eddacc09f9db58d2023cdfc5e85e12cd15d71a5b0dc5eeacf091c44ca170bc96e56913e7f172e6dea8da337d4db28d9f8cf5059fe83731e07e4245a57138b9e07b34baad1cca7b29bd7d728b5b515e6a114e8f0827084e850af14143edd8b29dabb60afc10bc65d866bb0805a90a59bdc9155a4b7a7ce8499718752139f0534472137b0440da45146077952a43e372b2da1e20285f31dadcabf320ddd264b3ebe498189b458de0e10929e9c20e5c1706b72f56dfccff6b03946e1e6d5649f9a25b00a080606c3baaa99cf596c92b78586c2974bc058a1e0b80d1ce60e9130721841ee2d0dd3d35ec7df58d457d4467b7c2037c9f82056d8eacfdba76f1fcc7cf8e0e9a391fbf446b51251c1c4def0ab7e0508fe5819da972bc8b600606a771464b6f868a2b57d2846aaddaf5fe1b9f9d20c95a92d407768cbda80b4c561d062b0ab7adcf4cd33ddb7032a606a36f3e042770adcb7aa2f3acdf0bb5a2342945d39d29da8f9993474c456d7ab9fd3d7ab635fc0a0639ecb89767bb721fd267dc0fa0300511befa3312efc51d1caa0e99cad2dc7edb1a4228527b464ad7a65ebf1aa03c02f07f5faa26f35fe087e0a3ac0205651a47a4deac2a65202e26e0461063ff8883cf19fcb1d8e80c06abac154d34618ed9f3d63348406072824e8be577024edffceedfc65457069b5c834e249e5301a091d4d8479434b0d4dcb86212e7c3471847511222ccec03d5342600354af4f62b024a4412b90014ccf6739979924d97200a979a6a84d540b9fe2d6b31e6f65c3639033c78536fea230d100e2d9132f1c9e04c4be0c58e44eb979b507d28212844ce0d237e7bafc3664bb37ef74dfbfca0d0d81d90c3e4a0af3ce552daf711a0dd92433b0bf89890e513adb17af3014f6ac9e14e00c82014e2bafd8533a1fb8cbb4e1246779dd34ad74d69bfca38d0244e0f4882d6b8325f19add23b8c84e9a4845878769fd11b9952d5b1d979f36db0c15a000000000000000000000000000000000000000000000000000000000000000001000000000000009aeeeeb2b3c763bdcd6a2c4378359252d2a499120cb7920eaf89111f87e85399de045fc7b4b1f64a11d47051fa47e66027e8fe6676f964bd97bdb8dcbb68ce3551000000000000005200000000000000530000000000000054000000000000000a000000000000000700000000000000460000000000000001000000000000002a00000000000000000000000000000000000000000000000d00000000000000d50000000000000065000000000000002d0100000000000052ecc79539769c6621076358681f865c85dcb08c42d43f0574c070a781cee1e3f54541c457ec11447bf4a2ba965bf55f02286635aee2e0de1d98072cb3963c02006c16f5bfaf698e6a424e1f534d8fb153e2b1f752602a15acc4c18dbd73ae4482c230ab05a2ca56474c1764dc93e60ff8bea246a420ffd0da89cdb213a6e14aab4117fbe42169315dea4644391136b623a052543e899ce50f801a17137f839449f9999e1858bfb2496b34ca94d91b56633dda9712ec17ee59e9d32bf4e80be302c9ccb2366b046780e064abd50cc34e164b44a3617d18ab570372fbcfbb1bc36adbc5b224a767223c33484f4b0a720a25b75483df7ff2e5a4648a5df43e7ec09434c0d036e50426a947a676cbd3375f5cc416145ccabe9d6052a6ae7f6123039054c156832aecd6d6126ae8f2fc53bbffd9e13d005adfeaa918894170eddacc09f9db58d2023cdfc5e85e12cd15d71a5b0dc5eeacf091c44ca170bc96e56913e7f172e6dea8da337d4db28d9f8cf5059fe83731e07e4245a57138b9e07b34baad1cca7b29bd7d728b5b515e6a114e8f0827084e850af14143edd8b29dabb60afc10bc65d866bb0805a90a59bdc9155a4b7a7ce8499718752139f0534472137b0440da45146077952a43e372b2da1e20285f31dadcabf320ddd264b3ebe498189b458de0e10929e9c20e5c1706b72f56dfccff6b03946e1e6d5649f9a25b00a080606c3baaa99cf596c92b78586c2974bc058a1e0b80d1ce60e9130721841ee2d0dd3d35ec7df58d457d4467b7c2037c9f82056d8eacfdba76f1fcc7cf8e0e9a391fbf446b51251c1c4def0ab7e0508fe5819da972bc8b600606a771464b6f868a2b57d2846aaddaf5fe1b9f9d20c95a92d407768cbda80b4c561d062b0ab7adcf4cd33ddb7032a606a36f3e042770adcb7aa2f3acdf0bb5a2342945d39d29da8f9993474c456d7ab9fd3d7ab635fc0a0639ecb89767bb721fd267dc0fa0300511befa3312efc51d1caa0e99cad2dc7edb1a4228527b464ad7a65ebf1aa03c02f07f5faa26f35fe087e0a3ac0205651a47a4deac2a65202e26e0461063ff8883cf19fcb1d8e80c06abac154d34618ed9f3d63348406072824e8be577024edffceedfc65457069b5c834e249e5301a091d4d8479434b0d4dcb86212e7c3471847511222ccec03d5342600354af4f62b024a4412b90014ccf6739979924d97200a979a6a84d540b9fe2d6b31e6f65c3639033c78536fea230d100e2d9132f1c9e04c4be0c58e44eb979b507d28212844ce0d237e7bafc3664bb37ef74dfbfca0d0d81d90c3e4a0af3ce552daf711a0dd92433b0bf89890e513adb17af3014f6ac9e14e00c82014e2bafd8533a1fb8cbb4e1246779dd34ad74d69bfca38d0244e0f4882d6b8325f19add23b8c84e9a4845878769fd11b9952d5b1d979f36db0c15a010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a78ec82e6387ada91ca63dff9391b0fdaa4b831cc02da2cd50e06aa02da82c5d2a000000000000000000000000000000e8030000000000001500000000000000dd000000000000001600000000000000de00000000000000f44b9f50c6b09d3678dd82ac1d3bcc6da4229764c43770f2b9292d2f861980412a00000000000000000000000000000000000000000000001700000000000000df000000000000001800000000000000e00000000000000000000000000000000000000000000000cdab000000000000ceab000000000000cfab000000000000d0ab0000000000000500000000000000",
            "HTLC witness (2728 B) wire drift"
        );
    }

    #[test]
    fn non_canonical_field_element_rejected() {
        // a digest limb of exactly p is non-canonical ⇒ parse fails ⇒ verify fails-closed
        let pis = crate::joinsplit_air::public_values(&crate::joinsplit_air::demo_witness());
        let mut pib = encode_joinsplit_public_inputs(&pis).unwrap();
        pib[0..8].copy_from_slice(&GOLDILOCKS_ORDER.to_le_bytes());
        assert!(parse_joinsplit_public_inputs(&pib).is_none());
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
        // tampered proof bytes (still postcard-shaped) → reject, and must not unwind across the ABI
        let mut bad_proof = proof.clone();
        bad_proof[proof.len() / 2] ^= 0xFF;
        assert_ne!(
            unsafe { lattica_joinsplit_verify(bad_proof.as_ptr(), bad_proof.len(), pib.as_ptr(), pib.len()) },
            0
        );
        // garbage proof buffers of various lengths → reject, never panic (catch_unwind isolation)
        for len in [0usize, 1, 31, 5000] {
            const G: [u8; 5000] = [0xAB; 5000];
            assert_ne!(
                unsafe { lattica_joinsplit_verify(G.as_ptr(), len, pib.as_ptr(), pib.len()) },
                0
            );
        }
    }

    #[test]
    fn joinsplit_prove_abi_roundtrips() {
        let w = crate::joinsplit_air::demo_witness();
        let wb = encode_joinsplit_witness(&w);
        assert_eq!(wb.len(), JS_WITNESS_LEN);
        // the serialized witness parses back to the same public statement
        let parsed = parse_joinsplit_witness(&wb).unwrap();
        assert_eq!(
            crate::joinsplit_air::public_values(&parsed),
            crate::joinsplit_air::public_values(&w)
        );
        // prove via the wallet ABI → the proof verifies against the returned public inputs
        let mut proof = vec![0u8; 1 << 20];
        let mut pi = vec![0u8; 512];
        let (mut pl, mut pil) = (0usize, 0usize);
        let rc = unsafe {
            lattica_joinsplit_prove(
                wb.as_ptr(), wb.len(),
                proof.as_mut_ptr(), proof.len(), &mut pl,
                pi.as_mut_ptr(), pi.len(), &mut pil,
            )
        };
        assert_eq!(rc, 0);
        assert_eq!(
            unsafe { lattica_joinsplit_verify(proof.as_ptr(), pl, pi.as_ptr(), pil) },
            0
        );
        // a truncated witness is rejected (fail-closed, no unwind across the ABI)
        let rc_bad = unsafe {
            lattica_joinsplit_prove(
                wb.as_ptr(), wb.len() - 1,
                proof.as_mut_ptr(), proof.len(), &mut pl,
                pi.as_mut_ptr(), pi.len(), &mut pil,
            )
        };
        assert_eq!(rc_bad, 1);
    }

    #[test]
    fn joinsplit_prove_abi_rejects_null_output_pointers() {
        // Every pointer argument is fail-closed, including the output length pointers (audit M-01).
        let w = crate::joinsplit_air::demo_witness();
        let wb = encode_joinsplit_witness(&w);
        let mut proof = vec![0u8; 1 << 20];
        let mut pi = vec![0u8; 512];
        let (mut pl, mut pil) = (0usize, 0usize);
        let np: *mut u8 = core::ptr::null_mut();
        let nl: *mut usize = core::ptr::null_mut();
        let prove = |wp: *const u8, wl: usize, po: *mut u8, pc: usize, plp: *mut usize, pio: *mut u8, pic: usize, pilp: *mut usize| unsafe {
            lattica_joinsplit_prove(wp, wl, po, pc, plp, pio, pic, pilp)
        };
        let (wp, wl) = (wb.as_ptr(), wb.len());
        let (po, pc) = (proof.as_mut_ptr(), proof.len());
        let (pio, pic) = (pi.as_mut_ptr(), pi.len());
        assert_eq!(prove(core::ptr::null(), 0, po, pc, &mut pl, pio, pic, &mut pil), 1); // witness_ptr
        assert_eq!(prove(wp, wl, np, pc, &mut pl, pio, pic, &mut pil), 1); // proof_out
        assert_eq!(prove(wp, wl, po, pc, nl, pio, pic, &mut pil), 1); // proof_len
        assert_eq!(prove(wp, wl, po, pc, &mut pl, np, pic, &mut pil), 1); // pi_out
        assert_eq!(prove(wp, wl, po, pc, &mut pl, pio, pic, nl), 1); // pi_len
        // demo prover: each output pointer null → fail-closed
        assert_eq!(unsafe { lattica_joinsplit_prove_demo(np, pc, &mut pl, pio, pic, &mut pil) }, 1);
        assert_eq!(unsafe { lattica_joinsplit_prove_demo(po, pc, nl, pio, pic, &mut pil) }, 1);
        assert_eq!(unsafe { lattica_joinsplit_prove_demo(po, pc, &mut pl, np, pic, &mut pil) }, 1);
        assert_eq!(unsafe { lattica_joinsplit_prove_demo(po, pc, &mut pl, pio, pic, nl) }, 1);
    }

    #[test]
    fn joinsplit_witness_non_canonical_bit_rejected() {
        // A path-bit byte other than 0/1 is non-canonical ⇒ parse fails ⇒ prove returns nonzero (M-03).
        let w = crate::joinsplit_air::demo_witness();
        let mut wb = encode_joinsplit_witness(&w);
        // input 0's path bits start after nk(16)+div(8)+value(8)+rho(16)+rcm(16)+sib(DEPTH*32) = 64+DEPTH*32.
        let bits0 = 64 + crate::joinsplit_air::DEPTH * 32;
        wb[bits0] = 2;
        let mut proof = vec![0u8; 1 << 20];
        let mut pi = vec![0u8; 512];
        let (mut pl, mut pil) = (0usize, 0usize);
        let rc = unsafe {
            lattica_joinsplit_prove(wb.as_ptr(), wb.len(), proof.as_mut_ptr(), proof.len(), &mut pl, pi.as_mut_ptr(), pi.len(), &mut pil)
        };
        assert_eq!(rc, 1);
    }

    #[test]
    fn joinsplit_verify_rejects_oversize_proof() {
        // An oversize `proof_len` is rejected before the slice is deserialized (audit M-08). We pass a
        // tiny real buffer with a huge claimed length; the size check returns before any deref.
        let pis = crate::joinsplit_air::public_values(&crate::joinsplit_air::demo_witness());
        let pib = encode_joinsplit_public_inputs(&pis).unwrap();
        let buf = [0u8; 8];
        assert_ne!(
            unsafe { lattica_joinsplit_verify(buf.as_ptr(), MAX_PROOF_LEN + 1, pib.as_ptr(), pib.len()) },
            0
        );
    }

    #[test]
    fn htlc_c_abi_roundtrip() {
        let w = crate::htlc_air::demo_htlc_witness();
        let proof = crate::htlc_air::prove_to_bytes(&w);
        let pis = crate::htlc_air::public_values(&w);
        let pib = encode_htlc_public_inputs(&pis).unwrap();
        assert_eq!(pib.len(), HTLC_PUBLIC_INPUTS_LEN);
        assert_eq!(parse_htlc_public_inputs(&pib).unwrap(), pis);
        // accept the real proof against the encoded public inputs
        assert_eq!(
            unsafe { lattica_htlc_verify(proof.as_ptr(), proof.len(), pib.as_ptr(), pib.len()) },
            0
        );
        // tamper the redeem_hashlock public input (last limb) → reject
        let mut bad = pis.clone();
        let last = bad.len() - 1;
        bad[last] += Goldilocks::ONE;
        let badb = encode_htlc_public_inputs(&bad).unwrap();
        assert_ne!(
            unsafe { lattica_htlc_verify(proof.as_ptr(), proof.len(), badb.as_ptr(), badb.len()) },
            0
        );
        // demo prover ABI → proof verifies against its returned public inputs
        let mut pbuf = vec![0u8; 1 << 20];
        let mut pibuf = vec![0u8; 512];
        let (mut pl, mut pil) = (0usize, 0usize);
        let rc = unsafe {
            lattica_htlc_prove_demo(pbuf.as_mut_ptr(), pbuf.len(), &mut pl, pibuf.as_mut_ptr(), pibuf.len(), &mut pil)
        };
        assert_eq!(rc, 0);
        assert_eq!(
            unsafe { lattica_htlc_verify(pbuf.as_ptr(), pl, pibuf.as_ptr(), pil) },
            0
        );
    }

    #[test]
    fn htlc_prove_abi_roundtrip() {
        // The wallet→prover path: encode an HTLC witness, prove it via the C ABI, verify the result.
        let w = crate::htlc_air::demo_htlc_witness();
        let wb = encode_htlc_witness(&w);
        assert_eq!(wb.len(), HTLC_WITNESS_LEN);
        // the byte layout round-trips to the same statement
        let w2 = parse_htlc_witness(&wb).unwrap();
        assert_eq!(crate::htlc_air::public_values(&w2), crate::htlc_air::public_values(&w));
        // prove from the serialized witness → the proof verifies against the returned public inputs
        let mut pbuf = vec![0u8; 1 << 20];
        let mut pibuf = vec![0u8; 512];
        let (mut pl, mut pil) = (0usize, 0usize);
        let rc = unsafe {
            lattica_htlc_prove(wb.as_ptr(), wb.len(), pbuf.as_mut_ptr(), pbuf.len(), &mut pl, pibuf.as_mut_ptr(), pibuf.len(), &mut pil)
        };
        assert_eq!(rc, 0);
        assert_eq!(unsafe { lattica_htlc_verify(pbuf.as_ptr(), pl, pibuf.as_ptr(), pil) }, 0);
        // a truncated witness is rejected (fail-closed)
        assert_eq!(
            unsafe { lattica_htlc_prove(wb.as_ptr(), wb.len() - 1, pbuf.as_mut_ptr(), pbuf.len(), &mut pl, pibuf.as_mut_ptr(), pibuf.len(), &mut pil) },
            1
        );
    }

    // --- HTLC ABI hardening regression tests (parallels of the join-split ones; audit O-3) ---

    #[test]
    fn htlc_verify_rejects_oversize_proof() {
        // Oversize proof_len rejected before the slice is built (audit M-08).
        let pis = crate::htlc_air::public_values(&crate::htlc_air::demo_htlc_witness());
        let pib = encode_htlc_public_inputs(&pis).unwrap();
        let buf = [0u8; 8];
        assert_ne!(
            unsafe { lattica_htlc_verify(buf.as_ptr(), MAX_PROOF_LEN + 1, pib.as_ptr(), pib.len()) },
            0
        );
    }

    #[test]
    fn htlc_public_input_non_canonical_rejected() {
        // A digest limb == p is non-canonical ⇒ parse fails ⇒ verify fails-closed (M-03).
        let pis = crate::htlc_air::public_values(&crate::htlc_air::demo_htlc_witness());
        let mut pib = encode_htlc_public_inputs(&pis).unwrap();
        pib[0..8].copy_from_slice(&GOLDILOCKS_ORDER.to_le_bytes()); // anchor limb 0 = p
        assert!(parse_htlc_public_inputs(&pib).is_none());
        let proof = [0u8; 8];
        assert_ne!(
            unsafe { lattica_htlc_verify(proof.as_ptr(), proof.len(), pib.as_ptr(), pib.len()) },
            0
        );
    }

    #[test]
    fn htlc_prove_abi_rejects_null_output_pointers() {
        // Every pointer incl. the output length pointers is fail-closed (audit M-01).
        let wb = encode_htlc_witness(&crate::htlc_air::demo_htlc_witness());
        let mut proof = vec![0u8; 1 << 20];
        let mut pi = vec![0u8; 512];
        let (mut pl, mut pil) = (0usize, 0usize);
        let np: *mut u8 = core::ptr::null_mut();
        let nl: *mut usize = core::ptr::null_mut();
        let (wp, wl) = (wb.as_ptr(), wb.len());
        let (po, pc) = (proof.as_mut_ptr(), proof.len());
        let (pio, pic) = (pi.as_mut_ptr(), pi.len());
        let prove = |wp, wl, po, pc, plp, pio, pic, pilp| unsafe {
            lattica_htlc_prove(wp, wl, po, pc, plp, pio, pic, pilp)
        };
        assert_eq!(prove(core::ptr::null(), 0, po, pc, &mut pl, pio, pic, &mut pil), 1);
        assert_eq!(prove(wp, wl, np, pc, &mut pl, pio, pic, &mut pil), 1);
        assert_eq!(prove(wp, wl, po, pc, nl, pio, pic, &mut pil), 1);
        assert_eq!(prove(wp, wl, po, pc, &mut pl, np, pic, &mut pil), 1);
        assert_eq!(prove(wp, wl, po, pc, &mut pl, pio, pic, nl), 1);
    }

    #[test]
    fn htlc_witness_non_canonical_bit_rejected() {
        // A path-bit byte other than 0/1 ⇒ parse fails ⇒ prove returns nonzero (M-03). Input 0's bits
        // begin after nk(16)+div(8)+asset(8)+note_type(8)+value(8)+rho(16)+rcm(16)+sib(DEPTH*32).
        let mut wb = encode_htlc_witness(&crate::htlc_air::demo_htlc_witness());
        let bits0 = 80 + crate::htlc_air::DEPTH * 32;
        wb[bits0] = 2;
        let mut proof = vec![0u8; 1 << 20];
        let mut pi = vec![0u8; 512];
        let (mut pl, mut pil) = (0usize, 0usize);
        let rc = unsafe {
            lattica_htlc_prove(wb.as_ptr(), wb.len(), proof.as_mut_ptr(), proof.len(), &mut pl, pi.as_mut_ptr(), pi.len(), &mut pil)
        };
        assert_eq!(rc, 1);
    }

    // --- batch (one proof per block) C ABI ---

    #[test]
    #[ignore = "slow: batch prove (2 tiles) via the C ABI"]
    fn batch_c_abi_roundtrip() {
        // two distinct join-split witnesses concatenated (demo + a tx_binding variant)
        let w0 = crate::joinsplit_air::demo_witness();
        let mut w1 = crate::joinsplit_air::demo_witness();
        w1.tx_binding[0] += Goldilocks::ONE;
        let mut wb = encode_joinsplit_witness(&w0);
        wb.extend_from_slice(&encode_joinsplit_witness(&w1));
        assert_eq!(wb.len(), 2 * JS_WITNESS_LEN);

        let mut proof = vec![0u8; 1 << 21];
        let mut root = [0u8; 32];
        let (mut pl, mut rl) = (0usize, 0usize);
        let rc = unsafe {
            lattica_batch_prove(wb.as_ptr(), wb.len(), 2, proof.as_mut_ptr(), proof.len(), &mut pl, root.as_mut_ptr(), root.len(), &mut rl)
        };
        assert_eq!(rc, 0);
        assert_eq!(rl, 32);
        // the proof verifies against the returned root
        assert_eq!(unsafe { lattica_batch_verify(proof.as_ptr(), pl, root.as_ptr(), rl) }, 0);
        // a tampered root is rejected
        let mut bad = root;
        bad[0] ^= 1;
        assert_ne!(unsafe { lattica_batch_verify(proof.as_ptr(), pl, bad.as_ptr(), 32) }, 0);
    }

    #[test]
    fn batch_abi_fail_closed() {
        let (mut pl, mut rl) = (0usize, 0usize);
        let mut p = [0u8; 8];
        let mut r = [0u8; 32];
        // null witness pointer ⇒ 1
        assert_eq!(
            unsafe { lattica_batch_prove(core::ptr::null(), 0, 1, p.as_mut_ptr(), p.len(), &mut pl, r.as_mut_ptr(), r.len(), &mut rl) },
            1
        );
        // null proof pointer on verify ⇒ reject
        assert_ne!(unsafe { lattica_batch_verify(core::ptr::null(), 0, r.as_ptr(), 32) }, 0);
        // witness_len not == n_tx · JS_WITNESS_LEN ⇒ 1
        let wb = vec![0u8; JS_WITNESS_LEN + 1];
        assert_eq!(
            unsafe { lattica_batch_prove(wb.as_ptr(), wb.len(), 1, p.as_mut_ptr(), p.len(), &mut pl, r.as_mut_ptr(), r.len(), &mut rl) },
            1
        );
        // n_tx beyond MAX_BATCH_TILES ⇒ rejected before any parsing/proving
        let big = vec![0u8; 65 * JS_WITNESS_LEN];
        assert_eq!(
            unsafe { lattica_batch_prove(big.as_ptr(), big.len(), 65, p.as_mut_ptr(), p.len(), &mut pl, r.as_mut_ptr(), r.len(), &mut rl) },
            1
        );
        // oversize proof_len on verify ⇒ rejected before deref (M-08)
        assert_ne!(unsafe { lattica_batch_verify(r.as_ptr(), MAX_PROOF_LEN + 1, r.as_ptr(), 32) }, 0);
        // wrong root length ⇒ reject
        assert_ne!(unsafe { lattica_batch_verify(r.as_ptr(), 0, r.as_ptr(), 31) }, 0);
    }

    #[test]
    #[ignore = "slow: HTLC batch prove (2 tiles) via the C ABI"]
    fn htlc_batch_c_abi_roundtrip() {
        let w0 = crate::htlc_air::demo_htlc_witness();
        let mut w1 = crate::htlc_air::demo_htlc_witness();
        w1.tx_binding[0] += Goldilocks::ONE;
        let mut wb = encode_htlc_witness(&w0);
        wb.extend_from_slice(&encode_htlc_witness(&w1));
        assert_eq!(wb.len(), 2 * HTLC_WITNESS_LEN);
        let mut proof = vec![0u8; 1 << 21];
        let mut root = [0u8; 32];
        let (mut pl, mut rl) = (0usize, 0usize);
        let rc = unsafe {
            lattica_htlc_batch_prove(wb.as_ptr(), wb.len(), 2, proof.as_mut_ptr(), proof.len(), &mut pl, root.as_mut_ptr(), root.len(), &mut rl)
        };
        assert_eq!(rc, 0);
        assert_eq!(rl, 32);
        assert_eq!(unsafe { lattica_htlc_batch_verify(proof.as_ptr(), pl, root.as_ptr(), rl) }, 0);
        let mut bad = root;
        bad[0] ^= 1;
        assert_ne!(unsafe { lattica_htlc_batch_verify(proof.as_ptr(), pl, bad.as_ptr(), 32) }, 0);
    }

    #[test]
    fn htlc_batch_abi_fail_closed() {
        let (mut pl, mut rl) = (0usize, 0usize);
        let mut p = [0u8; 8];
        let mut r = [0u8; 32];
        assert_eq!(
            unsafe { lattica_htlc_batch_prove(core::ptr::null(), 0, 1, p.as_mut_ptr(), p.len(), &mut pl, r.as_mut_ptr(), r.len(), &mut rl) },
            1
        );
        assert_ne!(unsafe { lattica_htlc_batch_verify(core::ptr::null(), 0, r.as_ptr(), 32) }, 0);
        let wb = vec![0u8; HTLC_WITNESS_LEN + 1];
        assert_eq!(
            unsafe { lattica_htlc_batch_prove(wb.as_ptr(), wb.len(), 1, p.as_mut_ptr(), p.len(), &mut pl, r.as_mut_ptr(), r.len(), &mut rl) },
            1
        );
        assert_ne!(unsafe { lattica_htlc_batch_verify(r.as_ptr(), MAX_PROOF_LEN + 1, r.as_ptr(), 32) }, 0);
        assert_ne!(unsafe { lattica_htlc_batch_verify(r.as_ptr(), 0, r.as_ptr(), 31) }, 0);
    }
}
