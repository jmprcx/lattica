//! Production join-split prover/verifier on Plonky3 (zero-knowledge, transparent, post-quantum,
//! stable). `joinsplit_air` is the single production circuit (N-in/M-out, the audit target);
//! `poseidon2_air`/`spend_air` are its building blocks. This top level adds the canonical proof
//! serialization and the `lattica_joinsplit_verify`/`lattica_joinsplit_prove_demo` **C ABI** the Zig
//! node calls — matching `src/ffi.zig`.

pub mod joinsplit_air;
pub mod htlc_air; // v3: shielded HTLC spend (redeem/refund) — clone of joinsplit_air, extended
pub mod poseidon2_air;
pub mod spend_air;

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
    push_digest(&b[off..off + 32], &mut txb)?; // tx_binding (appended after fee/mint, circuit order)
    off += 32;
    pis.push(parse_felt(&b[off..off + 8])?); // fee
    off += 8;
    pis.push(parse_felt(&b[off..off + 8])?); // mint
    pis.extend_from_slice(&txb);
    Some(pis)
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
    if proof_ptr.is_null() || pi_ptr.is_null() {
        return 1;
    }
    // Bound the proof size before building/deserializing the slice, so C callers get fail-closed
    // behaviour even if a Zig-side cap is bypassed (audit M-08). Must match `ffi.MAX_PROOF_LEN`.
    if proof_len > MAX_PROOF_LEN {
        return 1;
    }
    let proof = slice::from_raw_parts(proof_ptr, proof_len);
    let pib = slice::from_raw_parts(pi_ptr, pi_len);
    let pis = match parse_joinsplit_public_inputs(pib) {
        Some(p) => p,
        None => return 1,
    };
    // Isolate any panic in deserialization / the STARK verifier (malformed-but-deserializable proofs
    // from the network must not unwind across `extern "C"`).
    let ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| joinsplit_air::verify_bytes(proof, &pis)));
    if matches!(ok, Ok(true)) {
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
    if proof_out.is_null() || pi_out.is_null() || proof_len.is_null() || pi_len.is_null() {
        return 1; // fail-closed on any null pointer (audit M-01)
    }
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
    let mut pis = Vec::with_capacity(htlc_air::NUM_PUBLIC_INPUTS);
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
    if pis.len() != htlc_air::NUM_PUBLIC_INPUTS {
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
    if proof_ptr.is_null() || pi_ptr.is_null() {
        return 1;
    }
    if proof_len > MAX_PROOF_LEN {
        return 1;
    }
    let proof = slice::from_raw_parts(proof_ptr, proof_len);
    let pib = slice::from_raw_parts(pi_ptr, pi_len);
    let pis = match parse_htlc_public_inputs(pib) {
        Some(p) => p,
        None => return 1,
    };
    let ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| htlc_air::verify_bytes(proof, &pis)));
    if matches!(ok, Ok(true)) {
        0
    } else {
        1
    }
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
    if proof.len() > proof_cap || pib.len() > pi_cap {
        return 2;
    }
    core::ptr::copy_nonoverlapping(proof.as_ptr(), proof_out, proof.len());
    *proof_len = proof.len();
    core::ptr::copy_nonoverlapping(pib.as_ptr(), pi_out, pib.len());
    *pi_len = pib.len();
    0
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
    if proof.len() > proof_cap || pib.len() > pi_cap {
        return 2;
    }
    core::ptr::copy_nonoverlapping(proof.as_ptr(), proof_out, proof.len());
    *proof_len = proof.len();
    core::ptr::copy_nonoverlapping(pib.as_ptr(), pi_out, pib.len());
    *pi_len = pib.len();
    0
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
    if proof.len() > proof_cap || pib.len() > pi_cap {
        return 2;
    }
    core::ptr::copy_nonoverlapping(proof.as_ptr(), proof_out, proof.len());
    *proof_len = proof.len();
    core::ptr::copy_nonoverlapping(pib.as_ptr(), pi_out, pib.len());
    *pi_len = pib.len();
    0
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;

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
}
