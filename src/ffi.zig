//! The spend-proof **verify boundary** between the Zig protocol layer and the production prover
//! (`lattica-prover`, a Winterfell crate exposed over a C ABI).
//!
//! This defines:
//!   * `SpendPublicInputs` — the exact public statement a spend proof binds, and its canonical
//!     byte layout (what is passed across the ABI / hashed into the proof);
//!   * a pluggable `backend` verifier the node installs at startup (either the Rust FFI verifier
//!     or, for differential testing, the hand-rolled reference). The default is **fail-closed**
//!     (no backend ⇒ reject), so a misconfigured node never accepts an unverified proof.
//!
//! The production C ABI the prover crate implements:
//!   `int32_t lattica_spend_verify(const uint8_t* proof, size_t proof_len,
//!                                 const uint8_t* public_inputs, size_t pi_len);`
//!   returns 0 to accept, non-zero to reject. A thin shim installs it via `setBackend`.

const std = @import("std");
const p = @import("primitives.zig");
const Hash32 = p.Hash32;

/// The public statement of a (1-input, 1-output) shielded spend. Note *values* are never here —
/// they are hidden inside the proof; the proof enforces `in_value = out_value + fee` and that
/// `out_cm` commits to `out_value`. Reconstructed by the verifier from the transaction so it can
/// never disagree with the body.
pub const SpendPublicInputs = struct {
    anchor: Hash32, // note-commitment tree root the spent note is proven under
    nullifier: Hash32, // revealed nullifier
    out_cm: Hash32, // output note commitment (binds the output value)
    tx_binding: Hash32, // the transaction-binding digest (sighash)
    fee: u64, // public fee

    pub const ENCODED_LEN: usize = 32 * 4 + 8;

    /// Canonical byte layout passed across the ABI.
    pub fn encode(self: SpendPublicInputs) [ENCODED_LEN]u8 {
        var out: [ENCODED_LEN]u8 = undefined;
        @memcpy(out[0..32], &self.anchor);
        @memcpy(out[32..64], &self.nullifier);
        @memcpy(out[64..96], &self.out_cm);
        @memcpy(out[96..128], &self.tx_binding);
        std.mem.writeInt(u64, out[128..136], self.fee, .little);
        return out;
    }
};

/// The C ABI shape the production verifier implements.
pub const VerifyFn = *const fn (
    proof_ptr: [*]const u8,
    proof_len: usize,
    pi_ptr: [*]const u8,
    pi_len: usize,
) callconv(.c) i32;

var backend: ?VerifyFn = null;

/// Install the verifier backend (the Rust FFI verifier in production, or the reference oracle in
/// differential tests). Called once at node startup.
pub fn setBackend(f: VerifyFn) void {
    backend = f;
}

pub fn clearBackend() void {
    backend = null;
}

/// Verify a spend proof against its public inputs. Fail-closed: with no backend installed, returns
/// false (never accepts an unverified proof).
pub fn verifySpend(proof: []const u8, pi: SpendPublicInputs) bool {
    const f = backend orelse return false;
    const enc = pi.encode();
    return f(proof.ptr, proof.len, &enc, enc.len) == 0;
}

// ---------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------

const testing = std.testing;

test "ffi: public inputs encode to the fixed canonical layout" {
    const pi = SpendPublicInputs{
        .anchor = [_]u8{1} ** 32,
        .nullifier = [_]u8{2} ** 32,
        .out_cm = [_]u8{3} ** 32,
        .tx_binding = [_]u8{4} ** 32,
        .fee = 0x0102_0304_0506_0708,
    };
    const e = pi.encode();
    try testing.expectEqual(SpendPublicInputs.ENCODED_LEN, e.len);
    try testing.expectEqual(@as(u8, 1), e[0]);
    try testing.expectEqual(@as(u8, 4), e[96]);
    try testing.expectEqual(@as(u8, 0x08), e[128]); // fee LSB
}

test "ffi: fail-closed without a backend" {
    clearBackend();
    const pi = std.mem.zeroes(SpendPublicInputs);
    try testing.expect(!verifySpend("proof", pi));
}

// A stub backend that accepts iff the proof is exactly "good" and the anchor's first byte is 7 —
// just enough to prove the plumbing (and that public inputs reach the backend) works.
fn stubVerify(proof_ptr: [*]const u8, proof_len: usize, pi_ptr: [*]const u8, pi_len: usize) callconv(.c) i32 {
    const proof = proof_ptr[0..proof_len];
    const pi = pi_ptr[0..pi_len];
    if (std.mem.eql(u8, proof, "good") and pi.len == SpendPublicInputs.ENCODED_LEN and pi[0] == 7) return 0;
    return 1;
}

test "ffi: installed backend receives proof and public inputs" {
    setBackend(&stubVerify);
    defer clearBackend();
    var pi = std.mem.zeroes(SpendPublicInputs);
    pi.anchor[0] = 7;
    try testing.expect(verifySpend("good", pi));
    try testing.expect(!verifySpend("bad", pi));
    pi.anchor[0] = 0;
    try testing.expect(!verifySpend("good", pi));
}
