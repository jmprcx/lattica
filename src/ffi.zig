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

/// The public statement of a **join-split** (N-input, M-output) shielded transaction — the
/// audit-target shape (`lattica-prover-p3::joinsplit_air`). All inputs are proven under one
/// `anchor`; `N` nullifiers + `M` output commitments are revealed; the proof enforces
/// `Σ in_value = Σ out_value + fee` with every value range-bounded. Must match the circuit's
/// `N_IN`/`M_OUT`.
pub const JOINSPLIT_N_IN: usize = 2;
pub const JOINSPLIT_M_OUT: usize = 2;

pub const JoinSplitPublicInputs = struct {
    anchor: Hash32,
    nullifiers: [JOINSPLIT_N_IN]Hash32,
    out_cms: [JOINSPLIT_M_OUT]Hash32,
    tx_binding: Hash32,
    fee: u64,
    mint: u64, // public issuance (0 for a normal tx; consensus enforces issuance rules)

    pub const ENCODED_LEN: usize = 32 * (2 + JOINSPLIT_N_IN + JOINSPLIT_M_OUT) + 8 + 8;

    /// Canonical byte layout: anchor ‖ N·nullifier ‖ M·out_cm ‖ tx_binding ‖ fee(LE) ‖ mint(LE).
    pub fn encode(self: JoinSplitPublicInputs) [ENCODED_LEN]u8 {
        var out: [ENCODED_LEN]u8 = undefined;
        var off: usize = 0;
        @memcpy(out[off..][0..32], &self.anchor);
        off += 32;
        for (self.nullifiers) |nf| {
            @memcpy(out[off..][0..32], &nf);
            off += 32;
        }
        for (self.out_cms) |oc| {
            @memcpy(out[off..][0..32], &oc);
            off += 32;
        }
        @memcpy(out[off..][0..32], &self.tx_binding);
        off += 32;
        std.mem.writeInt(u64, out[off..][0..8], self.fee, .little);
        off += 8;
        std.mem.writeInt(u64, out[off..][0..8], self.mint, .little);
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

/// Join-split verifier backend (the Rust `lattica_joinsplit_verify`), installed at startup.
var joinsplit_backend: ?VerifyFn = null;

pub fn setJoinSplitBackend(f: VerifyFn) void {
    joinsplit_backend = f;
}

/// Verify a join-split proof against its public inputs. Fail-closed (no backend ⇒ reject).
pub fn verifyJoinSplit(proof: []const u8, pi: JoinSplitPublicInputs) bool {
    const f = joinsplit_backend orelse return false;
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

test "ffi: join-split public inputs encode to the fixed canonical layout" {
    var pi = std.mem.zeroes(JoinSplitPublicInputs);
    pi.anchor = [_]u8{1} ** 32;
    pi.nullifiers[1] = [_]u8{9} ** 32;
    pi.tx_binding = [_]u8{4} ** 32;
    pi.fee = 0x0102_0304_0506_0708;
    pi.mint = 0x1100;
    const e = pi.encode();
    // anchor(32) ‖ 2·nf(32) ‖ 2·out_cm(32) ‖ tx_binding(32) ‖ fee(8) ‖ mint(8) = 208
    try testing.expectEqual(@as(usize, 208), JoinSplitPublicInputs.ENCODED_LEN);
    try testing.expectEqual(@as(u8, 1), e[0]); // anchor
    try testing.expectEqual(@as(u8, 9), e[64]); // nullifiers[1] starts at 32+32
    try testing.expectEqual(@as(u8, 4), e[160]); // tx_binding at 32·5
    try testing.expectEqual(@as(u8, 0x08), e[192]); // fee LSB at 32·6
    try testing.expectEqual(@as(u8, 0x00), e[200]); // mint LSB
    try testing.expectEqual(@as(u8, 0x11), e[201]); // mint next byte
}

test "ffi: join-split fail-closed without a backend" {
    const pi = std.mem.zeroes(JoinSplitPublicInputs);
    try testing.expect(!verifyJoinSplit("proof", pi));
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
