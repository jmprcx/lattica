//! The prove/verify **boundary** between the Zig protocol layer and the production Plonky3 prover
//! (`lattica-prover-p3`, exposed over a C ABI).
//!
//! Two statement shapes cross this boundary, each with a canonical byte layout and a pluggable,
//! **fail-closed** (no backend ⇒ reject), **proof-size-bounded** (`MAX_PROOF_LEN`), panic-isolated
//! verifier the node installs at startup:
//!   * `JoinSplitPublicInputs` + `verifyJoinSplit`/`proveJoinSplit` — the v1 N-in/M-out join-split
//!     (`lattica_joinsplit_verify`/`lattica_joinsplit_prove`).
//!   * `HtlcPublicInputs` + `verifyHtlc`/`proveHtlc` — the v3 shielded-HTLC spend
//!     (`lattica_htlc_verify`/`lattica_htlc_prove`).
//!
//! The production C ABI the prover crate implements (per statement):
//!   `int32_t lattica_{joinsplit,htlc}_verify(const uint8_t* proof, size_t proof_len,
//!                                            const uint8_t* public_inputs, size_t pi_len);`
//!   returns 0 to accept, non-zero to reject. The node installs it via `setJoinSplitBackend` /
//!   `setHtlcBackend`. (The pre-Plonky3 one-input `lattica_spend_verify` path has been removed.)

const std = @import("std");
const p = @import("primitives.zig");
const Hash32 = p.Hash32;

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

/// The C ABI shape the production verifier implements (shared by the join-split + HTLC seams).
pub const VerifyFn = *const fn (
    proof_ptr: [*]const u8,
    proof_len: usize,
    pi_ptr: [*]const u8,
    pi_len: usize,
) callconv(.c) i32;

/// Comptime generator for one pluggable backend slot: the `?Fn` global plus the set/clear/has and
/// the fail-closed, size-bounded call wrappers every seam repeats. `seam` makes each instantiation
/// a distinct type — its own `backend` global — even when two seams share the same `Fn` shape (Zig
/// memoizes generic instantiations by argument values). Only the methods matching `Fn`'s shape are
/// ever referenced for a given slot (Zig analyzes lazily), so one generator serves the `VerifyFn`,
/// `ProveFn` and `BatchProveFn` seams. The public `set*/clear*/has*/verify*/prove*` fns below keep
/// their exact names, signatures and semantics and delegate here.
fn BackendSlot(comptime seam: @TypeOf(.enum_literal), comptime Fn: type) type {
    return struct {
        const tag = seam; // ties the instantiation to the seam (distinct backend storage per seam)

        var backend: ?Fn = null;

        fn set(f: Fn) void {
            backend = f;
        }
        fn clear() void {
            backend = null;
        }
        fn has() bool {
            return backend != null;
        }

        /// Fail-closed (no backend ⇒ reject), proof-size-bounded verify. The oversize check runs
        /// BEFORE the backend is fetched/called, so the backend/deserializer is never invoked on an
        /// oversize buffer (M-08). `pi_bytes` is the seam's raw public-input encoding (`Fn` must be
        /// `VerifyFn`).
        fn verify(proof: []const u8, pi_bytes: []const u8) bool {
            if (proof.len > MAX_PROOF_LEN) return false;
            const f = backend orelse return false;
            return f(proof.ptr, proof.len, pi_bytes.ptr, pi_bytes.len) == 0;
        }

        /// `ProveFn`-shaped prove: serialized witness → allocator-owned proof bytes, with the
        /// backend's public-input echo written to a `pi_cap`-byte scratch buffer.
        fn prove(comptime pi_cap: usize, allocator: std.mem.Allocator, witness: []const u8) ![]u8 {
            const f = backend orelse return error.NoProveBackend;
            const buf = try allocator.alloc(u8, MAX_PROOF_LEN);
            defer allocator.free(buf); // `buf` is max-size scratch — always freed; we return an exact-sized copy.
            var pi: [pi_cap]u8 = undefined;
            var proof_len: usize = 0;
            var pi_len: usize = 0;
            const rc = f(witness.ptr, witness.len, buf.ptr, buf.len, &proof_len, &pi, pi.len, &pi_len);
            if (rc != 0) return error.ProveFailed;
            if (proof_len > buf.len) return error.ProveFailed; // backend must not claim more than the buffer
            // Exact-sized copy so the returned slice's length matches its allocation — avoids a wrong-size
            // free for allocators with exact-size semantics (audit M-04).
            return allocator.dupe(u8, buf[0..proof_len]);
        }

        /// `BatchProveFn`-shaped prove: `n_tx` concatenated witnesses → allocator-owned proof bytes
        /// + the 32-byte block tx-root the verifier checks against.
        fn proveBatch(allocator: std.mem.Allocator, witness: []const u8, n_tx: usize) !struct { proof: []u8, root: Hash32 } {
            const f = backend orelse return error.NoProveBackend;
            const buf = try allocator.alloc(u8, MAX_PROOF_LEN);
            defer allocator.free(buf);
            var root: Hash32 = undefined;
            var proof_len: usize = 0;
            var root_len: usize = 0;
            const rc = f(witness.ptr, witness.len, n_tx, buf.ptr, buf.len, &proof_len, &root, root.len, &root_len);
            if (rc != 0 or proof_len > buf.len or root_len != 32) return error.ProveFailed;
            return .{ .proof = try allocator.dupe(u8, buf[0..proof_len]), .root = root };
        }
    };
}

/// Join-split verifier backend (the Rust `lattica_joinsplit_verify`), installed at startup.
const joinsplit_slot = BackendSlot(.joinsplit_verify, VerifyFn);

pub fn setJoinSplitBackend(f: VerifyFn) void {
    joinsplit_slot.set(f);
}

/// Whether a join-split verifier backend is installed (production installs the Rust verifier at
/// startup; without one the node is in pre-cutover mode and relies on its native checks).
pub fn hasJoinSplitBackend() bool {
    return joinsplit_slot.has();
}

pub fn clearJoinSplitBackend() void {
    joinsplit_slot.clear();
}

/// Verify a join-split proof against its public inputs. Fail-closed (no backend ⇒ reject). Bounds the
/// proof size at this reusable seam so any direct caller — not just `node.applyChecked` — is protected
/// from oversize-proof DoS, and the backend/deserializer is never invoked on an oversize buffer (M-08).
pub fn verifyJoinSplit(proof: []const u8, pi: JoinSplitPublicInputs) bool {
    const enc = pi.encode();
    return joinsplit_slot.verify(proof, &enc);
}

// --- v3 shielded HTLC verifier seam (mirrors the join-split seam; backend = Rust lattica_htlc_verify) ---

/// Public statement of a shielded HTLC spend. Adds `current_height` (timeout compare) and
/// `redeem_hashlock` (= SHA256(preimage) for a redeem) to the join-split statement.
pub const HtlcPublicInputs = struct {
    anchor: Hash32,
    nullifiers: [JOINSPLIT_N_IN]Hash32,
    out_cms: [JOINSPLIT_M_OUT]Hash32,
    tx_binding: Hash32,
    fee: u64,
    mint: u64,
    current_height: u64,
    redeem_hashlock: Hash32,

    pub const ENCODED_LEN: usize = 32 * (2 + JOINSPLIT_N_IN + JOINSPLIT_M_OUT) + 8 + 8 + 8 + 32;

    /// anchor ‖ N·nf ‖ M·out_cm ‖ tx_binding ‖ fee(LE) ‖ mint(LE) ‖ current_height(LE) ‖ redeem_hashlock.
    /// Matches `lattica-prover-p3`'s `HtlcPublicInputs` byte layout (`parse_htlc_public_inputs`).
    pub fn encode(self: HtlcPublicInputs) [ENCODED_LEN]u8 {
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
        off += 8;
        std.mem.writeInt(u64, out[off..][0..8], self.current_height, .little);
        off += 8;
        @memcpy(out[off..][0..32], &self.redeem_hashlock);
        return out;
    }
};

const htlc_slot = BackendSlot(.htlc_verify, VerifyFn);

pub fn setHtlcBackend(f: VerifyFn) void {
    htlc_slot.set(f);
}
pub fn clearHtlcBackend() void {
    htlc_slot.clear();
}
pub fn hasHtlcBackend() bool {
    return htlc_slot.has();
}

/// Verify an HTLC spend proof. Fail-closed (no backend ⇒ reject) and proof-size-bounded at the seam
/// (audit M-08), exactly like `verifyJoinSplit`.
pub fn verifyHtlc(proof: []const u8, pi: HtlcPublicInputs) bool {
    const enc = pi.encode();
    return htlc_slot.verify(proof, &enc);
}

/// The C ABI the production prover implements (`lattica_joinsplit_prove`): consume a serialized
/// witness, write the proof + the `JoinSplitPublicInputs` bytes. Returns 0 ok, nonzero on failure.
pub const ProveFn = *const fn (
    witness_ptr: [*]const u8,
    witness_len: usize,
    proof_out: [*]u8,
    proof_cap: usize,
    proof_len: *usize,
    pi_out: [*]u8,
    pi_cap: usize,
    pi_len: *usize,
) callconv(.c) i32;

const joinsplit_prove_slot = BackendSlot(.joinsplit_prove, ProveFn);

pub fn setJoinSplitProveBackend(f: ProveFn) void {
    joinsplit_prove_slot.set(f);
}
pub fn clearJoinSplitProveBackend() void {
    joinsplit_prove_slot.clear();
}

/// Maximum join-split proof size the wallet buffers for (the real proof is ~0.5 MB).
pub const MAX_PROOF_LEN: usize = 1 << 21;

/// Prove a join-split from a serialized witness via the installed prover backend (the Rust
/// `lattica_joinsplit_prove` in production). Returns the proof bytes (allocator-owned).
pub fn proveJoinSplit(allocator: std.mem.Allocator, witness: []const u8) ![]u8 {
    return joinsplit_prove_slot.prove(JoinSplitPublicInputs.ENCODED_LEN, allocator, witness);
}

const htlc_prove_slot = BackendSlot(.htlc_prove, ProveFn);

pub fn setHtlcProveBackend(f: ProveFn) void {
    htlc_prove_slot.set(f);
}
pub fn clearHtlcProveBackend() void {
    htlc_prove_slot.clear();
}

/// Prove an HTLC spend from a serialized witness via the installed prover backend (the Rust
/// `lattica_htlc_prove` in production). Returns the proof bytes (allocator-owned).
pub fn proveHtlc(allocator: std.mem.Allocator, witness: []const u8) ![]u8 {
    return htlc_prove_slot.prove(HtlcPublicInputs.ENCODED_LEN, allocator, witness);
}

// --- v3 batch aggregation seam (one proof per block; backend = Rust lattica_batch_* ) -----------

/// Verify a **batch** proof against the 32-byte block tx-root. The verify backend shape is the shared
/// `VerifyFn` (the "public inputs" are the 32-byte root). Fail-closed (no backend ⇒ reject) and
/// proof-size-bounded at the seam (M-08).
const batch_slot = BackendSlot(.batch_verify, VerifyFn);

pub fn setBatchBackend(f: VerifyFn) void {
    batch_slot.set(f);
}
pub fn clearBatchBackend() void {
    batch_slot.clear();
}
pub fn hasBatchBackend() bool {
    return batch_slot.has();
}

pub fn verifyBatch(proof: []const u8, root: Hash32) bool {
    return batch_slot.verify(proof, &root);
}

/// The C ABI the batch prover implements (`lattica_batch_prove`): `n_tx` concatenated join-split
/// witnesses → one proof + the 32-byte block tx-root. (A distinct shape from `ProveFn`: it takes `n_tx`
/// and writes a fixed 32-byte root rather than a public-inputs struct.)
pub const BatchProveFn = *const fn (
    witness_ptr: [*]const u8,
    witness_len: usize,
    n_tx: usize,
    proof_out: [*]u8,
    proof_cap: usize,
    proof_len: *usize,
    root_out: [*]u8,
    root_cap: usize,
    root_len: *usize,
) callconv(.c) i32;

const batch_prove_slot = BackendSlot(.batch_prove, BatchProveFn);

pub fn setBatchProveBackend(f: BatchProveFn) void {
    batch_prove_slot.set(f);
}
pub fn clearBatchProveBackend() void {
    batch_prove_slot.clear();
}

/// Prove a batch of `n_tx` concatenated join-split witnesses via the installed backend (the Rust
/// `lattica_batch_prove` in production). Returns the proof bytes (allocator-owned) + the 32-byte block
/// tx-root the verifier checks against (the node recomputes the same root via `node.batchRoot`).
pub fn proveBatch(allocator: std.mem.Allocator, witness: []const u8, n_tx: usize) !struct { proof: []u8, root: Hash32 } {
    const r = try batch_prove_slot.proveBatch(allocator, witness, n_tx);
    return .{ .proof = r.proof, .root = r.root };
}

// --- v3 HTLC batch seam (backend = Rust lattica_htlc_batch_*; same shapes as the join-split batch) ---

const htlc_batch_slot = BackendSlot(.htlc_batch_verify, VerifyFn);

pub fn setHtlcBatchBackend(f: VerifyFn) void {
    htlc_batch_slot.set(f);
}
pub fn clearHtlcBatchBackend() void {
    htlc_batch_slot.clear();
}

/// Verify an HTLC batch proof against the 32-byte block tx-root (fail-closed + size-bounded).
pub fn verifyHtlcBatch(proof: []const u8, root: Hash32) bool {
    return htlc_batch_slot.verify(proof, &root);
}

const htlc_batch_prove_slot = BackendSlot(.htlc_batch_prove, BatchProveFn);

pub fn setHtlcBatchProveBackend(f: BatchProveFn) void {
    htlc_batch_prove_slot.set(f);
}
pub fn clearHtlcBatchProveBackend() void {
    htlc_batch_prove_slot.clear();
}

/// Prove a batch of `n_tx` concatenated HTLC witnesses via the installed backend (Rust
/// lattica_htlc_batch_prove). Returns the proof bytes (allocator-owned) + the 32-byte block tx-root.
pub fn proveHtlcBatch(allocator: std.mem.Allocator, witness: []const u8, n_tx: usize) !struct { proof: []u8, root: Hash32 } {
    const r = try htlc_batch_prove_slot.proveBatch(allocator, witness, n_tx);
    return .{ .proof = r.proof, .root = r.root };
}

// ---------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------

const testing = std.testing;

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

test "ffi: verifyJoinSplit rejects an oversize proof without invoking the backend (M-08)" {
    const Rec = struct {
        var called: bool = false;
        fn vfn(_: [*]const u8, _: usize, _: [*]const u8, _: usize) callconv(.c) i32 {
            called = true;
            return 0; // would "accept" if it were reached
        }
    };
    Rec.called = false;
    setJoinSplitBackend(&Rec.vfn);
    defer clearJoinSplitBackend();
    const pi = std.mem.zeroes(JoinSplitPublicInputs);
    const oversize = try testing.allocator.alloc(u8, MAX_PROOF_LEN + 1);
    defer testing.allocator.free(oversize);
    // Oversize ⇒ rejected at the seam, backend never called.
    try testing.expect(!verifyJoinSplit(oversize, pi));
    try testing.expect(!Rec.called);
    // Sanity: a normal-size proof DOES reach the backend.
    try testing.expect(verifyJoinSplit("x", pi));
    try testing.expect(Rec.called);
}

test "ffi: htlc public inputs encode + fail-closed + size-bound" {
    var pi = std.mem.zeroes(HtlcPublicInputs);
    pi.anchor = [_]u8{1} ** 32;
    pi.current_height = 0x0102_0304_0506_0708;
    pi.redeem_hashlock = [_]u8{7} ** 32;
    const e = pi.encode();
    try testing.expectEqual(@as(usize, 32 * 6 + 24 + 32), HtlcPublicInputs.ENCODED_LEN); // == Rust HTLC_PUBLIC_INPUTS_LEN
    try testing.expectEqual(HtlcPublicInputs.ENCODED_LEN, e.len);
    try testing.expect(!verifyHtlc("proof", pi)); // fail-closed without a backend
    const Rec = struct {
        var called: bool = false;
        fn vfn(_: [*]const u8, _: usize, _: [*]const u8, _: usize) callconv(.c) i32 {
            called = true;
            return 0;
        }
    };
    Rec.called = false;
    setHtlcBackend(&Rec.vfn);
    defer clearHtlcBackend();
    const oversize = try testing.allocator.alloc(u8, MAX_PROOF_LEN + 1);
    defer testing.allocator.free(oversize);
    try testing.expect(!verifyHtlc(oversize, pi)); // oversize ⇒ rejected, backend not called
    try testing.expect(!Rec.called);
    try testing.expect(verifyHtlc("x", pi)); // normal-size reaches the backend
    try testing.expect(Rec.called);
}

test "ffi: batch verify fail-closed + size-bound + backend plumbing" {
    const root = [_]u8{7} ** 32;
    try testing.expect(!verifyBatch("proof", root)); // fail-closed without a backend
    const Rec = struct {
        var called: bool = false;
        fn vfn(_: [*]const u8, _: usize, _: [*]const u8, _: usize) callconv(.c) i32 {
            called = true;
            return 0;
        }
    };
    Rec.called = false;
    setBatchBackend(&Rec.vfn);
    defer clearBatchBackend();
    const oversize = try testing.allocator.alloc(u8, MAX_PROOF_LEN + 1);
    defer testing.allocator.free(oversize);
    try testing.expect(!verifyBatch(oversize, root)); // oversize ⇒ rejected, backend not called
    try testing.expect(!Rec.called);
    try testing.expect(verifyBatch("x", root)); // normal-size reaches the backend
    try testing.expect(Rec.called);
}
