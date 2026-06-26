//! # circuit — spend-authorization proof
//!
//! The zero-knowledge proving system for Lattica spends, built on a **transparent, hash-based
//! FRI-STARK** (implemented from scratch in `stark.zig`). This is the single most important
//! component for quantum safety: it replaces Zcash's Halo 2 (whose soundness rests on
//! elliptic-curve discrete log, broken by Shor) with a proof whose soundness rests only on the
//! collision resistance of SHA3. There is **no trusted setup and no elliptic curve** anywhere.
//!
//! The statement proved, in zero knowledge, is knowledge of a secret `s` with
//! `rescue.hash(s) = image` — a preimage of the arithmetization-friendly hash in `rescue.zig`
//! (a Poseidon-style SPN), proven in-circuit as a multi-column AIR — *without revealing `s`*.
//! This closes gap R1 (the relation is now a genuine one-way hash, not the old algebraic
//! `x³ + C`). The remaining production work is R3: folding membership/nullifier/balance into the
//! same AIR (they are still enforced natively by the node) — see `SPEC.md §8`.
//!
//! This module is a thin façade over `stark.zig`, keeping the proof as opaque bytes so the rest
//! of the protocol (transaction digest, node validation) is unaffected.

const std = @import("std");
const Allocator = std.mem.Allocator;
const stark = @import("stark.zig");
const field = @import("field.zig");

/// A spend-authorization proof: the public image plus the serialized FRI-STARK proof.
/// `proof` is allocator-owned.
pub const AuthProof = struct {
    image: [16]u8,
    proof: []u8,
};

/// The public authorization image for a secret (16 bytes: the field element in the low 8).
pub fn authorizationImage(secret: *const [32]u8) [16]u8 {
    const img = stark.imageFelt(secret);
    var out = [_]u8{0} ** 16;
    const img_bytes = field.toBytes(img);
    @memcpy(out[0..8], &img_bytes);
    return out;
}

/// Prove knowledge of the spend secret. Returns the public image and a serialized FRI-STARK
/// proof owned by `allocator`.
pub fn proveAuthorization(allocator: Allocator, secret: *const [32]u8) !AuthProof {
    // The proof's internal objects (trace, layers, Merkle paths) are scratch; only the
    // serialized bytes escape into the caller's allocator.
    var scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer scratch.deinit();
    const sp = try stark.prove(scratch.allocator(), secret);
    const bytes = try stark.serialize(allocator, sp);
    return .{ .image = authorizationImage(secret), .proof = bytes };
}

/// Verify a spend-authorization proof.
pub fn verifyAuthorization(auth: AuthProof) bool {
    // Canonical image: a Goldilocks element fits in 8 bytes (< p), and the upper 8 bytes of the
    // 16-byte field must be zero. Rejecting non-canonical encodings removes image malleability.
    if (!std.mem.eql(u8, auth.image[8..16], &[_]u8{0} ** 8)) return false;
    const image = std.mem.readInt(u64, auth.image[0..8], .little);
    if (image >= field.P) return false;

    var scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer scratch.deinit();
    const a = scratch.allocator();
    const sp = stark.deserialize(a, auth.proof) catch return false;
    return stark.verify(a, image, sp) catch return false;
}

// ---------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------

const testing = std.testing;

test "valid proof verifies" {
    const a = testing.allocator;
    const secret = [_]u8{7} ** 32;
    const auth = try proveAuthorization(a, &secret);
    defer a.free(auth.proof);
    try testing.expect(verifyAuthorization(auth));
}

test "image matches independent recomputation" {
    const a = testing.allocator;
    const secret = [_]u8{9} ** 32;
    const auth = try proveAuthorization(a, &secret);
    defer a.free(auth.proof);
    try testing.expectEqualSlices(u8, &auth.image, &authorizationImage(&secret));
}

test "tampered image rejected" {
    const a = testing.allocator;
    const secret = [_]u8{7} ** 32;
    var auth = try proveAuthorization(a, &secret);
    defer a.free(auth.proof);
    auth.image[0] ^= 0xff;
    try testing.expect(!verifyAuthorization(auth));
}

test "corrupted proof rejected" {
    const a = testing.allocator;
    const secret = [_]u8{7} ** 32;
    var auth = try proveAuthorization(a, &secret);
    defer a.free(auth.proof);
    auth.proof[auth.proof.len / 2] ^= 0xff;
    try testing.expect(!verifyAuthorization(auth));
}
