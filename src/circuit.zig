//! # circuit — spend-authorization proof (STUB)
//!
//! In the full protocol this is the zero-knowledge proving system for Lattica spends, built
//! on a **transparent, hash-based FRI-STARK** — the single most important component for
//! quantum safety, replacing Zcash's Halo 2 (whose soundness rests on elliptic-curve discrete
//! log) with a proof whose soundness rests only on the collision resistance of a hash. There
//! is no trusted setup and no elliptic curve anywhere.
//!
//! ## Status in this Zig port: STUB
//!
//! A real FRI-STARK prover/verifier has **no Zig (or readily vendorable C/C++) equivalent**,
//! so it is the one component deferred to a follow-up phase. This module:
//!
//!  * Keeps the **relation shape** intact — the authorization "image" is the result of the
//!    1024-step chain `x -> x^3 + C` over a prime field, exactly as the reference AIR computes
//!    it — so a real FRI-STARK can be dropped in later over the same statement.
//!  * Ships a **placeholder proof**: `proof = H("auth-stub", image)`. Verification recomputes
//!    that and compares, which makes tampering with either the image or the proof detectable
//!    (so the surrounding transaction logic and its tests behave correctly).
//!
//! It is **honestly not zero-knowledge and proves nothing about knowledge of the secret** —
//! anyone holding the public image can produce the placeholder. The PoC's real validation
//! (membership, nullifier, balance, binding signature) is enforced natively by `node`, exactly
//! as in the reference. Replacing this stub with a genuine FRI-STARK is tracked as future work.

const std = @import("std");
const Allocator = std.mem.Allocator;
const p = @import("primitives.zig");
const Hash32 = p.Hash32;

/// Number of steps in the authorization chain (must be a power of two).
const NUM_STEPS: usize = 1024;
/// Round constant in the chain transition `x -> x^3 + C`.
const C: u128 = 42;
/// Prime modulus of the reference STARK field (Winterfell f128: 2^128 - 45*2^40 + 1).
const MOD: u128 = 340282366920938463463374557953744961537;

const STUB_DOMAIN: []const u8 = "lattica:v1:auth-stub-proof";

fn mulmod(a: u128, b: u128) u128 {
    return @intCast((@as(u256, a) * @as(u256, b)) % MOD);
}

/// One transition of the authorization chain: `x -> x^3 + C (mod MOD)`.
fn step(x: u128) u128 {
    const x3 = mulmod(mulmod(x, x), x);
    return @intCast((@as(u256, x3) + C) % MOD);
}

fn secretToField(secret: *const Hash32) u128 {
    var b: [16]u8 = undefined;
    @memcpy(&b, secret[0..16]);
    return std.mem.readInt(u128, &b, .little) % MOD;
}

/// A spend-authorization proof: the public image plus the serialized proof (stub: a 32-byte
/// hash binding it to the image). `proof` is allocator-owned.
pub const AuthProof = struct {
    image: [16]u8,
    proof: []u8,
};

/// Recompute the public authorization image for a secret (what an address would commit to):
/// the final state of the 1024-step chain.
pub fn authorizationImage(secret: *const Hash32) [16]u8 {
    var s = secretToField(secret);
    var i: usize = 0;
    while (i < NUM_STEPS - 1) : (i += 1) s = step(s);
    var out: [16]u8 = undefined;
    std.mem.writeInt(u128, &out, s, .little);
    return out;
}

/// Prove knowledge of the spend secret. STUB: returns the image and a placeholder proof bound
/// to it. See the module docs — this proves nothing in zero knowledge.
pub fn proveAuthorization(allocator: Allocator, secret: *const Hash32) !AuthProof {
    const image = authorizationImage(secret);
    const tag = p.hashDomain(STUB_DOMAIN, &.{&image});
    const proof = try allocator.dupe(u8, &tag);
    return .{ .image = image, .proof = proof };
}

/// Verify a spend-authorization proof. STUB: checks the placeholder binds to the image.
pub fn verifyAuthorization(auth: AuthProof) bool {
    const expected = p.hashDomain(STUB_DOMAIN, &.{&auth.image});
    if (auth.proof.len != expected.len) return false;
    return std.mem.eql(u8, auth.proof, &expected);
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
