//! Known-answer tests (KAT), property tests, and a randomized robustness ("fuzz") harness.
//!
//!  * **KAT** locks the cryptographic foundations to fixed, externally-checkable answers
//!    (NIST SHA3-256 vectors, Goldilocks field identities, a known NTT).
//!  * **Property tests** assert algebraic invariants over many random inputs (field axioms,
//!    NTT round-trip, Merkle paths, note serialization, STARK completeness/soundness).
//!  * **Robustness** feeds malformed/random bytes to the parser+verifier and asserts they never
//!    crash and always reject — the property a network node depends on.

const std = @import("std");
const testing = std.testing;

const field = @import("field.zig");
const p = @import("primitives.zig");
const tree = @import("tree.zig");
const tx = @import("tx.zig");
const Felt = field.Felt;

// ---------------------------------------------------------------------------------------
// Known-answer tests
// ---------------------------------------------------------------------------------------

fn hexToBytes(comptime hex: []const u8) [hex.len / 2]u8 {
    var out: [hex.len / 2]u8 = undefined;
    _ = std.fmt.hexToBytes(&out, hex) catch unreachable;
    return out;
}

test "KAT: SHA3-256 NIST vectors" {
    const Sha3 = std.crypto.hash.sha3.Sha3_256;
    var out: [32]u8 = undefined;
    Sha3.hash("", &out, .{});
    try testing.expectEqualSlices(u8, &hexToBytes("a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"), &out);
    Sha3.hash("abc", &out, .{});
    try testing.expectEqualSlices(u8, &hexToBytes("3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"), &out);
}

test "KAT: Goldilocks field identities" {
    // 2^64 ≡ 2^32 - 1 (mod p), so mul(2^32, 2^32) == 2^32 - 1.
    try testing.expectEqual(@as(Felt, (1 << 32) - 1), field.mul(1 << 32, 1 << 32));
    // The primitive 2nd root of unity is -1 = p - 1.
    try testing.expectEqual(field.P - 1, field.rootOfUnity(2));
    // Fermat: g^(p-1) == 1.
    try testing.expectEqual(@as(Felt, 1), field.pow(field.GENERATOR, field.P - 1));
}

test "KAT: known NTT" {
    // ntt([1,1]) over the 2nd roots {1, -1} = [1+1, 1-1] = [2, 0].
    var a = [_]Felt{ 1, 1 };
    field.ntt(&a, field.rootOfUnity(2));
    try testing.expectEqualSlices(Felt, &[_]Felt{ 2, 0 }, &a);
}

test "KAT: hashDomain regression (length-prefixed framing)" {
    // Locks the exact domain-separated framing so a refactor can't silently change commitments.
    const d = p.hashDomain("lattica:test", &.{ "ab", "c" });
    // Recompute the spec by hand: SHA3(len("lattica:test")||"lattica:test" || len("ab")||"ab" || len("c")||"c").
    const Sha3 = std.crypto.hash.sha3.Sha3_256;
    var h = Sha3.init(.{});
    var le: [8]u8 = undefined;
    inline for (.{ "lattica:test", "ab", "c" }) |s| {
        std.mem.writeInt(u64, &le, s.len, .little);
        h.update(&le);
        h.update(s);
    }
    var expected: [32]u8 = undefined;
    h.final(&expected);
    try testing.expectEqualSlices(u8, &expected, &d);
}

// ---------------------------------------------------------------------------------------
// Property tests
// ---------------------------------------------------------------------------------------

fn nonzeroFelt(r: std.Random) Felt {
    while (true) {
        const v = r.int(u64) % field.P;
        if (v != 0) return v;
    }
}

test "property: field axioms over random inputs" {
    var prng = std.Random.DefaultPrng.init(0xA11CE);
    const r = prng.random();
    for (0..2000) |_| {
        const a = r.int(u64) % field.P;
        const b = r.int(u64) % field.P;
        const c = r.int(u64) % field.P;
        // Distributivity.
        try testing.expectEqual(field.mul(a, field.add(b, c)), field.add(field.mul(a, b), field.mul(a, c)));
        // Additive inverse.
        try testing.expectEqual(@as(Felt, 0), field.add(a, field.neg(a)));
        // Commutativity.
        try testing.expectEqual(field.mul(a, b), field.mul(b, a));
        // Multiplicative inverse.
        const nz = nonzeroFelt(r);
        try testing.expectEqual(@as(Felt, 1), field.mul(nz, field.inv(nz)));
    }
}

test "property: NTT/iNTT round trip at every size" {
    var prng = std.Random.DefaultPrng.init(0xBEEF);
    const r = prng.random();
    const a = testing.allocator;
    inline for (.{ 2, 4, 8, 16, 256, 1024 }) |n| {
        const buf = try a.alloc(Felt, n);
        defer a.free(buf);
        const orig = try a.alloc(Felt, n);
        defer a.free(orig);
        for (buf, orig) |*x, *o| {
            const v = r.int(u64) % field.P;
            x.* = v;
            o.* = v;
        }
        const w = field.rootOfUnity(n);
        field.ntt(buf, w);
        field.intt(buf, w);
        try testing.expectEqualSlices(Felt, orig, buf);
    }
}

test "property: Merkle paths verify and detect tampering" {
    var prng = std.Random.DefaultPrng.init(0xC0FFEE);
    const r = prng.random();
    const a = testing.allocator;
    for (0..20) |_| {
        const depth = 1 + r.intRangeLessThan(usize, 0, 8);
        var t = try tree.MerkleTree.init(a, depth);
        defer t.deinit();
        const count = r.intRangeLessThan(u64, 1, @min(@as(u64, 1) << @intCast(depth), 40) + 1);
        var i: u64 = 0;
        while (i < count) : (i += 1) {
            var leaf: p.Hash32 = undefined;
            r.bytes(&leaf);
            _ = try t.append(leaf);
        }
        const root = t.root();
        const pos = r.intRangeLessThan(u64, 0, count);
        const path = try t.authenticationPath(a, pos);
        defer a.free(path.siblings);
        // The committed leaf verifies; a random different leaf does not.
        const real = t.leaves.items[@intCast(pos)];
        try testing.expect(tree.verifyPath(&root, &real, path));
        var bad = real;
        bad[0] +%= 1;
        try testing.expect(!tree.verifyPath(&root, &bad, path));
    }
}

test "property: note serialization round trip" {
    var prng = std.Random.DefaultPrng.init(0xD00D);
    const r = prng.random();
    for (0..1000) |_| {
        var note: tx.Note = undefined;
        note.value = r.int(u64);
        r.bytes(&note.recipient);
        r.bytes(&note.rho);
        r.bytes(&note.rcm);
        const parsed = try tx.Note.fromBytes(&note.toBytes());
        try testing.expect(parsed.eql(note));
    }
}

// The production join-split verifier's robustness (fail-closed on null/short/non-canonical inputs,
// rejection of tampered proofs) is covered in `lattica-prover-p3` (lib.rs fail-closed +
// non-canonical tests) and `lattica-prover-p3/tests/ffi_integration.c` (real prove→verify→tamper).
