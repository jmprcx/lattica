//! The Goldilocks prime field `p = 2^64 - 2^32 + 1`, with roots of unity and a radix-2 NTT.
//!
//! Goldilocks is the canonical small STARK field: arithmetic fits in 64 bits (with 128-bit
//! intermediates), and `p - 1 = 2^32 · (2^32 - 1)` has 2-adicity 32, giving multiplicative
//! subgroups of every size up to `2^32` — far more than the FRI-STARK here needs.

const std = @import("std");

/// A field element, always held as its canonical representative in `[0, P)`.
pub const Felt = u64;

/// The Goldilocks prime, `2^64 - 2^32 + 1`.
pub const P: u64 = 0xFFFF_FFFF_0000_0001;

/// A multiplicative generator of `F_p^*` (order `p - 1`).
pub const GENERATOR: Felt = 7;

/// 2-adicity of `p - 1`: the largest `k` with `2^k | (p - 1)`.
pub const TWO_ADICITY: u6 = 32;

pub fn add(a: Felt, b: Felt) Felt {
    const s: u128 = @as(u128, a) + @as(u128, b);
    return @intCast(if (s >= P) s - P else s);
}

pub fn sub(a: Felt, b: Felt) Felt {
    return if (a >= b) a - b else @intCast(@as(u128, a) + P - b);
}

pub fn neg(a: Felt) Felt {
    return if (a == 0) 0 else P - a;
}

pub fn mul(a: Felt, b: Felt) Felt {
    return @intCast((@as(u128, a) * @as(u128, b)) % P);
}

/// Modular exponentiation by square-and-multiply.
pub fn pow(base: Felt, exp: u64) Felt {
    var result: Felt = 1;
    var b = base % P;
    var e = exp;
    while (e > 0) : (e >>= 1) {
        if (e & 1 == 1) result = mul(result, b);
        b = mul(b, b);
    }
    return result;
}

/// Multiplicative inverse via Fermat's little theorem (`a^(p-2)`). Undefined for `a == 0`.
pub fn inv(a: Felt) Felt {
    return pow(a, P - 2);
}

/// A primitive `n`-th root of unity, where `n` is a power of two dividing `2^32`.
pub fn rootOfUnity(n: u64) Felt {
    std.debug.assert(n != 0 and (n & (n - 1)) == 0); // power of two
    std.debug.assert((P - 1) % n == 0);
    return pow(GENERATOR, (P - 1) / n);
}

/// Reduce 16 bytes (little-endian) to a field element — used by the Fiat-Shamir transcript.
pub fn fromBytes(bytes: *const [16]u8) Felt {
    const x = std.mem.readInt(u128, bytes, .little);
    return @intCast(x % P);
}

pub fn toBytes(a: Felt) [8]u8 {
    var out: [8]u8 = undefined;
    std.mem.writeInt(u64, &out, a, .little);
    return out;
}

// ---------------------------------------------------------------------------------------
// Number-theoretic transform (iterative Cooley-Tukey, decimation-in-time)
// ---------------------------------------------------------------------------------------

fn bitReverse(a: []Felt) void {
    const n = a.len;
    var i: usize = 1;
    var j: usize = 0;
    while (i < n) : (i += 1) {
        var bit = n >> 1;
        while (j & bit != 0) : (bit >>= 1) j ^= bit;
        j ^= bit;
        if (i < j) std.mem.swap(Felt, &a[i], &a[j]);
    }
}

/// In-place forward NTT: interprets `a` as polynomial coefficients and overwrites it with the
/// evaluations at `root^0, root^1, …, root^(n-1)`, where `root` is a primitive `n`-th root of
/// unity (`n = a.len`, a power of two).
pub fn ntt(a: []Felt, root: Felt) void {
    const n = a.len;
    if (n <= 1) return;
    bitReverse(a);
    var len: usize = 2;
    while (len <= n) : (len <<= 1) {
        const w_len = pow(root, @intCast(n / len));
        var i: usize = 0;
        while (i < n) : (i += len) {
            var w: Felt = 1;
            var k: usize = 0;
            while (k < len / 2) : (k += 1) {
                const u = a[i + k];
                const v = mul(a[i + k + len / 2], w);
                a[i + k] = add(u, v);
                a[i + k + len / 2] = sub(u, v);
                w = mul(w, w_len);
            }
        }
    }
}

/// In-place inverse NTT: the exact inverse of `ntt` with the same `root`.
pub fn intt(a: []Felt, root: Felt) void {
    const n = a.len;
    if (n <= 1) return;
    ntt(a, inv(root));
    const n_inv = inv(@intCast(n));
    for (a) |*x| x.* = mul(x.*, n_inv);
}

// ---------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------

const testing = std.testing;

test "field axioms" {
    try testing.expectEqual(@as(Felt, 0), add(P - 1, 1));
    try testing.expectEqual(P - 1, sub(0, 1));
    try testing.expectEqual(@as(Felt, 1), mul(2, inv(2)));
    const a: Felt = 123456789;
    try testing.expectEqual(@as(Felt, 1), mul(a, inv(a)));
    try testing.expectEqual(@as(Felt, 0), add(a, neg(a)));
    // Fermat: a^(p-1) == 1.
    try testing.expectEqual(@as(Felt, 1), pow(a, P - 1));
}

test "roots of unity are primitive" {
    inline for (.{ 2, 4, 8, 1024, 8192 }) |n| {
        const w = rootOfUnity(n);
        try testing.expectEqual(@as(Felt, 1), pow(w, n)); // w^n == 1
        try testing.expect(pow(w, n / 2) != 1); // but no smaller power is 1
    }
}

test "ntt and intt round trip" {
    const n = 16;
    var coeffs: [n]Felt = undefined;
    for (&coeffs, 0..) |*c, i| c.* = @intCast(i * 7 + 3);
    const orig = coeffs;
    const w = rootOfUnity(n);
    ntt(&coeffs, w);
    intt(&coeffs, w);
    try testing.expectEqualSlices(Felt, &orig, &coeffs);
}

test "ntt matches naive evaluation" {
    const n = 8;
    const coeffs: [n]Felt = .{ 5, 0, 9, 2, 0, 7, 1, 4 };
    const w = rootOfUnity(n);
    var evals = coeffs;
    ntt(&evals, w);
    // Naive: evals[k] = sum_j coeffs[j] * w^(j*k).
    for (0..n) |k| {
        var acc: Felt = 0;
        var wjk: Felt = 1;
        const wk = pow(w, @intCast(k));
        for (0..n) |j| {
            acc = add(acc, mul(coeffs[j], wjk));
            wjk = mul(wjk, wk);
        }
        try testing.expectEqual(acc, evals[k]);
    }
}
