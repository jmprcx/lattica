//! A **grand-product permutation argument** — the gating primitive for completing R3.
//!
//! It proves, with a FRI-STARK, that one committed column `B` is a permutation of another `A`
//! (i.e. they hold the same multiset of field elements). This is the exact mechanism a
//! copy-constraint / wiring argument is built on: a committed running-product column `Z` with
//!
//!     Z[0] = 1,    Z[r+1] = Z[r] · (A[r] + γ) / (B[r] + γ),
//!
//! whose cyclic transition telescopes to `∏(A[r]+γ) = ∏(B[r]+γ)` — which, over a random
//! Fiat-Shamir `γ` drawn *after* `A,B` are committed, holds iff the multisets are equal
//! (Schwartz–Zippel). The novel, soundness-critical ingredients validated here are:
//!   * the running-product column and its transition/boundary constraints (the "wrap" at the
//!     last row is what forces the total product to 1);
//!   * the **two-round** Fiat-Shamir flow: commit `A,B` → draw `γ` → commit `Z` → draw the
//!     constraint-combination challenges → FRI.
//!
//! ## Scope
//! This is a standalone, non-zero-knowledge primitive focused on the grand-product mechanism.
//! ZK blinding + masked FRI are additive (see `stark.zig`/`membership.zig`) and omitted here for
//! clarity. **Copy constraints** (wiring specific cells equal, as a full spend proof needs) are
//! the *same* `Z` mechanism with an id/σ encoding in the numerator/denominator
//! (`num = ∏(v + β·id + γ)`, `den = ∏(v + β·σ(id) + γ)`); that extension and how the spend
//! circuit uses it are described in `docs/soundness.md §6`. The engine is duplicated from the
//! other modules pending a generic-engine refactor.

const std = @import("std");
const Allocator = std.mem.Allocator;
const p = @import("primitives.zig");
const field = @import("field.zig");
const Felt = field.Felt;

const Hash = [32]u8;

// ---------------------------------------------------------------------------------------
// Parameters
// ---------------------------------------------------------------------------------------

const N: usize = 64; // number of elements compared
const BLOWUP: usize = 8;
const LDE_SIZE: usize = N * BLOWUP; // 512
const NUM_FOLDS: usize = 5;
const FINAL_SIZE: usize = LDE_SIZE >> NUM_FOLDS; // 16
const COMP_DEGREE_BOUND: usize = 128;
const FINAL_DEGREE_BOUND: usize = COMP_DEGREE_BOUND >> NUM_FOLDS; // 4
const NUM_QUERIES: usize = 40;
const TRACE_WIDTH: usize = 2; // A, B

fn ldeOffset() Felt {
    return field.GENERATOR;
}
fn ldeGen() Felt {
    return field.rootOfUnity(LDE_SIZE);
}

// ---------------------------------------------------------------------------------------
// Merkle, transcript, FRI — engine adapted from the other modules
// ---------------------------------------------------------------------------------------

fn hashLeaf(v: Felt) Hash {
    return p.hashDomain("lattica:perm:leaf", &.{&field.toBytes(v)});
}
fn hashPair(a: Felt, b: Felt) Hash {
    return p.hashDomain("lattica:perm:row", &.{ &field.toBytes(a), &field.toBytes(b) });
}
fn hashNode(l: Hash, r: Hash) Hash {
    return p.hashDomain("lattica:perm:node", &.{ &l, &r });
}

const MerkleTree = struct {
    allocator: Allocator,
    n: usize,
    nodes: []Hash,

    fn fromLeafHashes(allocator: Allocator, leaf_hashes: []const Hash) !MerkleTree {
        const n = leaf_hashes.len;
        const nodes = try allocator.alloc(Hash, 2 * n);
        for (leaf_hashes, 0..) |h, i| nodes[n + i] = h;
        var i: usize = n - 1;
        while (i >= 1) : (i -= 1) {
            nodes[i] = hashNode(nodes[2 * i], nodes[2 * i + 1]);
            if (i == 1) break;
        }
        return .{ .allocator = allocator, .n = n, .nodes = nodes };
    }
    fn build(allocator: Allocator, leaves: []const Felt) !MerkleTree {
        const hs = try allocator.alloc(Hash, leaves.len);
        defer allocator.free(hs);
        for (leaves, hs) |v, *h| h.* = hashLeaf(v);
        return fromLeafHashes(allocator, hs);
    }
    fn buildPairs(allocator: Allocator, col0: []const Felt, col1: []const Felt) !MerkleTree {
        const hs = try allocator.alloc(Hash, col0.len);
        defer allocator.free(hs);
        for (0..col0.len) |r| hs[r] = hashPair(col0[r], col1[r]);
        return fromLeafHashes(allocator, hs);
    }
    fn deinit(self: *MerkleTree) void {
        self.allocator.free(self.nodes);
    }
    fn root(self: MerkleTree) Hash {
        return self.nodes[1];
    }
    fn open(self: MerkleTree, allocator: Allocator, index: usize) ![]Hash {
        const depth = std.math.log2_int(usize, self.n);
        const path = try allocator.alloc(Hash, depth);
        var pos = self.n + index;
        var d: usize = 0;
        while (pos > 1) : (pos >>= 1) {
            path[d] = self.nodes[pos ^ 1];
            d += 1;
        }
        return path;
    }
};

fn verifyHash(root: Hash, n: usize, index: usize, leaf_hash: Hash, path: []const Hash) bool {
    if (path.len != std.math.log2_int(usize, n)) return false;
    var h = leaf_hash;
    var idx = index;
    for (path) |sib| {
        h = if (idx & 1 == 0) hashNode(h, sib) else hashNode(sib, h);
        idx >>= 1;
    }
    return std.mem.eql(u8, &h, &root);
}
fn verifyLeaf(root: Hash, n: usize, index: usize, val: Felt, path: []const Hash) bool {
    return verifyHash(root, n, index, hashLeaf(val), path);
}
fn verifyPair(root: Hash, n: usize, index: usize, a: Felt, b: Felt, path: []const Hash) bool {
    return verifyHash(root, n, index, hashPair(a, b), path);
}

const Transcript = struct {
    state: Hash,
    counter: u64,
    fn init(label: []const u8) Transcript {
        return .{ .state = p.hashDomain("lattica:perm:transcript", &.{label}), .counter = 0 };
    }
    fn absorb(self: *Transcript, bytes: []const u8) void {
        self.state = p.hashDomain("lattica:perm:absorb", &.{ &self.state, bytes });
        self.counter = 0;
    }
    fn absorbHash(self: *Transcript, h: Hash) void {
        self.absorb(&h);
    }
    fn absorbFelt(self: *Transcript, v: Felt) void {
        self.absorb(&field.toBytes(v));
    }
    fn squeeze(self: *Transcript) Hash {
        var ctr: [8]u8 = undefined;
        std.mem.writeInt(u64, &ctr, self.counter, .little);
        self.counter += 1;
        return p.hashDomain("lattica:perm:squeeze", &.{ &self.state, &ctr });
    }
    fn challengeFelt(self: *Transcript) Felt {
        return field.fromBytes(self.squeeze()[0..16]);
    }
    fn challengeIndex(self: *Transcript, bound: usize) usize {
        return @intCast(std.mem.readInt(u64, self.squeeze()[0..8], .little) % bound);
    }
};

fn coeffsToLde(allocator: Allocator, coeffs: []const Felt) ![]Felt {
    const lde = try allocator.alloc(Felt, LDE_SIZE);
    @memset(lde, 0);
    @memcpy(lde[0..coeffs.len], coeffs);
    var off_pow: Felt = 1;
    for (0..LDE_SIZE) |i| {
        lde[i] = field.mul(lde[i], off_pow);
        off_pow = field.mul(off_pow, ldeOffset());
    }
    field.ntt(lde, ldeGen());
    return lde;
}

/// Interpolate `N` values over H and evaluate over the LDE coset.
fn valuesToLde(allocator: Allocator, values: [N]Felt) ![]Felt {
    var coeffs = values;
    field.intt(&coeffs, field.rootOfUnity(N));
    return coeffsToLde(allocator, &coeffs);
}

const FriQueryLayer = struct { a: Felt, b: Felt, path_a: []Hash, path_b: []Hash };
const FriQuery = struct { layers: [NUM_FOLDS]FriQueryLayer };

fn friFold(allocator: Allocator, cur: []const Felt, beta: Felt, offset: Felt, gen: Felt) ![]Felt {
    const half = cur.len / 2;
    const next = try allocator.alloc(Felt, half);
    const inv2 = field.inv(2);
    var x = offset;
    for (0..half) |i| {
        const even = field.mul(field.add(cur[i], cur[i + half]), inv2);
        const odd = field.mul(field.mul(field.sub(cur[i], cur[i + half]), inv2), field.inv(x));
        next[i] = field.add(even, field.mul(beta, odd));
        x = field.mul(x, gen);
    }
    return next;
}

const FriProver = struct {
    allocator: Allocator,
    layer_evals: [NUM_FOLDS][]Felt,
    trees: [NUM_FOLDS]MerkleTree,
    roots: [NUM_FOLDS]Hash,
    betas: [NUM_FOLDS]Felt,
    final_layer: []Felt,

    fn commit(allocator: Allocator, transcript: *Transcript, evals: []const Felt) !FriProver {
        var self: FriProver = undefined;
        self.allocator = allocator;
        var cur = try allocator.dupe(Felt, evals);
        for (0..NUM_FOLDS) |k| {
            self.layer_evals[k] = cur;
            self.trees[k] = try MerkleTree.build(allocator, cur);
            self.roots[k] = self.trees[k].root();
            transcript.absorbHash(self.roots[k]);
            self.betas[k] = transcript.challengeFelt();
            const offset_k = field.pow(ldeOffset(), @as(u64, 1) << @intCast(k));
            const gen_k = field.pow(ldeGen(), @as(u64, 1) << @intCast(k));
            cur = try friFold(allocator, cur, self.betas[k], offset_k, gen_k);
        }
        self.final_layer = cur;
        for (self.final_layer) |v| transcript.absorbFelt(v);
        return self;
    }
    fn open(self: FriProver, allocator: Allocator, q0: usize) !FriQuery {
        var q: FriQuery = undefined;
        for (0..NUM_FOLDS) |k| {
            const half_k = (LDE_SIZE >> @intCast(k)) / 2;
            const a_idx = q0 % half_k;
            q.layers[k] = .{
                .a = self.layer_evals[k][a_idx],
                .b = self.layer_evals[k][a_idx + half_k],
                .path_a = try self.trees[k].open(allocator, a_idx),
                .path_b = try self.trees[k].open(allocator, a_idx + half_k),
            };
        }
        return q;
    }
    fn deinit(self: *FriProver) void {
        for (0..NUM_FOLDS) |k| {
            self.trees[k].deinit();
            self.allocator.free(self.layer_evals[k]);
        }
    }
};

fn friCheckFinalLowDegree(allocator: Allocator, final_layer: []const Felt) !bool {
    const gen_f = field.pow(ldeGen(), @as(u64, 1) << @intCast(NUM_FOLDS));
    const coeffs = try allocator.dupe(Felt, final_layer);
    defer allocator.free(coeffs);
    field.intt(coeffs, gen_f);
    for (coeffs[FINAL_DEGREE_BOUND..]) |c| if (c != 0) return false;
    return true;
}

// ---------------------------------------------------------------------------------------
// The permutation AIR
// ---------------------------------------------------------------------------------------

/// Composition at one point. `a,b,z` are the values of columns A,B,Z at `x`; `z_next = Z(ωx)`.
/// Constraint 0 (all rows): `Z(ωx)·(B+γ) − Z(x)·(A+γ) = 0`. Constraint 1 (row 0): `Z − 1 = 0`.
fn compositionAt(a: Felt, b: Felt, z: Felt, z_next: Felt, x: Felt, gamma: Felt, comb: [2]Felt) Felt {
    const z_trans = field.sub(field.mul(z_next, field.add(b, gamma)), field.mul(z, field.add(a, gamma)));
    const q_trans = field.mul(z_trans, field.inv(field.sub(field.pow(x, N), 1)));
    const q_bound = field.mul(field.sub(z, 1), field.inv(field.sub(x, 1)));
    return field.add(field.mul(comb[0], q_trans), field.mul(comb[1], q_bound));
}

/// The running-product column on H: `Z[0]=1`, `Z[r+1]=Z[r]·(A[r]+γ)/(B[r]+γ)`.
fn grandProduct(a: [N]Felt, b: [N]Felt, gamma: Felt) [N]Felt {
    var z: [N]Felt = undefined;
    z[0] = 1;
    for (0..N - 1) |r| {
        const num = field.add(a[r], gamma);
        const den = field.add(b[r], gamma);
        z[r + 1] = field.mul(z[r], field.mul(num, field.inv(den)));
    }
    return z;
}

pub const Proof = struct {
    trace_root: Hash,
    z_root: Hash,
    fri_roots: [NUM_FOLDS]Hash,
    fri_final: []Felt,
    queries: []Query,
};

const PairOpen = struct { a: Felt, b: Felt, path: []Hash };
const ValOpen = struct { val: Felt, path: []Hash };
const Query = struct {
    fri: FriQuery,
    ab_a: PairOpen, // (A,B) at q
    ab_b: PairOpen, // (A,B) at q + half0
    z_a: ValOpen, // Z at q
    z_an: ValOpen, // Z at (q + BLOWUP)
    z_b: ValOpen, // Z at q + half0
    z_bn: ValOpen, // Z at (q + half0 + BLOWUP)
};

const LABEL = "lattica:permutation:v1";

/// Prove that `b` is a permutation of `a` (equal multisets).
pub fn prove(allocator: Allocator, a: [N]Felt, b: [N]Felt) !Proof {
    const a_lde = try valuesToLde(allocator, a);
    defer allocator.free(a_lde);
    const b_lde = try valuesToLde(allocator, b);
    defer allocator.free(b_lde);

    var trace_tree = try MerkleTree.buildPairs(allocator, a_lde, b_lde);
    defer trace_tree.deinit();
    const trace_root = trace_tree.root();

    var tr = Transcript.init(LABEL);
    tr.absorbHash(trace_root);
    const gamma = tr.challengeFelt(); // round-1 challenge: must follow the A,B commitment

    const z = grandProduct(a, b, gamma);
    const z_lde = try valuesToLde(allocator, z);
    defer allocator.free(z_lde);
    var z_tree = try MerkleTree.build(allocator, z_lde);
    defer z_tree.deinit();
    const z_root = z_tree.root();

    tr.absorbHash(z_root);
    const comb = [2]Felt{ tr.challengeFelt(), tr.challengeFelt() };

    // Composition over the LDE.
    const cp = try allocator.alloc(Felt, LDE_SIZE);
    defer allocator.free(cp);
    var x = ldeOffset();
    for (0..LDE_SIZE) |j| {
        const z_next = z_lde[(j + BLOWUP) % LDE_SIZE];
        cp[j] = compositionAt(a_lde[j], b_lde[j], z_lde[j], z_next, x, gamma, comb);
        x = field.mul(x, ldeGen());
    }

    var fri = try FriProver.commit(allocator, &tr, cp);
    const fri_roots = fri.roots;
    const fri_final = try allocator.dupe(Felt, fri.final_layer);

    const half0 = LDE_SIZE / 2;
    const queries = try allocator.alloc(Query, NUM_QUERIES);
    for (queries) |*q| {
        const q0 = tr.challengeIndex(half0);
        const qa = q0;
        const qb = q0 + half0;
        q.fri = try fri.open(allocator, q0);
        q.ab_a = .{ .a = a_lde[qa], .b = b_lde[qa], .path = try trace_tree.open(allocator, qa) };
        q.ab_b = .{ .a = a_lde[qb], .b = b_lde[qb], .path = try trace_tree.open(allocator, qb) };
        q.z_a = .{ .val = z_lde[qa], .path = try z_tree.open(allocator, qa) };
        q.z_an = .{ .val = z_lde[(qa + BLOWUP) % LDE_SIZE], .path = try z_tree.open(allocator, (qa + BLOWUP) % LDE_SIZE) };
        q.z_b = .{ .val = z_lde[qb], .path = try z_tree.open(allocator, qb) };
        q.z_bn = .{ .val = z_lde[(qb + BLOWUP) % LDE_SIZE], .path = try z_tree.open(allocator, (qb + BLOWUP) % LDE_SIZE) };
    }
    allocator.free(fri.final_layer);
    fri.deinit();
    return .{ .trace_root = trace_root, .z_root = z_root, .fri_roots = fri_roots, .fri_final = fri_final, .queries = queries };
}

pub fn verify(allocator: Allocator, proof: Proof) !bool {
    if (proof.fri_final.len != FINAL_SIZE or proof.queries.len != NUM_QUERIES) return false;

    var tr = Transcript.init(LABEL);
    tr.absorbHash(proof.trace_root);
    const gamma = tr.challengeFelt();
    tr.absorbHash(proof.z_root);
    const comb = [2]Felt{ tr.challengeFelt(), tr.challengeFelt() };

    var betas: [NUM_FOLDS]Felt = undefined;
    for (0..NUM_FOLDS) |k| {
        tr.absorbHash(proof.fri_roots[k]);
        betas[k] = tr.challengeFelt();
    }
    for (proof.fri_final) |v| tr.absorbFelt(v);
    if (!try friCheckFinalLowDegree(allocator, proof.fri_final)) return false;

    const inv2 = field.inv(2);
    const half0 = LDE_SIZE / 2;
    var ok = true;

    for (proof.queries) |q| {
        const q0 = tr.challengeIndex(half0);
        const qa = q0;
        const qb = q0 + half0;

        if (!verifyPair(proof.trace_root, LDE_SIZE, qa, q.ab_a.a, q.ab_a.b, q.ab_a.path)) ok = false;
        if (!verifyPair(proof.trace_root, LDE_SIZE, qb, q.ab_b.a, q.ab_b.b, q.ab_b.path)) ok = false;
        if (!verifyLeaf(proof.z_root, LDE_SIZE, qa, q.z_a.val, q.z_a.path)) ok = false;
        if (!verifyLeaf(proof.z_root, LDE_SIZE, (qa + BLOWUP) % LDE_SIZE, q.z_an.val, q.z_an.path)) ok = false;
        if (!verifyLeaf(proof.z_root, LDE_SIZE, qb, q.z_b.val, q.z_b.path)) ok = false;
        if (!verifyLeaf(proof.z_root, LDE_SIZE, (qb + BLOWUP) % LDE_SIZE, q.z_bn.val, q.z_bn.path)) ok = false;

        const x_a = field.mul(ldeOffset(), field.pow(ldeGen(), @intCast(qa)));
        const x_b = field.mul(ldeOffset(), field.pow(ldeGen(), @intCast(qb)));
        const h_a = compositionAt(q.ab_a.a, q.ab_a.b, q.z_a.val, q.z_an.val, x_a, gamma, comb);
        const h_b = compositionAt(q.ab_b.a, q.ab_b.b, q.z_b.val, q.z_bn.val, x_b, gamma, comb);
        if (h_a != q.fri.layers[0].a) ok = false;
        if (h_b != q.fri.layers[0].b) ok = false;

        for (0..NUM_FOLDS) |k| {
            const size_k = LDE_SIZE >> @intCast(k);
            const half_k = size_k / 2;
            const ai = q0 % half_k;
            const off_k = field.pow(ldeOffset(), @as(u64, 1) << @intCast(k));
            const gen_k = field.pow(ldeGen(), @as(u64, 1) << @intCast(k));
            const layer = q.fri.layers[k];
            if (!verifyLeaf(proof.fri_roots[k], size_k, ai, layer.a, layer.path_a)) ok = false;
            if (!verifyLeaf(proof.fri_roots[k], size_k, ai + half_k, layer.b, layer.path_b)) ok = false;
            const x = field.mul(off_k, field.pow(gen_k, @intCast(ai)));
            const even = field.mul(field.add(layer.a, layer.b), inv2);
            const odd = field.mul(field.mul(field.sub(layer.a, layer.b), inv2), field.inv(x));
            const folded = field.add(even, field.mul(betas[k], odd));
            if (k + 1 < NUM_FOLDS) {
                const half_next = half_k / 2;
                const expected = if (ai < half_next) q.fri.layers[k + 1].a else q.fri.layers[k + 1].b;
                if (folded != expected) ok = false;
            } else {
                if (folded != proof.fri_final[ai % FINAL_SIZE]) ok = false;
            }
        }
    }
    return ok;
}

// ---------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------

const testing = std.testing;

fn sampleA(seed: u64) [N]Felt {
    var a: [N]Felt = undefined;
    for (0..N) |i| a[i] = (@as(Felt, @intCast(i)) *% 2654435761 +% seed) % field.P;
    return a;
}

test "permutation: a reversal of A verifies as a permutation" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const a = sampleA(12345);
    var b: [N]Felt = undefined;
    for (0..N) |i| b[i] = a[N - 1 - i]; // a permutation of a
    const proof = try prove(al, a, b);
    try testing.expect(try verify(al, proof));
}

test "permutation: a cyclic shift verifies" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const a = sampleA(777);
    var b: [N]Felt = undefined;
    for (0..N) |i| b[i] = a[(i + 7) % N];
    const proof = try prove(al, a, b);
    try testing.expect(try verify(al, proof));
}

test "permutation: a non-permutation is rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const a = sampleA(42);
    var b: [N]Felt = undefined;
    for (0..N) |i| b[i] = a[i];
    b[3] = field.add(b[3], 1); // change one element: no longer the same multiset
    const proof = try prove(al, a, b);
    try testing.expect(!try verify(al, proof));
}

test "permutation: identity (A == B) verifies" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const a = sampleA(99);
    const proof = try prove(al, a, a);
    try testing.expect(try verify(al, proof));
}

test "permutation: a duplicate-swap (same values, different positions) verifies" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    var a = sampleA(5);
    a[10] = a[20]; // introduce a duplicate value
    var b: [N]Felt = undefined;
    for (0..N) |i| b[i] = a[i];
    std.mem.swap(Felt, &b[10], &b[40]); // permute; multiset unchanged
    const proof = try prove(al, a, b);
    try testing.expect(try verify(al, proof));
}
