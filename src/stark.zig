//! A self-contained, transparent, **zero-knowledge** FRI-STARK proving knowledge of a preimage
//! of the arithmetization-friendly hash in `rescue.zig` — no elliptic curves, no trusted setup,
//! soundness resting on SHA3 collision resistance.
//!
//! ## Statement
//!
//! `verify(image, π)` accepts iff the prover knew `s` with `rescue.hash(s) = image`, i.e. a full
//! execution trace of the SPN permutation `[s,0,0] → … → out` with `out[0] = image`, **without
//! revealing `s`** (the input rate cell is never asserted/opened in the clear).
//!
//! ## AIR (multi-column)
//!
//! The trace is `WIDTH` columns × `N` rows (`N = ROUNDS+1`); row `r` is the permutation state
//! after `r` rounds. Constraints:
//!   * **Transition** (rows 0..N-2), one per state element `i`:
//!         `T_i(ωx) − ( Σ_j M[i][j]·T_j(x)^7 + RC[r][i] ) = 0`
//!     where `M` is the MDS matrix and `RC` are the (periodic) round constants, supplied to the
//!     verifier as low-degree polynomials evaluated at the query points.
//!   * **Boundary**: `T_1(1)=0`, `T_2(1)=0` (capacity initialised to 0) and `T_0(ω^{N-1})=image`.
//!
//! ## Construction (classic FRI-STARK + ZK)
//!   1. Interpolate each trace column and **blind** it: `T'_i = T_i + Z_H·b_i` (random `b_i`).
//!   2. Evaluate over an LDE coset (blowup), Merkle-commit the rows.
//!   3. Compose the constraint quotients with Fiat-Shamir coefficients into `CP`.
//!   4. **Mask** the FRI input: `H = CP + ζ·g` for a committed random `g`.
//!   5. FRI low-degree test on `H`; query openings bind `H` to the trace (ALI) and to `g`.
//!
//! Zero-knowledge: trace blinding makes every opened row uniform; the `g` mask makes the FRI
//! openings uniform. Both blindings use the OS CSPRNG, so proofs are randomized. See
//! `docs/soundness.md` for the full argument and `docs/parameters.md` for the parameters.

const std = @import("std");
const Allocator = std.mem.Allocator;
const p = @import("primitives.zig");
const field = @import("field.zig");
const rescue = @import("rescue.zig");
const Felt = field.Felt;

const Hash = [32]u8;
const WIDTH = rescue.WIDTH;

// ---------------------------------------------------------------------------------------
// Merkle tree over field-element leaves (single value or a WIDTH-wide row)
// ---------------------------------------------------------------------------------------

fn hashLeaf(v: Felt) Hash {
    return p.hashDomain("lattica:stark:leaf", &.{&field.toBytes(v)});
}

fn hashRow(row: [WIDTH]Felt) Hash {
    var bytes: [WIDTH][8]u8 = undefined;
    var fields: [WIDTH][]const u8 = undefined;
    for (0..WIDTH) |i| {
        bytes[i] = field.toBytes(row[i]);
        fields[i] = &bytes[i];
    }
    return p.hashDomain("lattica:stark:row", &fields);
}

fn hashNode(l: Hash, r: Hash) Hash {
    return p.hashDomain("lattica:stark:node", &.{ &l, &r });
}

/// A binary Merkle tree over `2^k` leaf hashes (1-indexed heap; root at `nodes[1]`).
const MerkleTree = struct {
    allocator: Allocator,
    n: usize,
    nodes: []Hash,

    fn fromLeafHashes(allocator: Allocator, leaf_hashes: []const Hash) !MerkleTree {
        const n = leaf_hashes.len;
        std.debug.assert(n != 0 and (n & (n - 1)) == 0);
        const nodes = try allocator.alloc(Hash, 2 * n);
        for (leaf_hashes, 0..) |h, i| nodes[n + i] = h;
        var i: usize = n - 1;
        while (i >= 1) : (i -= 1) {
            nodes[i] = hashNode(nodes[2 * i], nodes[2 * i + 1]);
            if (i == 1) break;
        }
        return .{ .allocator = allocator, .n = n, .nodes = nodes };
    }

    /// Build from single-value leaves (FRI layers, the mask `g`).
    fn build(allocator: Allocator, leaves: []const Felt) !MerkleTree {
        const hs = try allocator.alloc(Hash, leaves.len);
        defer allocator.free(hs);
        for (leaves, hs) |v, *h| h.* = hashLeaf(v);
        return fromLeafHashes(allocator, hs);
    }

    /// Build from WIDTH-wide rows (the trace); leaf `r` = `hashRow(cols[*][r])`.
    fn buildRows(allocator: Allocator, cols: [WIDTH][]const Felt) !MerkleTree {
        const n = cols[0].len;
        const hs = try allocator.alloc(Hash, n);
        defer allocator.free(hs);
        for (0..n) |r| {
            var row: [WIDTH]Felt = undefined;
            for (0..WIDTH) |i| row[i] = cols[i][r];
            hs[r] = hashRow(row);
        }
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

fn merkleVerifyHash(root: Hash, n: usize, index: usize, leaf_hash: Hash, path: []const Hash) bool {
    if (path.len != std.math.log2_int(usize, n)) return false;
    var h = leaf_hash;
    var idx = index;
    for (path) |sib| {
        h = if (idx & 1 == 0) hashNode(h, sib) else hashNode(sib, h);
        idx >>= 1;
    }
    return std.mem.eql(u8, &h, &root);
}

fn merkleVerify(root: Hash, n: usize, index: usize, val: Felt, path: []const Hash) bool {
    return merkleVerifyHash(root, n, index, hashLeaf(val), path);
}

fn merkleVerifyRow(root: Hash, n: usize, index: usize, row: [WIDTH]Felt, path: []const Hash) bool {
    return merkleVerifyHash(root, n, index, hashRow(row), path);
}

// ---------------------------------------------------------------------------------------
// Fiat-Shamir transcript (SHA3 duplex)
// ---------------------------------------------------------------------------------------

const Transcript = struct {
    state: Hash,
    counter: u64,

    fn init(label: []const u8) Transcript {
        return .{ .state = p.hashDomain("lattica:stark:transcript", &.{label}), .counter = 0 };
    }
    fn absorb(self: *Transcript, bytes: []const u8) void {
        self.state = p.hashDomain("lattica:stark:absorb", &.{ &self.state, bytes });
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
        return p.hashDomain("lattica:stark:squeeze", &.{ &self.state, &ctr });
    }
    fn challengeFelt(self: *Transcript) Felt {
        return field.fromBytes(self.squeeze()[0..16]);
    }
    fn challengeIndex(self: *Transcript, bound: usize) usize {
        const h = self.squeeze();
        return @intCast(std.mem.readInt(u64, h[0..8], .little) % bound);
    }
};

// ---------------------------------------------------------------------------------------
// Parameters
// ---------------------------------------------------------------------------------------

/// Trace length = rounds + 1 (one round per transition); a power of two.
const N: usize = rescue.ROUNDS + 1; // 16
/// Constraint count: WIDTH transition + 3 boundary.
const N_CONSTRAINTS: usize = WIDTH + 3;
/// Random coefficients masking each trace column (ZK). Must exceed the per-column open count
/// (4 rows/query · NUM_QUERIES = 128).
const TRACE_BLIND: usize = 160;
/// LDE blowup. The degree-7 S-box raises the composition degree to ~7·(N+TRACE_BLIND), so the
/// blowup is large relative to N (the trace is short).
const BLOWUP: usize = 512;
const LDE_SIZE: usize = N * BLOWUP; // 8192
const NUM_FOLDS: usize = 7;
const FINAL_SIZE: usize = LDE_SIZE >> NUM_FOLDS; // 64
/// Composition-polynomial degree bound (> its true max ~1210).
const COMP_DEGREE_BOUND: usize = 2048;
const FINAL_DEGREE_BOUND: usize = COMP_DEGREE_BOUND >> NUM_FOLDS; // 16
const NUM_QUERIES: usize = 32;

fn ldeOffset() Felt {
    return field.GENERATOR;
}
fn ldeGen() Felt {
    return field.rootOfUnity(LDE_SIZE);
}

// ---------------------------------------------------------------------------------------
// Randomness for the zero-knowledge blinding (OS CSPRNG)
// ---------------------------------------------------------------------------------------

fn osRandom(buf: []u8) void {
    var off: usize = 0;
    while (off < buf.len) {
        const rc = std.os.linux.getrandom(buf.ptr + off, buf.len - off, 0);
        std.debug.assert(rc != 0 and rc <= buf.len - off);
        off += rc;
    }
}

const Rng = struct {
    inner: std.Random.DefaultCsprng,
    fn init() Rng {
        var seed: [std.Random.DefaultCsprng.secret_seed_length]u8 = undefined;
        osRandom(&seed);
        return .{ .inner = std.Random.DefaultCsprng.init(seed) };
    }
    fn felt(self: *Rng) Felt {
        return self.inner.random().int(u64) % field.P;
    }
    fn fillFelts(self: *Rng, out: []Felt) void {
        for (out) |*v| v.* = self.felt();
    }
};

// ---------------------------------------------------------------------------------------
// FRI: low-degree test by repeated folding
// ---------------------------------------------------------------------------------------

const FriQueryLayer = struct { a: Felt, b: Felt, path_a: []Hash, path_b: []Hash };
const FriQuery = struct { layers: [NUM_FOLDS]FriQueryLayer };
const FriProof = struct { roots: [NUM_FOLDS]Hash, final_layer: []Felt, queries: []FriQuery };

fn friFold(allocator: Allocator, cur: []const Felt, beta: Felt, offset: Felt, gen: Felt) ![]Felt {
    const half = cur.len / 2;
    const next = try allocator.alloc(Felt, half);
    const inv2 = field.inv(2);
    var x = offset;
    for (0..half) |i| {
        const a = cur[i];
        const b = cur[i + half];
        const even = field.mul(field.add(a, b), inv2);
        const odd = field.mul(field.mul(field.sub(a, b), inv2), field.inv(x));
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
// The authorization AIR
// ---------------------------------------------------------------------------------------

fn secretToField(secret: *const [32]u8) Felt {
    var b: [16]u8 = undefined;
    @memcpy(&b, secret[0..16]);
    return field.fromBytes(&b);
}

/// Public authorization image: `rescue.hash(secret)`.
pub fn imageFelt(secret: *const [32]u8) Felt {
    return rescue.hash(secretToField(secret));
}

fn evalPoly(coeffs: []const Felt, x: Felt) Felt {
    var acc: Felt = 0;
    var i = coeffs.len;
    while (i > 0) {
        i -= 1;
        acc = field.add(field.mul(acc, x), coeffs[i]);
    }
    return acc;
}

/// Coefficients of the round-constant interpolation polynomials (one per state element), so the
/// verifier can evaluate the periodic constants at any query point. Deterministic and public.
fn roundConstantCoeffs() [WIDTH][N]Felt {
    const rc = rescue.roundConstants();
    const w = field.rootOfUnity(N);
    var out: [WIDTH][N]Felt = undefined;
    for (0..WIDTH) |i| {
        var vals: [N]Felt = undefined;
        for (0..N) |r| vals[r] = if (r < rescue.ROUNDS) rc[r][i] else 0;
        field.intt(&vals, w);
        out[i] = vals;
    }
    return out;
}

/// Evaluate the composition polynomial at one point from the current/next trace rows. Identical
/// for prover (over the whole LDE) and verifier (at query points), so they cannot disagree.
fn compositionAt(
    cur: [WIDTH]Felt,
    next: [WIDTH]Felt,
    x: Felt,
    image: Felt,
    comb: [N_CONSTRAINTS]Felt,
    rc_at: [WIDTH]Felt,
    m: [WIDTH][WIDTH]Felt,
    omega_last: Felt,
) Felt {
    var sb: [WIDTH]Felt = undefined;
    for (0..WIDTH) |j| sb[j] = rescue.sbox(cur[j]);

    const z_trans = field.mul(field.sub(field.pow(x, N), 1), field.inv(field.sub(x, omega_last)));
    const z_trans_inv = field.inv(z_trans);

    var cp: Felt = 0;
    // Transition constraints: next_i - (Σ_j M[i][j]·cur_j^7 + rc_i).
    for (0..WIDTH) |i| {
        var roundi = rc_at[i];
        for (0..WIDTH) |j| roundi = field.add(roundi, field.mul(m[i][j], sb[j]));
        const ctrans = field.sub(next[i], roundi);
        cp = field.add(cp, field.mul(comb[i], field.mul(ctrans, z_trans_inv)));
    }
    // Boundary constraints: capacity cells zero at row 0; output = image at the last row.
    const inv_x1 = field.inv(field.sub(x, 1));
    const inv_xl = field.inv(field.sub(x, omega_last));
    cp = field.add(cp, field.mul(comb[WIDTH + 0], field.mul(cur[1], inv_x1)));
    cp = field.add(cp, field.mul(comb[WIDTH + 1], field.mul(cur[2], inv_x1)));
    cp = field.add(cp, field.mul(comb[WIDTH + 2], field.mul(field.sub(cur[0], image), inv_xl)));
    return cp;
}

/// Evaluate a coefficient vector (length <= LDE_SIZE) over the LDE coset.
fn coeffsToLde(allocator: Allocator, coeffs: []const Felt) ![]Felt {
    std.debug.assert(coeffs.len <= LDE_SIZE);
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

/// Build the trace, interpolate each column, add ZK blinding `Z_H·b_i`, and evaluate over the
/// LDE coset. Returns the WIDTH LDE columns (each owned by `allocator`).
fn buildTraceLde(allocator: Allocator, secret_felt: Felt, rng: *Rng) ![WIDTH][]Felt {
    const m = rescue.mds();
    const rc = rescue.roundConstants();
    // Raw execution trace: N rows of WIDTH columns.
    var rows: [N]rescue.State = undefined;
    rows[0] = .{ secret_felt, 0, 0 };
    for (0..rescue.ROUNDS) |r| rows[r + 1] = rescue.round(rows[r], m, rc[r]);

    const w = field.rootOfUnity(N);
    var out: [WIDTH][]Felt = undefined;
    for (0..WIDTH) |i| {
        // Interpolate column i over H.
        var col: [N]Felt = undefined;
        for (0..N) |r| col[r] = rows[r][i];
        field.intt(&col, w);
        // Blinded coefficients: col + (x^N - 1)·b_i, degree < N + TRACE_BLIND.
        const mc = try allocator.alloc(Felt, N + TRACE_BLIND);
        defer allocator.free(mc);
        @memset(mc, 0);
        @memcpy(mc[0..N], &col);
        var b: [TRACE_BLIND]Felt = undefined;
        rng.fillFelts(&b);
        for (0..TRACE_BLIND) |k| {
            mc[k] = field.sub(mc[k], b[k]);
            mc[N + k] = field.add(mc[N + k], b[k]);
        }
        out[i] = try coeffsToLde(allocator, mc);
    }
    return out;
}

fn buildRandomPolyLde(allocator: Allocator, rng: *Rng) ![]Felt {
    const coeffs = try allocator.alloc(Felt, COMP_DEGREE_BOUND);
    defer allocator.free(coeffs);
    rng.fillFelts(coeffs);
    return coeffsToLde(allocator, coeffs);
}

// ---------------------------------------------------------------------------------------
// Proof object
// ---------------------------------------------------------------------------------------

const RowOpen = struct { row: [WIDTH]Felt, path: []Hash };
const ValOpen = struct { val: Felt, path: []Hash };

const StarkQuery = struct {
    fri: FriQuery,
    cur_a: RowOpen, // trace row at q
    next_a: RowOpen, // trace row at (q + BLOWUP) mod LDE
    cur_b: RowOpen, // trace row at q + LDE/2
    next_b: RowOpen, // trace row at (q + LDE/2 + BLOWUP) mod LDE
    g_a: ValOpen, // mask g at q
    g_b: ValOpen, // mask g at q + LDE/2
};

pub const StarkProof = struct {
    trace_root: Hash,
    g_root: Hash,
    fri_roots: [NUM_FOLDS]Hash,
    fri_final: []Felt,
    queries: []StarkQuery,
};

const TRANSCRIPT_LABEL = "lattica:auth-stark:v2-rescue";

fn rowAt(cols: [WIDTH][]const Felt, idx: usize) [WIDTH]Felt {
    var row: [WIDTH]Felt = undefined;
    for (0..WIDTH) |i| row[i] = cols[i][idx];
    return row;
}

// ---------------------------------------------------------------------------------------
// Prove
// ---------------------------------------------------------------------------------------

pub fn prove(allocator: Allocator, secret: *const [32]u8) !StarkProof {
    var rng = Rng.init();
    const image = imageFelt(secret);
    const m = rescue.mds();
    const omega_last = field.pow(field.rootOfUnity(N), N - 1);

    const trace_lde = try buildTraceLde(allocator, secretToField(secret), &rng);
    defer for (trace_lde) |c| allocator.free(c);
    const trace_const: [WIDTH][]const Felt = blk: {
        var c: [WIDTH][]const Felt = undefined;
        for (0..WIDTH) |i| c[i] = trace_lde[i];
        break :blk c;
    };
    const g_lde = try buildRandomPolyLde(allocator, &rng);
    defer allocator.free(g_lde);

    // Round-constant evaluations over the LDE (for the composition).
    const rc_coeffs = roundConstantCoeffs();
    var rc_lde: [WIDTH][]Felt = undefined;
    for (0..WIDTH) |i| rc_lde[i] = try coeffsToLde(allocator, &rc_coeffs[i]);
    defer for (rc_lde) |c| allocator.free(c);

    var trace_tree = try MerkleTree.buildRows(allocator, trace_const);
    defer trace_tree.deinit();
    var g_tree = try MerkleTree.build(allocator, g_lde);
    defer g_tree.deinit();
    const trace_root = trace_tree.root();
    const g_root = g_tree.root();

    var tr = Transcript.init(TRANSCRIPT_LABEL);
    tr.absorbFelt(image);
    tr.absorbHash(trace_root);
    tr.absorbHash(g_root);
    var comb: [N_CONSTRAINTS]Felt = undefined;
    for (&comb) |*c| c.* = tr.challengeFelt();
    const zeta = tr.challengeFelt();

    // FRI input H = CP + zeta·g.
    const h = try allocator.alloc(Felt, LDE_SIZE);
    defer allocator.free(h);
    var x = ldeOffset();
    for (0..LDE_SIZE) |j| {
        const cur = rowAt(trace_const, j);
        const next = rowAt(trace_const, (j + BLOWUP) % LDE_SIZE);
        const rc_at = [WIDTH]Felt{ rc_lde[0][j], rc_lde[1][j], rc_lde[2][j] };
        const cp = compositionAt(cur, next, x, image, comb, rc_at, m, omega_last);
        h[j] = field.add(cp, field.mul(zeta, g_lde[j]));
        x = field.mul(x, ldeGen());
    }

    var fri = try FriProver.commit(allocator, &tr, h);
    const fri_roots = fri.roots;
    const fri_final = try allocator.dupe(Felt, fri.final_layer);

    const half0 = LDE_SIZE / 2;
    const queries = try allocator.alloc(StarkQuery, NUM_QUERIES);
    for (queries) |*sq| {
        const q0 = tr.challengeIndex(half0);
        const a = q0;
        const an = (q0 + BLOWUP) % LDE_SIZE;
        const b = q0 + half0;
        const bn = (b + BLOWUP) % LDE_SIZE;
        sq.fri = try fri.open(allocator, q0);
        sq.cur_a = .{ .row = rowAt(trace_const, a), .path = try trace_tree.open(allocator, a) };
        sq.next_a = .{ .row = rowAt(trace_const, an), .path = try trace_tree.open(allocator, an) };
        sq.cur_b = .{ .row = rowAt(trace_const, b), .path = try trace_tree.open(allocator, b) };
        sq.next_b = .{ .row = rowAt(trace_const, bn), .path = try trace_tree.open(allocator, bn) };
        sq.g_a = .{ .val = g_lde[a], .path = try g_tree.open(allocator, a) };
        sq.g_b = .{ .val = g_lde[b], .path = try g_tree.open(allocator, b) };
    }
    allocator.free(fri.final_layer);
    fri.deinit();
    return .{ .trace_root = trace_root, .g_root = g_root, .fri_roots = fri_roots, .fri_final = fri_final, .queries = queries };
}

// ---------------------------------------------------------------------------------------
// Verify
// ---------------------------------------------------------------------------------------

pub fn verify(allocator: Allocator, image: Felt, proof: StarkProof) !bool {
    if (proof.fri_final.len != FINAL_SIZE) return false;
    if (proof.queries.len != NUM_QUERIES) return false;

    const m = rescue.mds();
    const omega_last = field.pow(field.rootOfUnity(N), N - 1);
    const rc_coeffs = roundConstantCoeffs();

    var tr = Transcript.init(TRANSCRIPT_LABEL);
    tr.absorbFelt(image);
    tr.absorbHash(proof.trace_root);
    tr.absorbHash(proof.g_root);
    var comb: [N_CONSTRAINTS]Felt = undefined;
    for (&comb) |*c| c.* = tr.challengeFelt();
    const zeta = tr.challengeFelt();

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

    for (proof.queries) |sq| {
        const q0 = tr.challengeIndex(half0);
        const a = q0;
        const an = (q0 + BLOWUP) % LDE_SIZE;
        const b = q0 + half0;
        const bn = (b + BLOWUP) % LDE_SIZE;

        // Trace + mask Merkle openings.
        if (!merkleVerifyRow(proof.trace_root, LDE_SIZE, a, sq.cur_a.row, sq.cur_a.path)) ok = false;
        if (!merkleVerifyRow(proof.trace_root, LDE_SIZE, an, sq.next_a.row, sq.next_a.path)) ok = false;
        if (!merkleVerifyRow(proof.trace_root, LDE_SIZE, b, sq.cur_b.row, sq.cur_b.path)) ok = false;
        if (!merkleVerifyRow(proof.trace_root, LDE_SIZE, bn, sq.next_b.row, sq.next_b.path)) ok = false;
        if (!merkleVerify(proof.g_root, LDE_SIZE, a, sq.g_a.val, sq.g_a.path)) ok = false;
        if (!merkleVerify(proof.g_root, LDE_SIZE, b, sq.g_b.val, sq.g_b.path)) ok = false;

        // ALI: H(x) must equal CP(trace) + zeta·g at both layer-0 query points.
        const x_a = field.mul(ldeOffset(), field.pow(ldeGen(), @intCast(a)));
        const x_b = field.mul(ldeOffset(), field.pow(ldeGen(), @intCast(b)));
        const rc_a = [WIDTH]Felt{ evalPoly(&rc_coeffs[0], x_a), evalPoly(&rc_coeffs[1], x_a), evalPoly(&rc_coeffs[2], x_a) };
        const rc_b = [WIDTH]Felt{ evalPoly(&rc_coeffs[0], x_b), evalPoly(&rc_coeffs[1], x_b), evalPoly(&rc_coeffs[2], x_b) };
        const h_a = field.add(compositionAt(sq.cur_a.row, sq.next_a.row, x_a, image, comb, rc_a, m, omega_last), field.mul(zeta, sq.g_a.val));
        const h_b = field.add(compositionAt(sq.cur_b.row, sq.next_b.row, x_b, image, comb, rc_b, m, omega_last), field.mul(zeta, sq.g_b.val));
        if (h_a != sq.fri.layers[0].a) ok = false;
        if (h_b != sq.fri.layers[0].b) ok = false;

        // FRI fold-consistency chain.
        for (0..NUM_FOLDS) |k| {
            const size_k = LDE_SIZE >> @intCast(k);
            const half_k = size_k / 2;
            const ai = q0 % half_k;
            const off_k = field.pow(ldeOffset(), @as(u64, 1) << @intCast(k));
            const gen_k = field.pow(ldeGen(), @as(u64, 1) << @intCast(k));
            const layer = sq.fri.layers[k];
            if (!merkleVerify(proof.fri_roots[k], size_k, ai, layer.a, layer.path_a)) ok = false;
            if (!merkleVerify(proof.fri_roots[k], size_k, ai + half_k, layer.b, layer.path_b)) ok = false;
            const x = field.mul(off_k, field.pow(gen_k, @intCast(ai)));
            const even = field.mul(field.add(layer.a, layer.b), inv2);
            const odd = field.mul(field.mul(field.sub(layer.a, layer.b), inv2), field.inv(x));
            const folded = field.add(even, field.mul(betas[k], odd));
            if (k + 1 < NUM_FOLDS) {
                const half_next = half_k / 2;
                const expected = if (ai < half_next) sq.fri.layers[k + 1].a else sq.fri.layers[k + 1].b;
                if (folded != expected) ok = false;
            } else {
                if (folded != proof.fri_final[ai % FINAL_SIZE]) ok = false;
            }
        }
    }
    return ok;
}

pub fn starkFree(allocator: Allocator, proof: StarkProof) void {
    for (proof.queries) |sq| {
        for (sq.fri.layers) |layer| {
            allocator.free(layer.path_a);
            allocator.free(layer.path_b);
        }
        allocator.free(sq.cur_a.path);
        allocator.free(sq.next_a.path);
        allocator.free(sq.cur_b.path);
        allocator.free(sq.next_b.path);
        allocator.free(sq.g_a.path);
        allocator.free(sq.g_b.path);
    }
    allocator.free(proof.queries);
    allocator.free(proof.fri_final);
}

// ---------------------------------------------------------------------------------------
// Serialization (positional; all sub-object sizes are fixed by the parameters)
// ---------------------------------------------------------------------------------------

fn putFelt(buf: *std.ArrayList(u8), allocator: Allocator, v: Felt) !void {
    try buf.appendSlice(allocator, &field.toBytes(v));
}
fn putHash(buf: *std.ArrayList(u8), allocator: Allocator, h: Hash) !void {
    try buf.appendSlice(allocator, &h);
}
fn putRowOpen(buf: *std.ArrayList(u8), allocator: Allocator, o: RowOpen) !void {
    for (o.row) |v| try putFelt(buf, allocator, v);
    for (o.path) |h| try putHash(buf, allocator, h);
}
fn putValOpen(buf: *std.ArrayList(u8), allocator: Allocator, o: ValOpen) !void {
    try putFelt(buf, allocator, o.val);
    for (o.path) |h| try putHash(buf, allocator, h);
}

pub fn serialize(allocator: Allocator, proof: StarkProof) ![]u8 {
    var buf: std.ArrayList(u8) = .empty;
    errdefer buf.deinit(allocator);
    try putHash(&buf, allocator, proof.trace_root);
    try putHash(&buf, allocator, proof.g_root);
    for (proof.fri_roots) |r| try putHash(&buf, allocator, r);
    for (proof.fri_final) |v| try putFelt(&buf, allocator, v);
    for (proof.queries) |sq| {
        for (sq.fri.layers) |layer| {
            try putFelt(&buf, allocator, layer.a);
            try putFelt(&buf, allocator, layer.b);
            for (layer.path_a) |h| try putHash(&buf, allocator, h);
            for (layer.path_b) |h| try putHash(&buf, allocator, h);
        }
        try putRowOpen(&buf, allocator, sq.cur_a);
        try putRowOpen(&buf, allocator, sq.next_a);
        try putRowOpen(&buf, allocator, sq.cur_b);
        try putRowOpen(&buf, allocator, sq.next_b);
        try putValOpen(&buf, allocator, sq.g_a);
        try putValOpen(&buf, allocator, sq.g_b);
    }
    return buf.toOwnedSlice(allocator);
}

const Reader = struct {
    data: []const u8,
    pos: usize = 0,
    fn getBytes(self: *Reader, n: usize) ![]const u8 {
        if (self.pos + n > self.data.len) return error.Truncated;
        const s = self.data[self.pos .. self.pos + n];
        self.pos += n;
        return s;
    }
    fn getFelt(self: *Reader) !Felt {
        // Canonical encoding: a field element must be < P. Reject the non-canonical
        // representatives (v and v+P would otherwise both decode), so proof bytes are unique.
        const v = std.mem.readInt(u64, (try self.getBytes(8))[0..8], .little);
        if (v >= field.P) return error.NonCanonical;
        return v;
    }
    fn getHash(self: *Reader) !Hash {
        var h: Hash = undefined;
        @memcpy(&h, try self.getBytes(32));
        return h;
    }
    fn getPath(self: *Reader, allocator: Allocator, len: usize) ![]Hash {
        const path = try allocator.alloc(Hash, len);
        for (path) |*h| h.* = try self.getHash();
        return path;
    }
    fn getRowOpen(self: *Reader, allocator: Allocator, depth: usize) !RowOpen {
        var row: [WIDTH]Felt = undefined;
        for (0..WIDTH) |i| row[i] = try self.getFelt();
        return .{ .row = row, .path = try self.getPath(allocator, depth) };
    }
    fn getValOpen(self: *Reader, allocator: Allocator, depth: usize) !ValOpen {
        return .{ .val = try self.getFelt(), .path = try self.getPath(allocator, depth) };
    }
};

pub fn deserialize(allocator: Allocator, bytes: []const u8) !StarkProof {
    var r = Reader{ .data = bytes };
    const trace_root = try r.getHash();
    const g_root = try r.getHash();
    var fri_roots: [NUM_FOLDS]Hash = undefined;
    for (&fri_roots) |*x| x.* = try r.getHash();
    const fri_final = try allocator.alloc(Felt, FINAL_SIZE);
    errdefer allocator.free(fri_final);
    for (fri_final) |*v| v.* = try r.getFelt();

    const depth = std.math.log2_int(usize, LDE_SIZE);
    const queries = try allocator.alloc(StarkQuery, NUM_QUERIES);
    for (queries) |*sq| {
        for (0..NUM_FOLDS) |k| {
            const ld = std.math.log2_int(usize, LDE_SIZE >> @intCast(k));
            sq.fri.layers[k].a = try r.getFelt();
            sq.fri.layers[k].b = try r.getFelt();
            sq.fri.layers[k].path_a = try r.getPath(allocator, ld);
            sq.fri.layers[k].path_b = try r.getPath(allocator, ld);
        }
        sq.cur_a = try r.getRowOpen(allocator, depth);
        sq.next_a = try r.getRowOpen(allocator, depth);
        sq.cur_b = try r.getRowOpen(allocator, depth);
        sq.next_b = try r.getRowOpen(allocator, depth);
        sq.g_a = try r.getValOpen(allocator, depth);
        sq.g_b = try r.getValOpen(allocator, depth);
    }
    // Canonical encoding: the proof must consume exactly its bytes — no trailing data.
    if (r.pos != bytes.len) return error.TrailingBytes;
    return .{ .trace_root = trace_root, .g_root = g_root, .fri_roots = fri_roots, .fri_final = fri_final, .queries = queries };
}

// ---------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------

const testing = std.testing;

test "stark: valid proof verifies" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const secret = [_]u8{7} ** 32;
    const proof = try prove(a, &secret);
    try testing.expect(try verify(a, imageFelt(&secret), proof));
}

test "stark: deserialize rejects trailing bytes" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const secret = [_]u8{7} ** 32;
    const bytes = try serialize(a, try prove(a, &secret));
    const extended = try a.alloc(u8, bytes.len + 1);
    @memcpy(extended[0..bytes.len], bytes);
    extended[bytes.len] = 0xAA;
    try testing.expectError(error.TrailingBytes, deserialize(a, extended));
}

test "stark: deserialize rejects a non-canonical field element" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const secret = [_]u8{7} ** 32;
    const bytes = try serialize(a, try prove(a, &secret));
    // The first field element (fri_final[0]) follows trace_root, g_root, and the FRI roots.
    // Overwrite it with P, which is not a canonical residue in [0, P).
    const off = 32 + 32 + NUM_FOLDS * 32;
    std.mem.writeInt(u64, bytes[off..][0..8], field.P, .little);
    try testing.expectError(error.NonCanonical, deserialize(a, bytes));
}

test "stark: wrong image rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const secret = [_]u8{7} ** 32;
    const proof = try prove(a, &secret);
    try testing.expect(!try verify(a, imageFelt(&secret) + 1, proof));
}

test "stark: tampered trace row rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const secret = [_]u8{7} ** 32;
    var proof = try prove(a, &secret);
    proof.queries[0].cur_a.row[0] = field.add(proof.queries[0].cur_a.row[0], 1);
    try testing.expect(!try verify(a, imageFelt(&secret), proof));
}

test "stark: tampered mask opening rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const secret = [_]u8{7} ** 32;
    var proof = try prove(a, &secret);
    proof.queries[0].g_a.val = field.add(proof.queries[0].g_a.val, 1);
    try testing.expect(!try verify(a, imageFelt(&secret), proof));
}

test "stark: tampered fri final rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const secret = [_]u8{7} ** 32;
    var proof = try prove(a, &secret);
    proof.fri_final[0] = field.add(proof.fri_final[0], 1);
    try testing.expect(!try verify(a, imageFelt(&secret), proof));
}

test "stark: proof binds to its own image only" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const secret = [_]u8{7} ** 32;
    const other = [_]u8{8} ** 32;
    const proof = try prove(a, &secret);
    try testing.expect(!try verify(a, imageFelt(&other), proof));
    try testing.expect(try verify(a, imageFelt(&secret), proof));
}

test "stark: serialize/deserialize round trip verifies" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const secret = [_]u8{7} ** 32;
    const proof = try prove(a, &secret);
    const bytes = try serialize(a, proof);
    const parsed = try deserialize(a, bytes);
    try testing.expect(try verify(a, imageFelt(&secret), parsed));
}

test "stark: proofs are randomized (zero-knowledge blinding)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const secret = [_]u8{7} ** 32;
    const b1 = try serialize(a, try prove(a, &secret));
    const b2 = try serialize(a, try prove(a, &secret));
    try testing.expectEqual(b1.len, b2.len);
    try testing.expect(!std.mem.eql(u8, b1, b2));
}
