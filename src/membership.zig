//! In-circuit **zero-knowledge Merkle membership** — the first constraint of R3 folded into an
//! AIR. It proves, in zero knowledge, knowledge of a leaf and an authentication path that hash up
//! to a public anchor, using the arithmetization-friendly field hash (`rescue.zig`) as the 2-to-1
//! compression. This is the hardest of the four spend constraints to arithmetize; it needs **no
//! copy-constraint/permutation argument** because its wiring is a pure chain (each level's output
//! is the next level's input — adjacent rows).
//!
//! Scope and honesty:
//!  * The path is the **leftmost** position (each step folds `H(cur, sibling)`); general
//!    positions add one boolean ordering selector per level (designed in `docs/soundness.md §6`).
//!  * Folding membership together with the nullifier, balance, and commitment-opening into a
//!    single spend proof requires a **permutation argument** to wire shared witness values — that
//!    is the next reviewed increment, not done here.
//!  * The STARK engine here is adapted from `stark.zig` (duplicated for isolation; dedupe once
//!    the engine is generic). Serialization is omitted — this is a standalone proof, not yet
//!    node-integrated.
//!
//! AIR: WIDTH columns, N = DEPTH·(ROUNDS+1) rows. Each DEPTH-block is one `rescue.permute`
//! (ROUNDS round-transitions); the block-boundary transition is a **link** carrying the
//! compressed output into the next block's left input and resetting the capacity, with the next
//! sibling supplied as the free right-input cell. Constraints: WIDTH transition (degree 7,
//! periodic round constants), 2 link, 2 boundary (capacity 0 at row 0, output = anchor at row N-1).

const std = @import("std");
const Allocator = std.mem.Allocator;
const p = @import("primitives.zig");
const field = @import("field.zig");
const rescue = @import("rescue.zig");
const Felt = field.Felt;

const Hash = [32]u8;
const WIDTH = rescue.WIDTH;

// ---------------------------------------------------------------------------------------
// Parameters
// ---------------------------------------------------------------------------------------

const DEPTH: usize = 8; // demo tree depth (production: 32)
const BLOCK: usize = rescue.ROUNDS + 1; // 16 rows per compression
const N: usize = DEPTH * BLOCK; // 128
const N_CONSTRAINTS: usize = WIDTH + 2 + 2; // 3 transition + 2 link + 2 boundary
const TRACE_BLIND: usize = 160; // >= per-column openings (4/query · 32 = 128)
const BLOWUP: usize = 64;
const LDE_SIZE: usize = N * BLOWUP; // 8192
const NUM_FOLDS: usize = 7;
const FINAL_SIZE: usize = LDE_SIZE >> NUM_FOLDS; // 64
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
// Merkle tree, transcript, RNG, FRI — engine adapted from stark.zig
// ---------------------------------------------------------------------------------------

fn hashLeaf(v: Felt) Hash {
    return p.hashDomain("lattica:mship:leaf", &.{&field.toBytes(v)});
}
fn hashRow(row: [WIDTH]Felt) Hash {
    var bytes: [WIDTH][8]u8 = undefined;
    var fields: [WIDTH][]const u8 = undefined;
    for (0..WIDTH) |i| {
        bytes[i] = field.toBytes(row[i]);
        fields[i] = &bytes[i];
    }
    return p.hashDomain("lattica:mship:row", &fields);
}
fn hashNode(l: Hash, r: Hash) Hash {
    return p.hashDomain("lattica:mship:node", &.{ &l, &r });
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

const Transcript = struct {
    state: Hash,
    counter: u64,
    fn init(label: []const u8) Transcript {
        return .{ .state = p.hashDomain("lattica:mship:transcript", &.{label}), .counter = 0 };
    }
    fn absorb(self: *Transcript, bytes: []const u8) void {
        self.state = p.hashDomain("lattica:mship:absorb", &.{ &self.state, bytes });
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
        return p.hashDomain("lattica:mship:squeeze", &.{ &self.state, &ctr });
    }
    fn challengeFelt(self: *Transcript) Felt {
        return field.fromBytes(self.squeeze()[0..16]);
    }
    fn challengeIndex(self: *Transcript, bound: usize) usize {
        return @intCast(std.mem.readInt(u64, self.squeeze()[0..8], .little) % bound);
    }
};

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

fn evalPoly(coeffs: []const Felt, x: Felt) Felt {
    var acc: Felt = 0;
    var i = coeffs.len;
    while (i > 0) {
        i -= 1;
        acc = field.add(field.mul(acc, x), coeffs[i]);
    }
    return acc;
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
// Membership AIR
// ---------------------------------------------------------------------------------------

/// Round-constant interpolation polynomials, periodic with period BLOCK (each block is a fresh
/// permutation). `rc_i(x) = RC_i(x^{N/BLOCK})`; coeffs of `RC_i` (degree < BLOCK) returned here.
fn roundConstantCoeffs() [WIDTH][BLOCK]Felt {
    const rc = rescue.roundConstants();
    const w = field.rootOfUnity(BLOCK);
    var out: [WIDTH][BLOCK]Felt = undefined;
    for (0..WIDTH) |i| {
        var vals: [BLOCK]Felt = undefined;
        for (0..BLOCK) |k| vals[k] = if (k < rescue.ROUNDS) rc[k][i] else 0;
        field.intt(&vals, w);
        out[i] = vals;
    }
    return out;
}

/// `rc_i` evaluated at `x` (using the periodic trick `RC_i(x^{N/BLOCK})`).
fn rcAt(rc_coeffs: [WIDTH][BLOCK]Felt, x: Felt) [WIDTH]Felt {
    const xb = field.pow(x, N / BLOCK);
    var out: [WIDTH]Felt = undefined;
    for (0..WIDTH) |i| out[i] = evalPoly(&rc_coeffs[i], xb);
    return out;
}

/// The DEPTH-1 link rows (last row of each block except the final block): `ω^{d·BLOCK + BLOCK-1}`.
fn linkPoints() [DEPTH - 1]Felt {
    const w = field.rootOfUnity(N);
    var pts: [DEPTH - 1]Felt = undefined;
    for (0..DEPTH - 1) |d| pts[d] = field.pow(w, @intCast(d * BLOCK + BLOCK - 1));
    return pts;
}

/// `Z_link(x) = Π (x − link_point)`; vanishes exactly on the link rows.
fn zLink(x: Felt, links: [DEPTH - 1]Felt) Felt {
    var z: Felt = 1;
    for (links) |lp| z = field.mul(z, field.sub(x, lp));
    return z;
}

/// Composition at one point. `comb`: [0..WIDTH) transition, [WIDTH] link-carry, [WIDTH+1]
/// link-capacity, [WIDTH+2] boundary-cap0, [WIDTH+3] boundary-output=anchor.
fn compositionAt(
    cur: [WIDTH]Felt,
    next: [WIDTH]Felt,
    x: Felt,
    anchor: Felt,
    comb: [N_CONSTRAINTS]Felt,
    rc_row: [WIDTH]Felt,
    m: [WIDTH][WIDTH]Felt,
    omega_last: Felt,
    links: [DEPTH - 1]Felt,
) Felt {
    const z_link = zLink(x, links);
    // Z_round = (x^N - 1) / ((x - ω^{N-1}) · Z_link): vanishes on all transition rows except the
    // link rows and the last row.
    const x_n_minus_1 = field.sub(field.pow(x, N), 1);
    const z_round = field.mul(x_n_minus_1, field.inv(field.mul(field.sub(x, omega_last), z_link)));
    const inv_z_round = field.inv(z_round);
    const inv_z_link = field.inv(z_link);

    var sb: [WIDTH]Felt = undefined;
    for (0..WIDTH) |j| sb[j] = rescue.sbox(cur[j]);

    var cp: Felt = 0;
    // Transition: next_i = Σ_j M[i][j]·cur_j^7 + rc_i  (one full Rescue round), on non-link rows.
    for (0..WIDTH) |i| {
        var roundi = rc_row[i];
        for (0..WIDTH) |j| roundi = field.add(roundi, field.mul(m[i][j], sb[j]));
        const c = field.sub(next[i], roundi);
        cp = field.add(cp, field.mul(comb[i], field.mul(c, inv_z_round)));
    }
    // Link (on link rows): carry the compressed output into the next left input, reset capacity.
    const c_carry = field.sub(next[0], cur[0]);
    const c_cap = next[2];
    cp = field.add(cp, field.mul(comb[WIDTH + 0], field.mul(c_carry, inv_z_link)));
    cp = field.add(cp, field.mul(comb[WIDTH + 1], field.mul(c_cap, inv_z_link)));
    // Boundary: capacity 0 at row 0; output[0] = anchor at the last row.
    cp = field.add(cp, field.mul(comb[WIDTH + 2], field.mul(cur[2], field.inv(field.sub(x, 1)))));
    cp = field.add(cp, field.mul(comb[WIDTH + 3], field.mul(field.sub(cur[0], anchor), field.inv(field.sub(x, omega_last)))));
    return cp;
}

/// Compute the Merkle root (anchor) by folding `leaf` up with `siblings` (leftmost path).
pub fn computeRoot(leaf: Felt, siblings: [DEPTH]Felt) Felt {
    var cur = leaf;
    for (0..DEPTH) |d| cur = rescue.permute(.{ cur, siblings[d], 0 })[0];
    return cur;
}

/// Build the execution trace (DEPTH blocks of one permutation each) and return its blinded LDE
/// columns. The leftmost-path siblings are placed as the free right-input cell of each block.
fn buildTraceLde(allocator: Allocator, leaf: Felt, siblings: [DEPTH]Felt, rng: *Rng) ![WIDTH][]Felt {
    const m = rescue.mds();
    const rc = rescue.roundConstants();
    var rows: [N][WIDTH]Felt = undefined;
    var cur = leaf;
    for (0..DEPTH) |d| {
        const base = d * BLOCK;
        rows[base] = .{ cur, siblings[d], 0 }; // block input [left, right, capacity]
        for (0..rescue.ROUNDS) |r| rows[base + r + 1] = rescue.round(rows[base + r], m, rc[r]);
        cur = rows[base + rescue.ROUNDS][0]; // compressed output carried to next block
    }

    const w = field.rootOfUnity(N);
    var out: [WIDTH][]Felt = undefined;
    for (0..WIDTH) |i| {
        var col: [N]Felt = undefined;
        for (0..N) |r| col[r] = rows[r][i];
        field.intt(&col, w);
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
// Proof
// ---------------------------------------------------------------------------------------

const RowOpen = struct { row: [WIDTH]Felt, path: []Hash };
const ValOpen = struct { val: Felt, path: []Hash };
const Query = struct {
    fri: FriQuery,
    cur_a: RowOpen,
    next_a: RowOpen,
    cur_b: RowOpen,
    next_b: RowOpen,
    g_a: ValOpen,
    g_b: ValOpen,
};
pub const Proof = struct {
    trace_root: Hash,
    g_root: Hash,
    fri_roots: [NUM_FOLDS]Hash,
    fri_final: []Felt,
    queries: []Query,
};

const LABEL = "lattica:membership:v1";

fn rowAt(cols: [WIDTH][]const Felt, idx: usize) [WIDTH]Felt {
    var row: [WIDTH]Felt = undefined;
    for (0..WIDTH) |i| row[i] = cols[i][idx];
    return row;
}

/// Prove knowledge of `leaf` and `siblings` whose leftmost-path fold equals `computeRoot(...)`.
pub fn prove(allocator: Allocator, leaf: Felt, siblings: [DEPTH]Felt) !Proof {
    var rng = Rng.init();
    const m = rescue.mds();
    const omega_last = field.pow(field.rootOfUnity(N), N - 1);
    const links = linkPoints();
    const rc_coeffs = roundConstantCoeffs();
    const anchor = computeRoot(leaf, siblings);

    const trace_lde = try buildTraceLde(allocator, leaf, siblings, &rng);
    defer for (trace_lde) |c| allocator.free(c);
    var trace_c: [WIDTH][]const Felt = undefined;
    for (0..WIDTH) |i| trace_c[i] = trace_lde[i];
    const g_lde = try buildRandomPolyLde(allocator, &rng);
    defer allocator.free(g_lde);

    var trace_tree = try MerkleTree.buildRows(allocator, trace_c);
    defer trace_tree.deinit();
    var g_tree = try MerkleTree.build(allocator, g_lde);
    defer g_tree.deinit();
    const trace_root = trace_tree.root();
    const g_root = g_tree.root();

    var tr = Transcript.init(LABEL);
    tr.absorbFelt(anchor);
    tr.absorbHash(trace_root);
    tr.absorbHash(g_root);
    var comb: [N_CONSTRAINTS]Felt = undefined;
    for (&comb) |*c| c.* = tr.challengeFelt();
    const zeta = tr.challengeFelt();

    const h = try allocator.alloc(Felt, LDE_SIZE);
    defer allocator.free(h);
    var x = ldeOffset();
    for (0..LDE_SIZE) |j| {
        const cur = rowAt(trace_c, j);
        const next = rowAt(trace_c, (j + BLOWUP) % LDE_SIZE);
        const cp = compositionAt(cur, next, x, anchor, comb, rcAt(rc_coeffs, x), m, omega_last, links);
        h[j] = field.add(cp, field.mul(zeta, g_lde[j]));
        x = field.mul(x, ldeGen());
    }

    var fri = try FriProver.commit(allocator, &tr, h);
    const fri_roots = fri.roots;
    const fri_final = try allocator.dupe(Felt, fri.final_layer);

    const half0 = LDE_SIZE / 2;
    const queries = try allocator.alloc(Query, NUM_QUERIES);
    for (queries) |*q| {
        const q0 = tr.challengeIndex(half0);
        const a = q0;
        const an = (q0 + BLOWUP) % LDE_SIZE;
        const bb = q0 + half0;
        const bn = (bb + BLOWUP) % LDE_SIZE;
        q.fri = try fri.open(allocator, q0);
        q.cur_a = .{ .row = rowAt(trace_c, a), .path = try trace_tree.open(allocator, a) };
        q.next_a = .{ .row = rowAt(trace_c, an), .path = try trace_tree.open(allocator, an) };
        q.cur_b = .{ .row = rowAt(trace_c, bb), .path = try trace_tree.open(allocator, bb) };
        q.next_b = .{ .row = rowAt(trace_c, bn), .path = try trace_tree.open(allocator, bn) };
        q.g_a = .{ .val = g_lde[a], .path = try g_tree.open(allocator, a) };
        q.g_b = .{ .val = g_lde[bb], .path = try g_tree.open(allocator, bb) };
    }
    allocator.free(fri.final_layer);
    fri.deinit();
    return .{ .trace_root = trace_root, .g_root = g_root, .fri_roots = fri_roots, .fri_final = fri_final, .queries = queries };
}

pub fn verify(allocator: Allocator, anchor: Felt, proof: Proof) !bool {
    if (proof.fri_final.len != FINAL_SIZE or proof.queries.len != NUM_QUERIES) return false;
    const m = rescue.mds();
    const omega_last = field.pow(field.rootOfUnity(N), N - 1);
    const links = linkPoints();
    const rc_coeffs = roundConstantCoeffs();

    var tr = Transcript.init(LABEL);
    tr.absorbFelt(anchor);
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

    for (proof.queries) |q| {
        const q0 = tr.challengeIndex(half0);
        const a = q0;
        const an = (q0 + BLOWUP) % LDE_SIZE;
        const bb = q0 + half0;
        const bn = (bb + BLOWUP) % LDE_SIZE;

        if (!merkleVerifyRow(proof.trace_root, LDE_SIZE, a, q.cur_a.row, q.cur_a.path)) ok = false;
        if (!merkleVerifyRow(proof.trace_root, LDE_SIZE, an, q.next_a.row, q.next_a.path)) ok = false;
        if (!merkleVerifyRow(proof.trace_root, LDE_SIZE, bb, q.cur_b.row, q.cur_b.path)) ok = false;
        if (!merkleVerifyRow(proof.trace_root, LDE_SIZE, bn, q.next_b.row, q.next_b.path)) ok = false;
        if (!merkleVerify(proof.g_root, LDE_SIZE, a, q.g_a.val, q.g_a.path)) ok = false;
        if (!merkleVerify(proof.g_root, LDE_SIZE, bb, q.g_b.val, q.g_b.path)) ok = false;

        const x_a = field.mul(ldeOffset(), field.pow(ldeGen(), @intCast(a)));
        const x_b = field.mul(ldeOffset(), field.pow(ldeGen(), @intCast(bb)));
        const h_a = field.add(compositionAt(q.cur_a.row, q.next_a.row, x_a, anchor, comb, rcAt(rc_coeffs, x_a), m, omega_last, links), field.mul(zeta, q.g_a.val));
        const h_b = field.add(compositionAt(q.cur_b.row, q.next_b.row, x_b, anchor, comb, rcAt(rc_coeffs, x_b), m, omega_last, links), field.mul(zeta, q.g_b.val));
        if (h_a != q.fri.layers[0].a) ok = false;
        if (h_b != q.fri.layers[0].b) ok = false;

        for (0..NUM_FOLDS) |k| {
            const size_k = LDE_SIZE >> @intCast(k);
            const half_k = size_k / 2;
            const ai = q0 % half_k;
            const off_k = field.pow(ldeOffset(), @as(u64, 1) << @intCast(k));
            const gen_k = field.pow(ldeGen(), @as(u64, 1) << @intCast(k));
            const layer = q.fri.layers[k];
            if (!merkleVerify(proof.fri_roots[k], size_k, ai, layer.a, layer.path_a)) ok = false;
            if (!merkleVerify(proof.fri_roots[k], size_k, ai + half_k, layer.b, layer.path_b)) ok = false;
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

fn sampleSiblings(seed: u8) [DEPTH]Felt {
    var s: [DEPTH]Felt = undefined;
    for (0..DEPTH) |i| s[i] = @as(Felt, @intCast(i)) * 1000 + seed + 1;
    return s;
}

test "membership: valid path verifies" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const leaf: Felt = 123456789;
    const sib = sampleSiblings(7);
    const anchor = computeRoot(leaf, sib);
    const proof = try prove(a, leaf, sib);
    try testing.expect(try verify(a, anchor, proof));
}

test "membership: wrong anchor rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const leaf: Felt = 42;
    const sib = sampleSiblings(3);
    const proof = try prove(a, leaf, sib);
    try testing.expect(!try verify(a, computeRoot(leaf, sib) + 1, proof));
}

test "membership: tampered trace row rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const leaf: Felt = 42;
    const sib = sampleSiblings(3);
    const anchor = computeRoot(leaf, sib);
    var proof = try prove(a, leaf, sib);
    proof.queries[0].cur_a.row[0] = field.add(proof.queries[0].cur_a.row[0], 1);
    try testing.expect(!try verify(a, anchor, proof));
}

test "membership: a different leaf yields a different anchor" {
    // The proof binds to its own anchor; a proof for one leaf cannot pass for another's anchor.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const sib = sampleSiblings(1);
    const proof = try prove(a, 100, sib);
    try testing.expect(try verify(a, computeRoot(100, sib), proof));
    try testing.expect(!try verify(a, computeRoot(101, sib), proof));
}

test "membership: proofs are randomized (zero-knowledge)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const leaf: Felt = 9;
    const sib = sampleSiblings(2);
    const anchor = computeRoot(leaf, sib);
    const p1 = try prove(a, leaf, sib);
    const p2 = try prove(a, leaf, sib);
    // Different randomness ⇒ different FRI roots, but both verify against the same anchor.
    try testing.expect(!std.mem.eql(u8, &p1.fri_roots[0], &p2.fri_roots[0]));
    try testing.expect(try verify(a, anchor, p1));
    try testing.expect(try verify(a, anchor, p2));
}
