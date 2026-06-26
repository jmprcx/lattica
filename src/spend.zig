//! A **fully in-circuit shielded-spend proof** — the R3 goal on a self-contained example.
//!
//! One zero-... (non-ZK here; ZK is additive) FRI-STARK trace proves, for public
//! `(anchor, nf, send, fee)` and hidden witness `(value, rho, nk, siblings)`:
//!   1. **commitment opening** `cm = H(value, rho)`                         (region: block 0)
//!   2. **membership**         `cm` folds up the path to `anchor`           (blocks 1..DEPTH)
//!   3. **nullifier**          `nf = H(nk, rho)`                            (block DEPTH+1)
//!   4. **balance**            `value = send + fee`                         (linear constraint)
//! with `rho` the *same* in (1) and (3).  `H` is the arithmetization-friendly hash (`rescue`).
//!
//! `cm` is never revealed (ZK membership): it is an internal cell, carried into the Merkle leaf
//! by **adjacency** (the commitment block's output row precedes the first membership block's
//! input row), so it needs no copy constraint. The single copy constraint is the `rho` sharing
//! between the commitment and nullifier regions — the single-column grand product validated in
//! the permutation work. So all four constraints are folded with exactly one validated wiring
//! mechanism.
//!
//! ## Scope / honesty
//! Non-zero-knowledge (ZK blinding + masked FRI are additive, see `stark.zig`). The commitment is
//! `H(value, rho)` (omits `recipient`/`rcm`), and authorization is "knowledge of `nk` for `nf`
//! plus an opening of a committed leaf in the tree" (no explicit owner binding). The path is
//! leftmost-position. The engine is duplicated pending a generic-engine refactor. Not yet
//! node-integrated; not formally proven or audited. This demonstrates the full four-constraint
//! fold; production hardening (the items above, plus protocol-hash switch) remains.

const std = @import("std");
const Allocator = std.mem.Allocator;
const p = @import("primitives.zig");
const field = @import("field.zig");
const rescue = @import("rescue.zig");
const Felt = field.Felt;

const Hash = [32]u8;
const WIDTH = rescue.WIDTH; // 3 state columns

// ---------------------------------------------------------------------------------------
// Parameters / trace layout
// ---------------------------------------------------------------------------------------

const DEPTH: usize = 6; // Merkle levels (demo; production 32)
const BLOCK: usize = rescue.ROUNDS + 1; // 16 rows per hash region
const NUM_BLOCKS: usize = 2 + DEPTH; // commitment + DEPTH membership + nullifier = 8
const N: usize = NUM_BLOCKS * BLOCK; // 128
/// ZK: random coefficients masking each committed column. Must exceed the per-column open count
/// (4 rows/query · NUM_QUERIES = 128).
const TRACE_BLIND: usize = 160;
const BLOWUP: usize = 64;
const LDE_SIZE: usize = N * BLOWUP; // 8192
const NUM_FOLDS: usize = 9;
const FINAL_SIZE: usize = LDE_SIZE >> NUM_FOLDS; // 16
const COMP_DEGREE_BOUND: usize = 2048; // > round-constraint quotient degree (~1889 after blinding)
const FINAL_DEGREE_BOUND: usize = COMP_DEGREE_BOUND >> NUM_FOLDS; // 4
const NUM_QUERIES: usize = 32;
const N_CONSTRAINTS: usize = WIDTH + 1 + 1 + 1 + 2 + 2; // 3 round, 1 carry, 1 cap, 1 balance, 2 outputs, 2 grand-product

// Block index → first/last row.
fn blockStart(b: usize) usize {
    return b * BLOCK;
}
fn blockLast(b: usize) usize {
    return b * BLOCK + BLOCK - 1;
}
const CM_BLOCK: usize = 0;
const MEM_FIRST: usize = 1;
const MEM_LAST: usize = DEPTH; // block index of the last membership level
const NF_BLOCK: usize = NUM_BLOCKS - 1; // 7
const ROW_ANCHOR: usize = blockLast(MEM_LAST); // 111: membership output = anchor
const ROW_NF: usize = blockLast(NF_BLOCK); // 127
const ROW_NF_IN: usize = blockStart(NF_BLOCK); // 112
const RHO_A: usize = 0; // commitment-region rho cell (col1, row 0)
const RHO_B: usize = ROW_NF_IN; // nullifier-region rho cell (col1, row 112)

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
    return p.hashDomain("lattica:spend:leaf", &.{&field.toBytes(v)});
}
fn hashRow(row: [WIDTH]Felt) Hash {
    var bytes: [WIDTH][8]u8 = undefined;
    var fields: [WIDTH][]const u8 = undefined;
    for (0..WIDTH) |i| {
        bytes[i] = field.toBytes(row[i]);
        fields[i] = &bytes[i];
    }
    return p.hashDomain("lattica:spend:row", &fields);
}
fn hashNode(l: Hash, r: Hash) Hash {
    return p.hashDomain("lattica:spend:node", &.{ &l, &r });
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
fn verifyRow(root: Hash, n: usize, index: usize, row: [WIDTH]Felt, path: []const Hash) bool {
    return verifyHash(root, n, index, hashRow(row), path);
}

const Transcript = struct {
    state: Hash,
    counter: u64,
    fn init(label: []const u8) Transcript {
        return .{ .state = p.hashDomain("lattica:spend:transcript", &.{label}), .counter = 0 };
    }
    fn absorb(self: *Transcript, bytes: []const u8) void {
        self.state = p.hashDomain("lattica:spend:absorb", &.{ &self.state, bytes });
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
        return p.hashDomain("lattica:spend:squeeze", &.{ &self.state, &ctr });
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
fn valuesToLde(allocator: Allocator, values: [N]Felt) ![]Felt {
    var coeffs = values;
    field.intt(&coeffs, field.rootOfUnity(N));
    return coeffsToLde(allocator, &coeffs);
}

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

/// Interpolate `N` values over H, add the ZK blinding `Z_H·b` (random `b` of degree < TRACE_BLIND),
/// and evaluate over the LDE coset. Since `Z_H = x^N − 1` vanishes on H, the masked polynomial
/// equals the values on H (constraints unaffected) but every LDE opening is uniform.
fn valuesToBlindedLde(allocator: Allocator, values: [N]Felt, rng: *Rng) ![]Felt {
    var coeffs = values;
    field.intt(&coeffs, field.rootOfUnity(N));
    var mc = try allocator.alloc(Felt, N + TRACE_BLIND);
    defer allocator.free(mc);
    @memset(mc, 0);
    @memcpy(mc[0..N], &coeffs);
    var b: [TRACE_BLIND]Felt = undefined;
    rng.fillFelts(&b);
    for (0..TRACE_BLIND) |k| {
        mc[k] = field.sub(mc[k], b[k]);
        mc[N + k] = field.add(mc[N + k], b[k]);
    }
    return coeffsToLde(allocator, mc);
}

/// A uniformly random polynomial of degree < COMP_DEGREE_BOUND over the LDE — the FRI mask `g`.
fn buildRandomPolyLde(allocator: Allocator, rng: *Rng) ![]Felt {
    const coeffs = try allocator.alloc(Felt, COMP_DEGREE_BOUND);
    defer allocator.free(coeffs);
    rng.fillFelts(coeffs);
    return coeffsToLde(allocator, coeffs);
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
// AIR helpers
// ---------------------------------------------------------------------------------------

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
fn rcAt(rc_coeffs: [WIDTH][BLOCK]Felt, x: Felt) [WIDTH]Felt {
    const xb = field.pow(x, N / BLOCK);
    var out: [WIDTH]Felt = undefined;
    for (0..WIDTH) |i| out[i] = evalPoly(&rc_coeffs[i], xb);
    return out;
}

/// σ over col1: identity except the 2-cycle (row RHO_A) ↔ (row RHO_B), wiring the two `rho`
/// cells equal. Returns the interpolation coefficients of `σ(ω^r)`.
fn sigmaCoeffs() [N]Felt {
    const w = field.rootOfUnity(N);
    var vals: [N]Felt = undefined;
    for (0..N) |r| vals[r] = field.pow(w, @intCast(r));
    vals[RHO_A] = field.pow(w, RHO_B);
    vals[RHO_B] = field.pow(w, RHO_A);
    field.intt(&vals, w);
    return vals;
}

/// `Π_{r ∈ rows} (x − ω^r)`.
fn zProduct(x: Felt, comptime rows: []const usize, w: Felt) Felt {
    var z: Felt = 1;
    inline for (rows) |r| z = field.mul(z, field.sub(x, field.pow(w, @intCast(r))));
    return z;
}

// Row sets (block boundaries), computed from the layout.
const ROUND_EXCLUDED = blk: { // last row of every block
    var rows: [NUM_BLOCKS]usize = undefined;
    for (0..NUM_BLOCKS) |b| rows[b] = b * BLOCK + BLOCK - 1;
    break :blk rows;
};
const CARRY_ROWS = blk: { // last row of blocks 0..MEM_LAST-... i.e. the chained boundaries cm→memL0, memLd→memL(d+1)
    var rows: [MEM_LAST]usize = undefined; // blocks 0..MEM_LAST-1 → MEM_LAST carries
    for (0..MEM_LAST) |b| rows[b] = b * BLOCK + BLOCK - 1;
    break :blk rows;
};
const CAP_ROWS = blk: { // first row of every block
    var rows: [NUM_BLOCKS]usize = undefined;
    for (0..NUM_BLOCKS) |b| rows[b] = b * BLOCK;
    break :blk rows;
};

const Ctx = struct {
    anchor: Felt,
    nf: Felt,
    send_plus_fee: Felt,
    beta: Felt,
    gamma: Felt,
    comb: [N_CONSTRAINTS]Felt,
    mds: [WIDTH][WIDTH]Felt,
    rc_coeffs: [WIDTH][BLOCK]Felt,
    sigma_coeffs: [N]Felt,
    w: Felt, // ω = rootOfUnity(N)
    w_anchor: Felt, // ω^ROW_ANCHOR
    w_nf: Felt, // ω^ROW_NF
};

fn compositionAt(cur: [WIDTH]Felt, next: [WIDTH]Felt, z: Felt, z_next: Felt, x: Felt, ctx: Ctx) Felt {
    const x_n_minus_1 = field.sub(field.pow(x, N), 1);
    const z_round = field.mul(x_n_minus_1, field.inv(zProduct(x, &ROUND_EXCLUDED, ctx.w)));
    const inv_zr = field.inv(z_round);
    const inv_zcarry = field.inv(zProduct(x, &CARRY_ROWS, ctx.w));
    const inv_zcap = field.inv(zProduct(x, &CAP_ROWS, ctx.w));
    const inv_x1 = field.inv(field.sub(x, 1));
    const rc_row = rcAt(ctx.rc_coeffs, x);

    var sb: [WIDTH]Felt = undefined;
    for (0..WIDTH) |j| sb[j] = rescue.sbox(cur[j]);

    var cp: Felt = 0;
    // (a) Rescue round on the round rows.
    for (0..WIDTH) |i| {
        var roundi = rc_row[i];
        for (0..WIDTH) |j| roundi = field.add(roundi, field.mul(ctx.mds[i][j], sb[j]));
        cp = field.add(cp, field.mul(ctx.comb[i], field.mul(field.sub(next[i], roundi), inv_zr)));
    }
    // (b) Carry on the chained boundaries: the running hash `cur[0]` must be one of the next
    //     block's two inputs (general Merkle position — left or right child). The other input is
    //     the free sibling. Degree-2 "one-of" constraint; the position bit stays hidden.
    const carry = field.mul(field.sub(next[0], cur[0]), field.sub(next[1], cur[0]));
    cp = field.add(cp, field.mul(ctx.comb[WIDTH], field.mul(carry, inv_zcarry)));
    // (c) Capacity 0 at every block start.
    cp = field.add(cp, field.mul(ctx.comb[WIDTH + 1], field.mul(cur[2], inv_zcap)));
    // (d) Balance: value (col0, row 0) = send + fee.
    cp = field.add(cp, field.mul(ctx.comb[WIDTH + 2], field.mul(field.sub(cur[0], ctx.send_plus_fee), inv_x1)));
    // (e) Outputs: anchor at the membership output row, nf at the nullifier output row.
    cp = field.add(cp, field.mul(ctx.comb[WIDTH + 3], field.mul(field.sub(cur[0], ctx.anchor), field.inv(field.sub(x, ctx.w_anchor)))));
    cp = field.add(cp, field.mul(ctx.comb[WIDTH + 4], field.mul(field.sub(cur[0], ctx.nf), field.inv(field.sub(x, ctx.w_nf)))));
    // (f) Grand-product copy constraint on col1 (rho): Z(ωx)·D − Z(x)·Nu on all rows; Z(1)=1.
    const nu = field.add(field.add(cur[1], field.mul(ctx.beta, x)), ctx.gamma);
    const sigma_x = evalPoly(&ctx.sigma_coeffs, x);
    const d = field.add(field.add(cur[1], field.mul(ctx.beta, sigma_x)), ctx.gamma);
    cp = field.add(cp, field.mul(ctx.comb[WIDTH + 5], field.mul(field.sub(field.mul(z_next, d), field.mul(z, nu)), field.inv(x_n_minus_1))));
    cp = field.add(cp, field.mul(ctx.comb[WIDTH + 6], field.mul(field.sub(z, 1), inv_x1)));
    return cp;
}

// ---------------------------------------------------------------------------------------
// Witness / public inputs
// ---------------------------------------------------------------------------------------

pub const PublicInputs = struct { anchor: Felt, nf: Felt, send: Felt, fee: Felt };

/// Compute the public inputs for a witness. `positions[d] = true` means the running hash is the
/// *right* child at level `d` (sibling on the left); `false` means left child.
pub fn publicFor(value: Felt, rho: Felt, nk: Felt, fee: Felt, siblings: [DEPTH]Felt, positions: [DEPTH]bool) PublicInputs {
    const cm = rescue.permute(.{ value, rho, 0 })[0];
    var cur = cm;
    for (0..DEPTH) |d| {
        cur = if (positions[d]) rescue.permute(.{ siblings[d], cur, 0 })[0] else rescue.permute(.{ cur, siblings[d], 0 })[0];
    }
    return .{ .anchor = cur, .nf = rescue.permute(.{ nk, rho, 0 })[0], .send = field.sub(value, fee), .fee = fee };
}

/// Raw trace rows. `rho_a` feeds the commitment, `rho_b` the nullifier (honest: equal).
fn buildRows(value: Felt, rho_a: Felt, rho_b: Felt, nk: Felt, siblings: [DEPTH]Felt, positions: [DEPTH]bool) [N][WIDTH]Felt {
    const m = rescue.mds();
    const rc = rescue.roundConstants();
    var rows: [N][WIDTH]Felt = undefined;

    // Block 0: cm = H(value, rho_a).
    rows[blockStart(CM_BLOCK)] = .{ value, rho_a, 0 };
    for (0..rescue.ROUNDS) |r| rows[blockStart(CM_BLOCK) + r + 1] = rescue.round(rows[blockStart(CM_BLOCK) + r], m, rc[r]);

    // Blocks 1..DEPTH: membership. The running hash is placed left or right per the position bit;
    // the sibling takes the other input. Capacity 0.
    for (0..DEPTH) |level| {
        const b = MEM_FIRST + level;
        const prev_out = rows[blockLast(b - 1)][0];
        rows[blockStart(b)] = if (positions[level]) .{ siblings[level], prev_out, 0 } else .{ prev_out, siblings[level], 0 };
        for (0..rescue.ROUNDS) |r| rows[blockStart(b) + r + 1] = rescue.round(rows[blockStart(b) + r], m, rc[r]);
    }

    // Block NF_BLOCK: nf = H(nk, rho_b), loaded fresh.
    rows[blockStart(NF_BLOCK)] = .{ nk, rho_b, 0 };
    for (0..rescue.ROUNDS) |r| rows[blockStart(NF_BLOCK) + r + 1] = rescue.round(rows[blockStart(NF_BLOCK) + r], m, rc[r]);
    return rows;
}

fn buildTraceLde(allocator: Allocator, rows: [N][WIDTH]Felt, rng: *Rng) ![WIDTH][]Felt {
    var out: [WIDTH][]Felt = undefined;
    for (0..WIDTH) |i| {
        var col: [N]Felt = undefined;
        for (0..N) |r| col[r] = rows[r][i];
        out[i] = try valuesToBlindedLde(allocator, col, rng);
    }
    return out;
}

fn grandProduct(col1: [N]Felt, ctx: Ctx) [N]Felt {
    var z: [N]Felt = undefined;
    z[0] = 1;
    for (0..N - 1) |r| {
        const xr = field.pow(ctx.w, @intCast(r));
        const nu = field.add(field.add(col1[r], field.mul(ctx.beta, xr)), ctx.gamma);
        const den = field.add(field.add(col1[r], field.mul(ctx.beta, evalPoly(&ctx.sigma_coeffs, xr))), ctx.gamma);
        z[r + 1] = field.mul(z[r], field.mul(nu, field.inv(den)));
    }
    return z;
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
    z_a: ValOpen,
    z_an: ValOpen,
    z_b: ValOpen,
    z_bn: ValOpen,
    g_a: ValOpen,
    g_b: ValOpen,
};
pub const Proof = struct {
    trace_root: Hash,
    z_root: Hash,
    g_root: Hash,
    fri_roots: [NUM_FOLDS]Hash,
    fri_final: []Felt,
    queries: []Query,
};

const LABEL = "lattica:spend:v2-full";

fn rowAt(cols: [WIDTH][]const Felt, idx: usize) [WIDTH]Felt {
    var row: [WIDTH]Felt = undefined;
    for (0..WIDTH) |i| row[i] = cols[i][idx];
    return row;
}

fn newCtx(pub_in: PublicInputs, beta: Felt, gamma: Felt) Ctx {
    const w = field.rootOfUnity(N);
    return .{
        .anchor = pub_in.anchor,
        .nf = pub_in.nf,
        .send_plus_fee = field.add(pub_in.send, pub_in.fee),
        .beta = beta,
        .gamma = gamma,
        .comb = undefined,
        .mds = rescue.mds(),
        .rc_coeffs = roundConstantCoeffs(),
        .sigma_coeffs = sigmaCoeffs(),
        .w = w,
        .w_anchor = field.pow(w, ROW_ANCHOR),
        .w_nf = field.pow(w, ROW_NF),
    };
}

pub fn prove(allocator: Allocator, value: Felt, rho: Felt, nk: Felt, fee: Felt, siblings: [DEPTH]Felt, positions: [DEPTH]bool) !Proof {
    return proveRhos(allocator, value, rho, rho, nk, fee, siblings, positions);
}

/// Prover allowing distinct rho per region — used by tests to exercise the copy constraint.
fn proveRhos(allocator: Allocator, value: Felt, rho_a: Felt, rho_b: Felt, nk: Felt, fee: Felt, siblings: [DEPTH]Felt, positions: [DEPTH]bool) !Proof {
    const cm = rescue.permute(.{ value, rho_a, 0 })[0];
    var cur_root = cm;
    for (0..DEPTH) |d| {
        cur_root = if (positions[d]) rescue.permute(.{ siblings[d], cur_root, 0 })[0] else rescue.permute(.{ cur_root, siblings[d], 0 })[0];
    }
    const pub_in = PublicInputs{
        .anchor = cur_root,
        .nf = rescue.permute(.{ nk, rho_b, 0 })[0],
        .send = field.sub(value, fee),
        .fee = fee,
    };
    const rows = buildRows(value, rho_a, rho_b, nk, siblings, positions);

    var rng = Rng.init();
    const trace_lde = try buildTraceLde(allocator, rows, &rng);
    defer for (trace_lde) |c| allocator.free(c);
    var trace_c: [WIDTH][]const Felt = undefined;
    for (0..WIDTH) |i| trace_c[i] = trace_lde[i];

    var trace_tree = try MerkleTree.buildRows(allocator, trace_c);
    defer trace_tree.deinit();
    const trace_root = trace_tree.root();

    var tr = Transcript.init(LABEL);
    inline for (.{ pub_in.anchor, pub_in.nf, pub_in.send, pub_in.fee }) |v| tr.absorbFelt(v);
    tr.absorbHash(trace_root);
    const beta = tr.challengeFelt();
    const gamma = tr.challengeFelt();

    var ctx = newCtx(pub_in, beta, gamma);
    var col1_h: [N]Felt = undefined;
    for (0..N) |r| col1_h[r] = rows[r][1];
    const z_h = grandProduct(col1_h, ctx);
    const z_lde = try valuesToBlindedLde(allocator, z_h, &rng);
    defer allocator.free(z_lde);
    const g_lde = try buildRandomPolyLde(allocator, &rng);
    defer allocator.free(g_lde);
    var z_tree = try MerkleTree.build(allocator, z_lde);
    defer z_tree.deinit();
    var g_tree = try MerkleTree.build(allocator, g_lde);
    defer g_tree.deinit();
    const z_root = z_tree.root();
    const g_root = g_tree.root();

    tr.absorbHash(z_root);
    tr.absorbHash(g_root);
    for (&ctx.comb) |*c| c.* = tr.challengeFelt();
    const zeta = tr.challengeFelt();

    // FRI input H = CP + ζ·g (mask the low-degree test for zero-knowledge).
    const h = try allocator.alloc(Felt, LDE_SIZE);
    defer allocator.free(h);
    var x = ldeOffset();
    for (0..LDE_SIZE) |j| {
        const cur = rowAt(trace_c, j);
        const next = rowAt(trace_c, (j + BLOWUP) % LDE_SIZE);
        const cp = compositionAt(cur, next, z_lde[j], z_lde[(j + BLOWUP) % LDE_SIZE], x, ctx);
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
        q.z_a = .{ .val = z_lde[a], .path = try z_tree.open(allocator, a) };
        q.z_an = .{ .val = z_lde[an], .path = try z_tree.open(allocator, an) };
        q.z_b = .{ .val = z_lde[bb], .path = try z_tree.open(allocator, bb) };
        q.z_bn = .{ .val = z_lde[bn], .path = try z_tree.open(allocator, bn) };
        q.g_a = .{ .val = g_lde[a], .path = try g_tree.open(allocator, a) };
        q.g_b = .{ .val = g_lde[bb], .path = try g_tree.open(allocator, bb) };
    }
    allocator.free(fri.final_layer);
    fri.deinit();
    return .{ .trace_root = trace_root, .z_root = z_root, .g_root = g_root, .fri_roots = fri_roots, .fri_final = fri_final, .queries = queries };
}

pub fn verify(allocator: Allocator, pub_in: PublicInputs, proof: Proof) !bool {
    if (proof.fri_final.len != FINAL_SIZE or proof.queries.len != NUM_QUERIES) return false;

    var tr = Transcript.init(LABEL);
    inline for (.{ pub_in.anchor, pub_in.nf, pub_in.send, pub_in.fee }) |v| tr.absorbFelt(v);
    tr.absorbHash(proof.trace_root);
    const beta = tr.challengeFelt();
    const gamma = tr.challengeFelt();
    tr.absorbHash(proof.z_root);
    tr.absorbHash(proof.g_root);
    var ctx = newCtx(pub_in, beta, gamma);
    for (&ctx.comb) |*c| c.* = tr.challengeFelt();
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

        if (!verifyRow(proof.trace_root, LDE_SIZE, a, q.cur_a.row, q.cur_a.path)) ok = false;
        if (!verifyRow(proof.trace_root, LDE_SIZE, an, q.next_a.row, q.next_a.path)) ok = false;
        if (!verifyRow(proof.trace_root, LDE_SIZE, bb, q.cur_b.row, q.cur_b.path)) ok = false;
        if (!verifyRow(proof.trace_root, LDE_SIZE, bn, q.next_b.row, q.next_b.path)) ok = false;
        if (!verifyLeaf(proof.z_root, LDE_SIZE, a, q.z_a.val, q.z_a.path)) ok = false;
        if (!verifyLeaf(proof.z_root, LDE_SIZE, an, q.z_an.val, q.z_an.path)) ok = false;
        if (!verifyLeaf(proof.z_root, LDE_SIZE, bb, q.z_b.val, q.z_b.path)) ok = false;
        if (!verifyLeaf(proof.z_root, LDE_SIZE, bn, q.z_bn.val, q.z_bn.path)) ok = false;
        if (!verifyLeaf(proof.g_root, LDE_SIZE, a, q.g_a.val, q.g_a.path)) ok = false;
        if (!verifyLeaf(proof.g_root, LDE_SIZE, bb, q.g_b.val, q.g_b.path)) ok = false;

        // ALI: the FRI input H = CP(trace,Z) + ζ·g at both layer-0 query points.
        const x_a = field.mul(ldeOffset(), field.pow(ldeGen(), @intCast(a)));
        const x_b = field.mul(ldeOffset(), field.pow(ldeGen(), @intCast(bb)));
        const h_a = field.add(compositionAt(q.cur_a.row, q.next_a.row, q.z_a.val, q.z_an.val, x_a, ctx), field.mul(zeta, q.g_a.val));
        const h_b = field.add(compositionAt(q.cur_b.row, q.next_b.row, q.z_b.val, q.z_bn.val, x_b, ctx), field.mul(zeta, q.g_b.val));
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

fn sampleSiblings(seed: u64) [DEPTH]Felt {
    var s: [DEPTH]Felt = undefined;
    for (0..DEPTH) |i| s[i] = (@as(Felt, @intCast(i)) *% 1099511627791 +% seed +% 1) % field.P;
    return s;
}

/// A mixed left/right path (general position) derived from a seed bit pattern.
fn samplePositions(bits: u8) [DEPTH]bool {
    var pos: [DEPTH]bool = undefined;
    for (0..DEPTH) |i| pos[i] = (bits >> @intCast(i)) & 1 == 1;
    return pos;
}

test "spend: valid full spend verifies (general positions)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const sib = sampleSiblings(1);
    const pos = samplePositions(0b101101); // mixed left/right path
    const pub_in = publicFor(1000, 0xABCDEF, 0x123456, 100, sib, pos);
    const proof = try prove(al, 1000, 0xABCDEF, 0x123456, 100, sib, pos);
    try testing.expect(try verify(al, pub_in, proof));
}

test "spend: every position pattern verifies" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const sib = sampleSiblings(11);
    // A few representative patterns including all-left and all-right.
    for ([_]u8{ 0b000000, 0b111111, 0b010101, 0b110010 }) |bits| {
        const pos = samplePositions(bits);
        const pub_in = publicFor(500, 3, 4, 50, sib, pos);
        const proof = try prove(al, 500, 3, 4, 50, sib, pos);
        try testing.expect(try verify(al, pub_in, proof));
    }
}

test "spend: wrong anchor rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const sib = sampleSiblings(2);
    const pos = samplePositions(0b011010);
    var pub_in = publicFor(1000, 7, 9, 100, sib, pos);
    const proof = try prove(al, 1000, 7, 9, 100, sib, pos);
    pub_in.anchor = field.add(pub_in.anchor, 1);
    try testing.expect(!try verify(al, pub_in, proof));
}

test "spend: wrong nf rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const sib = sampleSiblings(3);
    const pos = samplePositions(0b001100);
    var pub_in = publicFor(1000, 7, 9, 100, sib, pos);
    const proof = try prove(al, 1000, 7, 9, 100, sib, pos);
    pub_in.nf = field.add(pub_in.nf, 1);
    try testing.expect(!try verify(al, pub_in, proof));
}

test "spend: unbalanced rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const sib = sampleSiblings(4);
    const pos = samplePositions(0b100001);
    var pub_in = publicFor(1000, 7, 9, 100, sib, pos);
    const proof = try prove(al, 1000, 7, 9, 100, sib, pos);
    pub_in.send = field.add(pub_in.send, 1);
    try testing.expect(!try verify(al, pub_in, proof));
}

test "spend: tampered trace row rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const sib = sampleSiblings(5);
    const pos = samplePositions(0b010010);
    const pub_in = publicFor(1000, 7, 9, 100, sib, pos);
    var proof = try prove(al, 1000, 7, 9, 100, sib, pos);
    proof.queries[0].cur_a.row[1] = field.add(proof.queries[0].cur_a.row[1], 1);
    try testing.expect(!try verify(al, pub_in, proof));
}

test "spend: inconsistent rho across regions rejected (copy constraint bites)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const sib = sampleSiblings(6);
    const pos = samplePositions(0b101010);
    const value: Felt = 1000;
    const rho_a: Felt = 7;
    const rho_b: Felt = 8; // != rho_a
    const nk: Felt = 9;
    const fee: Felt = 100;
    var cur_root = rescue.permute(.{ value, rho_a, 0 })[0];
    for (0..DEPTH) |d| cur_root = if (pos[d]) rescue.permute(.{ sib[d], cur_root, 0 })[0] else rescue.permute(.{ cur_root, sib[d], 0 })[0];
    const pub_in = PublicInputs{ .anchor = cur_root, .nf = rescue.permute(.{ nk, rho_b, 0 })[0], .send = field.sub(value, fee), .fee = fee };
    const proof = try proveRhos(al, value, rho_a, rho_b, nk, fee, sib, pos);
    try testing.expect(!try verify(al, pub_in, proof));
}

test "spend: a wrong sibling (not the real path) rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const sib = sampleSiblings(7);
    const pos = samplePositions(0b001011);
    const pub_in = publicFor(1000, 7, 9, 100, sib, pos); // anchor for the true path
    var wrong = sib;
    wrong[2] = field.add(wrong[2], 1); // different path ⇒ different root ≠ anchor
    const proof = try prove(al, 1000, 7, 9, 100, wrong, pos);
    try testing.expect(!try verify(al, pub_in, proof));
}

test "spend: a wrong position (different path shape) rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const sib = sampleSiblings(9);
    const pos = samplePositions(0b010101);
    const pub_in = publicFor(1000, 7, 9, 100, sib, pos); // anchor for this position pattern
    const other_pos = samplePositions(0b010111); // flip one position bit
    const proof = try prove(al, 1000, 7, 9, 100, sib, other_pos); // folds to a different root
    try testing.expect(!try verify(al, pub_in, proof));
}

test "spend: proofs are randomized (zero-knowledge blinding)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const sib = sampleSiblings(8);
    const pos = samplePositions(0b110011);
    const pub_in = publicFor(1000, 7, 9, 100, sib, pos);
    const p1 = try prove(al, 1000, 7, 9, 100, sib, pos);
    const p2 = try prove(al, 1000, 7, 9, 100, sib, pos);
    // Fresh blinding each time ⇒ different commitments, but both verify against the same publics.
    try testing.expect(!std.mem.eql(u8, &p1.trace_root, &p2.trace_root));
    try testing.expect(try verify(al, pub_in, p1));
    try testing.expect(try verify(al, pub_in, p2));
}
