//! A first **integrated multi-region spend circuit** — the R3 assembly on a minimal example.
//!
//! It proves, in one FRI-STARK trace, knowledge of `(value, rho, nk)` such that:
//!   * **commitment**   `cm = H(value, rho)`          (region 0)
//!   * **nullifier**    `nf = H(nk, rho)`             (region 1)
//!   * **balance**      `value = send + fee`          (a linear constraint)
//!   * **consistency**  the `rho` used in both regions is the same cell
//!
//! with `cm, nf, send, fee` public. `H` is the arithmetization-friendly hash (`rescue`). This is
//! the smallest circuit that combines every mechanism a full shielded spend needs: multiple
//! in-circuit hash regions, a non-hash (balance) constraint, and — the load-bearing part — a
//! **copy constraint** wiring a witness value (`rho`) shared across regions, enforced by a
//! PLONK-style grand product (the id/σ specialization validated in `permutation.zig`).
//!
//! ## What this demonstrates for R3
//! The full spend is "more of the same": add a commitment with `recipient`/`rcm`, fold `cm` up a
//! Merkle path (`membership.zig`), include the position in the nullifier, and add the copy
//! constraints (cm→leaf, shared `nk`). The trace/constraint/wiring machinery is exactly what is
//! here. Remaining beyond that: ZK blinding + masked FRI (additive, see `stark.zig`), switching
//! the protocol's commitment/nullifier/Merkle hashing to the field hash, and node integration.
//!
//! ## Scope / honesty
//! Non-zero-knowledge (focus is the assembly + wiring; ZK is additive). `cm = H(value,rho)` drops
//! `recipient`/`rcm` for minimality. The engine is duplicated from the other modules pending a
//! generic-engine refactor. Not formally proven or audited.

const std = @import("std");
const Allocator = std.mem.Allocator;
const p = @import("primitives.zig");
const field = @import("field.zig");
const rescue = @import("rescue.zig");
const Felt = field.Felt;

const Hash = [32]u8;
const WIDTH = rescue.WIDTH; // 3 state columns

// ---------------------------------------------------------------------------------------
// Parameters
// ---------------------------------------------------------------------------------------

const BLOCK: usize = rescue.ROUNDS + 1; // 16 rows per hash region
const N: usize = 2 * BLOCK; // 32 (region 0 = rows 0..15, region 1 = rows 16..31)
const N_CONSTRAINTS: usize = WIDTH + 1 + 2 + 2 + 2; // 3 round + 1 balance + 2 cap + 2 output + 2 grand-product
const BLOWUP: usize = 32;
const LDE_SIZE: usize = N * BLOWUP; // 1024
const NUM_FOLDS: usize = 6;
const FINAL_SIZE: usize = LDE_SIZE >> NUM_FOLDS; // 16
const COMP_DEGREE_BOUND: usize = 256;
const FINAL_DEGREE_BOUND: usize = COMP_DEGREE_BOUND >> NUM_FOLDS; // 4
const NUM_QUERIES: usize = 40;

// Rows with special roles.
const ROW_R0_OUT: usize = BLOCK - 1; // 15: region-0 output
const ROW_R1_IN: usize = BLOCK; // 16: region-1 input
const ROW_LAST: usize = N - 1; // 31: region-1 output
// The rho copy constraint wires (col1, row 0) ↔ (col1, ROW_R1_IN).
const RHO_A: usize = 0;
const RHO_B: usize = ROW_R1_IN;

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
// AIR helpers: periodic round constants (period BLOCK), the σ wiring polynomial
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

/// σ over col1's position ids: identity except the 2-cycle (row RHO_A) ↔ (row RHO_B). The id of
/// (col1, r) is `ω^r`; this returns the interpolation coefficients of `σ(ω^r)`.
fn sigmaCoeffs() [N]Felt {
    const w = field.rootOfUnity(N);
    var vals: [N]Felt = undefined;
    for (0..N) |r| vals[r] = field.pow(w, @intCast(r));
    vals[RHO_A] = field.pow(w, RHO_B); // σ(id_A) = id_B
    vals[RHO_B] = field.pow(w, RHO_A); // σ(id_B) = id_A
    field.intt(&vals, w);
    return vals;
}

const Ctx = struct {
    cm: Felt,
    nf: Felt,
    send_plus_fee: Felt,
    beta: Felt,
    gamma: Felt,
    comb: [N_CONSTRAINTS]Felt,
    mds: [WIDTH][WIDTH]Felt,
    rc_coeffs: [WIDTH][BLOCK]Felt,
    sigma_coeffs: [N]Felt,
    w_r0_out: Felt, // ω^15
    w_r1_in: Felt, // ω^16
    w_last: Felt, // ω^31
};

/// Composition at one point. `cur = T(x)`, `next = T(ωx)`, `z = Z(x)`, `z_next = Z(ωx)`.
fn compositionAt(cur: [WIDTH]Felt, next: [WIDTH]Felt, z: Felt, z_next: Felt, x: Felt, ctx: Ctx) Felt {
    const x_n_minus_1 = field.sub(field.pow(x, N), 1);
    // Z_round vanishes on every transition row except the two non-round rows (region-0 output and
    // last), so the round constraint is enforced exactly on the 2·ROUNDS round-transitions.
    const z_round = field.mul(x_n_minus_1, field.inv(field.mul(field.sub(x, ctx.w_r0_out), field.sub(x, ctx.w_last))));
    const inv_zr = field.inv(z_round);
    const rc_row = rcAt(ctx.rc_coeffs, x);

    var sb: [WIDTH]Felt = undefined;
    for (0..WIDTH) |j| sb[j] = rescue.sbox(cur[j]);

    var cp: Felt = 0;
    // (a) Rescue round: next_i = Σ_j M[i][j]·cur_j^7 + rc_i.
    for (0..WIDTH) |i| {
        var roundi = rc_row[i];
        for (0..WIDTH) |j| roundi = field.add(roundi, field.mul(ctx.mds[i][j], sb[j]));
        const c = field.sub(next[i], roundi);
        cp = field.add(cp, field.mul(ctx.comb[i], field.mul(c, inv_zr)));
    }
    // (b) Balance: value (col0 at row 0) = send + fee.
    const inv_x1 = field.inv(field.sub(x, 1));
    cp = field.add(cp, field.mul(ctx.comb[WIDTH], field.mul(field.sub(cur[0], ctx.send_plus_fee), inv_x1)));
    // (c) Capacity 0 at both region inputs (row 0 and row ROW_R1_IN).
    cp = field.add(cp, field.mul(ctx.comb[WIDTH + 1], field.mul(cur[2], inv_x1)));
    cp = field.add(cp, field.mul(ctx.comb[WIDTH + 2], field.mul(cur[2], field.inv(field.sub(x, ctx.w_r1_in)))));
    // (d) Outputs: cm at region-0 output (row 15), nf at region-1 output (row 31).
    cp = field.add(cp, field.mul(ctx.comb[WIDTH + 3], field.mul(field.sub(cur[0], ctx.cm), field.inv(field.sub(x, ctx.w_r0_out)))));
    cp = field.add(cp, field.mul(ctx.comb[WIDTH + 4], field.mul(field.sub(cur[0], ctx.nf), field.inv(field.sub(x, ctx.w_last)))));
    // (e) Grand-product copy constraint on col1 (rho): Z(ωx)·D − Z(x)·Nu on all rows; Z(1)=1.
    //     Nu = col1 + β·id + γ (id = ω^r = x);  D = col1 + β·σ(x) + γ.
    const nu = field.add(field.add(cur[1], field.mul(ctx.beta, x)), ctx.gamma);
    const sigma_x = evalPoly(&ctx.sigma_coeffs, x);
    const d = field.add(field.add(cur[1], field.mul(ctx.beta, sigma_x)), ctx.gamma);
    const z_trans = field.sub(field.mul(z_next, d), field.mul(z, nu));
    cp = field.add(cp, field.mul(ctx.comb[WIDTH + 5], field.mul(z_trans, field.inv(x_n_minus_1))));
    cp = field.add(cp, field.mul(ctx.comb[WIDTH + 6], field.mul(field.sub(z, 1), inv_x1)));
    return cp;
}

// ---------------------------------------------------------------------------------------
// Trace
// ---------------------------------------------------------------------------------------

const PublicInputs = struct { cm: Felt, nf: Felt, send: Felt, fee: Felt };

/// Compute the public outputs for a witness (for tests / wallet use).
pub fn publicFor(value: Felt, rho: Felt, nk: Felt, fee: Felt) PublicInputs {
    return .{
        .cm = rescue.permute(.{ value, rho, 0 })[0],
        .nf = rescue.permute(.{ nk, rho, 0 })[0],
        .send = field.sub(value, fee),
        .fee = fee,
    };
}

/// The raw two-region trace rows. `rho_a` feeds the commitment region, `rho_b` the nullifier
/// region; an honest spend has `rho_a == rho_b` (the copy constraint enforces it).
fn buildRows(value: Felt, rho_a: Felt, rho_b: Felt, nk: Felt) [N][WIDTH]Felt {
    const m = rescue.mds();
    const rc = rescue.roundConstants();
    var rows: [N][WIDTH]Felt = undefined;
    rows[0] = .{ value, rho_a, 0 }; // region 0: cm = H(value, rho_a)
    for (0..rescue.ROUNDS) |r| rows[r + 1] = rescue.round(rows[r], m, rc[r]);
    rows[ROW_R1_IN] = .{ nk, rho_b, 0 }; // region 1: nf = H(nk, rho_b), loaded fresh
    for (0..rescue.ROUNDS) |r| rows[ROW_R1_IN + r + 1] = rescue.round(rows[ROW_R1_IN + r], m, rc[r]);
    return rows;
}

/// Build the two-region trace columns over the LDE.
fn buildTraceLde(allocator: Allocator, rows: [N][WIDTH]Felt) ![WIDTH][]Felt {
    var out: [WIDTH][]Felt = undefined;
    for (0..WIDTH) |i| {
        var col: [N]Felt = undefined;
        for (0..N) |r| col[r] = rows[r][i];
        out[i] = try valuesToLde(allocator, col);
    }
    return out;
}

/// The grand-product column on H for the rho copy constraint (over col1 values).
fn grandProduct(col1: [N]Felt, ctx: Ctx) [N]Felt {
    const w = field.rootOfUnity(N);
    var z: [N]Felt = undefined;
    z[0] = 1;
    for (0..N - 1) |r| {
        const xr = field.pow(w, @intCast(r));
        const id = xr;
        const sg = evalPoly(&ctx.sigma_coeffs, xr);
        const nu = field.add(field.add(col1[r], field.mul(ctx.beta, id)), ctx.gamma);
        const den = field.add(field.add(col1[r], field.mul(ctx.beta, sg)), ctx.gamma);
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
};
pub const Proof = struct {
    trace_root: Hash,
    z_root: Hash,
    fri_roots: [NUM_FOLDS]Hash,
    fri_final: []Felt,
    queries: []Query,
};

const LABEL = "lattica:spend:v1";

fn rowAt(cols: [WIDTH][]const Felt, idx: usize) [WIDTH]Felt {
    var row: [WIDTH]Felt = undefined;
    for (0..WIDTH) |i| row[i] = cols[i][idx];
    return row;
}

pub fn prove(allocator: Allocator, value: Felt, rho: Felt, nk: Felt, fee: Felt) !Proof {
    return proveRhos(allocator, value, rho, rho, nk, fee);
}

/// Prover allowing distinct rho per region — used by tests to exercise the copy constraint. An
/// honest spend sets `rho_a == rho_b`; if they differ the grand product cannot telescope to 1.
fn proveRhos(allocator: Allocator, value: Felt, rho_a: Felt, rho_b: Felt, nk: Felt, fee: Felt) !Proof {
    const pub_in = PublicInputs{
        .cm = rescue.permute(.{ value, rho_a, 0 })[0],
        .nf = rescue.permute(.{ nk, rho_b, 0 })[0],
        .send = field.sub(value, fee),
        .fee = fee,
    };
    const rows = buildRows(value, rho_a, rho_b, nk);

    const trace_lde = try buildTraceLde(allocator, rows);
    defer for (trace_lde) |c| allocator.free(c);
    var trace_c: [WIDTH][]const Felt = undefined;
    for (0..WIDTH) |i| trace_c[i] = trace_lde[i];

    var trace_tree = try MerkleTree.buildRows(allocator, trace_c);
    defer trace_tree.deinit();
    const trace_root = trace_tree.root();

    var tr = Transcript.init(LABEL);
    tr.absorbFelt(pub_in.cm);
    tr.absorbFelt(pub_in.nf);
    tr.absorbFelt(pub_in.send);
    tr.absorbFelt(pub_in.fee);
    tr.absorbHash(trace_root);
    const beta = tr.challengeFelt(); // round-1 challenges (after the trace commitment)
    const gamma = tr.challengeFelt();

    var ctx = Ctx{
        .cm = pub_in.cm,
        .nf = pub_in.nf,
        .send_plus_fee = field.add(pub_in.send, pub_in.fee),
        .beta = beta,
        .gamma = gamma,
        .comb = undefined,
        .mds = rescue.mds(),
        .rc_coeffs = roundConstantCoeffs(),
        .sigma_coeffs = sigmaCoeffs(),
        .w_r0_out = field.pow(field.rootOfUnity(N), ROW_R0_OUT),
        .w_r1_in = field.pow(field.rootOfUnity(N), ROW_R1_IN),
        .w_last = field.pow(field.rootOfUnity(N), ROW_LAST),
    };

    // Grand-product column from col1 (rho) values on H.
    var col1_h: [N]Felt = undefined;
    for (0..N) |r| col1_h[r] = rows[r][1];
    const z_h = grandProduct(col1_h, ctx);
    const z_lde = try valuesToLde(allocator, z_h);
    defer allocator.free(z_lde);
    var z_tree = try MerkleTree.build(allocator, z_lde);
    defer z_tree.deinit();
    const z_root = z_tree.root();

    tr.absorbHash(z_root);
    for (&ctx.comb) |*c| c.* = tr.challengeFelt();

    const h = try allocator.alloc(Felt, LDE_SIZE);
    defer allocator.free(h);
    var x = ldeOffset();
    for (0..LDE_SIZE) |j| {
        const cur = rowAt(trace_c, j);
        const next = rowAt(trace_c, (j + BLOWUP) % LDE_SIZE);
        h[j] = compositionAt(cur, next, z_lde[j], z_lde[(j + BLOWUP) % LDE_SIZE], x, ctx);
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
    }
    allocator.free(fri.final_layer);
    fri.deinit();
    return .{ .trace_root = trace_root, .z_root = z_root, .fri_roots = fri_roots, .fri_final = fri_final, .queries = queries };
}

pub fn verify(allocator: Allocator, pub_in: PublicInputs, proof: Proof) !bool {
    if (proof.fri_final.len != FINAL_SIZE or proof.queries.len != NUM_QUERIES) return false;

    var tr = Transcript.init(LABEL);
    tr.absorbFelt(pub_in.cm);
    tr.absorbFelt(pub_in.nf);
    tr.absorbFelt(pub_in.send);
    tr.absorbFelt(pub_in.fee);
    tr.absorbHash(proof.trace_root);
    const beta = tr.challengeFelt();
    const gamma = tr.challengeFelt();
    tr.absorbHash(proof.z_root);

    var ctx = Ctx{
        .cm = pub_in.cm,
        .nf = pub_in.nf,
        .send_plus_fee = field.add(pub_in.send, pub_in.fee),
        .beta = beta,
        .gamma = gamma,
        .comb = undefined,
        .mds = rescue.mds(),
        .rc_coeffs = roundConstantCoeffs(),
        .sigma_coeffs = sigmaCoeffs(),
        .w_r0_out = field.pow(field.rootOfUnity(N), ROW_R0_OUT),
        .w_r1_in = field.pow(field.rootOfUnity(N), ROW_R1_IN),
        .w_last = field.pow(field.rootOfUnity(N), ROW_LAST),
    };
    for (&ctx.comb) |*c| c.* = tr.challengeFelt();

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

        const x_a = field.mul(ldeOffset(), field.pow(ldeGen(), @intCast(a)));
        const x_b = field.mul(ldeOffset(), field.pow(ldeGen(), @intCast(bb)));
        if (compositionAt(q.cur_a.row, q.next_a.row, q.z_a.val, q.z_an.val, x_a, ctx) != q.fri.layers[0].a) ok = false;
        if (compositionAt(q.cur_b.row, q.next_b.row, q.z_b.val, q.z_bn.val, x_b, ctx) != q.fri.layers[0].b) ok = false;

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

test "spend: valid witness verifies" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const value: Felt = 1000;
    const rho: Felt = 0xABCDEF;
    const nk: Felt = 0x123456;
    const fee: Felt = 100;
    const pub_in = publicFor(value, rho, nk, fee);
    const proof = try prove(al, value, rho, nk, fee);
    try testing.expect(try verify(al, pub_in, proof));
}

test "spend: wrong cm rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    var pub_in = publicFor(1000, 7, 9, 100);
    const proof = try prove(al, 1000, 7, 9, 100);
    pub_in.cm = field.add(pub_in.cm, 1);
    try testing.expect(!try verify(al, pub_in, proof));
}

test "spend: wrong nf rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    var pub_in = publicFor(1000, 7, 9, 100);
    const proof = try prove(al, 1000, 7, 9, 100);
    pub_in.nf = field.add(pub_in.nf, 1);
    try testing.expect(!try verify(al, pub_in, proof));
}

test "spend: unbalanced (send+fee != value) rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    var pub_in = publicFor(1000, 7, 9, 100); // send=900, fee=100
    const proof = try prove(al, 1000, 7, 9, 100);
    pub_in.send = field.add(pub_in.send, 1); // now send+fee = 1001 != value
    try testing.expect(!try verify(al, pub_in, proof));
}

test "spend: tampered trace row rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const pub_in = publicFor(1000, 7, 9, 100);
    var proof = try prove(al, 1000, 7, 9, 100);
    proof.queries[0].cur_a.row[1] = field.add(proof.queries[0].cur_a.row[1], 1);
    try testing.expect(!try verify(al, pub_in, proof));
}

test "spend: proof binds to its own public inputs" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const proof = try prove(al, 1000, 7, 9, 100);
    try testing.expect(try verify(al, publicFor(1000, 7, 9, 100), proof));
    try testing.expect(!try verify(al, publicFor(1000, 8, 9, 100), proof)); // different rho ⇒ different cm,nf
}

test "spend: inconsistent rho across regions is rejected (the copy constraint bites)" {
    // The attack the copy constraint prevents: use rho_a in the commitment but a different rho_b
    // in the nullifier. cm,nf are each internally consistent, so without the wiring this would
    // pass — but the grand product forces a single rho and cannot telescope to 1, so it rejects.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const al = arena.allocator();
    const value: Felt = 1000;
    const rho_a: Felt = 7;
    const rho_b: Felt = 8; // != rho_a
    const nk: Felt = 9;
    const fee: Felt = 100;
    const pub_in = PublicInputs{
        .cm = rescue.permute(.{ value, rho_a, 0 })[0],
        .nf = rescue.permute(.{ nk, rho_b, 0 })[0],
        .send = field.sub(value, fee),
        .fee = fee,
    };
    const proof = try proveRhos(al, value, rho_a, rho_b, nk, fee);
    try testing.expect(!try verify(al, pub_in, proof));

    // Sanity: the same prover with rho_a == rho_b does verify.
    const good = try proveRhos(al, value, rho_a, rho_a, nk, fee);
    try testing.expect(try verify(al, .{ .cm = rescue.permute(.{ value, rho_a, 0 })[0], .nf = rescue.permute(.{ nk, rho_a, 0 })[0], .send = field.sub(value, fee), .fee = fee }, good));
}
