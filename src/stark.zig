//! A self-contained, transparent, hash-based **FRI-STARK** for the Lattica spend-authorization
//! relation — no elliptic curves, no trusted setup, soundness resting only on SHA3 collision
//! resistance. This replaces the earlier placeholder in `circuit.zig` with a genuine proof.
//!
//! The statement proved (in the same shape as the reference AIR): the prover knows a secret
//! `s` such that iterating the transition `x → x³ + C` for `NUM_STEPS` steps over the
//! Goldilocks field reaches the public image, **without revealing `s`** (only the final state
//! is asserted; the starting secret is never opened).
//!
//! Construction (the classic FRI-STARK / "STARK101" shape):
//!  1. Build the execution trace and interpolate it (iNTT) into the trace polynomial.
//!  2. Evaluate it on a larger LDE coset (blowup ×8) and Merkle-commit those evaluations.
//!  3. Form the composition polynomial — a Fiat-Shamir-random combination of the transition
//!     and boundary constraint quotients — and Merkle-commit its LDE.
//!  4. Run FRI on the composition evaluations, folding to a constant, committing each layer.
//!  5. At Fiat-Shamir-random query positions, open the trace, the composition, and every FRI
//!     layer with Merkle proofs. The verifier re-derives all challenges and checks: Merkle
//!     paths, the algebraic link composition⇔trace at each query (binding constraints to the
//!     trace), and FRI fold consistency down to the committed constant.

const std = @import("std");
const Allocator = std.mem.Allocator;
const p = @import("primitives.zig");
const field = @import("field.zig");
const Felt = field.Felt;

const Hash = [32]u8;

// ---------------------------------------------------------------------------------------
// Merkle tree over field elements (SHA3, domain-separated)
// ---------------------------------------------------------------------------------------

fn hashLeaf(v: Felt) Hash {
    return p.hashDomain("lattica:stark:leaf", &.{&field.toBytes(v)});
}

fn hashNode(l: Hash, r: Hash) Hash {
    return p.hashDomain("lattica:stark:node", &.{ &l, &r });
}

/// A complete binary Merkle tree over a power-of-two number of field-element leaves, stored in
/// a 1-indexed heap array (`nodes[1]` is the root, leaves live at `nodes[n..2n]`).
const MerkleTree = struct {
    allocator: Allocator,
    n: usize,
    nodes: []Hash,

    fn build(allocator: Allocator, leaves: []const Felt) !MerkleTree {
        const n = leaves.len;
        std.debug.assert(n != 0 and (n & (n - 1)) == 0);
        const nodes = try allocator.alloc(Hash, 2 * n);
        for (leaves, 0..) |v, i| nodes[n + i] = hashLeaf(v);
        var i: usize = n - 1;
        while (i >= 1) : (i -= 1) {
            nodes[i] = hashNode(nodes[2 * i], nodes[2 * i + 1]);
            if (i == 1) break;
        }
        return .{ .allocator = allocator, .n = n, .nodes = nodes };
    }

    fn deinit(self: *MerkleTree) void {
        self.allocator.free(self.nodes);
    }

    fn root(self: MerkleTree) Hash {
        return self.nodes[1];
    }

    /// Sibling path from leaf `index` up to (excluding) the root.
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

/// Recompute the root from a leaf value and its sibling path, and compare to `root`.
fn merkleVerify(root: Hash, n: usize, index: usize, leaf_val: Felt, path: []const Hash) bool {
    if (path.len != std.math.log2_int(usize, n)) return false;
    var h = hashLeaf(leaf_val);
    var idx = index;
    for (path) |sib| {
        h = if (idx & 1 == 0) hashNode(h, sib) else hashNode(sib, h);
        idx >>= 1;
    }
    return std.mem.eql(u8, &h, &root);
}

// ---------------------------------------------------------------------------------------
// Fiat-Shamir transcript (SHA3 duplex)
// ---------------------------------------------------------------------------------------

/// A hash-based transcript. `absorb` mixes prover messages into the state; `challenge*` squeeze
/// pseudo-random challenges. Squeezes between absorbs are distinct (a counter is mixed in).
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
        const h = self.squeeze();
        return field.fromBytes(h[0..16]);
    }

    fn challengeIndex(self: *Transcript, bound: usize) usize {
        const h = self.squeeze();
        const x = std.mem.readInt(u64, h[0..8], .little);
        return @intCast(x % bound);
    }
};

// ---------------------------------------------------------------------------------------
// Protocol parameters
// ---------------------------------------------------------------------------------------

/// Trace length (steps in the authorization chain); a power of two.
const N: usize = 1024;
/// LDE blowup factor (RS code rate 1/BLOWUP).
const BLOWUP: usize = 8;
/// Size of the low-degree-extension evaluation domain.
const LDE_SIZE: usize = N * BLOWUP; // 8192
/// Number of FRI folding rounds.
const NUM_FOLDS: usize = 7;
/// Size of the final (uncommitted) FRI layer, sent in the clear.
const FINAL_SIZE: usize = LDE_SIZE >> NUM_FOLDS; // 64
/// Degree bound asserted for the composition polynomial (> its true max degree 2046).
const COMP_DEGREE_BOUND: usize = 2048;
/// Degree bound the final FRI layer must satisfy.
const FINAL_DEGREE_BOUND: usize = COMP_DEGREE_BOUND >> NUM_FOLDS; // 16
/// Number of FRI query repetitions (soundness amplification).
const NUM_QUERIES: usize = 32;
/// Round constant of the transition `x -> x^3 + C`.
const C_CONST: Felt = 42;

/// Coset shift for the LDE domain: a generator of F_p^*, so the coset is disjoint from every
/// subgroup used (keeps the vanishing polynomials nonzero on the domain).
fn ldeOffset() Felt {
    return field.GENERATOR;
}
/// Generator of the LDE evaluation domain (a primitive LDE_SIZE-th root of unity).
fn ldeGen() Felt {
    return field.rootOfUnity(LDE_SIZE);
}

// ---------------------------------------------------------------------------------------
// FRI: low-degree test by repeated folding
// ---------------------------------------------------------------------------------------

const FriQueryLayer = struct {
    a: Felt,
    b: Felt,
    path_a: []Hash,
    path_b: []Hash,
};

const FriQuery = struct {
    layers: [NUM_FOLDS]FriQueryLayer,
};

const FriProof = struct {
    roots: [NUM_FOLDS]Hash,
    final_layer: []Felt, // FINAL_SIZE values, in the clear
    queries: []FriQuery, // one per derived query position
};

/// Fold one FRI layer: `next[i] = even(x_i²) + beta·odd(x_i²)`, where `even`/`odd` are the
/// even/odd parts of the layer polynomial recovered from the ± pair `(cur[i], cur[i+half])`.
fn friFold(allocator: Allocator, cur: []const Felt, beta: Felt, offset: Felt, gen: Felt) ![]Felt {
    const half = cur.len / 2;
    const next = try allocator.alloc(Felt, half);
    const inv2 = field.inv(2);
    var x = offset; // x_i = offset · gen^i
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

/// Holds the committed FRI layers so individual query positions can be opened on demand (used
/// by the STARK, which interleaves FRI openings with trace openings for the same positions).
const FriProver = struct {
    allocator: Allocator,
    layer_evals: [NUM_FOLDS][]Felt,
    trees: [NUM_FOLDS]MerkleTree,
    roots: [NUM_FOLDS]Hash,
    betas: [NUM_FOLDS]Felt,
    final_layer: []Felt,

    /// Commit all fold layers into `transcript`, drawing a fold challenge per layer and finally
    /// absorbing the in-the-clear final layer.
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

    /// Open all layers at query position `q0` (in `[0, LDE_SIZE/2)`).
    fn open(self: FriProver, allocator: Allocator, q0: usize) !FriQuery {
        var q: FriQuery = undefined;
        for (0..NUM_FOLDS) |k| {
            const half_k = (LDE_SIZE >> @intCast(k)) / 2;
            const a_idx = q0 % half_k;
            const b_idx = a_idx + half_k;
            q.layers[k] = .{
                .a = self.layer_evals[k][a_idx],
                .b = self.layer_evals[k][b_idx],
                .path_a = try self.trees[k].open(allocator, a_idx),
                .path_b = try self.trees[k].open(allocator, b_idx),
            };
        }
        return q;
    }

    /// Free the committed layers and trees. Does not free `final_layer` (the caller keeps it).
    fn deinit(self: *FriProver) void {
        for (0..NUM_FOLDS) |k| {
            self.trees[k].deinit();
            self.allocator.free(self.layer_evals[k]);
        }
    }
};

/// Prove that `evals` (over the LDE coset) is close to a low-degree codeword. Caller owns the
/// result (free with `friFree`).
fn friProve(allocator: Allocator, transcript: *Transcript, evals: []const Felt) !FriProof {
    var prover = try FriProver.commit(allocator, transcript, evals);
    const roots = prover.roots;
    const final_layer = try allocator.dupe(Felt, prover.final_layer);
    const queries = try allocator.alloc(FriQuery, NUM_QUERIES);
    for (queries) |*q| {
        const q0 = transcript.challengeIndex(LDE_SIZE / 2);
        q.* = try prover.open(allocator, q0);
    }
    allocator.free(prover.final_layer);
    prover.deinit();
    return .{ .roots = roots, .final_layer = final_layer, .queries = queries };
}

/// Result of FRI verification: whether it passed, plus the layer-0 opened values per query (so
/// the STARK can bind them to the trace).
const FriVerifyResult = struct {
    ok: bool,
    /// For query i: the position q0 and the two opened layer-0 values.
    q0: [NUM_QUERIES]usize,
    a0: [NUM_QUERIES]Felt,
    b0: [NUM_QUERIES]Felt,
};

fn friCheckFinalLowDegree(allocator: Allocator, final_layer: []const Felt) !bool {
    const gen_f = field.pow(ldeGen(), @as(u64, 1) << @intCast(NUM_FOLDS));
    const coeffs = try allocator.dupe(Felt, final_layer);
    defer allocator.free(coeffs);
    field.intt(coeffs, gen_f);
    for (coeffs[FINAL_DEGREE_BOUND..]) |c| {
        if (c != 0) return false;
    }
    return true;
}

/// Verify a FRI proof against the transcript (which must be in the same state the prover's was
/// before `friProve`). Re-derives the fold challenges and query positions.
fn friVerify(allocator: Allocator, transcript: *Transcript, proof: FriProof) !FriVerifyResult {
    var betas: [NUM_FOLDS]Felt = undefined;
    for (0..NUM_FOLDS) |k| {
        transcript.absorbHash(proof.roots[k]);
        betas[k] = transcript.challengeFelt();
    }
    for (proof.final_layer) |v| transcript.absorbFelt(v);

    var result = FriVerifyResult{ .ok = true, .q0 = undefined, .a0 = undefined, .b0 = undefined };

    if (proof.final_layer.len != FINAL_SIZE) return .{ .ok = false, .q0 = undefined, .a0 = undefined, .b0 = undefined };
    if (!try friCheckFinalLowDegree(allocator, proof.final_layer)) {
        result.ok = false;
    }

    const inv2 = field.inv(2);
    for (proof.queries, 0..) |q, qi| {
        const q0 = transcript.challengeIndex(LDE_SIZE / 2);
        result.q0[qi] = q0;
        result.a0[qi] = q.layers[0].a;
        result.b0[qi] = q.layers[0].b;
        for (0..NUM_FOLDS) |k| {
            const size_k = LDE_SIZE >> @intCast(k);
            const half_k = size_k / 2;
            const a_idx = q0 % half_k;
            const b_idx = a_idx + half_k;
            const offset_k = field.pow(ldeOffset(), @as(u64, 1) << @intCast(k));
            const gen_k = field.pow(ldeGen(), @as(u64, 1) << @intCast(k));
            const layer = q.layers[k];
            // Merkle openings.
            if (!merkleVerify(proof.roots[k], size_k, a_idx, layer.a, layer.path_a)) result.ok = false;
            if (!merkleVerify(proof.roots[k], size_k, b_idx, layer.b, layer.path_b)) result.ok = false;
            // Fold consistency.
            const x = field.mul(offset_k, field.pow(gen_k, @intCast(a_idx)));
            const even = field.mul(field.add(layer.a, layer.b), inv2);
            const odd = field.mul(field.mul(field.sub(layer.a, layer.b), inv2), field.inv(x));
            const folded = field.add(even, field.mul(betas[k], odd));
            // The folded value must appear at position `a_idx` of the next layer.
            if (k + 1 < NUM_FOLDS) {
                const half_next = half_k / 2;
                const expected = if (a_idx < half_next) q.layers[k + 1].a else q.layers[k + 1].b;
                if (folded != expected) result.ok = false;
            } else {
                if (folded != proof.final_layer[a_idx % FINAL_SIZE]) result.ok = false;
            }
        }
    }
    return result;
}

fn friFree(allocator: Allocator, proof: FriProof) void {
    for (proof.queries) |q| {
        for (q.layers) |layer| {
            allocator.free(layer.path_a);
            allocator.free(layer.path_b);
        }
    }
    allocator.free(proof.queries);
    allocator.free(proof.final_layer);
}

// ---------------------------------------------------------------------------------------
// The authorization AIR: prove knowledge of a chain preimage
// ---------------------------------------------------------------------------------------

/// Map a 32-byte secret to a field element (low 16 bytes, reduced mod p).
fn secretToField(secret: *const [32]u8) Felt {
    var b: [16]u8 = undefined;
    @memcpy(&b, secret[0..16]);
    return field.fromBytes(&b);
}

/// One step of the authorization chain: `x -> x^3 + C`.
fn chainStep(x: Felt) Felt {
    return field.add(field.mul(field.mul(x, x), x), C_CONST);
}

/// The public authorization image: the final state after `N-1` chain steps from `secret`.
pub fn imageFelt(secret: *const [32]u8) Felt {
    var s = secretToField(secret);
    for (0..N - 1) |_| s = chainStep(s);
    return s;
}

/// Evaluate the composition polynomial at one point from the trace value, its "next" value, and
/// the domain point. Used identically by prover (over the whole LDE) and verifier (at queries),
/// so the two are guaranteed consistent.
fn compositionAt(t: Felt, t_next: Felt, x: Felt, image: Felt, alpha: Felt, gamma: Felt, omega_last: Felt) Felt {
    // transition: t^3 + C - t_next must vanish on the trace domain except the last row.
    const trans_num = field.sub(chainStep(t), t_next);
    const x_n = field.pow(x, N);
    const z_trans = field.mul(field.sub(x_n, 1), field.inv(field.sub(x, omega_last)));
    const q_trans = field.mul(trans_num, field.inv(z_trans));
    // boundary: t - image must vanish at the last row.
    const q_bound = field.mul(field.sub(t, image), field.inv(field.sub(x, omega_last)));
    return field.add(field.mul(alpha, q_trans), field.mul(gamma, q_bound));
}

/// Build the trace, interpolate it, and evaluate the trace polynomial over the LDE coset.
fn buildTraceLde(allocator: Allocator, secret_felt: Felt) ![]Felt {
    const trace = try allocator.alloc(Felt, N);
    defer allocator.free(trace);
    trace[0] = secret_felt;
    for (1..N) |i| trace[i] = chainStep(trace[i - 1]);

    // Interpolate: trace values are evaluations over <omega>; iNTT gives the coefficients.
    field.intt(trace, field.rootOfUnity(N));

    // Evaluate the degree-<N polynomial over the LDE coset (offset · gen^j).
    const lde = try allocator.alloc(Felt, LDE_SIZE);
    @memset(lde, 0);
    @memcpy(lde[0..N], trace);
    var off_pow: Felt = 1;
    for (0..LDE_SIZE) |i| {
        lde[i] = field.mul(lde[i], off_pow);
        off_pow = field.mul(off_pow, ldeOffset());
    }
    field.ntt(lde, ldeGen());
    return lde;
}

const TraceOpen = struct {
    val: Felt,
    path: []Hash,
};

const StarkQuery = struct {
    fri: FriQuery,
    ta: TraceOpen, // trace at q0
    ta_next: TraceOpen, // trace at (q0 + BLOWUP) mod LDE_SIZE
    tb: TraceOpen, // trace at q0 + LDE_SIZE/2
    tb_next: TraceOpen, // trace at (q0 + LDE_SIZE/2 + BLOWUP) mod LDE_SIZE
};

pub const StarkProof = struct {
    trace_root: Hash,
    fri_roots: [NUM_FOLDS]Hash,
    fri_final: []Felt,
    queries: []StarkQuery,
};

const TRANSCRIPT_LABEL = "lattica:auth-stark:v1";

/// Produce a real FRI-STARK proof that the prover knows a secret whose chain image is `image`.
pub fn prove(allocator: Allocator, secret: *const [32]u8) !StarkProof {
    const image = imageFelt(secret);
    const trace_lde = try buildTraceLde(allocator, secretToField(secret));
    defer allocator.free(trace_lde);

    var trace_tree = try MerkleTree.build(allocator, trace_lde);
    defer trace_tree.deinit();
    const trace_root = trace_tree.root();

    var tr = Transcript.init(TRANSCRIPT_LABEL);
    tr.absorbFelt(image);
    tr.absorbHash(trace_root);
    const alpha = tr.challengeFelt();
    const gamma = tr.challengeFelt();

    // Composition polynomial evaluations over the LDE.
    const omega_last = field.pow(field.rootOfUnity(N), N - 1);
    const cp = try allocator.alloc(Felt, LDE_SIZE);
    defer allocator.free(cp);
    var x = ldeOffset();
    for (0..LDE_SIZE) |j| {
        cp[j] = compositionAt(trace_lde[j], trace_lde[(j + BLOWUP) % LDE_SIZE], x, image, alpha, gamma, omega_last);
        x = field.mul(x, ldeGen());
    }

    var fri = try FriProver.commit(allocator, &tr, cp);
    const fri_roots = fri.roots;
    const fri_final = try allocator.dupe(Felt, fri.final_layer);

    const half0 = LDE_SIZE / 2;
    const queries = try allocator.alloc(StarkQuery, NUM_QUERIES);
    for (queries) |*sq| {
        const q0 = tr.challengeIndex(half0);
        const a_idx = q0;
        const b_idx = q0 + half0;
        sq.fri = try fri.open(allocator, q0);
        sq.ta = .{ .val = trace_lde[a_idx], .path = try trace_tree.open(allocator, a_idx) };
        sq.ta_next = .{ .val = trace_lde[(a_idx + BLOWUP) % LDE_SIZE], .path = try trace_tree.open(allocator, (a_idx + BLOWUP) % LDE_SIZE) };
        sq.tb = .{ .val = trace_lde[b_idx], .path = try trace_tree.open(allocator, b_idx) };
        sq.tb_next = .{ .val = trace_lde[(b_idx + BLOWUP) % LDE_SIZE], .path = try trace_tree.open(allocator, (b_idx + BLOWUP) % LDE_SIZE) };
    }
    allocator.free(fri.final_layer);
    fri.deinit();
    return .{ .trace_root = trace_root, .fri_roots = fri_roots, .fri_final = fri_final, .queries = queries };
}

/// Verify a FRI-STARK proof against the public `image`.
pub fn verify(allocator: Allocator, image: Felt, proof: StarkProof) !bool {
    if (proof.fri_final.len != FINAL_SIZE) return false;
    if (proof.queries.len != NUM_QUERIES) return false;

    var tr = Transcript.init(TRANSCRIPT_LABEL);
    tr.absorbFelt(image);
    tr.absorbHash(proof.trace_root);
    const alpha = tr.challengeFelt();
    const gamma = tr.challengeFelt();

    var betas: [NUM_FOLDS]Felt = undefined;
    for (0..NUM_FOLDS) |k| {
        tr.absorbHash(proof.fri_roots[k]);
        betas[k] = tr.challengeFelt();
    }
    for (proof.fri_final) |v| tr.absorbFelt(v);
    if (!try friCheckFinalLowDegree(allocator, proof.fri_final)) return false;

    const omega_last = field.pow(field.rootOfUnity(N), N - 1);
    const inv2 = field.inv(2);
    const half0 = LDE_SIZE / 2;
    var ok = true;

    for (proof.queries) |sq| {
        const q0 = tr.challengeIndex(half0);
        const a_idx = q0;
        const b_idx = q0 + half0;
        const a_next = (a_idx + BLOWUP) % LDE_SIZE;
        const b_next = (b_idx + BLOWUP) % LDE_SIZE;

        // Trace Merkle openings.
        if (!merkleVerify(proof.trace_root, LDE_SIZE, a_idx, sq.ta.val, sq.ta.path)) ok = false;
        if (!merkleVerify(proof.trace_root, LDE_SIZE, a_next, sq.ta_next.val, sq.ta_next.path)) ok = false;
        if (!merkleVerify(proof.trace_root, LDE_SIZE, b_idx, sq.tb.val, sq.tb.path)) ok = false;
        if (!merkleVerify(proof.trace_root, LDE_SIZE, b_next, sq.tb_next.val, sq.tb_next.path)) ok = false;

        // ALI: composition at the queried points must match what the trace implies.
        const x_a = field.mul(ldeOffset(), field.pow(ldeGen(), @intCast(a_idx)));
        const x_b = field.mul(ldeOffset(), field.pow(ldeGen(), @intCast(b_idx)));
        if (compositionAt(sq.ta.val, sq.ta_next.val, x_a, image, alpha, gamma, omega_last) != sq.fri.layers[0].a) ok = false;
        if (compositionAt(sq.tb.val, sq.tb_next.val, x_b, image, alpha, gamma, omega_last) != sq.fri.layers[0].b) ok = false;

        // FRI fold-consistency chain.
        for (0..NUM_FOLDS) |k| {
            const size_k = LDE_SIZE >> @intCast(k);
            const half_k = size_k / 2;
            const ai = q0 % half_k;
            const bi = ai + half_k;
            const off_k = field.pow(ldeOffset(), @as(u64, 1) << @intCast(k));
            const gen_k = field.pow(ldeGen(), @as(u64, 1) << @intCast(k));
            const layer = sq.fri.layers[k];
            if (!merkleVerify(proof.fri_roots[k], size_k, ai, layer.a, layer.path_a)) ok = false;
            if (!merkleVerify(proof.fri_roots[k], size_k, bi, layer.b, layer.path_b)) ok = false;
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
        allocator.free(sq.ta.path);
        allocator.free(sq.ta_next.path);
        allocator.free(sq.tb.path);
        allocator.free(sq.tb_next.path);
    }
    allocator.free(proof.queries);
    allocator.free(proof.fri_final);
}

// ---------------------------------------------------------------------------------------
// Serialization (StarkProof <-> bytes). All sub-object sizes are fixed by the parameters, so
// the layout is positional with no length prefixes.
// ---------------------------------------------------------------------------------------

fn putFelt(buf: *std.ArrayList(u8), allocator: Allocator, v: Felt) !void {
    try buf.appendSlice(allocator, &field.toBytes(v));
}

fn putHash(buf: *std.ArrayList(u8), allocator: Allocator, h: Hash) !void {
    try buf.appendSlice(allocator, &h);
}

pub fn serialize(allocator: Allocator, proof: StarkProof) ![]u8 {
    var buf: std.ArrayList(u8) = .empty;
    errdefer buf.deinit(allocator);
    try putHash(&buf, allocator, proof.trace_root);
    for (proof.fri_roots) |r| try putHash(&buf, allocator, r);
    for (proof.fri_final) |v| try putFelt(&buf, allocator, v);
    for (proof.queries) |sq| {
        for (sq.fri.layers) |layer| {
            try putFelt(&buf, allocator, layer.a);
            try putFelt(&buf, allocator, layer.b);
            for (layer.path_a) |h| try putHash(&buf, allocator, h);
            for (layer.path_b) |h| try putHash(&buf, allocator, h);
        }
        inline for (.{ sq.ta, sq.ta_next, sq.tb, sq.tb_next }) |to| {
            try putFelt(&buf, allocator, to.val);
            for (to.path) |h| try putHash(&buf, allocator, h);
        }
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
        const s = try self.getBytes(8);
        return std.mem.readInt(u64, s[0..8], .little);
    }
    fn getHash(self: *Reader) !Hash {
        const s = try self.getBytes(32);
        var h: Hash = undefined;
        @memcpy(&h, s);
        return h;
    }
    fn getPath(self: *Reader, allocator: Allocator, len: usize) ![]Hash {
        const path = try allocator.alloc(Hash, len);
        for (path) |*h| h.* = try self.getHash();
        return path;
    }
};

/// Parse a proof produced by `serialize`. Allocations are owned by `allocator` (free with
/// `starkFree`); on a malformed/truncated input returns an error.
pub fn deserialize(allocator: Allocator, bytes: []const u8) !StarkProof {
    var r = Reader{ .data = bytes };
    const trace_root = try r.getHash();
    var fri_roots: [NUM_FOLDS]Hash = undefined;
    for (&fri_roots) |*x| x.* = try r.getHash();
    const fri_final = try allocator.alloc(Felt, FINAL_SIZE);
    errdefer allocator.free(fri_final);
    for (fri_final) |*v| v.* = try r.getFelt();

    const trace_depth = std.math.log2_int(usize, LDE_SIZE);
    const queries = try allocator.alloc(StarkQuery, NUM_QUERIES);
    for (queries) |*sq| {
        for (0..NUM_FOLDS) |k| {
            const depth = std.math.log2_int(usize, LDE_SIZE >> @intCast(k));
            sq.fri.layers[k].a = try r.getFelt();
            sq.fri.layers[k].b = try r.getFelt();
            sq.fri.layers[k].path_a = try r.getPath(allocator, depth);
            sq.fri.layers[k].path_b = try r.getPath(allocator, depth);
        }
        sq.ta = .{ .val = try r.getFelt(), .path = try r.getPath(allocator, trace_depth) };
        sq.ta_next = .{ .val = try r.getFelt(), .path = try r.getPath(allocator, trace_depth) };
        sq.tb = .{ .val = try r.getFelt(), .path = try r.getPath(allocator, trace_depth) };
        sq.tb_next = .{ .val = try r.getFelt(), .path = try r.getPath(allocator, trace_depth) };
    }
    return .{ .trace_root = trace_root, .fri_roots = fri_roots, .fri_final = fri_final, .queries = queries };
}

// ---------------------------------------------------------------------------------------
// Tests (Merkle + transcript + FRI + STARK)
// ---------------------------------------------------------------------------------------

const testing = std.testing;

/// Evaluate a coefficient polynomial over the LDE coset (offset · gen^i), for tests.
fn evalOnLde(allocator: Allocator, coeffs: []const Felt) ![]Felt {
    const out = try allocator.alloc(Felt, LDE_SIZE);
    @memset(out, 0);
    for (coeffs, 0..) |c, i| out[i] = c;
    // scale by offset^i, then NTT over the LDE subgroup.
    var off_pow: Felt = 1;
    for (0..LDE_SIZE) |i| {
        out[i] = field.mul(out[i], off_pow);
        off_pow = field.mul(off_pow, ldeOffset());
    }
    field.ntt(out, ldeGen());
    return out;
}

test "fri accepts a low-degree polynomial" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();

    // A polynomial of degree < COMP_DEGREE_BOUND.
    const coeffs = try a.alloc(Felt, COMP_DEGREE_BOUND);
    for (coeffs, 0..) |*c, i| c.* = @intCast((i * 31 + 7) % field.P);
    const evals = try evalOnLde(a, coeffs);

    var tp = Transcript.init("fri-test");
    const proof = try friProve(a, &tp, evals);

    var tv = Transcript.init("fri-test");
    const res = try friVerify(a, &tv, proof);
    try testing.expect(res.ok);
}

test "fri rejects a high-degree (random) vector" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();

    // Pseudo-random evaluations: not low-degree.
    const evals = try a.alloc(Felt, LDE_SIZE);
    var s: Felt = 123456789;
    for (evals) |*e| {
        s = field.add(field.mul(s, 6364136223846793005 % field.P), 1442695040888963407 % field.P);
        e.* = s;
    }
    var tp = Transcript.init("fri-test");
    const proof = try friProve(a, &tp, evals);

    var tv = Transcript.init("fri-test");
    const res = try friVerify(a, &tv, proof);
    try testing.expect(!res.ok);
}

test "stark: valid proof verifies" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const secret = [_]u8{7} ** 32;
    const proof = try prove(a, &secret);
    try testing.expect(try verify(a, imageFelt(&secret), proof));
}

test "stark: wrong image rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const secret = [_]u8{7} ** 32;
    const proof = try prove(a, &secret);
    try testing.expect(!try verify(a, imageFelt(&secret) + 1, proof));
}

test "stark: tampered trace value rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const secret = [_]u8{7} ** 32;
    var proof = try prove(a, &secret);
    proof.queries[0].ta.val = field.add(proof.queries[0].ta.val, 1);
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

test "stark: proof from a different secret does not verify against this image" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const secret = [_]u8{7} ** 32;
    const other = [_]u8{8} ** 32;
    const proof = try prove(a, &secret);
    // The proof attests to `secret`'s image; verifying against a different image must fail.
    try testing.expect(!try verify(a, imageFelt(&other), proof));
    // And it does verify against its own image.
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
    // A flipped byte in the serialized proof must break verification.
    const tampered = try a.dupe(u8, bytes);
    tampered[bytes.len / 2] ^= 0xff;
    if (deserialize(a, tampered)) |bad| {
        try testing.expect(!try verify(a, imageFelt(&secret), bad));
    } else |_| {}
}

test "merkle commit/open/verify" {
    const a = testing.allocator;
    const n = 16;
    var leaves: [n]Felt = undefined;
    for (&leaves, 0..) |*v, i| v.* = @intCast(i * 1234 + 5);
    var tree = try MerkleTree.build(a, &leaves);
    defer tree.deinit();
    const root = tree.root();
    for (0..n) |i| {
        const path = try tree.open(a, i);
        defer a.free(path);
        try testing.expect(merkleVerify(root, n, i, leaves[i], path));
        // A wrong leaf value must not verify.
        try testing.expect(!merkleVerify(root, n, i, leaves[i] + 1, path));
        // A wrong index must not verify (except trivial self-match).
        if (i + 1 < n) try testing.expect(!merkleVerify(root, n, i + 1, leaves[i], path));
    }
}

test "transcript is deterministic and path-dependent" {
    var t1 = Transcript.init("test");
    var t2 = Transcript.init("test");
    t1.absorbFelt(42);
    t2.absorbFelt(42);
    try testing.expectEqual(t1.challengeFelt(), t2.challengeFelt());
    // Distinct squeezes between absorbs differ.
    try testing.expect(t1.challengeFelt() != t1.challengeFelt());
    // Diverging absorbs diverge the challenges.
    t1.absorbFelt(1);
    t2.absorbFelt(2);
    try testing.expect(t1.challengeFelt() != t2.challengeFelt());
}
