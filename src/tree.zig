//! Incremental Merkle commitment tree.
//!
//! Note commitments are appended as leaves; the root (the "anchor") is published with each
//! block. A spend proves its note's commitment is a leaf under some past anchor — without
//! revealing which leaf. Structurally identical to Zcash's Sapling/Orchard tree; the only
//! change for quantum safety is the node hash (SHA3 here, via `primitives`).
//!
//! Empty subtrees short-circuit to precomputed "empty roots", so a fixed depth of 32 (over
//! four billion notes) costs only `O(filled_leaves + depth)` work.

const std = @import("std");
const Allocator = std.mem.Allocator;
const p = @import("primitives.zig");
const poseidon2 = @import("poseidon2.zig");
const Hash32 = p.Hash32;

/// Hash of an unfilled leaf (the empty-note sentinel).
pub const EMPTY_LEAF: Hash32 = [_]u8{0} ** 32;

/// Internal-node hash: `H(left, right)` — the in-circuit Poseidon2 2-to-1 merge (C-03), so on-chain
/// anchors equal the join-split circuit's membership root.
pub fn merkleHash(left: *const Hash32, right: *const Hash32) Hash32 {
    return poseidon2.digestBytes(poseidon2.merge(poseidon2.digestFromBytes(left.*), poseidon2.digestFromBytes(right.*)));
}

/// An authentication path: the sibling at each level from the leaf up to (but excluding) the
/// root, plus the leaf's position. Length equals the tree depth. `siblings` is owned by the
/// allocator passed to `authenticationPath`.
pub const MerklePath = struct {
    position: u64,
    siblings: []Hash32,
};

/// A fixed-depth incremental Merkle tree.
pub const MerkleTree = struct {
    allocator: Allocator,
    depth: usize,
    leaves: std.ArrayList(Hash32),
    /// `empty[l]` is the root of a completely empty subtree of height `l`.
    empty: []Hash32,

    /// Create an empty tree of the given depth (capacity `2^depth` leaves).
    pub fn init(allocator: Allocator, depth: usize) !MerkleTree {
        const empty = try allocator.alloc(Hash32, depth + 1);
        empty[0] = EMPTY_LEAF;
        var l: usize = 1;
        while (l <= depth) : (l += 1) empty[l] = merkleHash(&empty[l - 1], &empty[l - 1]);
        return .{ .allocator = allocator, .depth = depth, .leaves = .empty, .empty = empty };
    }

    pub fn deinit(self: *MerkleTree) void {
        self.leaves.deinit(self.allocator);
        self.allocator.free(self.empty);
    }

    /// Number of leaves appended so far.
    pub fn len(self: MerkleTree) u64 {
        return @intCast(self.leaves.items.len);
    }

    /// Maximum number of leaves this tree can hold.
    pub fn capacity(self: MerkleTree) u128 {
        return @as(u128, 1) << @intCast(self.depth);
    }

    /// Append a leaf, returning its position.
    pub fn append(self: *MerkleTree, leaf: Hash32) !u64 {
        if (@as(u128, self.leaves.items.len) >= self.capacity()) return error.TreeFull;
        const pos: u64 = @intCast(self.leaves.items.len);
        try self.leaves.append(self.allocator, leaf);
        return pos;
    }

    /// Reserve room for `n` more leaves so a subsequent `appendAssumeCapacity` cannot fail — used for
    /// atomic state commit (audit H-03). Returns `error.TreeFull` if `n` exceeds remaining capacity.
    pub fn ensureUnusedCapacity(self: *MerkleTree, n: usize) !void {
        if (@as(u128, self.leaves.items.len) + n > self.capacity()) return error.TreeFull;
        try self.leaves.ensureUnusedCapacity(self.allocator, n);
    }

    /// Append a leaf using capacity reserved by `ensureUnusedCapacity` (infallible). Returns its position.
    pub fn appendAssumeCapacity(self: *MerkleTree, leaf: Hash32) u64 {
        const pos: u64 = @intCast(self.leaves.items.len);
        self.leaves.appendAssumeCapacity(leaf);
        return pos;
    }

    /// The current root (anchor).
    pub fn root(self: MerkleTree) Hash32 {
        return self.node(self.depth, 0);
    }

    /// Authentication path for the leaf at `position`.
    pub fn authenticationPath(self: MerkleTree, allocator: Allocator, position: u64) !MerklePath {
        if (position >= self.len()) return error.BadPosition;
        const siblings = try allocator.alloc(Hash32, self.depth);
        var idx = position;
        var level: usize = 0;
        while (level < self.depth) : (level += 1) {
            siblings[level] = self.node(level, idx ^ 1);
            idx >>= 1;
        }
        return .{ .position = position, .siblings = siblings };
    }

    /// Hash of the node at (`level`, `index`). Empty subtrees short-circuit.
    fn node(self: MerkleTree, level: usize, index: u64) Hash32 {
        if (level == 0) {
            if (index < self.leaves.items.len) return self.leaves.items[@intCast(index)];
            return self.empty[0];
        }
        // If no filled leaf falls under this subtree, it is the canonical empty root.
        const first_leaf = index << @intCast(level);
        if (first_leaf >= self.len()) return self.empty[level];
        const left = self.node(level - 1, index * 2);
        const right = self.node(level - 1, index * 2 + 1);
        return merkleHash(&left, &right);
    }
};

/// Recompute the root implied by a leaf and an authentication path, and compare to `root`.
/// This is exactly the check the zero-knowledge circuit performs in-circuit.
pub fn verifyPath(root: *const Hash32, leaf: *const Hash32, path: MerklePath) bool {
    var cur = leaf.*;
    var idx = path.position;
    for (path.siblings) |sib| {
        const s = sib;
        cur = if (idx & 1 == 0) merkleHash(&cur, &s) else merkleHash(&s, &cur);
        idx >>= 1;
    }
    return std.mem.eql(u8, &cur, root);
}

// ---------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------

const testing = std.testing;

fn mkLeaf(n: u8) Hash32 {
    return [_]u8{n} ** 32;
}

test "empty root is stable" {
    const a = testing.allocator;
    var t1 = try MerkleTree.init(a, 8);
    defer t1.deinit();
    var t2 = try MerkleTree.init(a, 8);
    defer t2.deinit();
    try testing.expectEqualSlices(u8, &t1.root(), &t2.root());
}

test "root changes on append" {
    const a = testing.allocator;
    var t = try MerkleTree.init(a, 8);
    defer t.deinit();
    const r0 = t.root();
    _ = try t.append(mkLeaf(1));
    try testing.expect(!std.mem.eql(u8, &r0, &t.root()));
}

test "paths verify for all leaves" {
    const a = testing.allocator;
    var t = try MerkleTree.init(a, 10);
    defer t.deinit();
    var i: u8 = 0;
    while (i < 50) : (i += 1) _ = try t.append(mkLeaf(i));
    const root = t.root();
    var j: u64 = 0;
    while (j < 50) : (j += 1) {
        const path = try t.authenticationPath(a, j);
        defer a.free(path.siblings);
        try testing.expectEqual(@as(usize, 10), path.siblings.len);
        try testing.expect(verifyPath(&root, &mkLeaf(@intCast(j)), path));
    }
}

test "wrong leaf fails verification" {
    const a = testing.allocator;
    var t = try MerkleTree.init(a, 10);
    defer t.deinit();
    var i: u8 = 0;
    while (i < 8) : (i += 1) _ = try t.append(mkLeaf(i));
    const root = t.root();
    const path = try t.authenticationPath(a, 3);
    defer a.free(path.siblings);
    try testing.expect(verifyPath(&root, &mkLeaf(3), path));
    try testing.expect(!verifyPath(&root, &mkLeaf(99), path));
}

test "stale root fails after growth" {
    const a = testing.allocator;
    var t = try MerkleTree.init(a, 10);
    defer t.deinit();
    var i: u8 = 0;
    while (i < 8) : (i += 1) _ = try t.append(mkLeaf(i));
    const path = try t.authenticationPath(a, 3);
    defer a.free(path.siblings);
    const old_root = t.root();
    try testing.expect(verifyPath(&old_root, &mkLeaf(3), path));
    _ = try t.append(mkLeaf(50));
    const new_root = t.root();
    try testing.expect(!verifyPath(&new_root, &mkLeaf(3), path));
}

test "deep tree is cheap" {
    const a = testing.allocator;
    var t = try MerkleTree.init(a, 32);
    defer t.deinit();
    const p0 = try t.append(mkLeaf(1));
    const p1 = try t.append(mkLeaf(2));
    try testing.expectEqual(@as(u64, 0), p0);
    try testing.expectEqual(@as(u64, 1), p1);
    const root = t.root();
    const path = try t.authenticationPath(a, 1);
    defer a.free(path.siblings);
    try testing.expectEqual(@as(usize, 32), path.siblings.len);
    try testing.expect(verifyPath(&root, &mkLeaf(2), path));
}
