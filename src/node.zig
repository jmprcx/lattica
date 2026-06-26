//! # node
//!
//! Minimal in-memory chain state and shielded-transaction validation — enough to demonstrate
//! a complete post-quantum shielded transfer end to end, without networking, mempool, or
//! proof-of-work. It models exactly the consensus-critical shielded state (commitment tree,
//! historical anchors, nullifier set) and the rules that validate a transaction against them.

const std = @import("std");
const Allocator = std.mem.Allocator;
const p = @import("primitives.zig");
const tree = @import("tree.zig");
const tx = @import("tx.zig");
const circuit = @import("circuit.zig");
const Hash32 = p.Hash32;

const TX_DOMAIN: []const u8 = "lattica:v1:tx-digest";

/// Reasons a shielded transaction can be rejected by the chain.
pub const TxError = error{
    BadBindingSignature,
    UnknownAnchor,
    BadMembership,
    DoubleSpend,
    BadAuthProof,
    Unbalanced,
    ValueOverflow,
    TreeFull,
    Internal,
};

/// A spend of one shielded note. In a production build `cm`/`value` would be hidden in the
/// AIR; this PoC reveals them so the node can check membership and balance natively while the
/// proof does authorization.
pub const Spend = struct {
    anchor: Hash32,
    cm: Hash32,
    value: u64,
    nullifier: Hash32,
    merkle: tree.MerklePath,
    auth: circuit.AuthProof,
};

/// A new shielded output.
pub const Output = struct {
    value: u64,
    note: tx.TransmittedNote,
};

/// A shielded transaction: spends, outputs, a fee, and an ML-DSA binding signature over the
/// whole body.
pub const ShieldedTx = struct {
    spends: []Spend,
    outputs: []Output,
    fee: u64,
    binding_pk: [p.PK_LEN]u8,
    binding_sig: [p.SIG_LEN]u8,

    /// Canonical 32-byte digest of everything except the binding signature.
    pub fn digest(self: ShieldedTx) Hash32 {
        var dh = p.DomainHasher.init(TX_DOMAIN);
        var le: [8]u8 = undefined;

        std.mem.writeInt(u64, &le, @intCast(self.spends.len), .little);
        dh.field(&le);
        for (self.spends) |s| {
            dh.field(&s.anchor);
            dh.field(&s.cm);
            std.mem.writeInt(u64, &le, s.value, .little);
            dh.field(&le);
            dh.field(&s.nullifier);
            dh.field(&s.auth.image);
            dh.field(s.auth.proof);
        }

        std.mem.writeInt(u64, &le, @intCast(self.outputs.len), .little);
        dh.field(&le);
        for (self.outputs) |o| {
            std.mem.writeInt(u64, &le, o.value, .little);
            dh.field(&le);
            dh.field(&o.note.cm);
            dh.field(&o.note.kem_ct);
            dh.field(o.note.ciphertext);
        }

        std.mem.writeInt(u64, &le, self.fee, .little);
        dh.field(&le);
        return dh.final();
    }
};

// ---------------------------------------------------------------------------------------
// Wallet-side transfer construction
// ---------------------------------------------------------------------------------------

/// Build a one-input, one-output shielded transfer that spends `spend_note` and pays
/// `send_value` to `recipient`, leaving `fee` for the miner. Allocations (the spends/outputs
/// arrays, the proof, the output ciphertext) are owned by `allocator`.
pub fn buildTransfer(
    allocator: Allocator,
    sender: tx.FullKey,
    spend_note: tx.Note,
    spend_position: u64,
    spend_path: tree.MerklePath,
    anchor: Hash32,
    recipient: tx.Address,
    send_value: u64,
    fee: u64,
) !ShieldedTx {
    const total_out = std.math.add(u64, send_value, fee) catch return TxError.ValueOverflow;
    if (total_out != spend_note.value) return TxError.Unbalanced;

    const nullifier = spend_note.nullifier(&sender.nk, spend_position);

    // Post-quantum proof of spend authorization (knowledge of the spend secret).
    const auth_secret = p.expand(&sender.seed, "spend-auth");
    const auth = circuit.proveAuthorization(allocator, &auth_secret) catch return TxError.Internal;

    // Output note to the recipient; its rho is the spend nullifier, tying uniqueness to the
    // consumed note exactly as Orchard does.
    const out_rcm = p.expand(&nullifier, "out-rcm");
    const out_note = tx.Note{
        .value = send_value,
        .recipient = recipient.recipientId(),
        .rho = nullifier,
        .rcm = out_rcm,
    };
    const out_tn = tx.encryptNote(allocator, recipient, out_note) catch return TxError.Internal;

    const spends = allocator.alloc(Spend, 1) catch return TxError.Internal;
    spends[0] = .{
        .anchor = anchor,
        .cm = spend_note.commitment(),
        .value = spend_note.value,
        .nullifier = nullifier,
        .merkle = spend_path,
        .auth = auth,
    };
    const outputs = allocator.alloc(Output, 1) catch return TxError.Internal;
    outputs[0] = .{ .value = send_value, .note = out_tn };

    var t = ShieldedTx{
        .spends = spends,
        .outputs = outputs,
        .fee = fee,
        .binding_pk = sender.sig.pkBytes(),
        .binding_sig = [_]u8{0} ** p.SIG_LEN,
    };
    const dg = t.digest();
    t.binding_sig = sender.sig.sign(&dg) catch return TxError.Internal;
    return t;
}

// ---------------------------------------------------------------------------------------
// Chain state
// ---------------------------------------------------------------------------------------

/// Commitment-tree depth (capacity 2^DEPTH notes).
pub const TREE_DEPTH: usize = 32;

const HashSet = std.AutoHashMap(Hash32, void);

/// The cleartext note plus its tree position, returned by `mint`.
pub const Minted = struct {
    note: tx.Note,
    pos: u64,
};

pub const Chain = struct {
    allocator: Allocator,
    tree: tree.MerkleTree,
    anchors: HashSet,
    nullifiers: HashSet,
    /// Every transmitted note ever added, so wallets can scan and trial-decrypt.
    transmitted: std.ArrayList(tx.TransmittedNote),

    pub fn init(allocator: Allocator) !Chain {
        var t = try tree.MerkleTree.init(allocator, TREE_DEPTH);
        var anchors = HashSet.init(allocator);
        try anchors.put(t.root(), {});
        return .{
            .allocator = allocator,
            .tree = t,
            .anchors = anchors,
            .nullifiers = HashSet.init(allocator),
            .transmitted = .empty,
        };
    }

    pub fn deinit(self: *Chain) void {
        self.tree.deinit();
        self.anchors.deinit();
        self.nullifiers.deinit();
        self.transmitted.deinit(self.allocator);
    }

    /// The current anchor (tree root).
    pub fn anchor(self: Chain) Hash32 {
        return self.tree.root();
    }

    pub fn isKnownAnchor(self: Chain, root: *const Hash32) bool {
        return self.anchors.contains(root.*);
    }

    /// Authentication path for a leaf position.
    pub fn merklePath(self: Chain, allocator: Allocator, position: u64) !tree.MerklePath {
        return self.tree.authenticationPath(allocator, position) catch return TxError.Internal;
    }

    fn insertCommitment(self: *Chain, cm: Hash32) !u64 {
        const pos = self.tree.append(cm) catch return TxError.TreeFull;
        self.anchors.put(self.tree.root(), {}) catch return TxError.Internal;
        return pos;
    }

    /// Mint funds directly into a shielded note (coinbase-style, to bootstrap the demo).
    pub fn mint(self: *Chain, address: tx.Address, value: u64, seed: Hash32) !Minted {
        var value_le: [8]u8 = undefined;
        std.mem.writeInt(u64, &value_le, value, .little);
        const rho = p.hashDomain("lattica:v1:mint-rho", &.{ &seed, &value_le });
        const rcm = p.expand(&seed, "mint-rcm");
        const note = tx.Note{ .value = value, .recipient = address.recipientId(), .rho = rho, .rcm = rcm };
        const tn = tx.encryptNote(self.allocator, address, note) catch return TxError.Internal;
        const pos = try self.insertCommitment(tn.cm);
        self.transmitted.append(self.allocator, tn) catch return TxError.Internal;
        return .{ .note = note, .pos = pos };
    }

    /// Validate and apply a shielded transaction. On success, nullifiers are recorded and the
    /// output commitments are appended to the tree.
    pub fn verifyAndApply(self: *Chain, t: ShieldedTx) TxError!void {
        // 1. Binding signature over the whole transaction body.
        const dg = t.digest();
        if (!p.verify(&t.binding_pk, &dg, &t.binding_sig)) return TxError.BadBindingSignature;

        // 2. Per-spend checks. Track in-transaction nullifiers to also reject duplicates.
        var seen = HashSet.init(self.allocator);
        defer seen.deinit();
        for (t.spends) |s| {
            if (!self.isKnownAnchor(&s.anchor)) return TxError.UnknownAnchor;
            if (!tree.verifyPath(&s.anchor, &s.cm, s.merkle)) return TxError.BadMembership;
            if (self.nullifiers.contains(s.nullifier)) return TxError.DoubleSpend;
            const gop = seen.getOrPut(s.nullifier) catch return TxError.Internal;
            if (gop.found_existing) return TxError.DoubleSpend;
            if (!circuit.verifyAuthorization(s.auth)) return TxError.BadAuthProof;
        }

        // 3. Value balance: inputs == outputs + fee. Checked sums — a malicious tx must not be
        //    able to wrap a u64 total (panic in safe builds; ambiguity in optimized builds).
        var inputs: u64 = 0;
        for (t.spends) |s| inputs = std.math.add(u64, inputs, s.value) catch return TxError.ValueOverflow;
        var outputs_plus_fee: u64 = t.fee;
        for (t.outputs) |o| outputs_plus_fee = std.math.add(u64, outputs_plus_fee, o.value) catch return TxError.ValueOverflow;
        if (inputs != outputs_plus_fee) return TxError.Unbalanced;

        // 4. Apply (only after all checks pass).
        for (t.spends) |s| self.nullifiers.put(s.nullifier, {}) catch return TxError.Internal;
        for (t.outputs) |o| {
            _ = self.insertCommitment(o.note.cm) catch return TxError.Internal;
            self.transmitted.append(self.allocator, o.note) catch return TxError.Internal;
        }
    }
};

// ---------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------

const testing = std.testing;

fn account(seed: u8) !tx.FullKey {
    return tx.FullKey.fromSeed([_]u8{seed} ** 32);
}

test "end to end shielded transfer" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();

    var chain = try Chain.init(a);
    const alice = try account(1);
    const bob = try account(2);

    // Alice receives 1000 via a mint.
    const minted = try chain.mint(alice.address(), 1000, [_]u8{11} ** 32);
    const decrypted = tx.tryDecrypt(a, alice, chain.transmitted.items[0]) orelse return error.TestUnexpectedNull;
    try testing.expect(decrypted.eql(minted.note));

    // Alice pays Bob 900, fee 100.
    const anchor = chain.anchor();
    const path = try chain.merklePath(a, minted.pos);
    const t = try buildTransfer(a, alice, minted.note, minted.pos, path, anchor, bob.address(), 900, 100);

    // Node accepts it.
    try chain.verifyAndApply(t);

    // Bob can find and decrypt his note; Alice cannot (it's not hers).
    var bob_total: u64 = 0;
    var bob_count: usize = 0;
    for (chain.transmitted.items) |tn| {
        if (tx.tryDecrypt(a, bob, tn)) |n| {
            bob_count += 1;
            bob_total += n.value;
        }
    }
    try testing.expectEqual(@as(usize, 1), bob_count);
    try testing.expectEqual(@as(u64, 900), bob_total);

    // Replaying the exact same transaction is a double-spend and is rejected.
    try testing.expectError(TxError.DoubleSpend, chain.verifyAndApply(t));
}

test "unbalanced transfer rejected at build" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var chain = try Chain.init(a);
    const alice = try account(1);
    const bob = try account(2);
    const minted = try chain.mint(alice.address(), 1000, [_]u8{5} ** 32);
    const path = try chain.merklePath(a, minted.pos);
    // 900 + 99 != 1000
    try testing.expectError(TxError.Unbalanced, buildTransfer(a, alice, minted.note, minted.pos, path, chain.anchor(), bob.address(), 900, 99));
}

test "tampered value breaks binding signature" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var chain = try Chain.init(a);
    const alice = try account(1);
    const bob = try account(2);
    const minted = try chain.mint(alice.address(), 1000, [_]u8{5} ** 32);
    const path = try chain.merklePath(a, minted.pos);
    var t = try buildTransfer(a, alice, minted.note, minted.pos, path, chain.anchor(), bob.address(), 900, 100);
    // Tamper with the output value after signing: the binding signature must now fail.
    t.outputs[0].value = 950;
    try testing.expectError(TxError.BadBindingSignature, chain.verifyAndApply(t));
}

test "value overflow rejected (checked arithmetic)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var chain = try Chain.init(a);
    const alice = try account(1);
    const bob = try account(2);
    const minted = try chain.mint(alice.address(), 1000, [_]u8{7} ** 32);
    const path = try chain.merklePath(a, minted.pos);
    var t = try buildTransfer(a, alice, minted.note, minted.pos, path, chain.anchor(), bob.address(), 900, 100);
    // Force the output+fee sum to wrap u64, then re-sign so the binding signature passes and the
    // checked value sum is what rejects (rather than a panic in safe builds).
    t.outputs[0].value = std.math.maxInt(u64);
    t.fee = 1;
    const dg = t.digest();
    t.binding_sig = try alice.sig.sign(&dg);
    try testing.expectError(TxError.ValueOverflow, chain.verifyAndApply(t));
}

test "unknown anchor rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var chain = try Chain.init(a);
    const alice = try account(1);
    const bob = try account(2);
    const minted = try chain.mint(alice.address(), 1000, [_]u8{5} ** 32);
    const path = try chain.merklePath(a, minted.pos);
    var t = try buildTransfer(a, alice, minted.note, minted.pos, path, chain.anchor(), bob.address(), 900, 100);
    // Point the spend at an anchor the chain never published, then re-sign so the binding
    // signature is valid and the anchor check is what fails.
    t.spends[0].anchor = [_]u8{0xaa} ** 32;
    const dg = t.digest();
    t.binding_sig = try alice.sig.sign(&dg);
    try testing.expectError(TxError.UnknownAnchor, chain.verifyAndApply(t));
}
