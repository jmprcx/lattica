//! # node
//!
//! Minimal in-memory chain state and shielded-transaction validation — enough to demonstrate a
//! complete post-quantum shielded transfer end to end, without networking, mempool, or
//! proof-of-work. It models exactly the consensus-critical shielded state (commitment tree,
//! historical anchors, nullifier set) and the rules that validate a transaction against them.
//!
//! Transactions are **hidden-value join-splits**: a single zero-knowledge proof
//! (`lattica-prover-p3::joinsplit_air`, installed via `ffi.setJoinSplitBackend`) proves ownership,
//! membership under a known anchor, nullifier correctness, value balance, and range — over inputs
//! and outputs whose values/commitments are never revealed. The node sees only the public statement:
//! the anchor, the N nullifiers, the M output commitments, the fee, the mint, and a `tx_binding`
//! digest of the whole body (so outputs can't be swapped — it replaces a binding signature).

const std = @import("std");
const Allocator = std.mem.Allocator;
const p = @import("primitives.zig");
const tree = @import("tree.zig");
const tx = @import("tx.zig");
const ffi = @import("ffi.zig");
const poseidon2 = @import("poseidon2.zig");
const Hash32 = p.Hash32;

const TX_DOMAIN: []const u8 = "lattica:v1:tx-binding";
const OUT_RHO_DOMAIN: []const u8 = "lattica:v1:out-rho";
const OUT_RCM_DOMAIN: []const u8 = "lattica:v1:out-rcm";

/// Fixed join-split shape (must match the circuit `N_IN`/`M_OUT`).
pub const N_IN: usize = ffi.JOINSPLIT_N_IN;
pub const M_OUT: usize = ffi.JOINSPLIT_M_OUT;

/// Reasons a shielded transaction can be rejected by the chain.
pub const TxError = error{
    UnknownAnchor,
    DoubleSpend,
    BadAuthProof,
    Unbalanced,
    IllegalIssuance,
    ValueOverflow,
    TreeFull,
    Internal,
};

/// A note the wallet owns and is about to spend: the note, its tree position, and its membership
/// path under the anchor being spent against.
pub const InputSpend = struct {
    note: tx.Note,
    position: u64,
    path: tree.MerklePath,
};

/// A requested output: pay `value` to `recipient`.
pub const OutputReq = struct {
    recipient: tx.Address,
    value: u64,
};

/// A shielded join-split transaction. The only public data is the join-split statement plus the
/// encrypted output notes; values and input commitments stay hidden in the proof.
pub const ShieldedTx = struct {
    anchor: Hash32,
    nullifiers: [N_IN]Hash32,
    out_cms: [M_OUT]Hash32,
    fee: u64,
    mint: u64,
    proof: []const u8,
    /// Encrypted output notes (recipients trial-decrypt to find theirs).
    outputs: [M_OUT]tx.TransmittedNote,

    /// Canonical 4-element digest of the public body — the sighash the proof binds via its
    /// `tx_binding` public input. Recomputed by the node so the prover can never disagree with the
    /// body it submitted. Canonicalized (each limb < p) so it round-trips through the field.
    pub fn txBinding(self: ShieldedTx) Hash32 {
        var dh = p.DomainHasher.init(TX_DOMAIN);
        var le: [8]u8 = undefined;
        dh.field(&self.anchor);
        for (self.nullifiers) |nf| dh.field(&nf);
        for (self.out_cms) |cm| dh.field(&cm);
        std.mem.writeInt(u64, &le, self.fee, .little);
        dh.field(&le);
        std.mem.writeInt(u64, &le, self.mint, .little);
        dh.field(&le);
        for (self.outputs) |tn| {
            dh.field(&tn.kem_ct);
            dh.field(tn.ciphertext);
        }
        const raw = dh.final();
        // reduce each 8-byte limb mod p so the digest is a canonical 4-element field value.
        return poseidon2.digestBytes(poseidon2.digestFromBytes(raw));
    }

    /// The join-split public statement the verifier checks against.
    pub fn publicInputs(self: ShieldedTx) ffi.JoinSplitPublicInputs {
        return .{
            .anchor = self.anchor,
            .nullifiers = self.nullifiers,
            .out_cms = self.out_cms,
            .tx_binding = self.txBinding(),
            .fee = self.fee,
            .mint = self.mint,
        };
    }
};

// ---------------------------------------------------------------------------------------
// Wallet-side transfer construction
// ---------------------------------------------------------------------------------------

const DEPTH = TREE_DEPTH;

fn putU64(w: *std.ArrayList(u8), a: Allocator, v: u64) !void {
    var b: [8]u8 = undefined;
    std.mem.writeInt(u64, &b, v, .little);
    try w.appendSlice(a, &b);
}
/// Append the canonical field element implied by up to 8 little-endian bytes.
fn putFelt(w: *std.ArrayList(u8), a: Allocator, bytes: []const u8) !void {
    try putU64(w, a, poseidon2.feltLE(bytes));
}
/// Append a 32-byte hash as 4 canonical field elements.
fn putDigest(w: *std.ArrayList(u8), a: Allocator, h: Hash32) !void {
    var k: usize = 0;
    while (k < 4) : (k += 1) try putFelt(w, a, h[k * 8 .. k * 8 + 8]);
}

/// Serialize a witness into the canonical wallet→prover layout (matching
/// `lattica-prover-p3::parse_joinsplit_witness`).
fn encodeWitness(
    a: Allocator,
    sender: tx.FullKey,
    inputs: []const InputSpend,
    out_notes: [M_OUT]tx.Note,
    fee: u64,
    mint: u64,
    tx_binding: Hash32,
) ![]u8 {
    var w: std.ArrayList(u8) = .empty;
    errdefer w.deinit(a);
    for (inputs) |in_| {
        try putU64(&w, a, std.mem.readInt(u64, sender.nk[0..8], .little)); // nk0
        try putU64(&w, a, std.mem.readInt(u64, sender.nk[8..16], .little)); // nk1
        try putU64(&w, a, in_.note.value);
        try putFelt(&w, a, in_.note.rho[0..8]);
        try putFelt(&w, a, in_.note.rcm[0..8]);
        for (in_.path.siblings) |sib| try putDigest(&w, a, sib);
        var d: usize = 0;
        while (d < DEPTH) : (d += 1) try w.append(a, @intCast((in_.position >> @intCast(d)) & 1));
    }
    for (out_notes) |o| {
        try putDigest(&w, a, o.recipient);
        try putU64(&w, a, o.value);
        try putFelt(&w, a, o.rho[0..8]);
        try putFelt(&w, a, o.rcm[0..8]);
    }
    try putU64(&w, a, fee);
    try putU64(&w, a, mint);
    try putDigest(&w, a, tx_binding);
    return w.toOwnedSlice(a);
}

/// Build a shielded join-split: spend the `N_IN` `inputs` (all real tree members under `anchor`;
/// pad with owned zero-value notes), pay the `outputs` (padded to `M_OUT` with zero-value notes back
/// to the sender), leaving `fee`, with public issuance `mint`. The proof is produced via the
/// installed prover backend. Allocations are owned by `allocator`.
pub fn buildTransfer(
    allocator: Allocator,
    sender: tx.FullKey,
    inputs: []const InputSpend,
    outputs: []const OutputReq,
    fee: u64,
    mint: u64,
    anchor: Hash32,
) !ShieldedTx {
    if (inputs.len != N_IN or outputs.len > M_OUT) return TxError.Internal;

    // Nullifiers for every input.
    var nfs: [N_IN]Hash32 = undefined;
    for (inputs, 0..) |in_, i| nfs[i] = in_.note.nullifier(&sender.nk, in_.position);

    // Output notes (pad to M_OUT with zero-value notes back to the sender), commitments, ciphertexts.
    var out_notes: [M_OUT]tx.Note = undefined;
    var tns: [M_OUT]tx.TransmittedNote = undefined;
    var out_cms: [M_OUT]Hash32 = undefined;
    for (0..M_OUT) |j| {
        const recipient: tx.Address = if (j < outputs.len) outputs[j].recipient else sender.address();
        const value: u64 = if (j < outputs.len) outputs[j].value else 0;
        const jb = [_]u8{@intCast(j)};
        const rho = p.hashDomain(OUT_RHO_DOMAIN, &.{ &nfs[0], &jb });
        const rcm = p.hashDomain(OUT_RCM_DOMAIN, &.{ &nfs[0], &jb });
        out_notes[j] = .{ .value = value, .recipient = recipient.recipientId(), .rho = rho, .rcm = rcm };
        out_cms[j] = out_notes[j].commitment();
        tns[j] = tx.encryptNote(allocator, recipient, out_notes[j]) catch return TxError.Internal;
    }

    // Value balance (wallet-side, before proving): Σin + mint = Σout + fee.
    var in_sum: u64 = mint;
    for (inputs) |in_| in_sum = std.math.add(u64, in_sum, in_.note.value) catch return TxError.ValueOverflow;
    var out_sum: u64 = fee;
    for (out_notes) |o| out_sum = std.math.add(u64, out_sum, o.value) catch return TxError.ValueOverflow;
    if (in_sum != out_sum) return TxError.Unbalanced;

    var t = ShieldedTx{
        .anchor = anchor,
        .nullifiers = nfs,
        .out_cms = out_cms,
        .fee = fee,
        .mint = mint,
        .proof = &.{},
        .outputs = tns,
    };
    const binding = t.txBinding();
    const witness = encodeWitness(allocator, sender, inputs, out_notes, fee, mint, binding) catch return TxError.Internal;
    t.proof = ffi.proveJoinSplit(allocator, witness) catch return TxError.Internal;
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

    /// Mint funds directly into a shielded note (coinbase-style, to bootstrap the demo / pad inputs).
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

    /// Validate and apply a normal (value-conserving) shielded join-split: issuance is forbidden
    /// (`mint` must be 0). On success, nullifiers are recorded and the output commitments appended.
    pub fn verifyAndApply(self: *Chain, t: ShieldedTx) TxError!void {
        return self.applyChecked(t, 0);
    }

    /// Validate and apply a **coinbase** (issuance) join-split: `t.mint` must equal `reward`, the
    /// issuance the consensus layer permits for this block (the block subsidy + the fees being
    /// claimed). All other checks are identical to a normal transaction. The reward *policy* (the
    /// emission schedule, and that exactly one coinbase exists per block) lives in the host
    /// consensus; lattica only enforces that the proven, range-checked `mint` matches what consensus
    /// authorized — so issuance is impossible except through this gated, value-accounted path.
    pub fn applyCoinbase(self: *Chain, t: ShieldedTx, reward: u64) TxError!void {
        return self.applyChecked(t, reward);
    }

    /// Shared validation + application. `allowed_mint` is the only permitted issuance (0 for a normal
    /// tx; the block reward for a coinbase).
    fn applyChecked(self: *Chain, t: ShieldedTx, allowed_mint: u64) TxError!void {
        // 1. The join-split proof is the sole authorization — fail-closed (no backend ⇒ reject). It
        //    binds ownership, membership under the anchor, nullifier correctness, balance, and range;
        //    its tx_binding == the public body (recomputed here) so nothing can be swapped.
        if (!ffi.verifyJoinSplit(t.proof, t.publicInputs())) return TxError.BadAuthProof;

        // 2. Issuance gate. The circuit only proves balance *given* `mint`, so the node must pin
        //    `mint` to the consensus-authorized amount — otherwise anyone could submit dummy inputs +
        //    mint > 0 + a matching output and inflate the supply. Normal txs require mint == 0;
        //    coinbase requires mint == reward.
        if (t.mint != allowed_mint) return TxError.IllegalIssuance;

        // 3. The anchor must be one the chain published.
        if (!self.isKnownAnchor(&t.anchor)) return TxError.UnknownAnchor;

        // 4. Nullifiers: reject any already spent, or duplicated within this transaction.
        var seen = HashSet.init(self.allocator);
        defer seen.deinit();
        for (t.nullifiers) |nf| {
            if (self.nullifiers.contains(nf)) return TxError.DoubleSpend;
            const gop = seen.getOrPut(nf) catch return TxError.Internal;
            if (gop.found_existing) return TxError.DoubleSpend;
        }

        // 5. Apply (only after all checks pass).
        for (t.nullifiers) |nf| self.nullifiers.put(nf, {}) catch return TxError.Internal;
        for (t.outputs) |o| {
            _ = self.insertCommitment(o.cm) catch return TxError.Internal;
            self.transmitted.append(self.allocator, o) catch return TxError.Internal;
        }
    }
};

// ---------------------------------------------------------------------------------------
// Mock backends — model the proof's tx-binding so node-level tests (and the wallet demo) exercise
// the real verify/prove seam without linking the Rust staticlib. Production installs the Rust
// `lattica_joinsplit_prove`/`lattica_joinsplit_verify` instead; the real prove→verify path is
// covered by `lattica-prover-p3/tests/ffi_integration.c` and `src/ffi_integration.zig`.
// ---------------------------------------------------------------------------------------

pub const mock = struct {
    const TXB_OFFSET: usize = 32 * (1 + N_IN + M_OUT); // anchor ‖ N·nf ‖ M·out_cm, then tx_binding

    /// "Proof" = the witness's tx_binding (its last 32 bytes), modeling that the proof commits to it.
    pub fn prove(
        witness_ptr: [*]const u8,
        witness_len: usize,
        proof_out: [*]u8,
        proof_cap: usize,
        proof_len: *usize,
        pi_out: [*]u8,
        pi_cap: usize,
        pi_len: *usize,
    ) callconv(.c) i32 {
        _ = pi_out;
        _ = pi_cap;
        if (witness_len < 32 or proof_cap < 32) return 1;
        @memcpy(proof_out[0..32], witness_ptr[witness_len - 32 .. witness_len]);
        proof_len.* = 32;
        pi_len.* = 0;
        return 0;
    }

    /// Accept iff the proof's tx_binding equals the public statement's tx_binding (so any tampering
    /// of the body — which changes tx_binding — is rejected, exactly like the real binding does).
    pub fn verify(proof_ptr: [*]const u8, proof_len: usize, pi_ptr: [*]const u8, pi_len: usize) callconv(.c) i32 {
        if (proof_len != 32 or pi_len != ffi.JoinSplitPublicInputs.ENCODED_LEN) return 1;
        const proof = proof_ptr[0..32];
        const pi = pi_ptr[0..pi_len];
        if (std.mem.eql(u8, proof, pi[TXB_OFFSET .. TXB_OFFSET + 32])) return 0;
        return 1;
    }

    /// Install both mock backends (test / demo only).
    pub fn install() void {
        ffi.setJoinSplitProveBackend(&prove);
        ffi.setJoinSplitBackend(&verify);
    }
    pub fn uninstall() void {
        ffi.clearJoinSplitProveBackend();
        ffi.clearJoinSplitBackend();
    }
};

// ---------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------

const testing = std.testing;

fn account(seed: u8) !tx.FullKey {
    return tx.FullKey.fromSeed([_]u8{seed} ** 32);
}

/// Mint a real note + a zero-value padding note to `key`, returning both as `InputSpend`s under the
/// current anchor (the join-split needs `N_IN` real tree members).
fn fundTwoInputs(a: Allocator, chain: *Chain, key: tx.FullKey, value: u64, salt: u8) ![N_IN]InputSpend {
    const m0 = try chain.mint(key.address(), value, [_]u8{salt} ** 32);
    const m1 = try chain.mint(key.address(), 0, [_]u8{salt +% 1} ** 32);
    return .{
        .{ .note = m0.note, .position = m0.pos, .path = try chain.merklePath(a, m0.pos) },
        .{ .note = m1.note, .position = m1.pos, .path = try chain.merklePath(a, m1.pos) },
    };
}

test "end to end shielded join-split transfer" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    mock.install();
    defer mock.uninstall();

    var chain = try Chain.init(a);
    const alice = try account(1);
    const bob = try account(2);

    // Alice holds 1000 (+ a zero-value padding note).
    const inputs = try fundTwoInputs(a, &chain, alice, 1000, 11);
    const anchor = chain.anchor();

    // Alice pays Bob 900, fee 100 (output 1 is a zero-value dummy back to Alice).
    const outs = [_]OutputReq{.{ .recipient = bob.address(), .value = 900 }};
    const t = try buildTransfer(a, alice, &inputs, &outs, 100, 0, anchor);

    try chain.verifyAndApply(t);

    // Bob finds and decrypts exactly his 900 note; Alice's dummy decrypts to her at 0.
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

    // Replaying the same transaction is a double-spend.
    try testing.expectError(TxError.DoubleSpend, chain.verifyAndApply(t));
}

test "join-split requires a verifier backend (fail-closed)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();

    var chain = try Chain.init(a);
    const alice = try account(1);
    const bob = try account(2);

    // Build with the mock prover installed, then verify with NO backend ⇒ rejected.
    mock.install();
    const inputs = try fundTwoInputs(a, &chain, alice, 1000, 7);
    const outs = [_]OutputReq{.{ .recipient = bob.address(), .value = 900 }};
    const t = try buildTransfer(a, alice, &inputs, &outs, 100, 0, chain.anchor());
    mock.uninstall(); // no verifier installed
    try testing.expectError(TxError.BadAuthProof, chain.verifyAndApply(t));
}

test "unbalanced transfer rejected at build" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    mock.install();
    defer mock.uninstall();
    var chain = try Chain.init(a);
    const alice = try account(1);
    const bob = try account(2);
    const inputs = try fundTwoInputs(a, &chain, alice, 1000, 5);
    // 900 + 99 != 1000
    const outs = [_]OutputReq{.{ .recipient = bob.address(), .value = 900 }};
    try testing.expectError(TxError.Unbalanced, buildTransfer(a, alice, &inputs, &outs, 99, 0, chain.anchor()));
}

test "tampered output is rejected (tx-binding)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    mock.install();
    defer mock.uninstall();
    var chain = try Chain.init(a);
    const alice = try account(1);
    const bob = try account(2);
    const inputs = try fundTwoInputs(a, &chain, alice, 1000, 5);
    const outs = [_]OutputReq{.{ .recipient = bob.address(), .value = 900 }};
    var t = try buildTransfer(a, alice, &inputs, &outs, 100, 0, chain.anchor());
    // Swap an output commitment after proving: tx_binding no longer matches the proof ⇒ rejected.
    t.out_cms[0][0] +%= 1;
    try testing.expectError(TxError.BadAuthProof, chain.verifyAndApply(t));
}

test "unknown anchor rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    mock.install();
    defer mock.uninstall();
    var chain = try Chain.init(a);
    const alice = try account(1);
    const bob = try account(2);
    const inputs = try fundTwoInputs(a, &chain, alice, 1000, 5);
    const outs = [_]OutputReq{.{ .recipient = bob.address(), .value = 900 }};
    var t = try buildTransfer(a, alice, &inputs, &outs, 100, 0, chain.anchor());
    // Point at an anchor the chain never published, re-binding the proof to it so the proof check
    // passes (the mock binds tx_binding) and the anchor check is what fails.
    t.anchor = [_]u8{0xaa} ** 32;
    var rebind = t.txBinding();
    t.proof = rebind[0..]; // proof = the new tx_binding ⇒ mock verify accepts
    try testing.expectError(TxError.UnknownAnchor, chain.verifyAndApply(t));
}

test "arbitrary issuance (mint > 0) is rejected on the normal path — no inflation" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    mock.install();
    defer mock.uninstall();
    var chain = try Chain.init(a);
    const attacker = try account(3);
    // The attacker tries to conjure value: two zero-value inputs, mint=500 funding a 500 output.
    // The circuit's balance holds (0 + 500 = 500 + 0), so a missing node-side gate would mint money.
    const inputs = try fundTwoInputs(a, &chain, attacker, 0, 20);
    const outs = [_]OutputReq{.{ .recipient = attacker.address(), .value = 500 }};
    const t = try buildTransfer(a, attacker, &inputs, &outs, 0, 500, chain.anchor());
    try testing.expectError(TxError.IllegalIssuance, chain.verifyAndApply(t));
}

test "coinbase issuance: mint accepted iff it matches the consensus reward" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    mock.install();
    defer mock.uninstall();
    var chain = try Chain.init(a);
    const miner = try account(4);

    // A coinbase issuing the wrong amount (reward=400 but mint=500) is rejected.
    const in_bad = try fundTwoInputs(a, &chain, miner, 0, 30);
    const out_bad = [_]OutputReq{.{ .recipient = miner.address(), .value = 500 }};
    const bad = try buildTransfer(a, miner, &in_bad, &out_bad, 0, 500, chain.anchor());
    try testing.expectError(TxError.IllegalIssuance, chain.applyCoinbase(bad, 400));

    // A coinbase whose mint == the authorized reward (500) is accepted; the miner gets a 500 note.
    const in_ok = try fundTwoInputs(a, &chain, miner, 0, 32);
    const out_ok = [_]OutputReq{.{ .recipient = miner.address(), .value = 500 }};
    const cb = try buildTransfer(a, miner, &in_ok, &out_ok, 0, 500, chain.anchor());
    try chain.applyCoinbase(cb, 500);

    var minted: u64 = 0;
    for (chain.transmitted.items) |tn| {
        if (tx.tryDecrypt(a, miner, tn)) |n| minted += n.value;
    }
    try testing.expectEqual(@as(u64, 500), minted);
}
