//! The unified **shielded-only** transaction format, canonical serialization, transaction-binding
//! digest, and the public supply model.
//!
//! **Status (audit L-01/L-02).** `SupplyState` (below) is **live** — wired into `node.zig`'s `Chain`
//! as the node's public supply accumulator. The `ShieldedTx` canonical codec / `bindingDigest` here
//! are **reference / transitional**: the live node uses its own `node.ShieldedTx` (join-split
//! statement) with its own `txBinding`; this codec is the canonical serialization design (not yet on
//! the live path). The header note below mentions Rescue-Prime/SHA3 for historical reasons — the
//! live hash is Poseidon2-Goldilocks (`poseidon2.zig`).
//!
//! Per `docs/full-node-security-integration.md`, a shielded-only chain keeps the supply invariant
//!   `issued - burned = shielded_pool_value + fees`
//! publicly recomputable without learning any note value. Each transaction proves, *in the spend
//! proof*, the hidden-value balance
//!   `sum(input_values) + mint = sum(output_values) + fee + burn`
//! while the protocol layer only ever touches the **public** counters (mint, burn, fee). Note
//! values stay private.
//!
//! Commitments (`cm`) and nullifiers (`nf`) are opaque 32-byte values here — they are produced by
//! the production prover (`lattica-prover`, Rescue-Prime `Rp64_256` over the field) so the
//! in-circuit hash and the on-chain value agree by construction. The tx-binding digest below is a
//! SHA3 hash of the canonical bytes; it is fed to the spend proof as a public input (the proof
//! binds to it — no in-circuit SHA3 is required).

const std = @import("std");
const Allocator = std.mem.Allocator;
const p = @import("primitives.zig");
const codec = @import("codec.zig");
const Hash32 = p.Hash32;

pub const VERSION: u8 = 1;

pub const Error = error{
    BadVersion,
    BadNetwork,
    TooManySpends,
    TooManyOutputs,
    SupplyOverflow,
    SupplyUnderflow,
    BadBindingSignature,
} || codec.Error || Allocator.Error;

// Consensus limits (DoS bounds; see integration doc §2 / mempool policy).
pub const MAX_SPENDS: usize = 1 << 12;
pub const MAX_OUTPUTS: usize = 1 << 12;

// ---------------------------------------------------------------------------------------
// Transaction
// ---------------------------------------------------------------------------------------

/// A shielded spend: the revealed nullifier and the STARK spend proof. The proof's public inputs
/// (anchor, nullifier, tx-binding digest) are reconstructed by the verifier from the transaction,
/// not carried separately, so they cannot disagree with the body.
pub const Spend = struct {
    nullifier: Hash32,
    proof: []const u8,
};

/// A shielded output: the note commitment and the encrypted note (ML-KEM ciphertext + AEAD).
pub const Output = struct {
    cm: Hash32,
    kem_ct: [p.CT_LEN]u8,
    ciphertext: []const u8,
};

/// A unified shielded transaction. `mint`/`burn` are the only public value events (issuance and
/// destruction); ordinary transfers leave both zero. `anchor` is shared by all spends.
pub const ShieldedTx = struct {
    version: u8 = VERSION,
    network: u8,
    anchor: Hash32,
    spends: []Spend,
    outputs: []Output,
    fee: u64,
    mint: u64 = 0,
    burn: u64 = 0,
    binding_pk: [p.PK_LEN]u8,
    binding_sig: [p.SIG_LEN]u8,

    /// Free the allocator-owned variable fields and the spend/output arrays.
    pub fn deinit(self: *ShieldedTx, a: Allocator) void {
        for (self.spends) |s| a.free(s.proof);
        for (self.outputs) |o| a.free(o.ciphertext);
        a.free(self.spends);
        a.free(self.outputs);
    }

    /// Write the part of the transaction that the binding signature covers (everything except the
    /// signature itself). The transaction-binding digest is taken over exactly these bytes.
    fn writeSignable(self: ShieldedTx, a: Allocator, w: *codec.Writer) !void {
        try w.u8v(a, self.version);
        try w.u8v(a, self.network);
        try w.fixed(a, &self.anchor);
        try w.u64v(a, self.fee);
        try w.u64v(a, self.mint);
        try w.u64v(a, self.burn);
        try w.u32v(a, @intCast(self.spends.len));
        for (self.spends) |s| {
            try w.fixed(a, &s.nullifier);
            try w.varBytes(a, s.proof);
        }
        try w.u32v(a, @intCast(self.outputs.len));
        for (self.outputs) |o| {
            try w.fixed(a, &o.cm);
            try w.fixed(a, &o.kem_ct);
            try w.varBytes(a, o.ciphertext);
        }
        try w.fixed(a, &self.binding_pk);
    }

    /// Canonical full encoding (signable part followed by the binding signature).
    pub fn serialize(self: ShieldedTx, a: Allocator) ![]u8 {
        var w = codec.Writer{};
        errdefer w.deinit(a);
        try self.writeSignable(a, &w);
        try w.fixed(a, &self.binding_sig);
        return w.toOwnedSlice(a);
    }

    /// The transaction-binding digest (sighash): a domain-separated SHA3 over the canonical
    /// signable bytes. Bound into the binding signature *and* fed to every spend proof as a public
    /// input, so a proof cannot be lifted to another transaction.
    pub fn bindingDigest(self: ShieldedTx, a: Allocator) !Hash32 {
        var w = codec.Writer{};
        defer w.deinit(a);
        try self.writeSignable(a, &w);
        return p.hashDomain("lattica:v1:txid", &.{w.buf.items});
    }

    /// Parse a canonically-encoded transaction. Allocates copies of the variable fields (the
    /// returned tx owns its data); rejects non-canonical encodings and trailing bytes.
    pub fn deserialize(a: Allocator, bytes: []const u8) Error!ShieldedTx {
        var r = codec.Reader.init(bytes);
        const version = try r.u8v();
        if (version != VERSION) return Error.BadVersion;
        const network = try r.u8v();
        const anchor = try r.fixed(32);
        const fee = try r.u64v();
        const mint = try r.u64v();
        const burn = try r.u64v();

        const n_spends = try r.u32v();
        if (n_spends > MAX_SPENDS) return Error.TooManySpends;
        const spends = try a.alloc(Spend, n_spends);
        errdefer a.free(spends);
        var built_spends: usize = 0;
        errdefer for (spends[0..built_spends]) |s| a.free(s.proof);
        for (spends) |*s| {
            s.nullifier = try r.fixed(32);
            s.proof = try a.dupe(u8, try r.varBytes());
            built_spends += 1;
        }

        const n_outputs = try r.u32v();
        if (n_outputs > MAX_OUTPUTS) return Error.TooManyOutputs;
        const outputs = try a.alloc(Output, n_outputs);
        errdefer a.free(outputs);
        var built_outputs: usize = 0;
        errdefer for (outputs[0..built_outputs]) |o| a.free(o.ciphertext);
        for (outputs) |*o| {
            o.cm = try r.fixed(32);
            o.kem_ct = try r.fixed(p.CT_LEN);
            o.ciphertext = try a.dupe(u8, try r.varBytes());
            built_outputs += 1;
        }

        const binding_pk = try r.fixed(p.PK_LEN);
        const binding_sig = try r.fixed(p.SIG_LEN);
        try r.finish();

        return .{
            .version = version,
            .network = network,
            .anchor = anchor,
            .spends = spends,
            .outputs = outputs,
            .fee = fee,
            .mint = mint,
            .burn = burn,
            .binding_pk = binding_pk,
            .binding_sig = binding_sig,
        };
    }

    /// Cheap context checks (integration doc §2): version/network, size limits, and the binding
    /// signature over the canonical digest. Proof verification and nullifier/anchor state checks
    /// are separate (see `ffi.zig` and the node).
    pub fn checkContext(self: ShieldedTx, a: Allocator, network: u8) Error!void {
        if (self.version != VERSION) return Error.BadVersion;
        if (self.network != network) return Error.BadNetwork;
        if (self.spends.len > MAX_SPENDS) return Error.TooManySpends;
        if (self.outputs.len > MAX_OUTPUTS) return Error.TooManyOutputs;
        const dg = try self.bindingDigest(a);
        if (!p.verify(&self.binding_pk, &dg, &self.binding_sig)) return Error.BadBindingSignature;
    }

    /// The public supply delta of this transaction (integration doc §5). The hidden-value balance
    /// `sum(in) + mint = sum(out) + fee + burn` is enforced inside the spend proof; here we only
    /// move the *public* counters.
    pub fn supplyDelta(self: ShieldedTx) SupplyDelta {
        return .{ .issued = self.mint, .burned = self.burn, .fee = self.fee };
    }
};

// ---------------------------------------------------------------------------------------
// Supply model
// ---------------------------------------------------------------------------------------

pub const SupplyDelta = struct {
    issued: u64,
    burned: u64,
    fee: u64,
};

/// Public, genesis-recomputable supply state. The invariant
/// `issued - burned == shielded_pool + fees_paid` holds after every applied transaction.
pub const SupplyState = struct {
    issued: u128 = 0,
    burned: u128 = 0,
    shielded_pool: u128 = 0,
    fees_paid: u128 = 0,

    /// Apply a transaction's public delta with checked wide arithmetic (integration doc §5):
    /// `mint` adds to issuance and the pool; `burn` removes from the pool and adds to burned; the
    /// `fee` leaves the shielded pool into fee accounting. Rejects overflow/underflow.
    pub fn apply(self: *SupplyState, d: SupplyDelta) Error!void {
        const minted: u128 = d.issued;
        const burned: u128 = d.burned;
        const fee: u128 = d.fee;

        self.issued = try add(self.issued, minted);
        self.burned = try add(self.burned, burned);
        self.fees_paid = try add(self.fees_paid, fee);
        // pool += mint; pool -= burn; pool -= fee (fee leaves the pool).
        self.shielded_pool = try add(self.shielded_pool, minted);
        self.shielded_pool = try sub(self.shielded_pool, burned);
        self.shielded_pool = try sub(self.shielded_pool, fee);
    }

    /// The audit invariant, recomputable by any full node.
    pub fn invariantHolds(self: SupplyState) bool {
        // issued - burned == shielded_pool + fees_paid
        const lhs = std.math.sub(u128, self.issued, self.burned) catch return false;
        const rhs = std.math.add(u128, self.shielded_pool, self.fees_paid) catch return false;
        return lhs == rhs;
    }
};

fn add(x: u128, y: u128) Error!u128 {
    return std.math.add(u128, x, y) catch Error.SupplyOverflow;
}
fn sub(x: u128, y: u128) Error!u128 {
    return std.math.sub(u128, x, y) catch Error.SupplyUnderflow;
}

// ---------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------

const testing = std.testing;

fn sampleTx(a: Allocator) !ShieldedTx {
    const spends = try a.alloc(Spend, 1);
    spends[0] = .{ .nullifier = [_]u8{0x11} ** 32, .proof = try a.dupe(u8, "proof-bytes-stand-in") };
    const outputs = try a.alloc(Output, 1);
    outputs[0] = .{ .cm = [_]u8{0x22} ** 32, .kem_ct = [_]u8{0x33} ** p.CT_LEN, .ciphertext = try a.dupe(u8, "ct") };
    return .{
        .network = 0,
        .anchor = [_]u8{0x44} ** 32,
        .spends = spends,
        .outputs = outputs,
        .fee = 100,
        .binding_pk = [_]u8{0x55} ** p.PK_LEN,
        .binding_sig = [_]u8{0x66} ** p.SIG_LEN,
    };
}

test "protocol: tx serialize/deserialize round trip" {
    const a = testing.allocator;
    var tx = try sampleTx(a);
    defer tx.deinit(a);
    const bytes = try tx.serialize(a);
    defer a.free(bytes);

    var parsed = try ShieldedTx.deserialize(a, bytes);
    defer parsed.deinit(a);
    try testing.expectEqual(tx.fee, parsed.fee);
    try testing.expectEqualSlices(u8, &tx.anchor, &parsed.anchor);
    try testing.expectEqual(@as(usize, 1), parsed.spends.len);
    try testing.expectEqualSlices(u8, tx.spends[0].proof, parsed.spends[0].proof);
    try testing.expectEqualSlices(u8, tx.outputs[0].ciphertext, parsed.outputs[0].ciphertext);

    // Re-serialization is byte-identical (canonical).
    const bytes2 = try parsed.serialize(a);
    defer a.free(bytes2);
    try testing.expectEqualSlices(u8, bytes, bytes2);
}

test "protocol: deserialize rejects trailing bytes" {
    const a = testing.allocator;
    var tx = try sampleTx(a);
    defer tx.deinit(a);
    const bytes = try tx.serialize(a);
    defer a.free(bytes);
    const ext = try a.alloc(u8, bytes.len + 1);
    defer a.free(ext);
    @memcpy(ext[0..bytes.len], bytes);
    ext[bytes.len] = 0;
    try testing.expectError(codec.Error.TrailingBytes, ShieldedTx.deserialize(a, ext));
}

test "protocol: binding digest changes if the body changes" {
    const a = testing.allocator;
    var tx = try sampleTx(a);
    defer tx.deinit(a);
    const d1 = try tx.bindingDigest(a);
    tx.fee += 1;
    const d2 = try tx.bindingDigest(a);
    try testing.expect(!std.mem.eql(u8, &d1, &d2));
}

test "protocol: supply invariant holds across mint, transfer, burn" {
    var s = SupplyState{};
    try testing.expect(s.invariantHolds());
    // Mint 1000 into the pool.
    try s.apply(.{ .issued = 1000, .burned = 0, .fee = 0 });
    try testing.expect(s.invariantHolds());
    try testing.expectEqual(@as(u128, 1000), s.shielded_pool);
    // Transfer with fee 100: pool -> 900, fees_paid -> 100, total unchanged.
    try s.apply(.{ .issued = 0, .burned = 0, .fee = 100 });
    try testing.expect(s.invariantHolds());
    try testing.expectEqual(@as(u128, 900), s.shielded_pool);
    try testing.expectEqual(@as(u128, 100), s.fees_paid);
    // Burn 200.
    try s.apply(.{ .issued = 0, .burned = 200, .fee = 0 });
    try testing.expect(s.invariantHolds());
    try testing.expectEqual(@as(u128, 700), s.shielded_pool);
}

test "protocol: supply rejects underflow (burn/fee exceeding pool)" {
    var s = SupplyState{};
    try s.apply(.{ .issued = 50, .burned = 0, .fee = 0 });
    try testing.expectError(Error.SupplyUnderflow, s.apply(.{ .issued = 0, .burned = 100, .fee = 0 }));
}
