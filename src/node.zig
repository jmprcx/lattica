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
const field = @import("field.zig");
const protocol = @import("protocol.zig");
const Hash32 = p.Hash32;

/// The circuit's range-check width (`htlc_air`/`joinsplit_air` `BITS`): every range-checked quantity
/// (values, fee, the HTLC timeout/height) is proven `< 2^RANGE_BITS`, chosen so `2·2^RANGE_BITS < p`
/// (no field wraparound). The node enforces the same bounds (defense-in-depth) so consensus never
/// trusts the proof alone for a quantity whose unboundedness would break soundness.
pub const RANGE_BITS: u6 = 52;
pub const MAX_RANGE_VALUE: u64 = @as(u64, 1) << RANGE_BITS; // exclusive bound on values / fee / height

/// True iff every 8-byte little-endian limb of `h` is a canonical field element (`< p`). A
/// non-canonical encoding is a *different* 32-byte key for the *same* field element, which would let a
/// byte-keyed nullifier set be bypassed if a verifier backend reduced instead of rejecting; the node
/// rejects non-canonical public fields as a backstop to the verifier's own canonical parse.
fn isCanonicalDigest(h: Hash32) bool {
    var k: usize = 0;
    while (k < 4) : (k += 1) {
        if (std.mem.readInt(u64, h[k * 8 ..][0..8], .little) >= field.P) return false;
    }
    return true;
}

const root_module = @import("root");
/// Genesis/test-only helpers — `Chain.bootstrapMint` and the `mock` backend — compile only when the
/// root module does NOT set `pub const lattica_production = true`. A production consensus build sets it,
/// turning any reference to those helpers into a **compile error** (audit M-09/M-10). The probe
/// `src/production_probe.zig` builds the production consensus surface with this flag on, proving the
/// live path is free of test-only APIs (`zig build check-production`, also run by `zig build test`).
const production: bool = @hasDecl(root_module, "lattica_production") and root_module.lattica_production;

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
    OversizeProof,
    OversizeOutput,
    OversizeFee, // fee ≥ 2^RANGE_BITS (defense-in-depth with the circuit's fee range check)
    OversizeHeight, // current_height ≥ 2^RANGE_BITS (would let the HTLC timeout compare wrap)
    HeightMismatch, // tx's current_height ≠ the consensus height the node is validating at
    NonCanonicalField, // a public 32-byte field has a limb ≥ p (non-canonical encoding)
    ProveFailed, // wallet-side: the prover rejected the witness (e.g. an unsatisfiable timelock)
    Internal,
};

/// Upper bound on a single output's note ciphertext (a 120-byte note plaintext + AEAD overhead is
/// ~136 bytes; this generous cap lets the node reject malformed/oversize outputs before the expensive
/// proof verification — audit M-05). The proof size bound is `ffi.MAX_PROOF_LEN`.
pub const MAX_NOTE_CIPHERTEXT_LEN: usize = 256;

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

/// A spendable HTLC note plus the swap terms the claiming party knows (the lock descriptor). The
/// claimer's key (`nk`) must own the mode-appropriate tag: `recipientId(nk, claim_div) == redeem_tag`
/// (redeem) or `== refund_tag` (refund). `note.recipient` is the htlc_root committing all four terms.
pub const HtlcSpend = struct {
    note: tx.Note, // recipient = htlc_root, note_type = poseidon2.NOTE_HTLC
    position: u64,
    path: tree.MerklePath,
    claim_div: u64, // diversifier s.t. recipientId(claimer.nk, claim_div) == the claimed tag
    mode: u64, // 1 = redeem, 0 = refund
    redeem_tag: Hash32,
    refund_tag: Hash32,
    hashlock: Hash32, // the note's committed hashlock (= SHA256(preimage))
    timeout: u64,
    preimage: ?[32]u8, // revealed on redeem; null for refund
};

/// A shielded join-split transaction. The only public data is the join-split statement plus the
/// encrypted output notes; values and input commitments stay hidden in the proof.
pub const ShieldedTx = struct {
    anchor: Hash32,
    nullifiers: [N_IN]Hash32,
    fee: u64,
    mint: u64,
    proof: []const u8,
    /// Encrypted output notes (recipients trial-decrypt to find theirs). **Each `outputs[j].cm` is
    /// the single source of truth for output commitment `j`** — it is the value appended to the note
    /// tree, the value fed to the verifier as a public input, AND the value hashed into `tx_binding`.
    /// There is no separate `out_cms` field, so the applied commitment can never differ from the
    /// proven one (audit C-01 / L-02).
    outputs: [M_OUT]tx.TransmittedNote,

    /// The output commitments, derived from the transmitted notes (the consensus-applied values).
    pub fn outCms(self: ShieldedTx) [M_OUT]Hash32 {
        var cms: [M_OUT]Hash32 = undefined;
        for (self.outputs, 0..) |o, j| cms[j] = o.cm;
        return cms;
    }

    /// Canonical 4-element digest of the public body — the sighash the proof binds via its
    /// `tx_binding` public input. Recomputed by the node so the prover can never disagree with the
    /// body it submitted. Canonicalized (each limb < p) so it round-trips through the field.
    pub fn txBinding(self: ShieldedTx) Hash32 {
        var dh = p.DomainHasher.init(TX_DOMAIN);
        var le: [8]u8 = undefined;
        dh.field(&self.anchor);
        for (self.nullifiers) |nf| dh.field(&nf);
        const out_cms = self.outCms();
        for (out_cms) |cm| dh.field(&cm);
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
            .out_cms = self.outCms(),
            .tx_binding = self.txBinding(),
            .fee = self.fee,
            .mint = self.mint,
        };
    }
};

/// A shielded **HTLC** spend (redeem or refund), verified by the `htlc_air` circuit. Like `ShieldedTx`
/// plus the timeout's `current_height` and, for a redeem, the revealed `redeem_preimage` — the node
/// derives `redeem_hashlock = SHA256(preimage)` and the circuit binds the redeemed note's committed
/// hashlock to it (the cross-chain atomic link). `outputs[j].cm` is the single source of truth (C-01).
pub const ShieldedHtlcTx = struct {
    anchor: Hash32,
    nullifiers: [N_IN]Hash32,
    fee: u64,
    mint: u64, // always 0 for an HTLC spend (issuance only via the join-split coinbase)
    current_height: u64,
    redeem_preimage: ?[32]u8, // Some(preimage) for a redeem; null for a refund
    proof: []const u8,
    outputs: [M_OUT]tx.TransmittedNote,

    pub fn outCms(self: ShieldedHtlcTx) [M_OUT]Hash32 {
        var cms: [M_OUT]Hash32 = undefined;
        for (self.outputs, 0..) |o, j| cms[j] = o.cm;
        return cms;
    }

    /// `redeem_hashlock = SHA256(preimage)` reduced to the canonical 4-limb digest (== the redeemed
    /// note's committed hashlock). All-zero for a refund (the circuit binds it only on redeem). The
    /// revealed preimage is what lets the cross-chain counterparty claim the other leg.
    pub fn redeemHashlock(self: ShieldedHtlcTx) Hash32 {
        const pre = self.redeem_preimage orelse return [_]u8{0} ** 32;
        var sha: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(&pre, &sha, .{});
        return poseidon2.digestBytes(poseidon2.digestFromBytes(sha));
    }

    /// Canonical body digest the proof binds (incl. current_height + redeem_hashlock so the whole HTLC
    /// body — not just the join-split fields — is bound).
    pub fn txBinding(self: ShieldedHtlcTx) Hash32 {
        var dh = p.DomainHasher.init(TX_DOMAIN);
        var le: [8]u8 = undefined;
        dh.field(&self.anchor);
        for (self.nullifiers) |nf| dh.field(&nf);
        const out_cms = self.outCms();
        for (out_cms) |cm| dh.field(&cm);
        std.mem.writeInt(u64, &le, self.fee, .little);
        dh.field(&le);
        std.mem.writeInt(u64, &le, self.mint, .little);
        dh.field(&le);
        std.mem.writeInt(u64, &le, self.current_height, .little);
        dh.field(&le);
        const hl = self.redeemHashlock();
        dh.field(&hl);
        for (self.outputs) |tn| {
            dh.field(&tn.kem_ct);
            dh.field(tn.ciphertext);
        }
        const raw = dh.final();
        return poseidon2.digestBytes(poseidon2.digestFromBytes(raw));
    }

    pub fn publicInputs(self: ShieldedHtlcTx) ffi.HtlcPublicInputs {
        return .{
            .anchor = self.anchor,
            .nullifiers = self.nullifiers,
            .out_cms = self.outCms(),
            .tx_binding = self.txBinding(),
            .fee = self.fee,
            .mint = self.mint,
            .current_height = self.current_height,
            .redeem_hashlock = self.redeemHashlock(),
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
        var div_le: [8]u8 = undefined;
        std.mem.writeInt(u64, &div_le, in_.note.div, .little);
        try putFelt(&w, a, &div_le); // diversifier (recipient = H(nk ‖ div))
        var asset_le: [8]u8 = undefined;
        std.mem.writeInt(u64, &asset_le, in_.note.asset, .little);
        try putFelt(&w, a, &asset_le); // hidden asset id
        try putU64(&w, a, in_.note.value);
        try putFelt(&w, a, in_.note.rho[0..8]);
        try putFelt(&w, a, in_.note.rho[8..16]); // rho limb 1 (128-bit)
        try putFelt(&w, a, in_.note.rcm[0..8]);
        try putFelt(&w, a, in_.note.rcm[8..16]); // rcm limb 1 (128-bit)
        for (in_.path.siblings) |sib| try putDigest(&w, a, sib);
        var d: usize = 0;
        while (d < DEPTH) : (d += 1) try w.append(a, @intCast((in_.position >> @intCast(d)) & 1));
    }
    for (out_notes) |o| {
        try putDigest(&w, a, o.recipient);
        var oa_le: [8]u8 = undefined;
        std.mem.writeInt(u64, &oa_le, o.asset, .little);
        try putFelt(&w, a, &oa_le); // hidden asset id
        try putU64(&w, a, o.value);
        try putFelt(&w, a, o.rho[0..8]);
        try putFelt(&w, a, o.rho[8..16]);
        try putFelt(&w, a, o.rcm[0..8]);
        try putFelt(&w, a, o.rcm[8..16]);
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
    for (0..M_OUT) |j| {
        const recipient: tx.Address = if (j < outputs.len) outputs[j].recipient else sender.address();
        const value: u64 = if (j < outputs.len) outputs[j].value else 0;
        const jb = [_]u8{@intCast(j)};
        const rho = p.hashDomain(OUT_RHO_DOMAIN, &.{ &nfs[0], &jb });
        const rcm = p.hashDomain(OUT_RCM_DOMAIN, &.{ &nfs[0], &jb });
        out_notes[j] = .{ .value = value, .recipient = recipient.recipientId(), .div = recipient.div, .rho = rho, .rcm = rcm };
        tns[j] = tx.encryptNote(allocator, recipient, out_notes[j]) catch return TxError.Internal; // tns[j].cm = out_notes[j].commitment()
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
        .fee = fee,
        .mint = mint,
        .proof = &.{},
        .outputs = tns,
    };
    const binding = t.txBinding();
    const witness = encodeWitness(allocator, sender, inputs, out_notes, fee, mint, binding) catch return TxError.Internal;
    t.proof = ffi.proveJoinSplit(allocator, witness) catch return TxError.ProveFailed;
    return t;
}

/// Serialize an HTLC spend witness (matching `lattica-prover-p3::parse_htlc_witness`): input 0 is the
/// HTLC note (note_type = HTLC + the claimed tag/terms), input 1 a PLAIN dummy, then the outputs
/// (each with note_type), then fee/mint/tx_binding/current_height.
fn encodeHtlcWitness(
    a: Allocator,
    claimer: tx.FullKey,
    spend: HtlcSpend,
    dummy: InputSpend,
    out_notes: [M_OUT]tx.Note,
    fee: u64,
    mint: u64,
    tx_binding: Hash32,
    current_height: u64,
) ![]u8 {
    var w: std.ArrayList(u8) = .empty;
    errdefer w.deinit(a);
    const nk0 = std.mem.readInt(u64, claimer.nk[0..8], .little);
    const nk1 = std.mem.readInt(u64, claimer.nk[8..16], .little);
    var le: [8]u8 = undefined;
    // input 0: the HTLC note.
    try putU64(&w, a, nk0);
    try putU64(&w, a, nk1);
    std.mem.writeInt(u64, &le, spend.claim_div, .little);
    try putFelt(&w, a, &le);
    std.mem.writeInt(u64, &le, spend.note.asset, .little);
    try putFelt(&w, a, &le);
    std.mem.writeInt(u64, &le, poseidon2.NOTE_HTLC, .little);
    try putFelt(&w, a, &le); // note_type
    try putU64(&w, a, spend.note.value);
    try putFelt(&w, a, spend.note.rho[0..8]);
    try putFelt(&w, a, spend.note.rho[8..16]);
    try putFelt(&w, a, spend.note.rcm[0..8]);
    try putFelt(&w, a, spend.note.rcm[8..16]);
    for (spend.path.siblings) |sib| try putDigest(&w, a, sib);
    var d: usize = 0;
    while (d < DEPTH) : (d += 1) try w.append(a, @intCast((spend.position >> @intCast(d)) & 1));
    std.mem.writeInt(u64, &le, spend.mode, .little);
    try putFelt(&w, a, &le); // mode
    try putDigest(&w, a, spend.redeem_tag);
    try putDigest(&w, a, spend.refund_tag);
    try putDigest(&w, a, spend.hashlock);
    try putU64(&w, a, spend.timeout);
    // input 1: a PLAIN dummy (htlc fields zeroed).
    try putU64(&w, a, nk0);
    try putU64(&w, a, nk1);
    std.mem.writeInt(u64, &le, dummy.note.div, .little);
    try putFelt(&w, a, &le);
    std.mem.writeInt(u64, &le, dummy.note.asset, .little);
    try putFelt(&w, a, &le);
    std.mem.writeInt(u64, &le, poseidon2.NOTE_PLAIN, .little);
    try putFelt(&w, a, &le);
    try putU64(&w, a, dummy.note.value);
    try putFelt(&w, a, dummy.note.rho[0..8]);
    try putFelt(&w, a, dummy.note.rho[8..16]);
    try putFelt(&w, a, dummy.note.rcm[0..8]);
    try putFelt(&w, a, dummy.note.rcm[8..16]);
    for (dummy.path.siblings) |sib| try putDigest(&w, a, sib);
    d = 0;
    while (d < DEPTH) : (d += 1) try w.append(a, @intCast((dummy.position >> @intCast(d)) & 1));
    std.mem.writeInt(u64, &le, 0, .little);
    try putFelt(&w, a, &le); // mode = 0
    try putDigest(&w, a, [_]u8{0} ** 32); // redeem_tag
    try putDigest(&w, a, [_]u8{0} ** 32); // refund_tag
    try putDigest(&w, a, [_]u8{0} ** 32); // hashlock
    try putU64(&w, a, 0); // timeout
    // outputs (note_type added vs join-split).
    for (out_notes) |o| {
        try putDigest(&w, a, o.recipient);
        std.mem.writeInt(u64, &le, o.asset, .little);
        try putFelt(&w, a, &le);
        std.mem.writeInt(u64, &le, o.note_type, .little);
        try putFelt(&w, a, &le);
        try putU64(&w, a, o.value);
        try putFelt(&w, a, o.rho[0..8]);
        try putFelt(&w, a, o.rho[8..16]);
        try putFelt(&w, a, o.rcm[0..8]);
        try putFelt(&w, a, o.rcm[8..16]);
    }
    try putU64(&w, a, fee);
    try putU64(&w, a, mint);
    try putDigest(&w, a, tx_binding);
    try putU64(&w, a, current_height);
    return w.toOwnedSlice(a);
}

/// Build a shielded HTLC spend (redeem or refund) for `spend` (input 0) padded with the owned
/// zero-value `dummy` (input 1), paying `outputs`, leaving `fee`, validated at `current_height`. The
/// proof is produced via the installed HTLC prover. The dummy's `asset` must equal the HTLC note's.
pub fn buildHtlcSpend(
    allocator: Allocator,
    claimer: tx.FullKey,
    spend: HtlcSpend,
    dummy: InputSpend,
    outputs: []const OutputReq,
    fee: u64,
    current_height: u64,
    anchor: Hash32,
) !ShieldedHtlcTx {
    if (outputs.len > M_OUT) return TxError.Internal;
    if (dummy.note.asset != spend.note.asset) return TxError.Internal; // single hidden asset per tx
    // nf0 = owner-based HTLC nullifier (mode/party-independent); nf1 = the PLAIN dummy's nullifier.
    const owner = poseidon2.digestFromBytes(spend.note.recipient);
    const rho = [2]u64{ poseidon2.feltLE(spend.note.rho[0..8]), poseidon2.feltLE(spend.note.rho[8..16]) };
    const nf0 = poseidon2.digestBytes(poseidon2.nullifierHtlc(owner, rho, spend.position));
    const nf1 = dummy.note.nullifier(&claimer.nk, dummy.position);
    const nfs = [_]Hash32{ nf0, nf1 };

    var out_notes: [M_OUT]tx.Note = undefined;
    var tns: [M_OUT]tx.TransmittedNote = undefined;
    for (0..M_OUT) |j| {
        const recipient: tx.Address = if (j < outputs.len) outputs[j].recipient else claimer.address();
        const value: u64 = if (j < outputs.len) outputs[j].value else 0;
        const jb = [_]u8{@intCast(j)};
        const orho = p.hashDomain(OUT_RHO_DOMAIN, &.{ &nf0, &jb });
        const orcm = p.hashDomain(OUT_RCM_DOMAIN, &.{ &nf0, &jb });
        out_notes[j] = .{ .value = value, .recipient = recipient.recipientId(), .div = recipient.div, .asset = spend.note.asset, .rho = orho, .rcm = orcm };
        tns[j] = tx.encryptNote(allocator, recipient, out_notes[j]) catch return TxError.Internal;
    }

    // Value balance (redeem/refund both conserve value): Σin = Σout + fee.
    const in_sum = std.math.add(u64, spend.note.value, dummy.note.value) catch return TxError.ValueOverflow;
    var out_sum: u64 = fee;
    for (out_notes) |o| out_sum = std.math.add(u64, out_sum, o.value) catch return TxError.ValueOverflow;
    if (in_sum != out_sum) return TxError.Unbalanced;

    var t = ShieldedHtlcTx{
        .anchor = anchor,
        .nullifiers = nfs,
        .fee = fee,
        .mint = 0,
        .current_height = current_height,
        .redeem_preimage = spend.preimage,
        .proof = &.{},
        .outputs = tns,
    };
    const binding = t.txBinding();
    const witness = encodeHtlcWitness(allocator, claimer, spend, dummy, out_notes, fee, 0, binding, current_height) catch return TxError.Internal;
    t.proof = ffi.proveHtlc(allocator, witness) catch return TxError.ProveFailed;
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
    /// Public, genesis-recomputable supply accounting (audit H-01). Updated from each transaction's
    /// PUBLIC delta (mint/fee) — never from hidden note values — so the invariant
    /// `issued - burned == shielded_pool + fees_paid` holds after every applied tx. The per-tx
    /// hidden-value balance itself is guaranteed cryptographically by the join-split proof; this is
    /// the node-visible aggregate a full node recomputes from genesis and a consensus layer compares
    /// against the emission schedule.
    supply: protocol.SupplyState,

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
            .supply = .{},
        };
    }

    pub fn deinit(self: *Chain) void {
        self.tree.deinit();
        self.anchors.deinit();
        self.nullifiers.deinit();
        // The chain owns every stored transmitted-note ciphertext (deep-copied on apply / allocated by
        // the bootstrap mint), so it frees them here (audit H-04 — no leak / no dangling pointers).
        for (self.transmitted.items) |tn| self.allocator.free(tn.ciphertext);
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

    /// **GENESIS / TEST-ONLY.** Mint value directly into a shielded note, bypassing the join-split
    /// proof — used only to bootstrap the demo and pad inputs (audit M-06). Production issuance MUST go
    /// through the proof- and consensus-gated coinbase path (`applyCoinbase`); host-chain/RPC code must
    /// never call this. Atomic: all fallible work (reservation, candidate supply) precedes any state
    /// mutation, so a failure leaves the chain unchanged (audit H-03).
    pub fn bootstrapMint(self: *Chain, address: tx.Address, value: u64, seed: Hash32) !Minted {
        if (production) @compileError("bootstrapMint is genesis/test-only; production issuance must go through applyCoinbase");
        var value_le: [8]u8 = undefined;
        std.mem.writeInt(u64, &value_le, value, .little);
        const rho = p.hashDomain("lattica:v1:mint-rho", &.{ &seed, &value_le });
        const rcm = p.expand(&seed, "mint-rcm");
        const note = tx.Note{ .value = value, .recipient = address.recipientId(), .div = address.div, .rho = rho, .rcm = rcm };
        const tn = tx.encryptNote(self.allocator, address, note) catch return TxError.Internal;
        errdefer self.allocator.free(tn.ciphertext); // freed unless ownership transfers to the chain below

        // Fallible phase: candidate supply + capacity reservation (no state mutation yet).
        var candidate_supply = self.supply;
        candidate_supply.apply(.{ .issued = value, .burned = 0, .fee = 0 }) catch return TxError.ValueOverflow;
        self.tree.ensureUnusedCapacity(1) catch return TxError.TreeFull;
        self.anchors.ensureUnusedCapacity(1) catch return TxError.Internal;
        self.transmitted.ensureUnusedCapacity(self.allocator, 1) catch return TxError.Internal;

        // Infallible commit.
        self.supply = candidate_supply;
        const pos = self.tree.appendAssumeCapacity(tn.cm);
        self.anchors.putAssumeCapacity(self.tree.root(), {});
        self.transmitted.appendAssumeCapacity(tn);
        return .{ .note = note, .pos = pos };
    }

    /// Genesis/test-only: insert a pre-built note (e.g. an HTLC note whose `recipient` is an htlc_root)
    /// as a tree member, crediting the shielded pool by its value. Mirrors `bootstrapMint`'s two-phase
    /// apply. HTLC notes are watched by commitment (not scanned), so the ciphertext is a placeholder.
    pub fn bootstrapNote(self: *Chain, note: tx.Note) !Minted {
        if (production) @compileError("bootstrapNote is genesis/test-only");
        const ct = self.allocator.alloc(u8, 0) catch return TxError.Internal;
        errdefer self.allocator.free(ct);
        const tn = tx.TransmittedNote{ .cm = note.commitment(), .kem_ct = [_]u8{0} ** p.CT_LEN, .ciphertext = ct };
        var candidate_supply = self.supply;
        candidate_supply.apply(.{ .issued = note.value, .burned = 0, .fee = 0 }) catch return TxError.ValueOverflow;
        self.tree.ensureUnusedCapacity(1) catch return TxError.TreeFull;
        self.anchors.ensureUnusedCapacity(1) catch return TxError.Internal;
        self.transmitted.ensureUnusedCapacity(self.allocator, 1) catch return TxError.Internal;
        self.supply = candidate_supply;
        const pos = self.tree.appendAssumeCapacity(tn.cm);
        self.anchors.putAssumeCapacity(self.tree.root(), {});
        self.transmitted.appendAssumeCapacity(tn);
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
        // ---- Cheap, deterministic checks run FIRST so an invalid tx is rejected before the expensive
        //      proof verification (DoS hardening — audit H-02). ----

        // Issuance gate. The circuit only proves balance *given* `mint`, so the node pins `mint` to the
        // consensus-authorized amount (normal txs: 0; coinbase: reward) — else dummy inputs + mint > 0 +
        // a matching output would inflate supply.
        if (t.mint != allowed_mint) return TxError.IllegalIssuance;

        // The anchor must be one the chain published.
        if (!self.isKnownAnchor(&t.anchor)) return TxError.UnknownAnchor;

        // Size limits before any heavy parsing/verification (DoS — audit M-05).
        if (t.proof.len > ffi.MAX_PROOF_LEN) return TxError.OversizeProof;
        for (t.outputs) |o| if (o.ciphertext.len > MAX_NOTE_CIPHERTEXT_LEN) return TxError.OversizeOutput;
        if (t.fee >= MAX_RANGE_VALUE) return TxError.OversizeFee; // defense-in-depth with the circuit range
        // Reject non-canonical public-field encodings before they key the nullifier set / enter the tree.
        if (!isCanonicalDigest(t.anchor)) return TxError.NonCanonicalField;
        for (t.nullifiers) |nf| if (!isCanonicalDigest(nf)) return TxError.NonCanonicalField;
        for (t.outputs) |o| if (!isCanonicalDigest(o.cm)) return TxError.NonCanonicalField;

        // Nullifiers: reject any already spent, or duplicated within this transaction.
        var seen = HashSet.init(self.allocator);
        defer seen.deinit();
        for (t.nullifiers) |nf| {
            if (self.nullifiers.contains(nf)) return TxError.DoubleSpend;
            const gop = seen.getOrPut(nf) catch return TxError.Internal;
            if (gop.found_existing) return TxError.DoubleSpend;
        }

        // ---- Proof verification: the sole authorization (fail-closed, panic-isolated). It binds
        //      ownership, membership, nullifiers, balance, range, and the whole body — incl. every
        //      output commitment, since `publicInputs().out_cms` derives from `outputs[j].cm` (the value
        //      committed below), so the proof binds exactly what enters the tree (no ghost coin; C-01). ----
        if (!ffi.verifyJoinSplit(t.proof, t.publicInputs())) return TxError.BadAuthProof;

        // ---- Atomic two-phase apply (audit H-03): perform ALL fallible work (supply arithmetic,
        //      capacity reservation, chain-owned ciphertext copies) before mutating any consensus state;
        //      the commit phase is then infallible, so a rejected/erroring tx never leaves partial state. ----
        // (a) candidate supply — atomic arithmetic on the public (mint, fee) delta (does not touch self).
        var candidate_supply = self.supply;
        candidate_supply.apply(.{ .issued = t.mint, .burned = 0, .fee = t.fee }) catch return TxError.ValueOverflow;
        // (b) reserve all capacity up front (so the commit-phase inserts/appends cannot fail).
        self.nullifiers.ensureUnusedCapacity(@intCast(N_IN)) catch return TxError.Internal;
        self.anchors.ensureUnusedCapacity(@intCast(M_OUT)) catch return TxError.Internal;
        self.transmitted.ensureUnusedCapacity(self.allocator, M_OUT) catch return TxError.Internal;
        self.tree.ensureUnusedCapacity(M_OUT) catch return TxError.TreeFull;
        // (c) chain-own each output's ciphertext via deep copy (audit H-04); on any failure, free the
        //     copies made so far (errdefer) and reject before mutating consensus state.
        var owned: [M_OUT]tx.TransmittedNote = undefined;
        var copied: usize = 0;
        errdefer for (owned[0..copied]) |o| self.allocator.free(o.ciphertext);
        for (&owned, t.outputs) |*dst, o| {
            const ct = self.allocator.dupe(u8, o.ciphertext) catch return TxError.Internal;
            dst.* = .{ .cm = o.cm, .kem_ct = o.kem_ct, .ciphertext = ct };
            copied += 1;
        }

        // ---- Infallible commit. ----
        self.supply = candidate_supply;
        for (t.nullifiers) |nf| self.nullifiers.putAssumeCapacity(nf, {});
        for (owned) |o| {
            _ = self.tree.appendAssumeCapacity(o.cm);
            self.anchors.putAssumeCapacity(self.tree.root(), {});
            self.transmitted.appendAssumeCapacity(o);
        }
    }

    /// Validate and apply a shielded **HTLC** spend (redeem or refund) at consensus height `at_height`.
    /// Same shape as `applyChecked` (cheap checks → htlc proof verify → atomic two-phase apply) but
    /// over the htlc_air statement: issuance is forbidden (`mint == 0`), and the node pins
    /// `current_height` so a prover can't backdate/forward the timeout window. The proof binds the
    /// redeem/refund mode, the party (tag-match), the timeout (vs `current_height`), and — on redeem —
    /// the committed hashlock == `SHA256(redeem_preimage)`.
    ///
    /// `at_height` MUST be the node's own consensus block height — never a value taken from the
    /// transaction. The node both pins `t.current_height == at_height` (so the timeout window is
    /// evaluated at the real height) and bounds it `< 2^RANGE_BITS` (so the in-circuit timeout
    /// subtraction cannot wrap); both checks are mirrored in the circuit (defense-in-depth).
    pub fn applyHtlc(self: *Chain, t: ShieldedHtlcTx, at_height: u64) TxError!void {
        if (t.mint != 0) return TxError.IllegalIssuance; // HTLC spends never issue (also forced in-circuit)
        if (t.current_height >= MAX_RANGE_VALUE) return TxError.OversizeHeight; // no field-wrap in the compare
        if (t.current_height != at_height) return TxError.HeightMismatch; // node-pinned consensus height
        if (t.fee >= MAX_RANGE_VALUE) return TxError.OversizeFee; // defense-in-depth with the circuit range
        if (!self.isKnownAnchor(&t.anchor)) return TxError.UnknownAnchor;
        if (t.proof.len > ffi.MAX_PROOF_LEN) return TxError.OversizeProof;
        for (t.outputs) |o| if (o.ciphertext.len > MAX_NOTE_CIPHERTEXT_LEN) return TxError.OversizeOutput;
        // Reject non-canonical encodings of the public field elements before they key the nullifier set
        // or enter the tree (backstop to the verifier's canonical parse).
        if (!isCanonicalDigest(t.anchor)) return TxError.NonCanonicalField;
        for (t.nullifiers) |nf| if (!isCanonicalDigest(nf)) return TxError.NonCanonicalField;
        for (t.outputs) |o| if (!isCanonicalDigest(o.cm)) return TxError.NonCanonicalField;

        var seen = HashSet.init(self.allocator);
        defer seen.deinit();
        for (t.nullifiers) |nf| {
            if (self.nullifiers.contains(nf)) return TxError.DoubleSpend;
            const gop = seen.getOrPut(nf) catch return TxError.Internal;
            if (gop.found_existing) return TxError.DoubleSpend;
        }

        if (!ffi.verifyHtlc(t.proof, t.publicInputs())) return TxError.BadAuthProof;

        // Atomic two-phase apply (H-03/H-04), identical discipline to applyChecked.
        var candidate_supply = self.supply;
        candidate_supply.apply(.{ .issued = 0, .burned = 0, .fee = t.fee }) catch return TxError.ValueOverflow;
        self.nullifiers.ensureUnusedCapacity(@intCast(N_IN)) catch return TxError.Internal;
        self.anchors.ensureUnusedCapacity(@intCast(M_OUT)) catch return TxError.Internal;
        self.transmitted.ensureUnusedCapacity(self.allocator, M_OUT) catch return TxError.Internal;
        self.tree.ensureUnusedCapacity(M_OUT) catch return TxError.TreeFull;
        var owned: [M_OUT]tx.TransmittedNote = undefined;
        var copied: usize = 0;
        errdefer for (owned[0..copied]) |o| self.allocator.free(o.ciphertext);
        for (&owned, t.outputs) |*dst, o| {
            const ct = self.allocator.dupe(u8, o.ciphertext) catch return TxError.Internal;
            dst.* = .{ .cm = o.cm, .kem_ct = o.kem_ct, .ciphertext = ct };
            copied += 1;
        }

        self.supply = candidate_supply;
        for (t.nullifiers) |nf| self.nullifiers.putAssumeCapacity(nf, {});
        for (owned) |o| {
            _ = self.tree.appendAssumeCapacity(o.cm);
            self.anchors.putAssumeCapacity(self.tree.root(), {});
            self.transmitted.appendAssumeCapacity(o);
        }
    }
};

// ---------------------------------------------------------------------------------------
// Mock backends — model the proof's tx-binding so node-level tests (and the wallet demo) exercise
// the real verify/prove seam without linking the Rust staticlib. Production installs the Rust
// `lattica_joinsplit_prove`/`lattica_joinsplit_verify` instead; the real prove→verify path is
// covered by `lattica-prover-p3/tests/ffi_integration.c` and `src/ffi_integration.zig`.
// ---------------------------------------------------------------------------------------

// The mock backend is compiled out of production builds (audit M-10): in a build whose root sets
// `lattica_production = true`, `mock` is an empty namespace, so `node.mock.install()` is a compile
// error — a production binary cannot install the test tx-binding backend instead of the real verifier.
pub const mock = if (production) struct {} else struct {
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

    /// HTLC "proof" = the witness's tx_binding. In the htlc witness layout tx_binding is the
    /// second-to-last field (the last 8 bytes are current_height), so it's at [len-40 .. len-8].
    pub fn proveHtlc(
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
        if (witness_len < 40 or proof_cap < 32) return 1;
        @memcpy(proof_out[0..32], witness_ptr[witness_len - 40 .. witness_len - 8]);
        proof_len.* = 32;
        pi_len.* = 0;
        return 0;
    }

    /// Same model for the HTLC statement: tx_binding sits at the same offset (anchor ‖ nf ‖ out_cm ‖
    /// tx_binding ‖ …), only the total length differs.
    pub fn verifyHtlc(proof_ptr: [*]const u8, proof_len: usize, pi_ptr: [*]const u8, pi_len: usize) callconv(.c) i32 {
        if (proof_len != 32 or pi_len != ffi.HtlcPublicInputs.ENCODED_LEN) return 1;
        const proof = proof_ptr[0..32];
        const pi = pi_ptr[0..pi_len];
        if (std.mem.eql(u8, proof, pi[TXB_OFFSET .. TXB_OFFSET + 32])) return 0;
        return 1;
    }

    /// Install the mock backends (test / demo only).
    pub fn install() void {
        ffi.setJoinSplitProveBackend(&prove);
        ffi.setJoinSplitBackend(&verify);
        ffi.setHtlcProveBackend(&proveHtlc);
        ffi.setHtlcBackend(&verifyHtlc);
    }
    pub fn uninstall() void {
        ffi.clearJoinSplitProveBackend();
        ffi.clearJoinSplitBackend();
        ffi.clearHtlcProveBackend();
        ffi.clearHtlcBackend();
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
    const m0 = try chain.bootstrapMint(key.address(), value, [_]u8{salt} ** 32);
    const m1 = try chain.bootstrapMint(key.address(), 0, [_]u8{salt +% 1} ** 32);
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

test "C-01: a swapped/ghost output commitment is rejected and not applied" {
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
    // Audit C-01: an attacker swaps output 0's commitment to an unproven (e.g. high-value ghost) note
    // after proving. outputs[j].cm is the SINGLE source bound by BOTH the proof (public input) and
    // tx_binding, so the proof no longer matches ⇒ rejected — and because apply happens only after
    // verify, the ghost commitment is never inserted (the anchor is unchanged).
    const anchor_before = chain.anchor();
    t.outputs[0].cm[0] +%= 1;
    try testing.expectError(TxError.BadAuthProof, chain.verifyAndApply(t));
    try testing.expectEqual(anchor_before, chain.anchor());
}

test "H-01: public supply accounting tracks mint/fee and the invariant holds" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    mock.install();
    defer mock.uninstall();
    var chain = try Chain.init(a);
    const alice = try account(1);
    const bob = try account(2);
    // Bootstrap issuance of 1000 into the shielded pool (the second padding mint is 0).
    const inputs = try fundTwoInputs(a, &chain, alice, 1000, 5);
    try testing.expect(chain.supply.invariantHolds());
    try testing.expectEqual(@as(u128, 1000), chain.supply.issued);
    try testing.expectEqual(@as(u128, 1000), chain.supply.shielded_pool);
    try testing.expectEqual(@as(u128, 0), chain.supply.fees_paid);
    // A transfer with fee=100: the fee leaves the pool, issuance is unchanged, invariant still holds.
    const outs = [_]OutputReq{.{ .recipient = bob.address(), .value = 900 }};
    const t = try buildTransfer(a, alice, &inputs, &outs, 100, 0, chain.anchor());
    try chain.verifyAndApply(t);
    try testing.expect(chain.supply.invariantHolds());
    try testing.expectEqual(@as(u128, 1000), chain.supply.issued);
    try testing.expectEqual(@as(u128, 100), chain.supply.fees_paid);
    try testing.expectEqual(@as(u128, 900), chain.supply.shielded_pool);
}

test "H-03: a rejected transaction leaves chain state unchanged (atomic apply)" {
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
    const supply_before = chain.supply;
    const anchor_before = chain.anchor();
    const nulls_before = chain.nullifiers.count();
    const tx_before = chain.transmitted.items.len;
    // Reject (tampered output ⇒ BadAuthProof). No supply/anchor/nullifier/transmitted mutation.
    t.outputs[0].cm[0] +%= 1;
    try testing.expectError(TxError.BadAuthProof, chain.verifyAndApply(t));
    try testing.expectEqual(supply_before.issued, chain.supply.issued);
    try testing.expectEqual(supply_before.shielded_pool, chain.supply.shielded_pool);
    try testing.expectEqual(supply_before.fees_paid, chain.supply.fees_paid);
    try testing.expectEqual(anchor_before, chain.anchor());
    try testing.expectEqual(nulls_before, chain.nullifiers.count());
    try testing.expectEqual(tx_before, chain.transmitted.items.len);
}

test "H-04: chain owns transmitted ciphertexts after the tx allocator is freed" {
    // chain uses a persistent arena; the tx uses a temporary arena that we free after apply.
    var chain_arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer chain_arena.deinit();
    const ca = chain_arena.allocator();
    mock.install();
    defer mock.uninstall();
    var chain = try Chain.init(ca);
    const alice = try account(1);
    const bob = try account(2);
    const inputs = try fundTwoInputs(ca, &chain, alice, 1000, 5);
    {
        var tx_arena = std.heap.ArenaAllocator.init(testing.allocator);
        const ta = tx_arena.allocator();
        const outs = [_]OutputReq{.{ .recipient = bob.address(), .value = 900 }};
        const t = try buildTransfer(ta, alice, &inputs, &outs, 100, 0, chain.anchor());
        try chain.verifyAndApply(t);
        tx_arena.deinit(); // frees the tx's proof + its output ciphertext buffers
    }
    // The chain deep-copied Bob's ciphertext, so it still decrypts from chain history (no dangling ptr).
    var bob_total: u64 = 0;
    for (chain.transmitted.items) |tn| {
        if (tx.tryDecrypt(ca, bob, tn)) |n| bob_total += n.value;
    }
    try testing.expectEqual(@as(u64, 900), bob_total);
}

test "M-05: oversize proof and oversize output ciphertext are rejected before verification" {
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
    // Oversize proof ⇒ rejected before the verifier is even called.
    const saved = t.proof;
    t.proof = try a.alloc(u8, ffi.MAX_PROOF_LEN + 1);
    try testing.expectError(TxError.OversizeProof, chain.verifyAndApply(t));
    t.proof = saved;
    // Oversize output ciphertext ⇒ rejected.
    t.outputs[0].ciphertext = try a.alloc(u8, MAX_NOTE_CIPHERTEXT_LEN + 1);
    try testing.expectError(TxError.OversizeOutput, chain.verifyAndApply(t));
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

test "node: a shielded HTLC redeem verifies and applies (mock backend)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    mock.install();
    defer mock.uninstall();
    var chain = try Chain.init(a);
    const claimer = try account(1);
    // Output notes: the redeemed funds → claimer (+ a zero-value dummy), like a join-split's outputs.
    var tns: [M_OUT]tx.TransmittedNote = undefined;
    const values = [_]u64{ 900, 0 };
    for (0..M_OUT) |j| {
        const jb = [_]u8{@intCast(j)};
        const rho = p.hashDomain("test:htlc-out-rho", &.{&jb});
        const rcm = p.hashDomain("test:htlc-out-rcm", &.{&jb});
        const note = tx.Note{ .value = values[j], .recipient = claimer.address().recipientId(), .div = claimer.address().div, .rho = rho, .rcm = rcm };
        tns[j] = try tx.encryptNote(a, claimer.address(), note);
    }
    var t = ShieldedHtlcTx{
        .anchor = chain.anchor(),
        .nullifiers = .{ [_]u8{7} ** 32, [_]u8{8} ** 32 },
        .fee = 0,
        .mint = 0,
        .current_height = 50,
        .redeem_preimage = [_]u8{0xAB} ** 32,
        .proof = &.{},
        .outputs = tns,
    };
    const binding = t.txBinding(); // the mock "proof" is the body's tx_binding
    t.proof = binding[0..];
    try chain.applyHtlc(t, 50);
    // applied: the nullifier is spent, the claimer can decrypt 900, and supply stays consistent.
    try testing.expect(chain.nullifiers.contains([_]u8{7} ** 32));
    try testing.expect(chain.supply.invariantHolds());
    var got: u64 = 0;
    for (chain.transmitted.items) |tn| {
        if (tx.tryDecrypt(a, claimer, tn)) |n| got += n.value;
    }
    try testing.expectEqual(@as(u64, 900), got);
    // The node pins current_height: a tx claiming a different height than consensus is rejected.
    try testing.expectError(TxError.HeightMismatch, chain.applyHtlc(t, 51));
}

test "node: a tampered HTLC body (different preimage) is rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    mock.install();
    defer mock.uninstall();
    var chain = try Chain.init(a);
    const claimer = try account(1);
    var tns: [M_OUT]tx.TransmittedNote = undefined;
    const ovals = [_]u64{ 900, 0 };
    for (0..M_OUT) |j| {
        const jb = [_]u8{@intCast(j)};
        const note = tx.Note{ .value = ovals[j], .recipient = claimer.address().recipientId(), .div = claimer.address().div, .rho = p.hashDomain("test:o-rho", &.{&jb}), .rcm = p.hashDomain("test:o-rcm", &.{&jb}) };
        tns[j] = try tx.encryptNote(a, claimer.address(), note);
    }
    var t = ShieldedHtlcTx{ .anchor = chain.anchor(), .nullifiers = .{ [_]u8{7} ** 32, [_]u8{8} ** 32 }, .fee = 0, .mint = 0, .current_height = 50, .redeem_preimage = [_]u8{0xAB} ** 32, .proof = &.{}, .outputs = tns };
    const binding = t.txBinding();
    t.proof = binding[0..];
    // Swap the revealed preimage after binding ⇒ redeem_hashlock (and tx_binding) change ⇒ the proof
    // no longer matches the body ⇒ rejected (the cross-chain atomic value can't be forged).
    t.redeem_preimage = [_]u8{0xCD} ** 32;
    try testing.expectError(TxError.BadAuthProof, chain.applyHtlc(t, 50));
}

test "node: buildHtlcSpend → applyHtlc end-to-end (mock backend)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    mock.install();
    defer mock.uninstall();
    var chain = try Chain.init(a);
    const claimer = try account(1); // the redeem party
    const refunder = try account(2);

    // The HTLC note: owner = htlc_root(redeem_tag, refund_tag, hashlock, timeout), note_type = HTLC.
    const preimage = [_]u8{0xAB} ** 32;
    var sha: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(&preimage, &sha, .{});
    const hashlock = poseidon2.digestBytes(poseidon2.digestFromBytes(sha));
    const redeem_tag = claimer.address().recipientId();
    const refund_tag = refunder.address().recipientId();
    const timeout: u64 = 100;
    const owner = poseidon2.digestBytes(poseidon2.htlcRoot(
        poseidon2.digestFromBytes(redeem_tag),
        poseidon2.digestFromBytes(refund_tag),
        poseidon2.digestFromBytes(hashlock),
        timeout,
    ));
    const htlc_note = tx.Note{ .value = 1000, .recipient = owner, .div = 0, .note_type = poseidon2.NOTE_HTLC, .rho = p.hashDomain("t:hrho", &.{}), .rcm = p.hashDomain("t:hrcm", &.{}) };
    const locked = try chain.bootstrapNote(htlc_note);
    const dummy = try chain.bootstrapMint(claimer.address(), 0, [_]u8{9} ** 32); // owned zero-value pad

    const spend = HtlcSpend{
        .note = htlc_note,
        .position = locked.pos,
        .path = try chain.merklePath(a, locked.pos),
        .claim_div = claimer.address().div,
        .mode = 1, // redeem
        .redeem_tag = redeem_tag,
        .refund_tag = refund_tag,
        .hashlock = hashlock,
        .timeout = timeout,
        .preimage = preimage,
    };
    const dummy_in = InputSpend{ .note = dummy.note, .position = dummy.pos, .path = try chain.merklePath(a, dummy.pos) };
    const outs = [_]OutputReq{.{ .recipient = claimer.address(), .value = 1000 }};

    const t = try buildHtlcSpend(a, claimer, spend, dummy_in, &outs, 0, 50, chain.anchor()); // height 50 < timeout 100
    try chain.applyHtlc(t, 50);

    var got: u64 = 0;
    for (chain.transmitted.items) |tn| {
        if (tx.tryDecrypt(a, claimer, tn)) |n| got += n.value;
    }
    try testing.expectEqual(@as(u64, 1000), got); // claimer redeemed the locked 1000
    try testing.expect(chain.supply.invariantHolds());
}

test "node: applyHtlc defense-in-depth rejects (height/fee bounds + non-canonical fields)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    mock.install();
    defer mock.uninstall();
    var chain = try Chain.init(a);
    const claimer = try account(1);
    var tns: [M_OUT]tx.TransmittedNote = undefined;
    for (0..M_OUT) |j| {
        const jb = [_]u8{@intCast(j)};
        const note = tx.Note{ .value = 0, .recipient = claimer.address().recipientId(), .div = claimer.address().div, .rho = p.hashDomain("t:dr", &.{&jb}), .rcm = p.hashDomain("t:dc", &.{&jb}) };
        tns[j] = try tx.encryptNote(a, claimer.address(), note);
    }
    const base = ShieldedHtlcTx{ .anchor = chain.anchor(), .nullifiers = .{ [_]u8{7} ** 32, [_]u8{8} ** 32 }, .fee = 0, .mint = 0, .current_height = 50, .redeem_preimage = null, .proof = &.{}, .outputs = tns };

    { // mint > 0 is forbidden (also forced in-circuit)
        var t = base;
        t.mint = 1;
        try testing.expectError(TxError.IllegalIssuance, chain.applyHtlc(t, 50));
    }
    { // current_height ≥ 2^RANGE_BITS would let the timeout compare wrap
        var t = base;
        t.current_height = MAX_RANGE_VALUE;
        try testing.expectError(TxError.OversizeHeight, chain.applyHtlc(t, MAX_RANGE_VALUE));
    }
    { // the node pins current_height to consensus (a tx claiming another height is rejected)
        try testing.expectError(TxError.HeightMismatch, chain.applyHtlc(base, 51));
    }
    { // fee ≥ 2^RANGE_BITS (defense-in-depth with the circuit range)
        var t = base;
        t.fee = MAX_RANGE_VALUE;
        try testing.expectError(TxError.OversizeFee, chain.applyHtlc(t, 50));
    }
    { // a non-canonical nullifier encoding (limb == p) is rejected before it keys the nullifier set
        var t = base;
        var nf: Hash32 = [_]u8{0} ** 32;
        std.mem.writeInt(u64, nf[0..8], field.P, .little);
        t.nullifiers[0] = nf;
        try testing.expectError(TxError.NonCanonicalField, chain.applyHtlc(t, 50));
    }
}
