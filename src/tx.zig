//! # tx
//!
//! Notes, the key hierarchy (with **diversified addresses** + a delegatable **incoming viewing
//! key**), and **post-quantum note encryption** for the Lattica shielded protocol.
//!
//! A shielded output carries an encrypted note so only the recipient learns its value and
//! randomness. Zcash does this with an ECDH key agreement on Jubjub; Lattica replaces that with
//! **ML-KEM** encapsulation feeding a SHA3 KDF and a ChaCha20-Poly1305 AEAD — all quantum-safe.
//!
//! Key hierarchy (all derived from the 32-byte seed, so the seed alone restores the wallet):
//!   * `nk` — the 128-bit nullifier / **spend** key. One `nk` spends notes to *any* of the wallet's
//!     addresses.
//!   * `div_master`, `kem_master` — together the **incoming viewing key** (`IncomingViewingKey`):
//!     they derive each address's diversifier + per-diversifier ML-KEM keypair, so a holder can
//!     *detect and decrypt* incoming notes **without** the spend key `nk` (it cannot spend).
//!   * `sig` — an ML-DSA keypair (wallet identity / future use).
//!
//! A **diversified address** at index `i` is `(d_i, recipientId = H(DOM_OWN ‖ nk ‖ d_i), ek_i)` where
//! `d_i` is a per-address diversifier and `ek_i` a per-address ML-KEM key. Different addresses are
//! unlinkable (the tags/keys share no observable structure), yet all are spendable by `nk` and
//! detectable by the viewing key. (ML-KEM has no "one secret, many public keys" structure, so the
//! KEM key is derived per diversifier rather than shared as in Sapling's `ivk·g_d`.)

const std = @import("std");
const Allocator = std.mem.Allocator;
const p = @import("primitives.zig");
const poseidon2 = @import("poseidon2.zig");
const Hash32 = p.Hash32;

/// How many diversified addresses a wallet scans when detecting incoming notes.
pub const SCAN_WINDOW: u32 = 8;

// ---------------------------------------------------------------------------------------
// Notes
// ---------------------------------------------------------------------------------------

/// A shielded note. Owning the note and the recipient's spend key lets you spend its `value`.
pub const Note = struct {
    value: u64,
    /// Recipient identifier (`Address.recipient_id` = `H(DOM_OWN ‖ nk ‖ div)`).
    recipient: Hash32,
    /// Diversifier of the address this note was sent to (a field element). The spender feeds it to
    /// the circuit so `recipient = H(nk ‖ div)` recomputes; carried in the encrypted note.
    div: u64,
    /// Hidden asset id (0 = native). Bound into the commitment; all notes in a tx share one asset.
    asset: u64 = 0,
    /// Note type: 0 = PLAIN, 1 = HTLC. For an HTLC note `recipient` is the htlc_root. Committed in
    /// commitment lane 7 so the spend circuit can distinguish PLAIN vs HTLC.
    note_type: u64 = 0,
    /// Uniqueness input tying this note to its nullifier.
    rho: Hash32,
    /// Commitment trapdoor (hiding randomness).
    rcm: Hash32,

    /// The note commitment that gets inserted into the Merkle tree.
    pub fn commitment(self: Note) Hash32 {
        return p.noteCommitment(.{
            .recipient = &self.recipient,
            .value = self.value,
            .rho = &self.rho,
            .rcm = &self.rcm,
            .asset = self.asset,
            .note_type = self.note_type,
        });
    }

    /// The nullifier revealed when this note is spent from `position`.
    pub fn nullifier(self: Note, nk: *const Hash32, position: u64) Hash32 {
        return p.nullifier(nk, &self.rho, position);
    }

    /// Fixed-length wire encoding of the note plaintext (128 bytes).
    pub fn toBytes(self: Note) [128]u8 {
        var out: [128]u8 = undefined;
        std.mem.writeInt(u64, out[0..8], self.value, .little);
        @memcpy(out[8..40], &self.recipient);
        std.mem.writeInt(u64, out[40..48], self.div, .little);
        std.mem.writeInt(u64, out[48..56], self.asset, .little);
        std.mem.writeInt(u64, out[56..64], self.note_type, .little);
        @memcpy(out[64..96], &self.rho);
        @memcpy(out[96..128], &self.rcm);
        return out;
    }

    /// Parse a note plaintext produced by `toBytes`.
    pub fn fromBytes(bytes: []const u8) !Note {
        if (bytes.len != 128) return error.BadNoteLength;
        var note: Note = undefined;
        note.value = std.mem.readInt(u64, bytes[0..8], .little);
        @memcpy(&note.recipient, bytes[8..40]);
        note.div = std.mem.readInt(u64, bytes[40..48], .little);
        note.asset = std.mem.readInt(u64, bytes[48..56], .little);
        note.note_type = std.mem.readInt(u64, bytes[56..64], .little);
        @memcpy(&note.rho, bytes[64..96]);
        @memcpy(&note.rcm, bytes[96..128]);
        return note;
    }

    pub fn eql(self: Note, other: Note) bool {
        return self.value == other.value and
            std.mem.eql(u8, &self.recipient, &other.recipient) and
            self.div == other.div and
            self.asset == other.asset and
            self.note_type == other.note_type and
            std.mem.eql(u8, &self.rho, &other.rho) and
            std.mem.eql(u8, &self.rcm, &other.rcm);
    }
};

// ---------------------------------------------------------------------------------------
// Key hierarchy and addresses
// ---------------------------------------------------------------------------------------

/// A public payment address: the in-circuit ownership tag, its diversifier, and the per-diversifier
/// ML-KEM encapsulation key. Two addresses of the same wallet are unlinkable.
pub const Address = struct {
    recipient_id: Hash32, // = H(DOM_OWN ‖ nk ‖ div)
    div: u64,
    kem_ek: [p.EK_LEN]u8,

    pub fn recipientId(self: Address) Hash32 {
        return self.recipient_id;
    }
};

/// Diversifier (a field element < p) for address index `i`.
fn deriveDiv(div_master: *const Hash32, index: u32) u64 {
    var lbl: [11]u8 = undefined;
    @memcpy(lbl[0..7], "lat-div");
    std.mem.writeInt(u32, lbl[7..11], index, .little);
    const h = p.expand(div_master, &lbl);
    return poseidon2.feltLE(h[0..8]);
}

/// Per-diversifier ML-KEM keypair for address index `i`.
fn deriveKem(kem_master: *const Hash32, index: u32) !p.KemKeypair {
    var ks: [64]u8 = undefined;
    var lbl: [11]u8 = undefined;
    @memcpy(lbl[0..7], "lat-kmd");
    std.mem.writeInt(u32, lbl[7..11], index, .little);
    const d = p.expand(kem_master, &lbl);
    @memcpy(lbl[0..7], "lat-kmz");
    const z = p.expand(kem_master, &lbl);
    @memcpy(ks[0..32], &d);
    @memcpy(ks[32..64], &z);
    return p.KemKeypair.fromSeed(ks);
}

/// `recipient_id = H(DOM_OWN ‖ nk ‖ div)` from the 128-bit `nk` and a diversifier.
fn recipientId(nk: *const Hash32, div: u64) Hash32 {
    return poseidon2.digestBytes(poseidon2.recipient(
        poseidon2.feltLE(nk[0..8]),
        poseidon2.feltLE(nk[8..16]),
        div, // already a canonical field element (deriveDiv reduces); the hash reduces regardless
    ));
}

/// The incoming viewing key: detects + decrypts incoming notes for all of a wallet's diversified
/// addresses, **without** the spend key. Safe to delegate (e.g. to an auditor or watch-only wallet).
pub const IncomingViewingKey = struct {
    div_master: Hash32,
    kem_master: Hash32,
    /// The recipient ids are `H(nk ‖ d_i)` and require `nk`; a pure viewing key checks ownership by
    /// successful AEAD decryption (the note was encrypted to `ek_i`), so it stores the spend key's
    /// public ownership tags to confirm the recovered recipient. (Detection works without them.)
    recipient_ids: [SCAN_WINDOW]Hash32,

    /// Scan a transmitted note across the wallet's diversified addresses. Returns the decrypted note
    /// (with its diversifier) and the matching address index, or null. Uses only viewing material.
    pub fn detect(self: IncomingViewingKey, allocator: Allocator, tn: TransmittedNote) ?struct { note: Note, index: u32 } {
        var i: u32 = 0;
        while (i < SCAN_WINDOW) : (i += 1) {
            const kem = deriveKem(&self.kem_master, i) catch continue;
            if (decryptWith(allocator, kem.sk, &self.recipient_ids[i], tn)) |note| {
                return .{ .note = note, .index = i };
            }
        }
        return null;
    }
};

/// The complete secret key material for a wallet account.
pub const FullKey = struct {
    seed: Hash32,
    nk: Hash32,
    div_master: Hash32,
    kem_master: Hash32,
    sig: p.SigKeypair,

    /// Create a wallet account from a spending seed.
    pub fn fromSeed(seed: Hash32) !FullKey {
        const nk = p.expand(&seed, "nk");
        const div_master = p.expand(&seed, "div-master");
        const kem_master = p.expand(&seed, "kem-master");
        const dsa_seed = p.expand(&seed, "ml-dsa");
        const sig = try p.SigKeypair.fromSeed(dsa_seed);
        return .{ .seed = seed, .nk = nk, .div_master = div_master, .kem_master = kem_master, .sig = sig };
    }

    /// The diversified payment address at index `i` (distinct, unlinkable addresses for `i = 0,1,…`).
    pub fn addressAt(self: FullKey, index: u32) !Address {
        const div = deriveDiv(&self.div_master, index);
        const kem = try deriveKem(&self.kem_master, index);
        return .{ .recipient_id = recipientId(&self.nk, div), .div = div, .kem_ek = kem.ekBytes() };
    }

    /// The default address (index 0).
    pub fn address(self: FullKey) Address {
        return self.addressAt(0) catch unreachable;
    }

    /// The delegatable incoming viewing key for this wallet.
    pub fn viewingKey(self: FullKey) IncomingViewingKey {
        var rids: [SCAN_WINDOW]Hash32 = undefined;
        var i: u32 = 0;
        while (i < SCAN_WINDOW) : (i += 1) rids[i] = recipientId(&self.nk, deriveDiv(&self.div_master, i));
        return .{ .div_master = self.div_master, .kem_master = self.kem_master, .recipient_ids = rids };
    }
};

// ---------------------------------------------------------------------------------------
// Note encryption
// ---------------------------------------------------------------------------------------

/// A note as transmitted on-chain: the public commitment, the ML-KEM ciphertext carrying the
/// shared secret, and the AEAD-encrypted note plaintext (`ciphertext` is allocator-owned).
pub const TransmittedNote = struct {
    cm: Hash32,
    kem_ct: [p.CT_LEN]u8,
    ciphertext: []u8,
};

/// Encrypt `note` to `address`, producing the on-chain transmitted note. The commitment is bound
/// into the encapsulation coins, the KDF, and the AEAD associated data.
pub fn encryptNote(allocator: Allocator, address: Address, note: Note) !TransmittedNote {
    if (!std.mem.eql(u8, &note.recipient, &address.recipient_id) or note.div != address.div) {
        return error.RecipientMismatch;
    }
    const cm = note.commitment();
    const coins = p.expand(&cm, "kem-encaps");
    const enc = try p.encapsulate(&address.kem_ek, coins);
    const key = p.deriveNoteKey(&enc.ss, &enc.ct, &cm);
    const pt = note.toBytes();
    const ciphertext = try p.seal(allocator, key, &pt, &cm);
    return .{ .cm = cm, .kem_ct = enc.ct, .ciphertext = ciphertext };
}

/// Decrypt with a specific KEM secret + expected recipient id. Returns the note iff it authenticates,
/// commits to `cm`, and is addressed to `expected_rid`.
fn decryptWith(allocator: Allocator, kem_sk: anytype, expected_rid: *const Hash32, tn: TransmittedNote) ?Note {
    const ss = p.decapsulate(kem_sk, &tn.kem_ct) catch return null;
    const note_key = p.deriveNoteKey(&ss, &tn.kem_ct, &tn.cm);
    const pt = p.open(allocator, note_key, tn.ciphertext, &tn.cm) catch return null;
    defer allocator.free(pt);
    const note = Note.fromBytes(pt) catch return null;
    const cm = note.commitment();
    if (!std.mem.eql(u8, &cm, &tn.cm)) return null;
    if (!std.mem.eql(u8, &note.recipient, expected_rid)) return null;
    return note;
}

/// Attempt to decrypt a transmitted note with `key`, scanning the wallet's diversified addresses.
/// Returns the note (with its diversifier) iff this wallet is the recipient.
pub fn tryDecrypt(allocator: Allocator, key: FullKey, tn: TransmittedNote) ?Note {
    var i: u32 = 0;
    while (i < SCAN_WINDOW) : (i += 1) {
        const kem = deriveKem(&key.kem_master, i) catch continue;
        const rid = recipientId(&key.nk, deriveDiv(&key.div_master, i));
        if (decryptWith(allocator, kem.sk, &rid, tn)) |note| return note;
    }
    return null;
}

// ---------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------

const testing = std.testing;

fn account(seed: u8) !FullKey {
    return FullKey.fromSeed([_]u8{seed} ** 32);
}

fn noteTo(addr: Address, value: u64) Note {
    return .{ .value = value, .recipient = addr.recipientId(), .div = addr.div, .rho = [_]u8{9} ** 32, .rcm = [_]u8{3} ** 32 };
}

test "encrypt decrypt round trip" {
    const a = testing.allocator;
    const alice = try account(1);
    const note = noteTo(alice.address(), 4242);
    const tn = try encryptNote(a, alice.address(), note);
    defer a.free(tn.ciphertext);
    const recovered = tryDecrypt(a, alice, tn) orelse return error.TestUnexpectedNull;
    try testing.expect(recovered.eql(note));
}

test "non-recipient cannot decrypt" {
    const a = testing.allocator;
    const alice = try account(1);
    const bob = try account(2);
    const note = noteTo(alice.address(), 4242);
    const tn = try encryptNote(a, alice.address(), note);
    defer a.free(tn.ciphertext);
    try testing.expect(tryDecrypt(a, bob, tn) == null);
}

test "diversified addresses are distinct but same-wallet detectable + spendable" {
    const a = testing.allocator;
    const alice = try account(1);
    const a0 = try alice.addressAt(0);
    const a3 = try alice.addressAt(3);
    // Unlinkable: different ownership tags, diversifiers, and KEM keys.
    try testing.expect(!std.mem.eql(u8, &a0.recipient_id, &a3.recipient_id));
    try testing.expect(a0.div != a3.div);
    try testing.expect(!std.mem.eql(u8, &a0.kem_ek, &a3.kem_ek));
    // A note to the diversified address a3 is detected + decrypted by the same wallet.
    const note = noteTo(a3, 777);
    const tn = try encryptNote(a, a3, note);
    defer a.free(tn.ciphertext);
    const got = tryDecrypt(a, alice, tn) orelse return error.TestUnexpectedNull;
    try testing.expect(got.eql(note));
    try testing.expectEqual(a3.div, got.div);
    // Spendable by the single nk: recipient = H(nk ‖ div) recomputes from the note's diversifier.
    try testing.expectEqualSlices(u8, &note.recipient, &recipientId(&alice.nk, got.div));
}

test "incoming viewing key detects without the spend key" {
    const a = testing.allocator;
    const alice = try account(1);
    const a2 = try alice.addressAt(2);
    const note = noteTo(a2, 555);
    const tn = try encryptNote(a, a2, note);
    defer a.free(tn.ciphertext);
    // The viewing key (div_master + kem_master, NO nk) finds + decrypts the note and its index.
    const ivk = alice.viewingKey();
    const found = ivk.detect(a, tn) orelse return error.TestUnexpectedNull;
    try testing.expect(found.note.eql(note));
    try testing.expectEqual(@as(u32, 2), found.index);
    // A different wallet's viewing key does not.
    const mallory = try account(9);
    try testing.expect(mallory.viewingKey().detect(a, tn) == null);
}

test "commitment in tree matches transmitted" {
    const a = testing.allocator;
    const alice = try account(1);
    const note = noteTo(alice.address(), 100);
    const tn = try encryptNote(a, alice.address(), note);
    defer a.free(tn.ciphertext);
    try testing.expectEqualSlices(u8, &tn.cm, &note.commitment());
}

test "nullifier is deterministic per position" {
    const alice = try account(1);
    const note = noteTo(alice.address(), 100);
    const x = note.nullifier(&alice.nk, 7);
    const y = note.nullifier(&alice.nk, 7);
    try testing.expectEqualSlices(u8, &x, &y);
    try testing.expect(!std.mem.eql(u8, &x, &note.nullifier(&alice.nk, 8)));
}

test "note serialization round trip" {
    const alice = try account(1);
    const note = noteTo(try alice.addressAt(5), 999);
    const parsed = try Note.fromBytes(&note.toBytes());
    try testing.expect(parsed.eql(note));
}
