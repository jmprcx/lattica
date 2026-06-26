//! # tx
//!
//! Notes, keys, addresses, and **post-quantum note encryption** for the Lattica shielded
//! protocol.
//!
//! A shielded output carries an encrypted note so only the recipient learns its value and
//! randomness. Zcash does this with an ECDH key agreement on Jubjub; Lattica replaces that
//! with **ML-KEM** encapsulation feeding a SHA3 KDF and a ChaCha20-Poly1305 AEAD — all
//! quantum-safe.
//!
//! Key derivation differs from the original PoC in one deliberate way: the ML-KEM and ML-DSA
//! keypairs are derived **deterministically from the 32-byte seed** (the production fix the
//! spec calls for), so a wallet restores from the seed alone. The encapsulation coins for
//! note encryption are likewise derived from the commitment, keeping the whole system
//! reproducible.

const std = @import("std");
const Allocator = std.mem.Allocator;
const p = @import("primitives.zig");
const Hash32 = p.Hash32;

// ---------------------------------------------------------------------------------------
// Notes
// ---------------------------------------------------------------------------------------

/// A shielded note. Owning the note and the recipient's key lets you spend its `value`.
pub const Note = struct {
    value: u64,
    /// Recipient identifier (`Address.recipientId`).
    recipient: Hash32,
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
        });
    }

    /// The nullifier revealed when this note is spent from `position`.
    pub fn nullifier(self: Note, nk: *const Hash32, position: u64) Hash32 {
        return p.nullifier(nk, &self.rho, position);
    }

    /// Fixed-length wire encoding of the note plaintext (104 bytes).
    pub fn toBytes(self: Note) [104]u8 {
        var out: [104]u8 = undefined;
        std.mem.writeInt(u64, out[0..8], self.value, .little);
        @memcpy(out[8..40], &self.recipient);
        @memcpy(out[40..72], &self.rho);
        @memcpy(out[72..104], &self.rcm);
        return out;
    }

    /// Parse a note plaintext produced by `toBytes`.
    pub fn fromBytes(bytes: []const u8) !Note {
        if (bytes.len != 104) return error.BadNoteLength;
        var note: Note = undefined;
        var value_le: [8]u8 = undefined;
        @memcpy(&value_le, bytes[0..8]);
        note.value = std.mem.readInt(u64, &value_le, .little);
        @memcpy(&note.recipient, bytes[8..40]);
        @memcpy(&note.rho, bytes[40..72]);
        @memcpy(&note.rcm, bytes[72..104]);
        return note;
    }

    pub fn eql(self: Note, other: Note) bool {
        return self.value == other.value and
            std.mem.eql(u8, &self.recipient, &other.recipient) and
            std.mem.eql(u8, &self.rho, &other.rho) and
            std.mem.eql(u8, &self.rcm, &other.rcm);
    }
};

// ---------------------------------------------------------------------------------------
// Key hierarchy and addresses
// ---------------------------------------------------------------------------------------

/// A public payment address: a viewing-key tag plus an ML-KEM encapsulation key.
pub const Address = struct {
    ivk_tag: Hash32,
    kem_ek: [p.EK_LEN]u8,

    /// The recipient identifier bound into a note commitment.
    pub fn recipientId(self: Address) Hash32 {
        return p.hashDomain(p.domain.IVK, &.{ &self.ivk_tag, &self.kem_ek });
    }
};

/// The complete secret key material for a wallet account.
pub const FullKey = struct {
    seed: Hash32,
    nk: Hash32,
    kem: p.KemKeypair,
    sig: p.SigKeypair,

    /// Create a wallet account from a spending seed. Every keypair is derived deterministically
    /// from the seed, so the seed alone restores the wallet.
    pub fn fromSeed(seed: Hash32) !FullKey {
        const nk = p.expand(&seed, "nk");

        // 64-byte ML-KEM seed = expand(seed,"ml-kem-d") || expand(seed,"ml-kem-z").
        var ks: [64]u8 = undefined;
        const d = p.expand(&seed, "ml-kem-d");
        const z = p.expand(&seed, "ml-kem-z");
        @memcpy(ks[0..32], &d);
        @memcpy(ks[32..64], &z);
        const kem = try p.KemKeypair.fromSeed(ks);

        const dsa_seed = p.expand(&seed, "ml-dsa");
        const sig = try p.SigKeypair.fromSeed(dsa_seed);

        return .{ .seed = seed, .nk = nk, .kem = kem, .sig = sig };
    }

    /// The public payment address derived from this key.
    pub fn address(self: FullKey) Address {
        const ivk_tag = p.hashDomain(p.domain.IVK, &.{ &self.seed, &self.nk });
        return .{ .ivk_tag = ivk_tag, .kem_ek = self.kem.ekBytes() };
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

/// Encrypt `note` to `address`, producing the on-chain transmitted note. The commitment is
/// bound into the encapsulation coins, the KDF, and the AEAD associated data.
pub fn encryptNote(allocator: Allocator, address: Address, note: Note) !TransmittedNote {
    const rid = address.recipientId();
    if (!std.mem.eql(u8, &note.recipient, &rid)) return error.RecipientMismatch;
    const cm = note.commitment();
    const coins = p.expand(&cm, "kem-encaps");
    const enc = try p.encapsulate(&address.kem_ek, coins);
    const key = p.deriveNoteKey(&enc.ss, &enc.ct, &cm);
    const pt = note.toBytes();
    const ciphertext = try p.seal(allocator, key, &pt, &cm);
    return .{ .cm = cm, .kem_ct = enc.ct, .ciphertext = ciphertext };
}

/// Attempt to decrypt a transmitted note with `key`. Returns the note iff this wallet is the
/// recipient and the ciphertext authenticates and is well-formed.
pub fn tryDecrypt(allocator: Allocator, key: FullKey, tn: TransmittedNote) ?Note {
    const ss = p.decapsulate(key.kem.sk, &tn.kem_ct) catch return null;
    const note_key = p.deriveNoteKey(&ss, &tn.kem_ct, &tn.cm);
    const pt = p.open(allocator, note_key, tn.ciphertext, &tn.cm) catch return null;
    defer allocator.free(pt);
    const note = Note.fromBytes(pt) catch return null;
    // Defend against a malicious sender: the recovered note must commit to `cm` and be ours.
    const cm = note.commitment();
    if (!std.mem.eql(u8, &cm, &tn.cm)) return null;
    const rid = key.address().recipientId();
    if (!std.mem.eql(u8, &note.recipient, &rid)) return null;
    return note;
}

// ---------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------

const testing = std.testing;

fn account(seed: u8) !FullKey {
    return FullKey.fromSeed([_]u8{seed} ** 32);
}

fn noteTo(addr: Address, value: u64) Note {
    return .{ .value = value, .recipient = addr.recipientId(), .rho = [_]u8{9} ** 32, .rcm = [_]u8{3} ** 32 };
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
    const note = noteTo(alice.address(), 999);
    const parsed = try Note.fromBytes(&note.toBytes());
    try testing.expect(parsed.eql(note));
}
