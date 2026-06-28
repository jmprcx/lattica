//! # primitives
//!
//! Pure post-quantum cryptographic primitives for the **Lattica** shielded protocol — a
//! clean-slate, Zcash-style private payment system with **no elliptic-curve / discrete-log
//! dependency anywhere on the critical path**.
//!
//! Everything here reduces to one of two believed-quantum-safe assumptions:
//!
//!  * **Hash security** (collision / preimage resistance) — via SHA3/Keccak for commitments,
//!    nullifiers, PRFs and key derivation.
//!  * **Module-lattice hardness** (MLWE / MSIS) — via ML-KEM (FIPS 203) for note-encryption
//!    key agreement and ML-DSA (FIPS 204) for signatures.
//!
//! Symmetric confidentiality uses ChaCha20-Poly1305 with 256-bit keys (~128-bit post-quantum
//! under Grover). No primitive is hand-rolled: every one is taken from Zig's `std.crypto`,
//! and this module only adds the protocol's domain-separated framing.

const std = @import("std");
const Allocator = std.mem.Allocator;

const poseidon2 = @import("poseidon2.zig"); // C-03: on-chain hashing == the circuit's Poseidon2
const Sha3_256 = std.crypto.hash.sha3.Sha3_256;
const ChaCha20Poly1305 = std.crypto.aead.chacha_poly.ChaCha20Poly1305;
const MlKem = std.crypto.kem.ml_kem.MLKem768;
const MlDsa = std.crypto.sign.mldsa.MLDSA44;

/// A 32-byte digest / field-sized value used throughout the protocol.
pub const Hash32 = [32]u8;

/// Domain-separation tags. Every hash invocation in the protocol is bound to exactly one of
/// these so a digest produced for one purpose can never be reinterpreted as another.
pub const domain = struct {
    pub const NOTE_COMMIT: []const u8 = "lattica:v1:note-commit";
    pub const NULLIFIER: []const u8 = "lattica:v1:nullifier";
    pub const MERKLE_NODE: []const u8 = "lattica:v1:merkle-node";
    pub const KDF_NOTE: []const u8 = "lattica:v1:kdf-note";
    pub const PRF_EXPAND: []const u8 = "lattica:v1:prf-expand";
    pub const IVK: []const u8 = "lattica:v1:ivk";
};

// ---------------------------------------------------------------------------------------
// Domain-separated hashing
// ---------------------------------------------------------------------------------------

/// Incremental domain-separated hasher. Each absorbed field is length-prefixed (8-byte
/// little-endian length) so that `["ab","c"]` and `["a","bc"]` never collide. The domain tag
/// is absorbed first, the same way.
pub const DomainHasher = struct {
    h: Sha3_256,

    pub fn init(dom: []const u8) DomainHasher {
        var dh = DomainHasher{ .h = Sha3_256.init(.{}) };
        dh.field(dom);
        return dh;
    }

    pub fn field(self: *DomainHasher, bytes: []const u8) void {
        var len_le: [8]u8 = undefined;
        std.mem.writeInt(u64, &len_le, @intCast(bytes.len), .little);
        self.h.update(&len_le);
        self.h.update(bytes);
    }

    pub fn final(self: *DomainHasher) Hash32 {
        var out: Hash32 = undefined;
        self.h.final(&out);
        return out;
    }
};

/// Hash a sequence of byte fields under a domain-separation tag.
pub fn hashDomain(dom: []const u8, fields: []const []const u8) Hash32 {
    var dh = DomainHasher.init(dom);
    for (fields) |f| dh.field(f);
    return dh.final();
}

// ---------------------------------------------------------------------------------------
// Note commitments
// ---------------------------------------------------------------------------------------

/// The opening of a note commitment — everything needed to recompute it.
pub const NoteCommitmentInput = struct {
    recipient: []const u8,
    value: u64,
    rho: *const Hash32,
    rcm: *const Hash32,
    asset: u64 = 0, // hidden asset id (0 = native); all notes in a tx share one asset
    note_type: u64 = 0, // 0 = PLAIN, 1 = HTLC (committed in commitment lane 7)
};

/// `cm = H(DOM_CM, recipient, value, rho, rcm)` — **the in-circuit Poseidon2 commitment** (C-03), so
/// the on-chain commitment equals what the join-split circuit proves. `recipient` is the 4-element
/// recipientId digest; `value` reduces to a field element; `rho`/`rcm` are each 128-bit (the first
/// 16 bytes → two field elements), matching the circuit's two-permutation commitment.
pub fn noteCommitment(in: NoteCommitmentInput) Hash32 {
    var rcp: [32]u8 = [_]u8{0} ** 32;
    const rn = @min(in.recipient.len, 32);
    @memcpy(rcp[0..rn], in.recipient[0..rn]);
    var value_le: [8]u8 = undefined;
    std.mem.writeInt(u64, &value_le, in.value, .little);
    var asset_le: [8]u8 = undefined;
    std.mem.writeInt(u64, &asset_le, in.asset, .little);
    var nt_le: [8]u8 = undefined;
    std.mem.writeInt(u64, &nt_le, in.note_type, .little);
    const cm = poseidon2.commitNote(
        poseidon2.digestFromBytes(rcp),
        poseidon2.feltLE(&value_le),
        .{ poseidon2.feltLE(in.rho[0..8]), poseidon2.feltLE(in.rho[8..16]) }, // 128-bit rho
        .{ poseidon2.feltLE(in.rcm[0..8]), poseidon2.feltLE(in.rcm[8..16]) }, // 128-bit rcm
        poseidon2.feltLE(&asset_le),
        poseidon2.feltLE(&nt_le),
    );
    return poseidon2.digestBytes(cm);
}

// ---------------------------------------------------------------------------------------
// PRFs: nullifier derivation and key expansion
// ---------------------------------------------------------------------------------------

/// `nf = PRF(nk, rho, position)`. Revealed on spend; detects double-spends without revealing
/// which note was spent.
pub fn nullifier(nk: *const Hash32, rho: *const Hash32, position: u64) Hash32 {
    var pos_le: [8]u8 = undefined;
    std.mem.writeInt(u64, &pos_le, position, .little);
    // C-03: nf = H(DOM_NF, nk0, nk1, rho, pos) — the in-circuit Poseidon2 nullifier. The 128-bit
    // nk is the first 16 bytes of the key material (two field elements).
    const nf = poseidon2.nullifierHash(
        poseidon2.feltLE(nk[0..8]),
        poseidon2.feltLE(nk[8..16]),
        .{ poseidon2.feltLE(rho[0..8]), poseidon2.feltLE(rho[8..16]) }, // 128-bit rho
        poseidon2.feltLE(&pos_le),
    );
    return poseidon2.digestBytes(nf);
}

/// `PRF_expand(seed, label)` — derive a labelled 32-byte subkey from a seed.
pub fn expand(seed: *const Hash32, label: []const u8) Hash32 {
    return hashDomain(domain.PRF_EXPAND, &.{ seed, label });
}

// ---------------------------------------------------------------------------------------
// KDF: ML-KEM shared secret -> AEAD key + nonce
// ---------------------------------------------------------------------------------------

/// AEAD keying material derived from a KEM shared secret.
pub const NoteKey = struct {
    key: [32]u8,
    nonce: [12]u8,
};

/// `key = H(ss, kem_ct, cm, "key")`, `nonce = H(ss, kem_ct, cm, "nonce")[..12]`. Binding the
/// commitment in means a note ciphertext cannot be replayed against a different note.
pub fn deriveNoteKey(shared_secret: []const u8, kem_ct: []const u8, cm: *const Hash32) NoteKey {
    const key = hashDomain(domain.KDF_NOTE, &.{ shared_secret, kem_ct, cm, "key" });
    const nonce_full = hashDomain(domain.KDF_NOTE, &.{ shared_secret, kem_ct, cm, "nonce" });
    var nonce: [12]u8 = undefined;
    @memcpy(&nonce, nonce_full[0..12]);
    return .{ .key = key, .nonce = nonce };
}

// ---------------------------------------------------------------------------------------
// AEAD note encryption (ChaCha20-Poly1305, 256-bit key)
// ---------------------------------------------------------------------------------------

pub const AeadError = error{Aead};

/// Encrypt `plaintext`, binding `aad` into the tag. Output is `ciphertext || tag` (the tag is
/// the trailing 16 bytes), matching the combined form the reference implementation produced.
pub fn seal(allocator: Allocator, nk: NoteKey, plaintext: []const u8, aad: []const u8) ![]u8 {
    const tag_len = ChaCha20Poly1305.tag_length;
    const out = try allocator.alloc(u8, plaintext.len + tag_len);
    var tag: [tag_len]u8 = undefined;
    ChaCha20Poly1305.encrypt(out[0..plaintext.len], &tag, plaintext, aad, nk.nonce, nk.key);
    @memcpy(out[plaintext.len..], &tag);
    return out;
}

/// Decrypt and authenticate. Returns `error.Aead` if the tag, key, nonce, or `aad` mismatch.
pub fn open(allocator: Allocator, nk: NoteKey, ciphertext: []const u8, aad: []const u8) ![]u8 {
    const tag_len = ChaCha20Poly1305.tag_length;
    if (ciphertext.len < tag_len) return AeadError.Aead;
    const msg_len = ciphertext.len - tag_len;
    const msg = try allocator.alloc(u8, msg_len);
    var tag: [tag_len]u8 = undefined;
    @memcpy(&tag, ciphertext[msg_len..]);
    ChaCha20Poly1305.decrypt(msg, ciphertext[0..msg_len], tag, aad, nk.nonce, nk.key) catch {
        allocator.free(msg);
        return AeadError.Aead;
    };
    return msg;
}

// ---------------------------------------------------------------------------------------
// ML-KEM-768 (FIPS 203) key encapsulation
// ---------------------------------------------------------------------------------------

/// Serialized encapsulation (public) key length.
pub const EK_LEN: usize = MlKem.PublicKey.encoded_length;
/// Serialized ciphertext length.
pub const CT_LEN: usize = MlKem.ciphertext_length;
/// Shared secret length.
pub const SS_LEN: usize = MlKem.shared_length;

pub const KemError = error{Kem};

/// Result of encapsulation: a shared secret and the ciphertext carrying it.
pub const Encapsulated = struct {
    ss: [SS_LEN]u8,
    ct: [CT_LEN]u8,
};

/// A recipient's KEM keypair, derived deterministically from a 64-byte seed.
pub const KemKeypair = struct {
    pk: MlKem.PublicKey,
    sk: MlKem.SecretKey,

    pub fn fromSeed(seed: [MlKem.seed_length]u8) !KemKeypair {
        const kp = try MlKem.KeyPair.generateDeterministic(seed);
        return .{ .pk = kp.public_key, .sk = kp.secret_key };
    }

    /// Serialize the public encapsulation key (goes into the recipient's address).
    pub fn ekBytes(self: KemKeypair) [EK_LEN]u8 {
        return self.pk.toBytes();
    }
};

/// Encapsulate to a serialized public key, producing `(shared_secret, ciphertext)`. The
/// encapsulation coins are supplied by the caller so the operation is deterministic.
pub fn encapsulate(ek_bytes: *const [EK_LEN]u8, coins: [32]u8) !Encapsulated {
    const pk = MlKem.PublicKey.fromBytes(ek_bytes) catch return KemError.Kem;
    const enc = pk.encapsDeterministic(&coins);
    return .{ .ss = enc.shared_secret, .ct = enc.ciphertext };
}

/// Decapsulate a ciphertext with the recipient's secret key, recovering the shared secret.
pub fn decapsulate(sk: MlKem.SecretKey, ct_bytes: *const [CT_LEN]u8) ![SS_LEN]u8 {
    return sk.decaps(ct_bytes) catch return KemError.Kem;
}

// ---------------------------------------------------------------------------------------
// ML-DSA-44 (FIPS 204) signatures
// ---------------------------------------------------------------------------------------

/// Serialized public-key length.
pub const PK_LEN: usize = MlDsa.PublicKey.encoded_length;
/// Serialized secret-key length.
pub const SK_LEN: usize = MlDsa.SecretKey.encoded_length;
/// Signature length.
pub const SIG_LEN: usize = MlDsa.Signature.encoded_length;

pub const SigError = error{Sig};

/// A signing keypair, derived deterministically from a 32-byte seed.
pub const SigKeypair = struct {
    kp: MlDsa.KeyPair,

    pub fn fromSeed(seed: [32]u8) !SigKeypair {
        return .{ .kp = try MlDsa.KeyPair.generateDeterministic(seed) };
    }

    pub fn pkBytes(self: SigKeypair) [PK_LEN]u8 {
        return self.kp.public_key.toBytes();
    }

    /// Sign `message` with an empty context string.
    pub fn sign(self: SigKeypair, message: []const u8) ![SIG_LEN]u8 {
        const s = self.kp.sign(message, null) catch return SigError.Sig;
        return s.toBytes();
    }
};

/// Verify a signature against a serialized public key.
pub fn verify(pk_bytes: *const [PK_LEN]u8, message: []const u8, sig_bytes: *const [SIG_LEN]u8) bool {
    const pk = MlDsa.PublicKey.fromBytes(pk_bytes.*) catch return false;
    const sig = MlDsa.Signature.fromBytes(sig_bytes.*) catch return false;
    sig.verify(message, pk) catch return false;
    return true;
}

// ---------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------

const testing = std.testing;

test "hash is deterministic" {
    const a = hashDomain("dom", &.{ "hello", "world" });
    const b = hashDomain("dom", &.{ "hello", "world" });
    try testing.expectEqualSlices(u8, &a, &b);
}

test "hash domain separation" {
    const a = hashDomain("dom1", &.{"x"});
    const b = hashDomain("dom2", &.{"x"});
    try testing.expect(!std.mem.eql(u8, &a, &b));
}

test "no concatenation ambiguity" {
    const a = hashDomain("dom", &.{ "ab", "c" });
    const b = hashDomain("dom", &.{ "a", "bc" });
    try testing.expect(!std.mem.eql(u8, &a, &b));
}

test "commitment binds value" {
    const rho = [_]u8{1} ** 32;
    const rcm = [_]u8{2} ** 32;
    const cm = noteCommitment(.{ .recipient = "alice", .value = 100, .rho = &rho, .rcm = &rcm });
    const cm2 = noteCommitment(.{ .recipient = "alice", .value = 101, .rho = &rho, .rcm = &rcm });
    try testing.expect(!std.mem.eql(u8, &cm, &cm2));
}

test "commitment hides with rcm" {
    const rho = [_]u8{1} ** 32;
    const a = noteCommitment(.{ .recipient = "alice", .value = 100, .rho = &rho, .rcm = &[_]u8{2} ** 32 });
    const b = noteCommitment(.{ .recipient = "alice", .value = 100, .rho = &rho, .rcm = &[_]u8{3} ** 32 });
    try testing.expect(!std.mem.eql(u8, &a, &b));
}

test "nullifier changes with position" {
    const nk = [_]u8{7} ** 32;
    const rho = [_]u8{9} ** 32;
    const a = nullifier(&nk, &rho, 0);
    const b = nullifier(&nk, &rho, 1);
    try testing.expect(!std.mem.eql(u8, &a, &b));
}

test "expand labels are separated" {
    const seed = [_]u8{4} ** 32;
    const a = expand(&seed, "nk");
    const b = expand(&seed, "ivk");
    try testing.expect(!std.mem.eql(u8, &a, &b));
}

test "kdf key binds to context" {
    const ss = [_]u8{1} ** 32;
    const ct = [_]u8{2} ** 48;
    const a = deriveNoteKey(&ss, &ct, &[_]u8{3} ** 32);
    const b = deriveNoteKey(&ss, &ct, &[_]u8{4} ** 32);
    try testing.expect(!std.mem.eql(u8, &a.key, &b.key));
}

test "aead round trip" {
    const a = testing.allocator;
    const nk = NoteKey{ .key = [_]u8{42} ** 32, .nonce = [_]u8{7} ** 12 };
    const ct = try seal(a, nk, "secret note", "cm");
    defer a.free(ct);
    try testing.expect(!std.mem.eql(u8, ct, "secret note"));
    const pt = try open(a, nk, ct, "cm");
    defer a.free(pt);
    try testing.expectEqualSlices(u8, "secret note", pt);
}

test "aead tampered ciphertext rejected" {
    const a = testing.allocator;
    const nk = NoteKey{ .key = [_]u8{42} ** 32, .nonce = [_]u8{7} ** 12 };
    const ct = try seal(a, nk, "secret note", "cm");
    defer a.free(ct);
    ct[0] ^= 0xff;
    try testing.expectError(AeadError.Aead, open(a, nk, ct, "cm"));
}

test "aead wrong aad rejected" {
    const a = testing.allocator;
    const nk = NoteKey{ .key = [_]u8{42} ** 32, .nonce = [_]u8{7} ** 12 };
    const ct = try seal(a, nk, "secret note", "cm");
    defer a.free(ct);
    try testing.expectError(AeadError.Aead, open(a, nk, ct, "other"));
}

test "kem encaps decaps round trip" {
    const kp = try KemKeypair.fromSeed([_]u8{5} ** MlKem.seed_length);
    const ek = kp.ekBytes();
    const enc = try encapsulate(&ek, [_]u8{8} ** 32);
    const ss2 = try decapsulate(kp.sk, &enc.ct);
    try testing.expectEqualSlices(u8, &enc.ss, &ss2);
}

test "kem wrong key yields different secret" {
    const kp = try KemKeypair.fromSeed([_]u8{5} ** MlKem.seed_length);
    const other = try KemKeypair.fromSeed([_]u8{6} ** MlKem.seed_length);
    const ek = kp.ekBytes();
    const enc = try encapsulate(&ek, [_]u8{8} ** 32);
    const ss_wrong = try decapsulate(other.sk, &enc.ct);
    try testing.expect(!std.mem.eql(u8, &enc.ss, &ss_wrong));
}

test "sig sign verify round trip" {
    const kp = try SigKeypair.fromSeed([_]u8{5} ** 32);
    const sig = try kp.sign("transaction body");
    const pk = kp.pkBytes();
    try testing.expect(verify(&pk, "transaction body", &sig));
}

test "sig tampered message rejected" {
    const kp = try SigKeypair.fromSeed([_]u8{5} ** 32);
    const sig = try kp.sign("transaction body");
    const pk = kp.pkBytes();
    try testing.expect(!verify(&pk, "different body", &sig));
}

test "sig wrong key rejected" {
    const kp = try SigKeypair.fromSeed([_]u8{5} ** 32);
    const other = try SigKeypair.fromSeed([_]u8{6} ** 32);
    const sig = try kp.sign("transaction body");
    const pk = other.pkBytes();
    try testing.expect(!verify(&pk, "transaction body", &sig));
}
