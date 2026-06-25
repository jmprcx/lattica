//! # lattica-primitives
//!
//! Pure post-quantum cryptographic primitives for the **Lattica** shielded protocol —
//! a clean-slate, Zcash-style private payment system with **no elliptic-curve / discrete-log
//! dependency anywhere on the critical path**.
//!
//! Everything here reduces to one of two believed-quantum-safe assumptions:
//!
//! * **Hash security** (collision / preimage resistance) — via SHA3/Keccak for commitments,
//!   nullifiers, PRFs and key derivation.
//! * **Module-lattice hardness** (MLWE / MSIS) — via NIST [`fips203`] (ML-KEM) for note
//!   encryption key agreement and [`fips204`] (ML-DSA) for signatures.
//!
//! Symmetric confidentiality uses ChaCha20-Poly1305 with 256-bit keys, which Grover only
//! weakens quadratically (≈128-bit post-quantum security — acceptable).
//!
//! This crate deliberately does **not** implement any primitive by hand; it wraps audited,
//! standards-tracking crates and adds domain-separated framing for the protocol.

pub mod hash;
pub mod commit;
pub mod prf;
pub mod kdf;
pub mod aead;
pub mod kem;
pub mod sig;

/// A 32-byte digest / field-sized value used throughout the protocol.
pub type Hash32 = [u8; 32];

/// Domain-separation tags. Every hash invocation in the protocol is bound to exactly one
/// of these so that a digest produced for one purpose can never be reinterpreted as another.
pub mod domain {
    pub const NOTE_COMMIT: &[u8] = b"lattica:v1:note-commit";
    pub const NULLIFIER: &[u8] = b"lattica:v1:nullifier";
    pub const MERKLE_NODE: &[u8] = b"lattica:v1:merkle-node";
    pub const KDF_NOTE: &[u8] = b"lattica:v1:kdf-note";
    pub const PRF_EXPAND: &[u8] = b"lattica:v1:prf-expand";
    pub const IVK: &[u8] = b"lattica:v1:ivk";
}
