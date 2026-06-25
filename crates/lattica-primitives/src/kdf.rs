//! Key derivation from an ML-KEM shared secret to a symmetric AEAD key + nonce.
//!
//! The ML-KEM shared secret is 32 bytes of high-entropy keying material. We bind it to the
//! transaction context (the encapsulation ciphertext and the commitment) before deriving
//! the AEAD key, so the note ciphertext cannot be replayed against a different note.

use crate::{domain, hash::hash_domain, Hash32};

/// AEAD keying material derived from a KEM shared secret.
pub struct NoteKey {
    pub key: [u8; 32],
    pub nonce: [u8; 12],
}

/// Derive the note-encryption key and nonce.
///
/// `key  = H(shared_secret, kem_ct, cm, "key")`
/// `nonce = H(shared_secret, kem_ct, cm, "nonce")[..12]`
pub fn derive_note_key(shared_secret: &[u8], kem_ct: &[u8], cm: &Hash32) -> NoteKey {
    let key = hash_domain(domain::KDF_NOTE, &[shared_secret, kem_ct, cm, b"key"]);
    let nonce_full = hash_domain(domain::KDF_NOTE, &[shared_secret, kem_ct, cm, b"nonce"]);
    let mut nonce = [0u8; 12];
    nonce.copy_from_slice(&nonce_full[..12]);
    NoteKey { key, nonce }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn key_binds_to_context() {
        let ss = [1u8; 32];
        let ct = [2u8; 48];
        let cm = [3u8; 32];
        let a = derive_note_key(&ss, &ct, &cm);
        let cm2 = [4u8; 32];
        let b = derive_note_key(&ss, &ct, &cm2);
        assert_ne!(a.key, b.key, "key must depend on the commitment");
    }
}
