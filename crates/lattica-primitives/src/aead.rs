//! Authenticated symmetric encryption for note plaintexts (ChaCha20-Poly1305, 256-bit key).
//!
//! Symmetric ciphers are not broken by Shor; Grover only halves the effective key length,
//! so a 256-bit key retains ~128-bit post-quantum security.

use chacha20poly1305::{
    aead::{Aead, KeyInit, Payload},
    ChaCha20Poly1305, Key, Nonce,
};

use crate::kdf::NoteKey;

#[derive(Debug, PartialEq, Eq)]
pub struct AeadError;

/// Encrypt `plaintext` with the derived note key, binding `aad` (associated data, e.g. the
/// commitment) into the authentication tag.
pub fn seal(nk: &NoteKey, plaintext: &[u8], aad: &[u8]) -> Result<Vec<u8>, AeadError> {
    let cipher = ChaCha20Poly1305::new(Key::from_slice(&nk.key));
    cipher
        .encrypt(Nonce::from_slice(&nk.nonce), Payload { msg: plaintext, aad })
        .map_err(|_| AeadError)
}

/// Decrypt and authenticate. Returns `Err` if the tag, key, nonce, or `aad` do not match.
pub fn open(nk: &NoteKey, ciphertext: &[u8], aad: &[u8]) -> Result<Vec<u8>, AeadError> {
    let cipher = ChaCha20Poly1305::new(Key::from_slice(&nk.key));
    cipher
        .decrypt(Nonce::from_slice(&nk.nonce), Payload { msg: ciphertext, aad })
        .map_err(|_| AeadError)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key() -> NoteKey {
        NoteKey { key: [42u8; 32], nonce: [7u8; 12] }
    }

    #[test]
    fn round_trip() {
        let nk = key();
        let ct = seal(&nk, b"secret note", b"cm").unwrap();
        assert_ne!(ct, b"secret note");
        assert_eq!(open(&nk, &ct, b"cm").unwrap(), b"secret note");
    }

    #[test]
    fn tampered_ciphertext_rejected() {
        let nk = key();
        let mut ct = seal(&nk, b"secret note", b"cm").unwrap();
        ct[0] ^= 0xff;
        assert!(open(&nk, &ct, b"cm").is_err());
    }

    #[test]
    fn wrong_aad_rejected() {
        let nk = key();
        let ct = seal(&nk, b"secret note", b"cm").unwrap();
        assert!(open(&nk, &ct, b"other").is_err());
    }
}
