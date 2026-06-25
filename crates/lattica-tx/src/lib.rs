//! # lattica-tx
//!
//! Notes, keys, addresses, and **post-quantum note encryption** for the Lattica shielded
//! protocol.
//!
//! A shielded output carries an encrypted note so only the recipient learns its value and
//! randomness. Zcash does this with an ECDH key agreement on the Jubjub curve; Lattica
//! replaces that with **ML-KEM** encapsulation feeding a SHA3 KDF and a ChaCha20-Poly1305
//! AEAD — all quantum-safe.

pub mod keys;
pub mod note;

use lattica_primitives::{
    aead,
    kdf::derive_note_key,
    kem::{decapsulate, encapsulate, CT_LEN},
    Hash32,
};

pub use keys::{Address, FullKey};
pub use note::Note;

/// A note as transmitted on-chain: the public commitment, the ML-KEM ciphertext carrying
/// the shared secret, and the AEAD-encrypted note plaintext.
#[derive(Clone, Debug)]
pub struct TransmittedNote {
    pub cm: Hash32,
    pub kem_ct: [u8; CT_LEN],
    pub ciphertext: Vec<u8>,
}

/// Encrypt `note` to `address`, producing the on-chain transmitted note.
///
/// The commitment is bound into both the KDF and the AEAD associated data, so a ciphertext
/// cannot be lifted and replayed against a different commitment.
pub fn encrypt_note(address: &Address, note: &Note) -> Result<TransmittedNote, &'static str> {
    if note.recipient != address.recipient_id() {
        return Err("note recipient does not match address");
    }
    let (shared_secret, kem_ct) = encapsulate(&address.kem_ek).map_err(|_| "encapsulation failed")?;
    let cm = note.commitment();
    let key = derive_note_key(&shared_secret, &kem_ct, &cm);
    let ciphertext = aead::seal(&key, &note.to_bytes(), &cm).map_err(|_| "seal failed")?;
    Ok(TransmittedNote { cm, kem_ct, ciphertext })
}

/// Attempt to decrypt a transmitted note with `key`. Returns `Some(note)` iff this wallet is
/// the recipient and the ciphertext authenticates and is well-formed.
pub fn try_decrypt(key: &FullKey, tn: &TransmittedNote) -> Option<Note> {
    let shared_secret = decapsulate(&key.kem.dk, &tn.kem_ct).ok()?;
    let note_key = derive_note_key(&shared_secret, &tn.kem_ct, &tn.cm);
    let plaintext = aead::open(&note_key, &tn.ciphertext, &tn.cm).ok()?;
    let note = Note::from_bytes(&plaintext).ok()?;
    // Defend against a malicious sender: the recovered note must actually commit to `cm`
    // and must be addressed to us.
    if note.commitment() != tn.cm {
        return None;
    }
    if note.recipient != key.address().recipient_id() {
        return None;
    }
    Some(note)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn account(seed: u8) -> FullKey {
        FullKey::from_seed([seed; 32]).unwrap()
    }

    fn note_to(addr: &Address, value: u64) -> Note {
        Note { value, recipient: addr.recipient_id(), rho: [9u8; 32], rcm: [3u8; 32] }
    }

    #[test]
    fn encrypt_decrypt_round_trip() {
        let alice = account(1);
        let note = note_to(&alice.address(), 4242);
        let tn = encrypt_note(&alice.address(), &note).unwrap();
        let recovered = try_decrypt(&alice, &tn).expect("recipient decrypts");
        assert_eq!(recovered, note);
    }

    #[test]
    fn non_recipient_cannot_decrypt() {
        let alice = account(1);
        let bob = account(2);
        let note = note_to(&alice.address(), 4242);
        let tn = encrypt_note(&alice.address(), &note).unwrap();
        assert!(try_decrypt(&bob, &tn).is_none(), "bob is not the recipient");
    }

    #[test]
    fn commitment_in_tree_matches_transmitted() {
        let alice = account(1);
        let note = note_to(&alice.address(), 100);
        let tn = encrypt_note(&alice.address(), &note).unwrap();
        assert_eq!(tn.cm, note.commitment());
    }

    #[test]
    fn nullifier_is_deterministic_per_position() {
        let alice = account(1);
        let note = note_to(&alice.address(), 100);
        let a = note.nullifier(&alice.nk, 7);
        let b = note.nullifier(&alice.nk, 7);
        assert_eq!(a, b);
        assert_ne!(a, note.nullifier(&alice.nk, 8));
    }

    #[test]
    fn note_serialization_round_trip() {
        let alice = account(1);
        let note = note_to(&alice.address(), 999);
        assert_eq!(Note::from_bytes(&note.to_bytes()).unwrap(), note);
    }
}
