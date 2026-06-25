//! ML-KEM (FIPS 203) key encapsulation — the quantum-safe replacement for the ECDH key
//! agreement Zcash uses to encrypt notes to a recipient.
//!
//! Security level 3 (ML-KEM-768) is used by default: a balance of conservative margin and
//! ciphertext size suitable for embedding one encapsulation per shielded output.
//!
//! Flow: the recipient publishes an encapsulation key (`ek`) as part of their address. The
//! sender calls [`encapsulate`] to get a shared secret plus a ciphertext; the shared secret
//! is fed to the KDF to encrypt the note, and the ciphertext travels with the transaction.
//! The recipient calls [`decapsulate`] with their decapsulation key to recover the same
//! shared secret.

use fips203::ml_kem_768::{self, CipherText, DecapsKey, EncapsKey};
use fips203::traits::{Decaps, Encaps, KeyGen, SerDes};

/// Length of a serialized encapsulation (public) key, in bytes.
pub const EK_LEN: usize = ml_kem_768::EK_LEN;
/// Length of a serialized decapsulation (secret) key, in bytes.
pub const DK_LEN: usize = ml_kem_768::DK_LEN;
/// Length of a serialized ciphertext, in bytes.
pub const CT_LEN: usize = ml_kem_768::CT_LEN;
/// Length of the shared secret, in bytes.
pub const SS_LEN: usize = 32;

#[derive(Debug, PartialEq, Eq)]
pub struct KemError;

/// A recipient's KEM keypair.
pub struct KemKeypair {
    pub ek: EncapsKey,
    pub dk: DecapsKey,
}

impl KemKeypair {
    /// Generate a fresh keypair using the OS CSPRNG.
    pub fn generate() -> Result<Self, KemError> {
        let (ek, dk) = ml_kem_768::KG::try_keygen().map_err(|_| KemError)?;
        Ok(Self { ek, dk })
    }

    /// Serialize the public encapsulation key (goes into the recipient's address).
    pub fn ek_bytes(&self) -> [u8; EK_LEN] {
        self.ek.clone().into_bytes()
    }
}

/// Encapsulate to a serialized public key, producing `(shared_secret, ciphertext)`.
pub fn encapsulate(ek_bytes: &[u8; EK_LEN]) -> Result<([u8; SS_LEN], [u8; CT_LEN]), KemError> {
    let ek = EncapsKey::try_from_bytes(*ek_bytes).map_err(|_| KemError)?;
    let (ssk, ct) = ek.try_encaps().map_err(|_| KemError)?;
    Ok((ssk.into_bytes(), ct.into_bytes()))
}

/// Decapsulate a serialized ciphertext with the recipient's secret key, recovering the
/// shared secret.
pub fn decapsulate(dk: &DecapsKey, ct_bytes: &[u8; CT_LEN]) -> Result<[u8; SS_LEN], KemError> {
    let ct = CipherText::try_from_bytes(*ct_bytes).map_err(|_| KemError)?;
    let ssk = dk.try_decaps(&ct).map_err(|_| KemError)?;
    Ok(ssk.into_bytes())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encaps_decaps_round_trip() {
        let kp = KemKeypair::generate().unwrap();
        let (ss_sender, ct) = encapsulate(&kp.ek_bytes()).unwrap();
        let ss_receiver = decapsulate(&kp.dk, &ct).unwrap();
        assert_eq!(ss_sender, ss_receiver, "both parties must derive the same secret");
    }

    #[test]
    fn wrong_key_yields_different_secret() {
        let kp = KemKeypair::generate().unwrap();
        let other = KemKeypair::generate().unwrap();
        let (ss_sender, ct) = encapsulate(&kp.ek_bytes()).unwrap();
        // ML-KEM is IND-CCA2: decapsulating under the wrong key yields a (deterministic)
        // pseudo-random secret, never the sender's secret.
        let ss_wrong = decapsulate(&other.dk, &ct).unwrap();
        assert_ne!(ss_sender, ss_wrong);
    }
}
