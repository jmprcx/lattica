//! ML-DSA (FIPS 204) signatures — the quantum-safe replacement for Zcash's RedPallas
//! transaction binding signature and for transparent-address authorization.
//!
//! Security level 2 (ML-DSA-44) is used by default for compact signatures; raise to
//! `ml_dsa_65` / `ml_dsa_87` for higher margins.
//!
//! Note: *spend authorization* in Lattica is proven inside the zero-knowledge circuit
//! (knowledge of the spend key), **not** via a re-randomizable signature, because no
//! standardized post-quantum re-randomizable signature scheme exists yet. ML-DSA is used
//! only where a plain (non-re-randomizable) signature suffices: binding the whole
//! transaction body, and authorizing transparent inputs.

use fips204::ml_dsa_44::{self, PrivateKey, PublicKey};
use fips204::traits::{SerDes, Signer, Verifier};

/// Length of a serialized public key, in bytes.
pub const PK_LEN: usize = ml_dsa_44::PK_LEN;
/// Length of a serialized secret key, in bytes.
pub const SK_LEN: usize = ml_dsa_44::SK_LEN;
/// Length of a signature, in bytes.
pub const SIG_LEN: usize = ml_dsa_44::SIG_LEN;

#[derive(Debug, PartialEq, Eq)]
pub struct SigError;

/// A signing keypair.
pub struct SigKeypair {
    pub pk: PublicKey,
    pub sk: PrivateKey,
}

impl SigKeypair {
    /// Generate a fresh keypair using the OS CSPRNG.
    pub fn generate() -> Result<Self, SigError> {
        let (pk, sk) = ml_dsa_44::try_keygen().map_err(|_| SigError)?;
        Ok(Self { pk, sk })
    }

    /// Serialize the public key.
    pub fn pk_bytes(&self) -> [u8; PK_LEN] {
        self.pk.clone().into_bytes()
    }

    /// Sign `message` (empty context string).
    pub fn sign(&self, message: &[u8]) -> Result<[u8; SIG_LEN], SigError> {
        self.sk.try_sign(message, &[]).map_err(|_| SigError)
    }
}

/// Verify a signature against a serialized public key.
pub fn verify(pk_bytes: &[u8; PK_LEN], message: &[u8], sig: &[u8; SIG_LEN]) -> bool {
    match PublicKey::try_from_bytes(*pk_bytes) {
        Ok(pk) => pk.verify(message, sig, &[]),
        Err(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sign_verify_round_trip() {
        let kp = SigKeypair::generate().unwrap();
        let sig = kp.sign(b"transaction body").unwrap();
        assert!(verify(&kp.pk_bytes(), b"transaction body", &sig));
    }

    #[test]
    fn tampered_message_rejected() {
        let kp = SigKeypair::generate().unwrap();
        let sig = kp.sign(b"transaction body").unwrap();
        assert!(!verify(&kp.pk_bytes(), b"different body", &sig));
    }

    #[test]
    fn wrong_key_rejected() {
        let kp = SigKeypair::generate().unwrap();
        let other = SigKeypair::generate().unwrap();
        let sig = kp.sign(b"transaction body").unwrap();
        assert!(!verify(&other.pk_bytes(), b"transaction body", &sig));
    }
}
