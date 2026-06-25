//! Key hierarchy and addresses.
//!
//! Mirrors Orchard's structure — a single spending seed expands into a nullifier key, a
//! note-encryption keypair, and a signing keypair — but every component is post-quantum.
//!
//! For PoC clarity the ML-KEM and ML-DSA keypairs are generated from the OS CSPRNG and held
//! alongside the seed, rather than derived deterministically from it. Production would seed
//! both deterministically (ML-KEM/ML-DSA both support seeded keygen) so the whole wallet
//! restores from the 32-byte seed; the protocol shape is unchanged.

use lattica_primitives::{domain, hash::hash_domain, kem::KemKeypair, prf, sig::SigKeypair, Hash32};

/// The complete secret key material for a wallet account.
pub struct FullKey {
    /// 32-byte spending seed (root of the hierarchy).
    pub seed: Hash32,
    /// Nullifier key — derived from the seed, used to compute nullifiers on spend.
    pub nk: Hash32,
    /// ML-KEM keypair for receiving (decrypting) notes.
    pub kem: KemKeypair,
    /// ML-DSA keypair for authorizing/binding transactions.
    pub sig: SigKeypair,
}

impl FullKey {
    /// Create a wallet account from a spending seed.
    pub fn from_seed(seed: Hash32) -> Result<Self, &'static str> {
        let nk = prf::expand(&seed, b"nk");
        let kem = KemKeypair::generate().map_err(|_| "kem keygen failed")?;
        let sig = SigKeypair::generate().map_err(|_| "sig keygen failed")?;
        Ok(Self { seed, nk, kem, sig })
    }

    /// The public payment address derived from this key.
    pub fn address(&self) -> Address {
        // The ivk tag is a viewing-key-derived public identifier; it lets the recipient
        // recognise their own notes and is bound into the note commitment.
        let ivk_tag = hash_domain(domain::IVK, &[&self.seed, &self.nk]);
        Address { ivk_tag, kem_ek: self.kem.ek_bytes() }
    }
}

/// A public payment address: an ML-KEM encapsulation key plus a viewing-key tag.
#[derive(Clone)]
pub struct Address {
    pub ivk_tag: Hash32,
    pub kem_ek: [u8; lattica_primitives::kem::EK_LEN],
}

impl Address {
    /// The recipient identifier bound into a note commitment. Hashing the ivk tag together
    /// with the KEM key means a note's commitment fixes *who* can spend and decrypt it.
    pub fn recipient_id(&self) -> Hash32 {
        hash_domain(domain::IVK, &[&self.ivk_tag, &self.kem_ek])
    }
}
