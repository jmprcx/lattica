//! Notes: the unit of shielded value, its commitment, and its nullifier.

use lattica_primitives::{
    commit::{note_commitment, NoteCommitmentInput},
    prf, Hash32,
};

/// A shielded note. Owning the note and the recipient's key lets you spend its `value`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Note {
    pub value: u64,
    /// Recipient identifier (`Address::recipient_id`).
    pub recipient: Hash32,
    /// Uniqueness input tying this note to its nullifier.
    pub rho: Hash32,
    /// Commitment trapdoor (hiding randomness).
    pub rcm: Hash32,
}

impl Note {
    /// The note commitment that gets inserted into the Merkle tree.
    pub fn commitment(&self) -> Hash32 {
        note_commitment(&NoteCommitmentInput {
            recipient: &self.recipient,
            value: self.value,
            rho: &self.rho,
            rcm: &self.rcm,
        })
    }

    /// The nullifier revealed when this note is spent from `position`, using the owner's
    /// nullifier key `nk`.
    pub fn nullifier(&self, nk: &Hash32, position: u64) -> Hash32 {
        prf::nullifier(nk, &self.rho, position)
    }

    /// Fixed-length wire encoding of the note plaintext (104 bytes).
    pub fn to_bytes(&self) -> [u8; 104] {
        let mut out = [0u8; 104];
        out[0..8].copy_from_slice(&self.value.to_le_bytes());
        out[8..40].copy_from_slice(&self.recipient);
        out[40..72].copy_from_slice(&self.rho);
        out[72..104].copy_from_slice(&self.rcm);
        out
    }

    /// Parse a note plaintext produced by [`Note::to_bytes`].
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, &'static str> {
        if bytes.len() != 104 {
            return Err("bad note length");
        }
        let mut value = [0u8; 8];
        value.copy_from_slice(&bytes[0..8]);
        let mut recipient = [0u8; 32];
        recipient.copy_from_slice(&bytes[8..40]);
        let mut rho = [0u8; 32];
        rho.copy_from_slice(&bytes[40..72]);
        let mut rcm = [0u8; 32];
        rcm.copy_from_slice(&bytes[72..104]);
        Ok(Self { value: u64::from_le_bytes(value), recipient, rho, rcm })
    }
}
