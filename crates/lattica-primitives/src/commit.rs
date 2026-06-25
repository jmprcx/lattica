//! Note commitments.
//!
//! Replaces Zcash's Sinsemilla / Bowe–Hopwood Pedersen commitments (which live on the
//! Pallas/Jubjub curves and are broken by Shor) with a plain hash commitment. The
//! commitment is *hiding* via the random trapdoor `rcm` and *binding* via collision
//! resistance of SHA3 — both quantum-safe.
//!
//! Note that value-balance is **not** enforced by a homomorphic property here (as it is
//! with Pedersen commitments). Instead the Lattica circuit checks the balance equation
//! `sum(inputs) == sum(outputs) + fee` directly over the cleartext values inside the
//! zero-knowledge proof. This removes the only place Zcash relied on a homomorphic group.

use crate::{domain, hash::hash_domain, Hash32};

/// The opening of a note commitment — everything needed to recompute it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NoteCommitmentInput<'a> {
    /// Hash of the recipient's payment address / public key material.
    pub recipient: &'a [u8],
    /// Note value in the smallest unit (zatoshi-equivalent).
    pub value: u64,
    /// `rho` — uniqueness input that ties the note to its future nullifier.
    pub rho: &'a Hash32,
    /// `rcm` — the random commitment trapdoor (hiding).
    pub rcm: &'a Hash32,
}

/// Compute the note commitment `cm = H(recipient, value, rho, rcm)`.
pub fn note_commitment(input: &NoteCommitmentInput) -> Hash32 {
    hash_domain(
        domain::NOTE_COMMIT,
        &[
            input.recipient,
            &input.value.to_le_bytes(),
            input.rho,
            input.rcm,
        ],
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn commitment_binds_value() {
        let rho = [1u8; 32];
        let rcm = [2u8; 32];
        let base = NoteCommitmentInput { recipient: b"alice", value: 100, rho: &rho, rcm: &rcm };
        let cm = note_commitment(&base);

        let changed = NoteCommitmentInput { value: 101, ..base.clone() };
        assert_ne!(cm, note_commitment(&changed), "value must be bound");
    }

    #[test]
    fn commitment_hides_with_rcm() {
        let rho = [1u8; 32];
        let rcm_a = [2u8; 32];
        let rcm_b = [3u8; 32];
        let a = note_commitment(&NoteCommitmentInput { recipient: b"alice", value: 100, rho: &rho, rcm: &rcm_a });
        let b = note_commitment(&NoteCommitmentInput { recipient: b"alice", value: 100, rho: &rho, rcm: &rcm_b });
        assert_ne!(a, b, "different trapdoors must give different commitments");
    }
}
