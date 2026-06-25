//! Pseudorandom functions: nullifier derivation and key expansion.
//!
//! In Zcash these are PRFs evaluated partly over the curve; here they are keyed SHA3
//! invocations, which are cheap to also express in-circuit with the STARK-friendly hash.

use crate::{domain, hash::hash_domain, Hash32};

/// Derive a note's nullifier from the nullifier key, the note's `rho`, and its leaf
/// position in the commitment tree.
///
/// `nf = PRF(nk, rho, position)`. Revealing `nf` on spend lets the network detect a
/// double-spend without learning *which* note was spent (the link to `cm` stays inside the
/// zero-knowledge proof).
pub fn nullifier(nk: &Hash32, rho: &Hash32, position: u64) -> Hash32 {
    hash_domain(domain::NULLIFIER, &[nk, rho, &position.to_le_bytes()])
}

/// Expand a seed into a labelled 32-byte subkey: `PRF_expand(seed, label)`.
/// Used to derive the key hierarchy (nullifier key, viewing key, randomness) from a seed.
pub fn expand(seed: &Hash32, label: &[u8]) -> Hash32 {
    hash_domain(domain::PRF_EXPAND, &[seed, label])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nullifier_changes_with_position() {
        let nk = [7u8; 32];
        let rho = [9u8; 32];
        assert_ne!(nullifier(&nk, &rho, 0), nullifier(&nk, &rho, 1));
    }

    #[test]
    fn expand_labels_are_separated() {
        let seed = [4u8; 32];
        assert_ne!(expand(&seed, b"nk"), expand(&seed, b"ivk"));
    }
}
