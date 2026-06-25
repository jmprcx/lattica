//! Domain-separated hashing.
//!
//! SHA3-256 (Keccak) is used as the conservative, out-of-circuit hash. The in-circuit
//! variant of the protocol substitutes an arithmetization-friendly hash (Poseidon2/Rescue)
//! over the STARK field — see the `lattica-circuit` crate — but the *framing* (domain tag
//! plus length-prefixed fields) is identical so commitments stay consistent across both.

use sha3::{Digest, Sha3_256};

use crate::Hash32;

/// Hash a sequence of byte fields under a domain-separation tag.
///
/// Each field is length-prefixed (8-byte little-endian length) before being absorbed, so
/// that `["ab", "c"]` and `["a", "bc"]` produce different digests (no concatenation
/// ambiguity). The domain tag is itself length-prefixed and absorbed first.
pub fn hash_domain(domain: &[u8], fields: &[&[u8]]) -> Hash32 {
    let mut h = Sha3_256::new();
    absorb_field(&mut h, domain);
    for f in fields {
        absorb_field(&mut h, f);
    }
    let out = h.finalize();
    let mut digest = [0u8; 32];
    digest.copy_from_slice(&out);
    digest
}

fn absorb_field(h: &mut Sha3_256, field: &[u8]) {
    h.update((field.len() as u64).to_le_bytes());
    h.update(field);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic() {
        let a = hash_domain(b"dom", &[b"hello", b"world"]);
        let b = hash_domain(b"dom", &[b"hello", b"world"]);
        assert_eq!(a, b);
    }

    #[test]
    fn domain_separation() {
        let a = hash_domain(b"dom1", &[b"x"]);
        let b = hash_domain(b"dom2", &[b"x"]);
        assert_ne!(a, b);
    }

    #[test]
    fn no_concatenation_ambiguity() {
        // Length-prefixing must prevent ["ab","c"] from colliding with ["a","bc"].
        let a = hash_domain(b"dom", &[b"ab", b"c"]);
        let b = hash_domain(b"dom", &[b"a", b"bc"]);
        assert_ne!(a, b);
    }
}
