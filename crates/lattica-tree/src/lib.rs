//! Incremental Merkle commitment tree.
//!
//! Note commitments are appended as leaves; the tree root (the "anchor") is published with
//! each block. A spend proves, in zero knowledge, that its note's commitment is a leaf
//! under some past anchor — without revealing which leaf.
//!
//! The tree is structurally identical to Zcash's Sapling/Orchard commitment tree; the only
//! change for quantum safety is the node hash. Zcash hashes nodes with Sinsemilla over the
//! Pallas curve; Lattica uses the post-quantum [`merkle_hash`] (SHA3 here; the in-circuit
//! build substitutes a STARK-friendly hash with identical framing).
//!
//! Empty subtrees short-circuit to precomputed "empty roots", so a fixed depth of 32 (over
//! four billion notes) costs only `O(filled_leaves + depth)` work despite the huge address
//! space.

use lattica_primitives::{domain, hash::hash_domain, Hash32};

/// Hash of an unfilled leaf (the empty-note sentinel).
pub const EMPTY_LEAF: Hash32 = [0u8; 32];

/// Internal-node hash: `H(left, right)`.
pub fn merkle_hash(left: &Hash32, right: &Hash32) -> Hash32 {
    hash_domain(domain::MERKLE_NODE, &[left, right])
}

/// An authentication path: the sibling at each level from the leaf up to (but excluding)
/// the root, together with the leaf's position. Length equals the tree depth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerklePath {
    pub position: u64,
    pub siblings: Vec<Hash32>,
}

/// A fixed-depth incremental Merkle tree.
#[derive(Clone, Debug)]
pub struct MerkleTree {
    depth: usize,
    leaves: Vec<Hash32>,
    /// `empty[l]` is the root of a completely empty subtree of height `l`.
    empty: Vec<Hash32>,
}

impl MerkleTree {
    /// Create an empty tree of the given depth (capacity `2^depth` leaves).
    pub fn new(depth: usize) -> Self {
        let mut empty = Vec::with_capacity(depth + 1);
        empty.push(EMPTY_LEAF);
        for l in 1..=depth {
            let prev = empty[l - 1];
            empty.push(merkle_hash(&prev, &prev));
        }
        Self { depth, leaves: Vec::new(), empty }
    }

    /// Number of leaves appended so far.
    pub fn len(&self) -> u64 {
        self.leaves.len() as u64
    }

    pub fn is_empty(&self) -> bool {
        self.leaves.is_empty()
    }

    /// Maximum number of leaves this tree can hold.
    pub fn capacity(&self) -> u128 {
        1u128 << self.depth
    }

    /// Append a leaf, returning its position.
    pub fn append(&mut self, leaf: Hash32) -> Result<u64, &'static str> {
        if (self.leaves.len() as u128) >= self.capacity() {
            return Err("tree is full");
        }
        let pos = self.leaves.len() as u64;
        self.leaves.push(leaf);
        Ok(pos)
    }

    /// The current root (anchor).
    pub fn root(&self) -> Hash32 {
        self.node(self.depth, 0)
    }

    /// Authentication path for the leaf at `position`.
    pub fn authentication_path(&self, position: u64) -> Result<MerklePath, &'static str> {
        if position >= self.len() {
            return Err("position not in tree");
        }
        let mut siblings = Vec::with_capacity(self.depth);
        let mut idx = position;
        for level in 0..self.depth {
            let sibling = idx ^ 1;
            siblings.push(self.node(level, sibling));
            idx >>= 1;
        }
        Ok(MerklePath { position, siblings })
    }

    /// Hash of the node at (`level`, `index`). Empty subtrees short-circuit.
    fn node(&self, level: usize, index: u64) -> Hash32 {
        if level == 0 {
            return self
                .leaves
                .get(index as usize)
                .copied()
                .unwrap_or(self.empty[0]);
        }
        // If no filled leaf falls under this subtree, it is the canonical empty root.
        let first_leaf = index << level;
        if first_leaf >= self.len() {
            return self.empty[level];
        }
        let left = self.node(level - 1, index * 2);
        let right = self.node(level - 1, index * 2 + 1);
        merkle_hash(&left, &right)
    }
}

/// Recompute the root implied by a leaf and an authentication path, and compare to `root`.
/// This is exactly the check the zero-knowledge circuit performs in-circuit.
pub fn verify_path(root: &Hash32, leaf: &Hash32, path: &MerklePath) -> bool {
    let mut cur = *leaf;
    let mut idx = path.position;
    for sibling in &path.siblings {
        cur = if idx & 1 == 0 {
            merkle_hash(&cur, sibling)
        } else {
            merkle_hash(sibling, &cur)
        };
        idx >>= 1;
    }
    &cur == root
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(n: u8) -> Hash32 {
        [n; 32]
    }

    #[test]
    fn empty_root_is_stable() {
        let a = MerkleTree::new(8);
        let b = MerkleTree::new(8);
        assert_eq!(a.root(), b.root());
    }

    #[test]
    fn root_changes_on_append() {
        let mut t = MerkleTree::new(8);
        let r0 = t.root();
        t.append(leaf(1)).unwrap();
        assert_ne!(r0, t.root());
    }

    #[test]
    fn paths_verify_for_all_leaves() {
        let mut t = MerkleTree::new(10);
        for i in 0..50u8 {
            t.append(leaf(i)).unwrap();
        }
        let root = t.root();
        for i in 0..50u64 {
            let path = t.authentication_path(i).unwrap();
            assert_eq!(path.siblings.len(), 10);
            assert!(verify_path(&root, &leaf(i as u8), &path), "leaf {i} should verify");
        }
    }

    #[test]
    fn wrong_leaf_fails_verification() {
        let mut t = MerkleTree::new(10);
        for i in 0..8u8 {
            t.append(leaf(i)).unwrap();
        }
        let root = t.root();
        let path = t.authentication_path(3).unwrap();
        assert!(verify_path(&root, &leaf(3), &path));
        assert!(!verify_path(&root, &leaf(99), &path), "a different leaf must not verify");
    }

    #[test]
    fn stale_root_fails_after_growth() {
        let mut t = MerkleTree::new(10);
        for i in 0..8u8 {
            t.append(leaf(i)).unwrap();
        }
        let path = t.authentication_path(3).unwrap();
        let old_root = t.root();
        // Path against the contemporaneous root verifies...
        assert!(verify_path(&old_root, &leaf(3), &path));
        // ...but appending more leaves changes the root, so the old path no longer matches
        // the new root (the spend must reference the anchor it was built against).
        t.append(leaf(50)).unwrap();
        let new_root = t.root();
        assert!(!verify_path(&new_root, &leaf(3), &path));
    }

    #[test]
    fn deep_tree_is_cheap() {
        // Depth 32 = >4e9 capacity; empty-subtree pruning keeps this instant.
        let mut t = MerkleTree::new(32);
        let p0 = t.append(leaf(1)).unwrap();
        let p1 = t.append(leaf(2)).unwrap();
        assert_eq!((p0, p1), (0, 1));
        let root = t.root();
        let path = t.authentication_path(1).unwrap();
        assert_eq!(path.siblings.len(), 32);
        assert!(verify_path(&root, &leaf(2), &path));
    }
}
