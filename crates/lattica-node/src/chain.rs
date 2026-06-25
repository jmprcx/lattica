//! Minimal in-memory chain state and shielded-transaction validation.
//!
//! This is deliberately *not* a full node: there is no networking, mempool, block
//! production, or proof-of-work. It models exactly the consensus-critical shielded state —
//! the commitment tree, the set of historical anchors, and the nullifier set — and the
//! rules that validate a shielded transaction against them.

use std::collections::HashSet;

use lattica_primitives::{hash::hash_domain, prf, sig::verify as sig_verify, Hash32};
use lattica_tree::{verify_path, MerkleTree};
use lattica_tx::{encrypt_note, Address, Note, TransmittedNote};

use crate::error::TxError;
use crate::tx::ShieldedTx;

/// Commitment-tree depth (capacity 2^DEPTH notes).
pub const TREE_DEPTH: usize = 32;

pub struct Chain {
    tree: MerkleTree,
    anchors: HashSet<Hash32>,
    nullifiers: HashSet<Hash32>,
    /// Every transmitted note ever added, so wallets can scan and trial-decrypt.
    pub transmitted: Vec<TransmittedNote>,
}

impl Chain {
    pub fn new() -> Self {
        let tree = MerkleTree::new(TREE_DEPTH);
        let mut anchors = HashSet::new();
        anchors.insert(tree.root());
        Self { tree, anchors, nullifiers: HashSet::new(), transmitted: Vec::new() }
    }

    /// The current anchor (tree root).
    pub fn anchor(&self) -> Hash32 {
        self.tree.root()
    }

    pub fn is_known_anchor(&self, root: &Hash32) -> bool {
        self.anchors.contains(root)
    }

    /// Authentication path for a leaf position.
    pub fn merkle_path(&self, position: u64) -> Result<lattica_tree::MerklePath, TxError> {
        self.tree.authentication_path(position).map_err(TxError::Internal)
    }

    /// Append an output commitment and record the new anchor.
    fn insert_commitment(&mut self, cm: Hash32) -> Result<u64, TxError> {
        let pos = self.tree.append(cm).map_err(|_| TxError::TreeFull)?;
        self.anchors.insert(self.tree.root());
        Ok(pos)
    }

    /// Mint funds directly into a shielded note (a coinbase-style output used to bootstrap
    /// the demo). Returns the cleartext note and its tree position so the owner's wallet can
    /// later spend it.
    pub fn mint(&mut self, address: &Address, value: u64, seed: Hash32) -> Result<(Note, u64), TxError> {
        let rho = hash_domain(b"lattica:v1:mint-rho", &[&seed, &value.to_le_bytes()]);
        let rcm = prf::expand(&seed, b"mint-rcm");
        let note = Note { value, recipient: address.recipient_id(), rho, rcm };
        let tn = encrypt_note(address, &note).map_err(TxError::Internal)?;
        let pos = self.insert_commitment(tn.cm)?;
        self.transmitted.push(tn);
        Ok((note, pos))
    }

    /// Validate and apply a shielded transaction. On success the nullifiers are recorded and
    /// the output commitments are appended to the tree.
    pub fn verify_and_apply(&mut self, tx: &ShieldedTx) -> Result<(), TxError> {
        // 1. Binding signature over the whole transaction body.
        if !sig_verify(&tx.binding_pk, &tx.digest(), &tx.binding_sig) {
            return Err(TxError::BadBindingSignature);
        }

        // 2. Per-spend checks. Collect nullifiers to also reject in-transaction duplicates.
        let mut seen_in_tx: HashSet<Hash32> = HashSet::new();
        for spend in &tx.spends {
            if !self.is_known_anchor(&spend.anchor) {
                return Err(TxError::UnknownAnchor);
            }
            if !verify_path(&spend.anchor, &spend.cm, &spend.merkle) {
                return Err(TxError::BadMembership);
            }
            if self.nullifiers.contains(&spend.nullifier) || !seen_in_tx.insert(spend.nullifier) {
                return Err(TxError::DoubleSpend);
            }
            if !lattica_circuit::verify_authorization(&spend.auth) {
                return Err(TxError::BadAuthProof);
            }
        }

        // 3. Value balance: inputs == outputs + fee.
        let inputs: u64 = tx.spends.iter().map(|s| s.value).sum();
        let outputs_plus_fee: u64 = tx.outputs.iter().map(|o| o.value).sum::<u64>() + tx.fee;
        if inputs != outputs_plus_fee {
            return Err(TxError::Unbalanced { inputs, outputs_plus_fee });
        }

        // 4. Apply (only after all checks pass).
        for spend in &tx.spends {
            self.nullifiers.insert(spend.nullifier);
        }
        for output in &tx.outputs {
            self.insert_commitment(output.note.cm)?;
            self.transmitted.push(output.note.clone());
        }
        Ok(())
    }
}

impl Default for Chain {
    fn default() -> Self {
        Self::new()
    }
}
