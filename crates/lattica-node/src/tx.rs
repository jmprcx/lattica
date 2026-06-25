//! The shielded transaction type and its canonical digest.

use lattica_circuit::AuthProof;
use lattica_primitives::{
    hash::hash_domain,
    sig::{PK_LEN, SIG_LEN},
    Hash32,
};
use lattica_tree::MerklePath;
use lattica_tx::TransmittedNote;

const TX_DOMAIN: &[u8] = b"lattica:v1:tx-digest";

/// A spend of one shielded note.
///
/// In a production build, `cm` and `value` would be hidden — proven inside the AIR rather
/// than revealed. This PoC reveals them so the node can check membership and balance
/// natively while the FRI proof (the hard, novel part) does the authorization; see
/// `lattica-circuit` docs.
#[derive(Clone, Debug)]
pub struct Spend {
    /// The tree root this spend's membership path was built against.
    pub anchor: Hash32,
    /// Commitment of the note being spent.
    pub cm: Hash32,
    /// Value of the note being spent.
    pub value: u64,
    /// Revealed nullifier (double-spend marker).
    pub nullifier: Hash32,
    /// Authentication path proving `cm` is under `anchor`.
    pub merkle: MerklePath,
    /// Post-quantum FRI-STARK proof of spend authorization.
    pub auth: AuthProof,
}

/// A new shielded output.
#[derive(Clone, Debug)]
pub struct Output {
    pub value: u64,
    pub note: TransmittedNote,
}

/// A shielded transaction: spends, outputs, a fee, and an ML-DSA binding signature over the
/// whole body.
#[derive(Clone, Debug)]
pub struct ShieldedTx {
    pub spends: Vec<Spend>,
    pub outputs: Vec<Output>,
    pub fee: u64,
    pub binding_pk: [u8; PK_LEN],
    pub binding_sig: [u8; SIG_LEN],
}

impl ShieldedTx {
    /// Canonical 32-byte digest of everything except the binding signature. This is the
    /// message the binding signature commits to.
    pub fn digest(&self) -> Hash32 {
        let mut fields: Vec<Vec<u8>> = Vec::new();
        fields.push((self.spends.len() as u64).to_le_bytes().to_vec());
        for s in &self.spends {
            fields.push(s.anchor.to_vec());
            fields.push(s.cm.to_vec());
            fields.push(s.value.to_le_bytes().to_vec());
            fields.push(s.nullifier.to_vec());
            fields.push(s.auth.image.to_vec());
            fields.push(s.auth.proof.clone());
        }
        fields.push((self.outputs.len() as u64).to_le_bytes().to_vec());
        for o in &self.outputs {
            fields.push(o.value.to_le_bytes().to_vec());
            fields.push(o.note.cm.to_vec());
            fields.push(o.note.kem_ct.to_vec());
            fields.push(o.note.ciphertext.clone());
        }
        fields.push(self.fee.to_le_bytes().to_vec());
        let refs: Vec<&[u8]> = fields.iter().map(|v| v.as_slice()).collect();
        hash_domain(TX_DOMAIN, &refs)
    }
}
