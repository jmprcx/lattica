//! Wallet-side construction of a shielded transfer.

use lattica_circuit::prove_authorization;
use lattica_primitives::{prf, Hash32};
use lattica_tree::MerklePath;
use lattica_tx::{encrypt_note, Address, FullKey, Note};

use crate::error::TxError;
use crate::tx::{Output, ShieldedTx, Spend};

/// Build a one-input, one-output shielded transfer that spends `spend_note` and pays
/// `send_value` to `recipient`, leaving `fee` for the miner.
///
/// `spend_position` / `spend_path` / `anchor` come from the chain (the wallet would obtain
/// these by scanning). The returned transaction is fully self-validating: it carries a FRI
/// authorization proof and an ML-DSA binding signature.
#[allow(clippy::too_many_arguments)]
pub fn build_transfer(
    sender: &FullKey,
    spend_note: &Note,
    spend_position: u64,
    spend_path: MerklePath,
    anchor: Hash32,
    recipient: &Address,
    send_value: u64,
    fee: u64,
) -> Result<ShieldedTx, TxError> {
    if send_value + fee != spend_note.value {
        return Err(TxError::Unbalanced {
            inputs: spend_note.value,
            outputs_plus_fee: send_value + fee,
        });
    }

    // Nullifier for the spent note.
    let nullifier = spend_note.nullifier(&sender.nk, spend_position);

    // Post-quantum FRI proof of spend authorization (knowledge of the spend secret).
    let auth_secret = prf::expand(&sender.seed, b"spend-auth");
    let auth = prove_authorization(&auth_secret).map_err(TxError::Internal)?;

    // Output note to the recipient. Its rho is the spend nullifier, tying uniqueness to the
    // consumed note exactly as Orchard does.
    let out_rcm = prf::expand(&nullifier, b"out-rcm");
    let out_note = Note {
        value: send_value,
        recipient: recipient.recipient_id(),
        rho: nullifier,
        rcm: out_rcm,
    };
    let out_tn = encrypt_note(recipient, &out_note).map_err(TxError::Internal)?;

    let spend = Spend {
        anchor,
        cm: spend_note.commitment(),
        value: spend_note.value,
        nullifier,
        merkle: spend_path,
        auth,
    };
    let output = Output { value: send_value, note: out_tn };

    let mut tx = ShieldedTx {
        spends: vec![spend],
        outputs: vec![output],
        fee,
        binding_pk: sender.sig.pk_bytes(),
        binding_sig: [0u8; lattica_primitives::sig::SIG_LEN],
    };

    // Sign the canonical digest (over everything but the signature itself).
    tx.binding_sig = sender.sig.sign(&tx.digest()).map_err(|_| TxError::Internal("signing failed"))?;
    Ok(tx)
}
