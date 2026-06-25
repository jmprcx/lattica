//! # lattica-node
//!
//! Minimal in-memory chain state and shielded-transaction validation for the Lattica
//! protocol — enough to demonstrate a complete post-quantum shielded transfer end to end,
//! without networking, mempool, or proof-of-work.

pub mod builder;
pub mod chain;
pub mod error;
pub mod tx;

pub use builder::build_transfer;
pub use chain::Chain;
pub use error::TxError;
pub use tx::{Output, ShieldedTx, Spend};

#[cfg(test)]
mod tests {
    use super::*;
    use lattica_tx::{try_decrypt, FullKey};

    fn account(seed: u8) -> FullKey {
        FullKey::from_seed([seed; 32]).unwrap()
    }

    /// Full lifecycle: mint to Alice, Alice spends to Bob, Bob decrypts, double-spend fails.
    #[test]
    fn end_to_end_shielded_transfer() {
        let mut chain = Chain::new();
        let alice = account(1);
        let bob = account(2);

        // Alice receives 1000 via a mint.
        let (alice_note, alice_pos) = chain.mint(&alice.address(), 1000, [11u8; 32]).unwrap();
        assert_eq!(try_decrypt(&alice, &chain.transmitted[0]).unwrap(), alice_note);

        // Alice pays Bob 900, fee 100.
        let anchor = chain.anchor();
        let path = chain.merkle_path(alice_pos).unwrap();
        let tx = build_transfer(&alice, &alice_note, alice_pos, path, anchor, &bob.address(), 900, 100)
            .unwrap();

        // Node accepts it.
        chain.verify_and_apply(&tx).unwrap();

        // Bob can find and decrypt his note; Alice cannot (it's not hers).
        let bobs = chain.transmitted.iter().filter_map(|tn| try_decrypt(&bob, tn)).collect::<Vec<_>>();
        assert_eq!(bobs.len(), 1);
        assert_eq!(bobs[0].value, 900);

        // Replaying the exact same transaction is a double-spend and is rejected.
        assert_eq!(chain.verify_and_apply(&tx), Err(TxError::DoubleSpend));
    }

    #[test]
    fn unbalanced_transfer_rejected_at_build() {
        let alice = account(1);
        let bob = account(2);
        let mut chain = Chain::new();
        let (note, pos) = chain.mint(&alice.address(), 1000, [5u8; 32]).unwrap();
        let path = chain.merkle_path(pos).unwrap();
        // 900 + 99 != 1000
        let res = build_transfer(&alice, &note, pos, path, chain.anchor(), &bob.address(), 900, 99);
        assert!(matches!(res, Err(TxError::Unbalanced { .. })));
    }

    #[test]
    fn tampered_value_breaks_binding_signature() {
        let alice = account(1);
        let bob = account(2);
        let mut chain = Chain::new();
        let (note, pos) = chain.mint(&alice.address(), 1000, [5u8; 32]).unwrap();
        let path = chain.merkle_path(pos).unwrap();
        let mut tx =
            build_transfer(&alice, &note, pos, path, chain.anchor(), &bob.address(), 900, 100).unwrap();
        // Tamper with the output value after signing: the binding signature must now fail.
        tx.outputs[0].value = 950;
        assert_eq!(chain.verify_and_apply(&tx), Err(TxError::BadBindingSignature));
    }

    #[test]
    fn unknown_anchor_rejected() {
        let alice = account(1);
        let bob = account(2);
        let mut chain = Chain::new();
        let (note, pos) = chain.mint(&alice.address(), 1000, [5u8; 32]).unwrap();
        let path = chain.merkle_path(pos).unwrap();
        let mut tx =
            build_transfer(&alice, &note, pos, path, chain.anchor(), &bob.address(), 900, 100).unwrap();
        // Point the spend at an anchor the chain never published, then re-sign so the
        // binding signature is valid and the anchor check is what fails.
        tx.spends[0].anchor = [0xaa; 32];
        tx.binding_sig = alice.sig.sign(&tx.digest()).unwrap();
        assert_eq!(chain.verify_and_apply(&tx), Err(TxError::UnknownAnchor));
    }
}
