//! Batch aggregation for the v3 shielded-HTLC spend — one proof per block for `htlc_air`. Mirrors
//! `batch_joinsplit_air`; the only delta is the per-transaction statement, which adds
//! `current_height` + `redeem_hashlock` (31 public elements vs the join-split 26), so the tx-root fold
//! absorbs two more chunks. The fold domain (`DOM_TXROOT`) is shared — an HTLC `s_k` (9 absorb blocks)
//! cannot collide with a join-split `s_k` (7 blocks), and the two batch circuits have separate roots.
//!
//! PHASE 9a (this commit): the native oracle. The in-circuit fold + ABI + Zig seam mirror the
//! join-split phases.

use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::Goldilocks;

use crate::batch_joinsplit_air::{padded_tiles, DOM_TXROOT};
use crate::htlc_air::{
    merge, public_values, Input, Output, Witness, DEPTH, DIGEST, M_OUT, N_IN, N_PUBLIC, PI_ANCHOR, PI_FEE,
    PI_HASHLOCK, PI_HEIGHT, PI_MINT, PI_NF, PI_OUTCM, PI_TXBIND,
};

type Val = Goldilocks;

/// Per-HTLC-transaction statement digest `s_k`: a domain-tagged MD-chain over the 31-element statement —
/// the join-split chunks (anchor ‖ nf ‖ out_cm ‖ [fee,mint,0,0] ‖ tx_binding) plus
/// `[current_height,0,0,0]` and `redeem_hashlock`. Must match the (later) `batch_htlc_air` circuit.
pub fn tx_statement_digest(pv: &[Val]) -> [Val; DIGEST] {
    debug_assert_eq!(pv.len(), N_PUBLIC);
    let chunk = |off: usize| -> [Val; DIGEST] { pv[off..off + DIGEST].try_into().unwrap() };
    let dom = [Val::from_u64(DOM_TXROOT), Val::ZERO, Val::ZERO, Val::ZERO];
    let mut c = merge(dom, chunk(PI_ANCHOR));
    for i in 0..N_IN {
        c = merge(c, chunk(PI_NF + i * DIGEST));
    }
    for j in 0..M_OUT {
        c = merge(c, chunk(PI_OUTCM + j * DIGEST));
    }
    c = merge(c, [pv[PI_FEE], pv[PI_MINT], Val::ZERO, Val::ZERO]);
    c = merge(c, chunk(PI_TXBIND));
    c = merge(c, [pv[PI_HEIGHT], Val::ZERO, Val::ZERO, Val::ZERO]);
    c = merge(c, chunk(PI_HASHLOCK));
    c
}

/// The canonical padding tile: a valid 0-value **PLAIN** 2-in/2-out spend (`htlc_air` is a superset that
/// also spends PLAIN notes), two identical inputs ⇒ a shared anchor; no HTLC fields, `current_height=0`.
pub fn dummy_witness() -> Witness {
    let z4 = [Val::ZERO; DIGEST];
    let inp = Input {
        nk: [0, 0],
        div: Val::ZERO,
        asset: Val::ZERO,
        note_type: Val::ZERO,
        value: 0,
        rho: [Val::ZERO; 2],
        rcm: [Val::ZERO; 2],
        sib: [z4; DEPTH],
        bits: [false; DEPTH],
        mode: Val::ZERO,
        redeem_tag: z4,
        refund_tag: z4,
        hashlock: z4,
        timeout: 0,
    };
    let out = Output { recipient: z4, asset: Val::ZERO, note_type: Val::ZERO, value: 0, rho: [Val::ZERO; 2], rcm: [Val::ZERO; 2] };
    Witness {
        inputs: core::array::from_fn(|_| inp.clone()),
        outputs: [out; M_OUT],
        fee: 0,
        mint: 0,
        tx_binding: z4,
        current_height: 0,
    }
}

/// The statement digest of a padding tile (the canonical `dummy_witness`).
pub fn dummy_sk() -> [Val; DIGEST] {
    tx_statement_digest(&public_values(&dummy_witness()))
}

/// The block tx-root for a batch of HTLC transactions: fold each `s_k` into a running digest (IV = 0),
/// then pad to a power of two with `dummy_sk`. The node recomputes this from the block's HTLC tx
/// statements to verify one batch proof.
pub fn batch_root(ws: &[Witness]) -> [Val; DIGEST] {
    let n_padded = padded_tiles(ws.len());
    let mut root = [Val::ZERO; DIGEST];
    for w in ws {
        root = merge(root, tx_statement_digest(&public_values(w)));
    }
    let dummy = dummy_sk();
    for _ in ws.len()..n_padded {
        root = merge(root, dummy);
    }
    root
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::htlc_air::demo_htlc_witness;

    fn variant(tag: u64) -> Witness {
        let mut w = demo_htlc_witness();
        w.tx_binding[0] += Val::from_u64(tag);
        w
    }

    #[test]
    fn htlc_batch_root_folds_in_order_with_padding() {
        let ws = [variant(1), variant(2), variant(3)];
        let mut expect = [Val::ZERO; DIGEST];
        for w in &ws {
            expect = merge(expect, tx_statement_digest(&public_values(w)));
        }
        expect = merge(expect, dummy_sk()); // pad 3 → 4
        assert_eq!(batch_root(&ws), expect);
    }

    #[test]
    fn htlc_dummy_sk_deterministic_and_distinct_from_real() {
        assert_eq!(dummy_sk(), dummy_sk());
        assert_ne!(dummy_sk(), tx_statement_digest(&public_values(&variant(5))));
    }

    #[test]
    fn htlc_tx_root_binds_height() {
        // two statements differing only in current_height ⇒ distinct digests (the fold absorbs it).
        // Use the PLAIN dummy (no redeem timeout constraint, so current_height is free).
        let mut a = dummy_witness();
        let mut b = dummy_witness();
        a.current_height = 50;
        b.current_height = 51;
        assert_ne!(tx_statement_digest(&public_values(&a)), tx_statement_digest(&public_values(&b)));
    }
}
