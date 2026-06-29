//! Batch aggregation — one STARK proof per block (join-split).
//!
//! A block-producer/sequencer proves N transactions as ONE proof: the per-tx join-split trace is tiled
//! vertically into a single trace and proven once, so a validator verifies a whole block in one check.
//! Proof size grows ~log N and verify is ~constant (see `docs/soundness-budget.md`).
//!
//! The N transactions are bound to a single public input — the block **tx-root**. Each tx's statement
//! (`anchor ‖ nullifiers ‖ out_cms ‖ fee ‖ mint ‖ tx_binding`, i.e. exactly
//! `joinsplit_air::public_values`) is hashed to a per-tx digest `s_k` under a fresh domain tag, then
//! chained `root_k = H(root_{k-1} ‖ s_k)` with IV = 0. The batch is padded to a power of two with
//! **dummy tiles** (the digest of the all-zero statement) so the tile count — hence the trace height —
//! is a power of two. The Zig node recomputes the same root from a block's transactions (no witnesses
//! needed) to check the single proof.
//!
//! PHASE 1 (this commit): the native oracle only — `tx_statement_digest`, `dummy_sk`, `batch_root`. The
//! in-circuit fold (a later phase) is differential-tested against this oracle, and the node's
//! `poseidon2.zig` recompute is KAT-tested against it.

use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::Goldilocks;

use crate::joinsplit_air::{merge, public_values, Witness, DIGEST, M_OUT, N_IN, NUM_PUBLIC_INPUTS};

type Val = Goldilocks;

/// Domain tag for the per-transaction statement digest (1=OWN, 2=CM, 3=NF, 4=HTLC, 5=NF_HTLC).
pub const DOM_TXROOT: u64 = 6;

// Public-statement layout — mirrors `joinsplit_air::public_values`, derived from the pub shape
// constants (DIGEST, N_IN, M_OUT). The `debug_assert` in `tx_statement_digest` catches any drift.
const PI_ANCHOR: usize = 0;
const PI_NF: usize = DIGEST;
const PI_OUTCM: usize = DIGEST * (1 + N_IN);
const PI_FEE: usize = DIGEST * (1 + N_IN + M_OUT);
const PI_MINT: usize = PI_FEE + 1;
const PI_TXBIND: usize = PI_MINT + 1;

/// Per-transaction statement digest `s_k`: a domain-tagged Merkle–Damgård chain over the public
/// statement. Block 0 = `H(DOM_TXROOT,0,0,0 ‖ anchor)` (a `merge` with the domain in the low half);
/// then merge-shaped blocks absorb each nullifier, each output commitment, `[fee,mint,0,0]`, and
/// `tx_binding` as 4-element chunks. The batch circuit reproduces this exact chain from the per-tile
/// staging columns, so the layout here is the cross-checked contract.
pub fn tx_statement_digest(pv: &[Val]) -> [Val; DIGEST] {
    debug_assert_eq!(pv.len(), NUM_PUBLIC_INPUTS);
    debug_assert_eq!(PI_TXBIND + DIGEST, NUM_PUBLIC_INPUTS);
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
    c
}

/// The statement digest of a dummy (padding) tile = the digest of the all-zero statement. A real tx has
/// a non-zero anchor and nullifiers, so a real `s_k` can never collide with this.
pub fn dummy_sk() -> [Val; DIGEST] {
    tx_statement_digest(&[Val::ZERO; NUM_PUBLIC_INPUTS])
}

/// The block **tx-root**: fold each transaction's `s_k` into a running digest (IV = 0), then pad to a
/// power of two with dummy tiles. `root_k = H(root_{k-1} ‖ s_k)`. This is the single public input of the
/// batch proof; the node recomputes it from the block's transactions to verify one proof per block.
pub fn batch_root(ws: &[Witness]) -> [Val; DIGEST] {
    let n_padded = ws.len().max(1).next_power_of_two();
    let mut root = [Val::ZERO; DIGEST]; // IV
    for w in ws {
        root = merge(root, tx_statement_digest(&public_values(w)));
    }
    let dummy = dummy_sk();
    for _ in ws.len()..n_padded {
        root = merge(root, dummy);
    }
    root
}

/// The padded tile count for a batch of `n` transactions (a power of two; ≥ 1).
pub fn padded_tiles(n: usize) -> usize {
    n.max(1).next_power_of_two()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::joinsplit_air::demo_witness;

    // Distinct, well-formed witnesses (vary tx_binding ⇒ distinct public statements). batch_root only
    // hashes public_values, so the witnesses need not balance for these oracle tests.
    fn variant(tag: u64) -> Witness {
        let mut w = demo_witness();
        w.tx_binding[0] += Val::from_u64(tag);
        w
    }

    #[test]
    fn batch_root_folds_in_order_with_iv_and_padding() {
        let ws = [variant(1), variant(2), variant(3)];
        // Manual fold: IV → s0 → s1 → s2 → one dummy (pad 3 → 4).
        let mut expect = [Val::ZERO; DIGEST];
        for w in &ws {
            expect = merge(expect, tx_statement_digest(&public_values(w)));
        }
        expect = merge(expect, dummy_sk());
        assert_eq!(batch_root(&ws), expect);
        assert_eq!(padded_tiles(3), 4);
    }

    #[test]
    fn single_tx_root_needs_no_padding() {
        let w = variant(1);
        let expect = merge([Val::ZERO; DIGEST], tx_statement_digest(&public_values(&w)));
        assert_eq!(batch_root(std::slice::from_ref(&w)), expect);
        assert_eq!(padded_tiles(1), 1);
        assert_eq!(padded_tiles(2), 2);
        assert_eq!(padded_tiles(5), 8);
    }

    #[test]
    fn dummy_sk_is_deterministic_and_distinct_from_real() {
        assert_eq!(dummy_sk(), dummy_sk());
        let real = tx_statement_digest(&public_values(&variant(7)));
        assert_ne!(dummy_sk(), real); // real anchor/nullifiers are non-zero ⇒ no collision with the zero statement
    }

    #[test]
    fn batch_root_is_order_sensitive() {
        let a = variant(1);
        let b = variant(2);
        assert_ne!(batch_root(&[a.clone(), b.clone()]), batch_root(&[b, a]));
    }

    #[test]
    fn distinct_statements_give_distinct_digests() {
        assert_ne!(
            tx_statement_digest(&public_values(&variant(1))),
            tx_statement_digest(&public_values(&variant(2))),
        );
    }
}
