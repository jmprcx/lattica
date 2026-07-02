//! Batch aggregation for the v3 shielded-HTLC spend — one proof per block for `htlc_air`. Mirrors
//! `batch_joinsplit_air`; the only delta is the per-transaction statement, which adds
//! `current_height` + `redeem_hashlock` (31 public elements vs the join-split 26), so the tx-root fold
//! absorbs two more chunks. The fold domain (`DOM_TXROOT`) is shared — an HTLC `s_k` (9 absorb blocks)
//! cannot collide with a join-split `s_k` (7 blocks), and the two batch circuits have separate roots.
//!
//! The native oracle is the cross-checked contract; the file contains the complete in-circuit HTLC
//! batch AIR (staging + fold, per-tile constraints = `htlc_air::eval_spend` reused verbatim), the
//! byte ABI, and the Zig-seam root recompute — mirroring `batch_joinsplit_air`.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::Goldilocks;
use p3_matrix::dense::RowMajorMatrix;
#[cfg(test)]
use p3_uni_stark::prove;

use crate::batch_common::padded_tiles;
use crate::domains::DOM_TXROOT;
use crate::poseidon2_air::BLOCK;
use crate::htlc_air::{
    build_trace, eval_spend, merge, periodic, public_values, Input, Output, Witness, DEPTH, DIGEST, HEIGHT,
    M_OUT, N_IN, N_PERIODIC, N_PUBLIC, PI_ANCHOR, PI_FEE, PI_HASHLOCK, PI_HEIGHT, PI_MINT, PI_NF, PI_OUTCM,
    PI_TXBIND, WIDTH,
};

type Val = Goldilocks;

/// Per-HTLC-transaction statement digest `s_k`: a domain-tagged MD-chain over the 31-element statement —
/// the join-split chunks (anchor ‖ nf ‖ out_cm ‖ [fee,mint,0,0] ‖ tx_binding) plus
/// `[current_height,0,0,0]` and `redeem_hashlock`. Must match the (later) `batch_htlc_air` circuit.
pub fn tx_statement_digest(pv: &[Val]) -> [Val; DIGEST] {
    debug_assert_eq!(pv.len(), N_PUBLIC);
    let chunks = statement_chunks(pv);
    let dom = [Val::from_u64(DOM_TXROOT), Val::ZERO, Val::ZERO, Val::ZERO];
    let mut c = merge(dom, chunks[0]);
    for chunk in &chunks[1..] {
        c = merge(c, *chunk);
    }
    c
}

/// The ordered 4-element statement chunks the HTLC s_k fold absorbs (the join-split chunks — anchor,
/// each nullifier, each out_cm, `[fee,mint,0,0]`, tx_binding — plus `[current_height,0,0,0]` and
/// redeem_hashlock). The SINGLE native source of the consensus chunk order: `tx_statement_digest`
/// folds these and the trace builder feeds them to the in-circuit fold. Lockstep with `fold_chunks`.
fn statement_chunks(pv: &[Val]) -> Vec<[Val; DIGEST]> {
    let chunk = |off: usize| -> [Val; DIGEST] { pv[off..off + DIGEST].try_into().unwrap() };
    let mut v = Vec::with_capacity(FOLD_SK_BLOCKS);
    v.push(chunk(PI_ANCHOR));
    for i in 0..N_IN {
        v.push(chunk(PI_NF + i * DIGEST));
    }
    for j in 0..M_OUT {
        v.push(chunk(PI_OUTCM + j * DIGEST));
    }
    v.push([pv[PI_FEE], pv[PI_MINT], Val::ZERO, Val::ZERO]);
    v.push(chunk(PI_TXBIND));
    v.push([pv[PI_HEIGHT], Val::ZERO, Val::ZERO, Val::ZERO]);
    v.push(chunk(PI_HASHLOCK));
    v
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

// =============================================================================================
// The HTLC batch AIR: htlc_air's spend tiled n times in one trace, proven once. The per-tile
// constraints are reused VERBATIM from htlc_air::eval_spend (fed the per-tile staging columns as the
// statement + the tile-boundary selector); only the tiling, staging, and tx-root fold are new.
// =============================================================================================

const TILE_HEIGHT: usize = HEIGHT;
const NUM_BLOCKS: usize = HEIGHT / BLOCK;

// staging columns (tile-persistent), holding this tile's 31-element statement for the fold + the
// eval_spend bindings. Layout parallels htlc_air's public-input order.
const S_ANCHOR: usize = WIDTH; // 4
const S_NF: usize = S_ANCHOR + DIGEST; // N_IN·4
const S_OUTCM: usize = S_NF + N_IN * DIGEST; // M_OUT·4
const S_FEE: usize = S_OUTCM + M_OUT * DIGEST;
const S_MINT: usize = S_FEE + 1;
const S_TXBIND: usize = S_MINT + 1; // 4
const S_HEIGHT: usize = S_TXBIND + DIGEST;
const S_HASHLOCK: usize = S_HEIGHT + 1; // 4
const ROOT: usize = S_HASHLOCK + DIGEST; // 4 — running tx-root chain (global-persistent)
const BATCH_WIDTH: usize = ROOT + DIGEST;

// the fold (in the trailing free padding): 9 s_k chunks (anchor, nf×N, out_cm×M, [fee,mint], tx_binding,
// [current_height], redeem_hashlock) + 1 root-chain block.
const FOLD_SK_BLOCKS: usize = 1 + N_IN + M_OUT + 4;
const FOLD_BLOCKS: usize = FOLD_SK_BLOCKS + 1;
const FOLD_BASE: usize = NUM_BLOCKS - FOLD_BLOCKS;
const ROOT_BLOCK: usize = FOLD_BASE + FOLD_SK_BLOCKS;

// Fold-block rows are now computed inside `batch_common::{append_batch_selectors, write_fold_blocks}`;
// only the root block's OUTPUT row is needed here, for threading the ROOT column.
const fn root_out_row() -> usize {
    ROOT_BLOCK * BLOCK + BLOCK - 1
}

const P_TILE_LAST: usize = N_PERIODIC;
const P_FOLD_IN: usize = P_TILE_LAST + 1; // FOLD_SK_BLOCKS chunk-injection one-hots
const P_SK_LINK: usize = P_FOLD_IN + FOLD_SK_BLOCKS;
const P_SK_TO_ROOT: usize = P_SK_LINK + 1;
const P_ROOT_IN: usize = P_SK_TO_ROOT + 1;
const P_ROOT_UPDATE: usize = P_ROOT_IN + 1;
const BATCH_N_PERIODIC: usize = P_ROOT_UPDATE + 1;

/// The AIR-side chunk table the tx-root fold injects, in fold order — the in-circuit twin of the native
/// `statement_chunks`. The HTLC statement extends the join-split one with `[S_HEIGHT,0,0,0]` and the
/// hashlock (an auditor checks this table against `statement_chunks` side by side).
fn fold_chunks() -> Vec<crate::batch_common::FoldChunk> {
    let full = |base: usize| [Some(base), Some(base + 1), Some(base + 2), Some(base + 3)];
    let mut v = Vec::with_capacity(FOLD_SK_BLOCKS);
    v.push(full(S_ANCHOR));
    for i in 0..N_IN {
        v.push(full(S_NF + i * DIGEST));
    }
    for j in 0..M_OUT {
        v.push(full(S_OUTCM + j * DIGEST));
    }
    v.push([Some(S_FEE), Some(S_MINT), None, None]);
    v.push(full(S_TXBIND));
    v.push([Some(S_HEIGHT), None, None, None]);
    v.push(full(S_HASHLOCK));
    v
}

// FRI / ZK config — the production family from crate::config (single audited source).
#[cfg(test)]
use crate::config::make_config;

fn batch_periodic() -> Vec<Vec<Val>> {
    let mut cols = periodic();
    // Same shared selectors as batch_joinsplit (geometry as data); the HTLC delta is only that
    // FOLD_SK_BLOCKS is larger (9 vs 7) — order MUST match the P_* indices above.
    crate::batch_common::append_batch_selectors(&mut cols, TILE_HEIGHT, FOLD_SK_BLOCKS, FOLD_BASE, ROOT_BLOCK);
    cols
}

pub struct HtlcBatchAir;

impl BaseAir<Goldilocks> for HtlcBatchAir {
    fn width(&self) -> usize {
        BATCH_WIDTH
    }
    fn num_public_values(&self) -> usize {
        DIGEST // the single block tx-root
    }
    fn num_periodic_columns(&self) -> usize {
        BATCH_N_PERIODIC
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        batch_periodic()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for HtlcBatchAir {
    fn eval(&self, builder: &mut AB) {
        let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = builder.main().next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let tile_last = p[P_TILE_LAST].clone();

        // 1. the per-tile statement = this tile's staging columns (layout parallels the public inputs).
        let mut statement = vec![AB::Expr::ZERO; N_PUBLIC];
        for k in 0..DIGEST {
            statement[PI_ANCHOR + k] = cur[S_ANCHOR + k].clone();
        }
        for i in 0..N_IN {
            for k in 0..DIGEST {
                statement[PI_NF + i * DIGEST + k] = cur[S_NF + i * DIGEST + k].clone();
            }
        }
        for j in 0..M_OUT {
            for k in 0..DIGEST {
                statement[PI_OUTCM + j * DIGEST + k] = cur[S_OUTCM + j * DIGEST + k].clone();
            }
        }
        statement[PI_FEE] = cur[S_FEE].clone();
        statement[PI_MINT] = cur[S_MINT].clone();
        for k in 0..DIGEST {
            statement[PI_TXBIND + k] = cur[S_TXBIND + k].clone();
        }
        statement[PI_HEIGHT] = cur[S_HEIGHT].clone();
        for k in 0..DIGEST {
            statement[PI_HASHLOCK + k] = cur[S_HASHLOCK + k].clone();
        }

        // 2. staging columns are tile-persistent (constant within a tile, free at the tile boundary).
        let tile_persist = one.clone() - tile_last.clone();
        let mut staged: Vec<usize> = vec![S_FEE, S_MINT, S_HEIGHT];
        for k in 0..DIGEST {
            staged.push(S_ANCHOR + k);
            staged.push(S_TXBIND + k);
            staged.push(S_HASHLOCK + k);
        }
        for i in 0..N_IN {
            for k in 0..DIGEST {
                staged.push(S_NF + i * DIGEST + k);
            }
        }
        for j in 0..M_OUT {
            for k in 0..DIGEST {
                staged.push(S_OUTCM + j * DIGEST + k);
            }
        }
        crate::batch_common::eval_tile_persistence(builder, &cur, &nxt, tile_persist, &staged);

        // 3. the per-tile HTLC spend constraints — reused verbatim, fed the staging statement + tile_last.
        //    (the cur == statement[..] bindings inside eval_spend double as the staging bindings.)
        eval_spend(builder, &statement, tile_last.clone());

        // 4. the in-circuit tx-root fold — the SAME shared emitter as batch_joinsplit_air; the HTLC delta
        //    is only the two extra chunks (Height, hashlock) in fold_chunks() and the larger FOLD_SK_BLOCKS.
        crate::batch_common::eval_txroot_fold(builder, &cur, &nxt, &pis, &p[P_FOLD_IN..], &fold_chunks(), ROOT);
    }
}

/// Tile `ws.len()` single-tile HTLC traces into one batch trace, fill staging, run the fold, thread ROOT.
pub fn build_batch_trace(ws: &[Witness]) -> RowMajorMatrix<Val> {
    let n = padded_tiles(ws.len());
    let dummy = dummy_witness();
    let mut t = vec![Val::ZERO; n * TILE_HEIGHT * BATCH_WIDTH];
    let mut root = [Val::ZERO; DIGEST];
    for tile in 0..n {
        let w = if tile < ws.len() { &ws[tile] } else { &dummy };
        let single = build_trace(w); // HEIGHT × WIDTH(36)
        let pv = public_values(w);
        let toff = tile * TILE_HEIGHT;
        for r in 0..TILE_HEIGHT {
            let dst = (toff + r) * BATCH_WIDTH;
            let src = r * WIDTH;
            t[dst..dst + WIDTH].copy_from_slice(&single.values[src..src + WIDTH]);
        }
        for r in 0..TILE_HEIGHT {
            let b = (toff + r) * BATCH_WIDTH;
            t[b + S_ANCHOR..b + S_ANCHOR + DIGEST].copy_from_slice(&pv[PI_ANCHOR..PI_ANCHOR + DIGEST]);
            t[b + S_NF..b + S_NF + N_IN * DIGEST].copy_from_slice(&pv[PI_NF..PI_NF + N_IN * DIGEST]);
            t[b + S_OUTCM..b + S_OUTCM + M_OUT * DIGEST].copy_from_slice(&pv[PI_OUTCM..PI_OUTCM + M_OUT * DIGEST]);
            t[b + S_FEE] = pv[PI_FEE];
            t[b + S_MINT] = pv[PI_MINT];
            t[b + S_TXBIND..b + S_TXBIND + DIGEST].copy_from_slice(&pv[PI_TXBIND..PI_TXBIND + DIGEST]);
            t[b + S_HEIGHT] = pv[PI_HEIGHT];
            t[b + S_HASHLOCK..b + S_HASHLOCK + DIGEST].copy_from_slice(&pv[PI_HASHLOCK..PI_HASHLOCK + DIGEST]);
        }
        let new_root =
            crate::batch_common::write_fold_blocks(&mut t, toff, BATCH_WIDTH, &statement_chunks(&pv), root, FOLD_BASE, ROOT_BLOCK);
        let rout = root_out_row();
        for r in 0..TILE_HEIGHT {
            let b = (toff + r) * BATCH_WIDTH;
            let val = if r <= rout { &root } else { &new_root };
            t[b + ROOT..b + ROOT + DIGEST].copy_from_slice(val);
        }
        root = new_root;
    }
    RowMajorMatrix::new(t, BATCH_WIDTH)
}

/// Prove a batch of HTLC transactions as one proof; the block tx-root is `batch_root(ws)`.
pub fn prove_batch_to_bytes(ws: &[Witness]) -> Vec<u8> {
    assert!(
        padded_tiles(ws.len()) <= crate::batch_common::MAX_BATCH_TILES,
        "batch exceeds MAX_BATCH_TILES; split the block into multiple batch proofs"
    );
    crate::config::proof_to_bytes(&HtlcBatchAir, build_batch_trace(ws), &batch_root(ws))
}

/// Proven (UDR) security bits at an HTLC batch of `n` transactions (same height as join-split, so the
/// floor matches — `MAX_BATCH_TILES = 64` holds; the extra HTLC columns/degree don't lower it).
pub fn proven_security_bits(n: usize) -> usize {
    crate::config::proven_security_bits(&HtlcBatchAir, padded_tiles(n) * TILE_HEIGHT)
}

/// Verify an HTLC batch proof against the block tx-root.
pub fn verify_batch_bytes(proof_bytes: &[u8], root: &[Val]) -> bool {
    crate::config::verify_proof_bytes(&HtlcBatchAir, DIGEST, proof_bytes, root)
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
    fn htlc_batch_kat_dump() {
        // CONSENSUS KAT (poseidon2.zig), seq statement = 1..=N_PUBLIC. PINNED at HEAD c7e54b1 — the node
        // recomputes these natively; a change is a chain fork. Prints kept for cross-language diff.
        use p3_field::PrimeField64;
        let seq: Vec<Val> = (1..=N_PUBLIC as u64).map(Val::from_u64).collect();
        let felts = |x: &[Val; DIGEST]| x.iter().map(|f| f.as_canonical_u64()).collect::<Vec<_>>();
        let s = felts(&tx_statement_digest(&seq));
        let d = felts(&dummy_sk());
        println!("htlc_seq_digest = {s:?}");
        println!("htlc_dummy_sk = {d:?}");
        assert_eq!(s, [12024734340241841742, 6068874100855730733, 14239999004995857547, 2452102150457936639]);
        assert_eq!(d, [10539992321146962576, 13450880049652540131, 10286920310671709176, 6485382129692956089]);
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

    // ---- circuit: distinct HTLC tiles bound to the tx-root (real prover) ----

    #[test]
    #[ignore = "slow: HTLC batch prove (1 tile)"]
    fn htlc_batch_n1_verifies_under_txroot() {
        let w = variant(1);
        let root = batch_root(std::slice::from_ref(&w));
        assert!(verify_batch_bytes(&prove_batch_to_bytes(std::slice::from_ref(&w)), &root));
    }

    #[test]
    #[ignore = "slow: HTLC batch prove (2 tiles)"]
    fn htlc_batch_distinct_tiles_verify_and_match_oracle() {
        let ws = [variant(1), variant(2)];
        let root = batch_root(&ws);
        assert!(verify_batch_bytes(&prove_batch_to_bytes(&ws), &root));
    }

    #[test]
    #[ignore = "slow: HTLC batch prove (2 tiles)"]
    fn htlc_batch_rejects_wrong_txroot() {
        let ws = [variant(1), variant(2)];
        let proof = prove_batch_to_bytes(&ws);
        let mut bad = batch_root(&ws);
        bad[0] += Val::ONE;
        assert!(!verify_batch_bytes(&proof, &bad));
    }

    #[test]
    fn htlc_batch_proven_security_floor() {
        use crate::batch_common::MAX_BATCH_TILES;
        assert!(proven_security_bits(1) >= 100);
        assert!(
            proven_security_bits(MAX_BATCH_TILES) >= 100,
            "HTLC batch must hold the ≥100-bit floor at MAX_BATCH_TILES"
        );
    }

    #[test]
    #[ignore = "slow: corrupted-trace HTLC batch prove"]
    fn htlc_batch_corrupted_staged_anchor_is_rejected() {
        let ws = [variant(1), variant(2)];
        let root = batch_root(&ws);
        let mut trace = build_batch_trace(&ws);
        for r in 0..TILE_HEIGHT {
            trace.values[r * BATCH_WIDTH + S_ANCHOR] += Val::ONE; // tile 0's staged anchor
        }
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let proof = prove(&make_config(), &HtlcBatchAir, trace, &root);
            verify_batch_bytes(&postcard::to_allocvec(&proof).unwrap(), &root)
        }));
        assert!(matches!(outcome, Ok(false) | Err(_)));
    }
}
