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
use p3_uni_stark::{prove, verify, Proof};

use crate::batch_common::padded_tiles;
use crate::domains::DOM_TXROOT;
use crate::poseidon2_air::{native_permute, BLOCK};
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

const fn fold_in_row(bi: usize) -> usize {
    (FOLD_BASE + bi) * BLOCK
}
const fn fold_out_row(bi: usize) -> usize {
    (FOLD_BASE + bi) * BLOCK + BLOCK - 1
}
const fn root_in_row() -> usize {
    ROOT_BLOCK * BLOCK
}
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

/// The statement chunk absorbed by s_k fold block `ci` (parallels the oracle's `tx_statement_digest`).
enum ChunkSrc {
    Full(usize), // a 4-element staging chunk at this column
    FeeMint,     // [S_FEE, S_MINT, 0, 0]
    Height,      // [S_HEIGHT, 0, 0, 0]
}
const fn chunk_src(ci: usize) -> ChunkSrc {
    if ci == 0 {
        ChunkSrc::Full(S_ANCHOR)
    } else if ci < 1 + N_IN {
        ChunkSrc::Full(S_NF + (ci - 1) * DIGEST)
    } else if ci < 1 + N_IN + M_OUT {
        ChunkSrc::Full(S_OUTCM + (ci - 1 - N_IN) * DIGEST)
    } else if ci == 1 + N_IN + M_OUT {
        ChunkSrc::FeeMint
    } else if ci == 2 + N_IN + M_OUT {
        ChunkSrc::Full(S_TXBIND)
    } else if ci == 3 + N_IN + M_OUT {
        ChunkSrc::Height
    } else {
        ChunkSrc::Full(S_HASHLOCK)
    }
}

// FRI / ZK config — the production family from crate::config (single audited source).
use crate::config::{make_config, MyConfig};

fn batch_periodic() -> Vec<Vec<Val>> {
    let mut cols = periodic();
    let oh = |rows: &[usize]| {
        let mut c = vec![Val::ZERO; TILE_HEIGHT];
        for &r in rows {
            c[r] = Val::ONE;
        }
        c
    };
    cols.push(oh(&[TILE_HEIGHT - 1])); // P_TILE_LAST
    for bi in 0..FOLD_SK_BLOCKS {
        cols.push(oh(&[fold_in_row(bi)])); // P_FOLD_IN + bi
    }
    let sk_link: Vec<usize> = (0..FOLD_SK_BLOCKS - 1).map(fold_out_row).collect();
    cols.push(oh(&sk_link)); // P_SK_LINK
    cols.push(oh(&[fold_out_row(FOLD_SK_BLOCKS - 1)])); // P_SK_TO_ROOT
    cols.push(oh(&[root_in_row()])); // P_ROOT_IN
    cols.push(oh(&[root_out_row()])); // P_ROOT_UPDATE
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
        for &c in &staged {
            builder.when_transition().assert_zero(tile_persist.clone() * (nxt[c].clone() - cur[c].clone()));
        }

        // 3. the per-tile HTLC spend constraints — reused verbatim, fed the staging statement + tile_last.
        //    (the cur == statement[..] bindings inside eval_spend double as the staging bindings.)
        eval_spend(builder, &statement, tile_last.clone());

        // 4. the in-circuit tx-root fold (identical structure to batch_joinsplit_air; 9 s_k chunks).
        let dom_txroot = AB::Expr::from(Goldilocks::from_u64(DOM_TXROOT));
        for bi in 0..FOLD_SK_BLOCKS {
            let sel = p[P_FOLD_IN + bi].clone();
            match chunk_src(bi) {
                ChunkSrc::Full(base) => {
                    for k in 0..DIGEST {
                        builder.assert_zero(sel.clone() * (cur[DIGEST + k].clone() - cur[base + k].clone()));
                    }
                }
                ChunkSrc::FeeMint => {
                    builder.assert_zero(sel.clone() * (cur[DIGEST].clone() - cur[S_FEE].clone()));
                    builder.assert_zero(sel.clone() * (cur[DIGEST + 1].clone() - cur[S_MINT].clone()));
                    builder.assert_zero(sel.clone() * cur[DIGEST + 2].clone());
                    builder.assert_zero(sel.clone() * cur[DIGEST + 3].clone());
                }
                ChunkSrc::Height => {
                    builder.assert_zero(sel.clone() * (cur[DIGEST].clone() - cur[S_HEIGHT].clone()));
                    for k in 1..DIGEST {
                        builder.assert_zero(sel.clone() * cur[DIGEST + k].clone());
                    }
                }
            }
        }
        let sk0 = p[P_FOLD_IN].clone(); // block 0 low lanes = [DOM_TXROOT, 0, 0, 0]
        builder.assert_zero(sk0.clone() * (cur[0].clone() - dom_txroot.clone()));
        for k in 1..DIGEST {
            builder.assert_zero(sk0.clone() * cur[k].clone());
        }
        let sl = p[P_SK_LINK].clone(); // s_k block output[0..4] → next block input[0..4]
        for k in 0..DIGEST {
            builder.when_transition().assert_zero(sl.clone() * (nxt[k].clone() - cur[k].clone()));
        }
        let s2r = p[P_SK_TO_ROOT].clone(); // last s_k block output → root block input lanes 4..8 (= s_k)
        for k in 0..DIGEST {
            builder.when_transition().assert_zero(s2r.clone() * (nxt[DIGEST + k].clone() - cur[k].clone()));
        }
        let ri = p[P_ROOT_IN].clone(); // root block input lanes 0..4 == the running ROOT
        for k in 0..DIGEST {
            builder.assert_zero(ri.clone() * (cur[k].clone() - cur[ROOT + k].clone()));
        }
        for k in 0..DIGEST {
            builder.when_first_row().assert_zero(cur[ROOT + k].clone()); // IV = 0
        }
        let ru = p[P_ROOT_UPDATE].clone();
        for k in 0..DIGEST {
            builder
                .when_transition()
                .assert_zero((one.clone() - ru.clone()) * (nxt[ROOT + k].clone() - cur[ROOT + k].clone()));
            builder.when_transition().assert_zero(ru.clone() * (nxt[ROOT + k].clone() - cur[k].clone()));
        }
        for k in 0..DIGEST {
            builder.when_last_row().assert_zero(cur[k].clone() - pis[k].clone()); // root block is the last block
        }
    }
}

/// The 4-element statement chunk for s_k fold block `ci` (mirrors the oracle's chunk order).
fn chunk_vals(pv: &[Val], ci: usize) -> [Val; DIGEST] {
    let g = |off: usize| -> [Val; DIGEST] { pv[off..off + DIGEST].try_into().unwrap() };
    if ci == 0 {
        g(PI_ANCHOR)
    } else if ci < 1 + N_IN {
        g(PI_NF + (ci - 1) * DIGEST)
    } else if ci < 1 + N_IN + M_OUT {
        g(PI_OUTCM + (ci - 1 - N_IN) * DIGEST)
    } else if ci == 1 + N_IN + M_OUT {
        [pv[PI_FEE], pv[PI_MINT], Val::ZERO, Val::ZERO]
    } else if ci == 2 + N_IN + M_OUT {
        g(PI_TXBIND)
    } else if ci == 3 + N_IN + M_OUT {
        [pv[PI_HEIGHT], Val::ZERO, Val::ZERO, Val::ZERO]
    } else {
        g(PI_HASHLOCK)
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
        let mut inp = [Val::ZERO; 8];
        inp[0] = Val::from_u64(DOM_TXROOT);
        inp[DIGEST..].copy_from_slice(&chunk_vals(&pv, 0));
        crate::batch_common::set_fold_block(&mut t, toff, FOLD_BASE, BATCH_WIDTH, inp);
        let mut c: [Val; DIGEST] = native_permute(inp)[..DIGEST].try_into().unwrap();
        for bi in 1..FOLD_SK_BLOCKS {
            let mut inp = [Val::ZERO; 8];
            inp[..DIGEST].copy_from_slice(&c);
            inp[DIGEST..].copy_from_slice(&chunk_vals(&pv, bi));
            crate::batch_common::set_fold_block(&mut t, toff, FOLD_BASE + bi, BATCH_WIDTH, inp);
            c = native_permute(inp)[..DIGEST].try_into().unwrap();
        }
        let mut rinp = [Val::ZERO; 8];
        rinp[..DIGEST].copy_from_slice(&root);
        rinp[DIGEST..].copy_from_slice(&c);
        crate::batch_common::set_fold_block(&mut t, toff, ROOT_BLOCK, BATCH_WIDTH, rinp);
        let new_root: [Val; DIGEST] = native_permute(rinp)[..DIGEST].try_into().unwrap();
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
    let pis = batch_root(ws);
    let proof = prove(&make_config(), &HtlcBatchAir, build_batch_trace(ws), &pis);
    postcard::to_allocvec(&proof).expect("proof serialization is infallible")
}

/// Proven (UDR) security bits at an HTLC batch of `n` transactions (same height as join-split, so the
/// floor matches — `MAX_BATCH_TILES = 64` holds; the extra HTLC columns/degree don't lower it).
pub fn proven_security_bits(n: usize) -> usize {
    crate::config::proven_security_bits(&HtlcBatchAir, padded_tiles(n) * TILE_HEIGHT)
}

/// Verify an HTLC batch proof against the block tx-root.
pub fn verify_batch_bytes(proof_bytes: &[u8], root: &[Val]) -> bool {
    if root.len() != DIGEST {
        return false;
    }
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), &HtlcBatchAir, &proof, root).is_ok()
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
        use p3_field::PrimeField64;
        let seq: Vec<Val> = (1..=N_PUBLIC as u64).map(Val::from_u64).collect();
        let s = tx_statement_digest(&seq);
        let d = dummy_sk();
        println!("htlc_seq_digest = {:?}", s.iter().map(|f| f.as_canonical_u64()).collect::<Vec<_>>());
        println!("htlc_dummy_sk = {:?}", d.iter().map(|f| f.as_canonical_u64()).collect::<Vec<_>>());
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
