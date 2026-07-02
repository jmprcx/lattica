//! Shared batch-aggregation machinery — the tile cap, tile padding, and the fold-block trace
//! writer used by BOTH batch circuits (`batch_joinsplit_air`, `batch_htlc_air`).
//!
//! The per-circuit fold GEOMETRY (`FOLD_SK_BLOCKS`, chunk schedules, staging column offsets) stays
//! in each circuit file by design: the two statements fold different chunk counts (`FOLD_SK_BLOCKS`
//! = 7 for join-split — anchor + 2·nf + 2·out_cm + [fee,mint,0,0] + tx_binding — and 9 for HTLC,
//! which adds [current_height,0,0,0] + redeem_hashlock), so those constants are circuit shape, not
//! shared machinery.

use p3_air::AirBuilder;
use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::Goldilocks;

use crate::domains::DOM_TXROOT;
use crate::poseidon2_air::{native_permute, write_perm_block, BLOCK};

type Val = Goldilocks;
const DIGEST: usize = 4;

/// One absorbed statement chunk of the in-circuit tx-root fold: 4 lanes, each either bound to a staged
/// column (`Some(col)` ⇒ the injected lane equals `cur[col]`) or pinned to 0 (`None`). Each batch
/// circuit's `fold_chunks()` returns these in fold order; an auditor checks that table against the
/// circuit's native `statement_chunks` (they encode the SAME consensus chunk order).
///
/// LANDMINE (fingerprint-pinned): a `None` lane MUST emit `sel · cur[DIGEST+k]`, never
/// `sel · (cur[DIGEST+k] − 0)` — the Debug-rendered constraint fnv distinguishes them.
pub(crate) type FoldChunk = [Option<usize>; DIGEST];

/// The largest batch (in tiles) that holds the ≥100-bit proven-soundness floor: measured 100 bits at
/// n=64 (height 2^18), 99 at n=128. A block needing more transactions emits **multiple** batch proofs
/// of ≤ `MAX_BATCH_TILES` tiles each (or a future config raises `num_queries`). Enforced by both
/// batch provers and both `lattica_*_batch_prove` ABI entry points; pinned by the per-circuit
/// `*_proven_security_floor` tests. The node's block production assumes this cap.
pub const MAX_BATCH_TILES: usize = 64;

/// The padded tile count for a batch of `n` transactions (a power of two; ≥ 1).
pub fn padded_tiles(n: usize) -> usize {
    n.max(1).next_power_of_two()
}

/// Write a tile's tx-root fold blocks into its trailing padding and return the tile's new running
/// root. `chunks` are the ordered 4-element statement chunks (see each circuit's `statement_chunks`):
/// block 0 injects `DOM_TXROOT` in lanes 0..4 and absorbs `chunks[0]`; each later s_k block chains
/// `perm(c ‖ chunk)`; the root block folds `perm(prev_root ‖ s_k)`. This reproduces the native
/// `tx_statement_digest` / `batch_root` chain on the trace side (no constraints, no periodic content).
pub(crate) fn write_fold_blocks(
    t: &mut [Val],
    toff: usize,
    width: usize,
    chunks: &[[Val; DIGEST]],
    prev_root: [Val; DIGEST],
    fold_base: usize,
    root_block: usize,
) -> [Val; DIGEST] {
    let mut inp = [Val::ZERO; 8];
    inp[0] = Val::from_u64(DOM_TXROOT);
    inp[DIGEST..].copy_from_slice(&chunks[0]);
    write_perm_block(t, toff + fold_base * BLOCK, width, inp);
    let mut c: [Val; DIGEST] = native_permute(inp)[..DIGEST].try_into().unwrap();
    for (bi, chunk) in chunks.iter().enumerate().skip(1) {
        let mut inp = [Val::ZERO; 8];
        inp[..DIGEST].copy_from_slice(&c);
        inp[DIGEST..].copy_from_slice(chunk);
        write_perm_block(t, toff + (fold_base + bi) * BLOCK, width, inp);
        c = native_permute(inp)[..DIGEST].try_into().unwrap();
    }
    let mut rinp = [Val::ZERO; 8];
    rinp[..DIGEST].copy_from_slice(&prev_root);
    rinp[DIGEST..].copy_from_slice(&c);
    write_perm_block(t, toff + root_block * BLOCK, width, rinp);
    native_permute(rinp)[..DIGEST].try_into().unwrap()
}

/// Append the tx-root fold's periodic selector columns after the tile-periodic columns (both batch
/// circuits, geometry passed as data): `P_TILE_LAST`, `fold_sk_blocks` chunk-injection one-hots,
/// s_k link, s_k→root, root-in, root-update. Emission order MUST match the circuit's `P_*` indices —
/// this is verifier-semantic periodic content, pinned by the constraint-fingerprint periodic fnv.
pub(crate) fn append_batch_selectors(
    cols: &mut Vec<Vec<Val>>,
    tile_height: usize,
    fold_sk_blocks: usize,
    fold_base: usize,
    root_block: usize,
) {
    let oh = |rows: &[usize]| {
        let mut c = vec![Val::ZERO; tile_height];
        for &r in rows {
            c[r] = Val::ONE;
        }
        c
    };
    let fold_in_row = |bi: usize| (fold_base + bi) * BLOCK;
    let fold_out_row = |bi: usize| (fold_base + bi) * BLOCK + BLOCK - 1;
    cols.push(oh(&[tile_height - 1])); // P_TILE_LAST
    for bi in 0..fold_sk_blocks {
        cols.push(oh(&[fold_in_row(bi)])); // P_FOLD_IN + bi
    }
    let sk_link: Vec<usize> = (0..fold_sk_blocks - 1).map(fold_out_row).collect();
    cols.push(oh(&sk_link)); // P_SK_LINK
    cols.push(oh(&[fold_out_row(fold_sk_blocks - 1)])); // P_SK_TO_ROOT
    cols.push(oh(&[root_block * BLOCK])); // P_ROOT_IN (= root_in_row)
    cols.push(oh(&[root_block * BLOCK + BLOCK - 1])); // P_ROOT_UPDATE (= root_out_row)
}

/// Within-tile persistence: each staged column is constant across a tile (freed at the tile boundary).
/// `staged`'s ORDER is the emission order, so it stays per-circuit (the constraint fnv pins it). Shared
/// body only — this is a straight-line builder loop, no control-flow knobs.
pub(crate) fn eval_tile_persistence<AB: AirBuilder<F = Goldilocks>>(
    builder: &mut AB,
    cur: &[AB::Expr],
    nxt: &[AB::Expr],
    tile_persist: AB::Expr,
    staged: &[usize],
) {
    for &c in staged {
        builder.when_transition().assert_zero(tile_persist.clone() * (nxt[c].clone() - cur[c].clone()));
    }
}

/// The in-circuit tx-root fold — ONE audited emitter for both batch circuits (the DOM_TXROOT fold is a
/// consensus object the Zig node mirrors; before, it was hand-synced in two files under the fingerprint
/// pins). `chunks` is the circuit's `fold_chunks()` (fold order); `p_fold = &periodic[P_FOLD_IN..]`
/// (so `p_fold[bi]` = chunk-injection selector `bi`, then `[n]` = s_k link, `[n+1]` = s_k→root,
/// `[n+2]` = root-in, `[n+3]` = root-update, where `n = chunks.len() = FOLD_SK_BLOCKS`); `root_col` is
/// the running-ROOT column base.
///
/// EMISSION ORDER (fingerprint-pinned — the verifier combines the AIR's constraints by powers of the
/// challenge α, so their emission ORDER is semantic; do NOT reorder): 1 chunk injection (bi ascending,
/// lanes k=0..DIGEST) · 2 block-0 low-lane pin `[DOM_TXROOT,0,0,0]` · 3 s_k link · 4 s_k→root handoff ·
/// 5 root-in bind · 6 ROOT IV=0 · 7 ROOT freeze/update pair per lane · 8 last-row == pis.
pub(crate) fn eval_txroot_fold<AB: AirBuilder<F = Goldilocks>>(
    builder: &mut AB,
    cur: &[AB::Expr],
    nxt: &[AB::Expr],
    pis: &[AB::Expr],
    p_fold: &[AB::Expr],
    chunks: &[FoldChunk],
    root_col: usize,
) {
    let n = chunks.len();
    let one = AB::Expr::ONE;
    let dom_txroot = AB::Expr::from(Goldilocks::from_u64(DOM_TXROOT));
    // 1. chunk injection: at fold block bi's input row, lanes DIGEST..2·DIGEST == the bi-th chunk.
    for (bi, chunk) in chunks.iter().enumerate() {
        let sel = p_fold[bi].clone();
        for (k, lane) in chunk.iter().enumerate() {
            match lane {
                Some(col) => builder.assert_zero(sel.clone() * (cur[DIGEST + k].clone() - cur[*col].clone())),
                None => builder.assert_zero(sel.clone() * cur[DIGEST + k].clone()),
            }
        }
    }
    // 2. block 0 pins the low lanes to [DOM_TXROOT, 0, 0, 0] (the chain start).
    let sk0 = p_fold[0].clone();
    builder.assert_zero(sk0.clone() * (cur[0].clone() - dom_txroot.clone()));
    for k in 1..DIGEST {
        builder.assert_zero(sk0.clone() * cur[k].clone());
    }
    // 3. s_k chain link: block bi output lanes 0..DIGEST → block bi+1 input lanes 0..DIGEST.
    let sl = p_fold[n].clone();
    for k in 0..DIGEST {
        builder.when_transition().assert_zero(sl.clone() * (nxt[k].clone() - cur[k].clone()));
    }
    // 4. last s_k block output (= s_k) → root block input lanes DIGEST..2·DIGEST.
    let s2r = p_fold[n + 1].clone();
    for k in 0..DIGEST {
        builder.when_transition().assert_zero(s2r.clone() * (nxt[DIGEST + k].clone() - cur[k].clone()));
    }
    // 5. root block input lanes 0..DIGEST == the running ROOT column (root_{k-1}).
    let ri = p_fold[n + 2].clone();
    for k in 0..DIGEST {
        builder.assert_zero(ri.clone() * (cur[k].clone() - cur[root_col + k].clone()));
    }
    // 6. IV: ROOT = 0 at the global first row.
    for k in 0..DIGEST {
        builder.when_first_row().assert_zero(cur[root_col + k].clone());
    }
    // 7. ROOT is constant except across the per-tile update (root block output row → next row).
    let ru = p_fold[n + 3].clone();
    for k in 0..DIGEST {
        builder
            .when_transition()
            .assert_zero((one.clone() - ru.clone()) * (nxt[root_col + k].clone() - cur[root_col + k].clone()));
        builder.when_transition().assert_zero(ru.clone() * (nxt[root_col + k].clone() - cur[k].clone()));
    }
    // 8. the root block is the LAST block, so the global last row's cur[0..DIGEST] IS the block tx-root.
    for k in 0..DIGEST {
        builder.when_last_row().assert_zero(cur[k].clone() - pis[k].clone());
    }
}
