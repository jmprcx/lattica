//! Shared batch-aggregation machinery — the tile cap, tile padding, and the fold-block trace
//! writer used by BOTH batch circuits (`batch_joinsplit_air`, `batch_htlc_air`).
//!
//! The per-circuit fold GEOMETRY (`FOLD_SK_BLOCKS`, chunk schedules, staging column offsets) stays
//! in each circuit file by design: the two statements fold different chunk counts (join-split 5,
//! HTLC 7 + height/hashlock), so those constants are circuit shape, not shared machinery.

use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::Goldilocks;

use crate::domains::DOM_TXROOT;
use crate::poseidon2_air::{native_permute, write_perm_block, BLOCK};

type Val = Goldilocks;
const DIGEST: usize = 4;

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
