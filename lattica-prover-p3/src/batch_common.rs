//! Shared batch-aggregation machinery — the tile cap, tile padding, and the fold-block trace
//! writer used by BOTH batch circuits (`batch_joinsplit_air`, `batch_htlc_air`).
//!
//! The per-circuit fold GEOMETRY (`FOLD_SK_BLOCKS`, chunk schedules, staging column offsets) stays
//! in each circuit file by design: the two statements fold different chunk counts (join-split 5,
//! HTLC 7 + height/hashlock), so those constants are circuit shape, not shared machinery.

use p3_goldilocks::Goldilocks;

use crate::poseidon2_air::{native_steps, BLOCK};

type Val = Goldilocks;

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

/// Write the Poseidon2 permutation of `input` into fold `block`'s state columns (cols 0..8) of a
/// batch trace with `width` columns, at tile offset `toff`.
pub(crate) fn set_fold_block(t: &mut [Val], toff: usize, block: usize, width: usize, input: [Val; 8]) {
    let rows = native_steps(input);
    for (r, row) in rows.iter().enumerate() {
        let base = (toff + block * BLOCK + r) * width;
        t[base..base + 8].copy_from_slice(row);
    }
}
