//! Phase 3 of the streaming-prover plan: an in-crate, prove-only fork that streams the commit so the
//! wide LDE leaves never all reside in RAM at once — the structural RAM win that the Phase 2 mmap
//! allocator could not deliver (the OS cannot stream p3's whole-buffer re-touch pattern from below the
//! `Vec` types; see `spill_alloc`). `verify` and every wire type stay upstream: this fork PRODUCES p3's
//! `Proof<MyConfig>` bytes, it never redefines them.
//!
//! Generalizes the proven `quotient_gpu::prove_gpu` fork (already byte-identical to `p3_uni_stark::prove`)
//! by pushing control BELOW the `Pcs` seam — into the Merkle commit and (later) the FRI open — which is
//! where the residency actually lives.
//!
//! ## This increment — the streaming (frontier) Merkle commit
//! The first, risk-retiring piece (the plan sequences it first, validated standalone before wiring): a
//! Merkle commitment that hashes leaf rows ONE AT A TIME from a streaming source, keeping only the
//! digest layers (`h × DIGEST` fields — tens of MiB) instead of the whole `h × w` leaf matrix (the
//! multi-GB buffer). It is BYTE-IDENTICAL to p3's `MerkleTreeMmcs` commitment for a single power-of-two
//! -height matrix: p3's SIMD `vertically_packed_row` hashing is just lanes of the same per-row digest,
//! and `padded_len(h, 2) == h` for a power-of-two height, so scalar per-row hashing + pairwise compress
//! reproduces p3's exact layers. Pinned by `stream_merkle_matches_p3`.
//!
//! Feature-gated (`stream`, off by default) — RESEARCH, not on any production path.

use crate::config::{MyCompress, MyHash, Val, CAP_HEIGHT};
use p3_goldilocks::default_goldilocks_poseidon2_8;
use p3_symmetric::{CryptographicHasher, PseudoCompressionFunction};

/// Poseidon2 digest width (Goldilocks-8 sponge squeezes 4).
pub const DIGEST: usize = 4;

/// A source of `h` leaf rows of width `w`, addressable one row at a time — the seam the streaming store
/// plugs into. `fill_row(i, buf)` writes row `i` (a `w`-wide slice) so the Merkle commit never holds the
/// whole `h × w` leaf matrix; a later increment backs this by an mmap'd, column-tiled LDE store.
pub trait LeafSource: Sync {
    fn height(&self) -> usize;
    fn width(&self) -> usize;
    fn fill_row(&self, row: usize, out: &mut [Val]);
}

/// A `LeafSource` over an already-materialized row-major matrix — the Vec-backed store used to pin the
/// streaming Merkle byte-identical before the mmap store exists.
pub struct SliceLeaves<'a> {
    pub vals: &'a [Val],
    pub h: usize,
    pub w: usize,
}

impl LeafSource for SliceLeaves<'_> {
    fn height(&self) -> usize {
        self.h
    }
    fn width(&self) -> usize {
        self.w
    }
    fn fill_row(&self, row: usize, out: &mut [Val]) {
        out.copy_from_slice(&self.vals[row * self.w..(row + 1) * self.w]);
    }
}

/// Streaming Merkle commitment of `src` (single matrix, power-of-two height): hash each leaf row on the
/// fly (only one row + the digest layers ever reside), then compress pairwise up to the `cap_height` cap.
/// Returns the cap digests — byte-identical to `MerkleTreeMmcs::commit(vec![matrix]).0` under the same
/// `MyHash`/`MyCompress`/`CAP_HEIGHT`. This is the frontier build that keeps the wide leaves off the heap.
pub fn stream_merkle_cap<S: LeafSource>(src: &S, cap_height: usize) -> Vec<[Val; DIGEST]> {
    let h = src.height();
    let w = src.width();
    assert!(h.is_power_of_two(), "stream_merkle_cap: leaf height must be a power of two (got {h})");
    let perm = default_goldilocks_poseidon2_8();
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm);

    // Leaf digest layer: hash each row from the source, discarding the row (only the digests survive).
    let mut layer: Vec<[Val; DIGEST]> = {
        let mut row = vec![Val::default(); w];
        (0..h)
            .map(|i| {
                src.fill_row(i, &mut row);
                hash.hash_iter(row.iter().copied())
            })
            .collect()
    };

    // Compress pairwise (arity 2) up to the cap. `h` is a power of two, so every layer length is even
    // until it reaches the cap; a tree shorter than the cap clamps to the leaf layer (p3's effective cap).
    let cap_len = (1usize << cap_height).min(layer.len());
    while layer.len() > cap_len {
        layer = layer.chunks_exact(2).map(|c| compress.compress([c[0], c[1]])).collect();
    }
    layer
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_commit::Mmcs;
    use p3_field::Field;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_merkle_tree::MerkleTreeMmcs;

    type RefMmcs = MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, 2, DIGEST>;

    /// The streaming (frontier) Merkle cap is byte-identical to p3's `MerkleTreeMmcs` commitment across
    /// heights/widths — proving the wide leaves can be hashed one row at a time (never fully resident)
    /// without changing the commitment. This is the standalone gate the plan requires before wiring the
    /// streaming store into the commit.
    #[test]
    fn stream_merkle_matches_p3() {
        let perm = default_goldilocks_poseidon2_8();
        let mmcs = RefMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm), CAP_HEIGHT);
        for &(log_h, w) in &[(3usize, 1usize), (6, 5), (7, 2), (10, 49), (12, 53), (13, 1291)] {
            let h = 1usize << log_h;
            // deterministic pseudo-random leaf values (canonical Goldilocks)
            let vals: Vec<Val> = (0..h * w)
                .map(|i| Val::new((i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) % 0xFFFF_FFFF_0000_0001))
                .collect();
            let mat = RowMajorMatrix::new(vals.clone(), w);
            let (p3_commit, _) = mmcs.commit(vec![mat]);
            let mine = stream_merkle_cap(&SliceLeaves { vals: &vals, h, w }, CAP_HEIGHT);
            // p3's commitment is the `MerkleCap` (AsRef<[digest]>) at CAP_HEIGHT
            let p3_cap: &[[Val; DIGEST]] = p3_commit.as_ref();
            assert_eq!(p3_cap, mine.as_slice(), "streaming Merkle cap != p3 at h=2^{log_h} w={w}");
        }
    }
}
