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

use crate::config::{Dft, MyCompress, MyHash, Val, CAP_HEIGHT};
use p3_dft::TwoAdicSubgroupDft;
use p3_goldilocks::default_goldilocks_poseidon2_8;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_symmetric::{CryptographicHasher, PseudoCompressionFunction};
use std::ffi::CString;
use std::mem::size_of;
use std::sync::atomic::{AtomicU64, Ordering};

/// Poseidon2 digest width (Goldilocks-8 sponge squeezes 4).
pub const DIGEST: usize = 4;

/// A source of `h` leaf rows of width `w`, addressable one row at a time — the seam the streaming store
/// plugs into. `fill_row(i, buf)` writes row `i` (a `w`-wide slice) so the Merkle commit never holds the
/// whole `h × w` leaf matrix; a later increment backs this by an mmap'd, column-tiled LDE store.
pub trait LeafSource: Sync {
    fn height(&self) -> usize;
    fn width(&self) -> usize;
    fn fill_row(&self, row: usize, out: &mut [Val]);
    /// Fill `nr` consecutive rows starting at `r0` into `out` (row-major `nr × width`). The frontier
    /// Merkle reads through THIS (in row-blocks), so a COLUMN-MAJOR store can override it to read `width`
    /// contiguous column-segments — `width` interleaved sequential streams, ~one pass — instead of the
    /// strided per-row gather. The default is the row-major per-row fill.
    fn fill_row_block(&self, r0: usize, nr: usize, out: &mut [Val]) {
        let w = self.width();
        for i in 0..nr {
            self.fill_row(r0 + i, &mut out[i * w..(i + 1) * w]);
        }
    }
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

    // Leaf digest layer: hash rows in blocks (so a column-major store reads `w` contiguous
    // column-segments per block — one streaming pass — rather than a strided per-row gather). Only the
    // block buffer (ROW_BLOCK × w) and the digests ever reside; the wide leaves are never fully held.
    const ROW_BLOCK: usize = 4096;
    let bh = ROW_BLOCK.min(h);
    let mut block = vec![Val::default(); bh * w];
    let mut layer: Vec<[Val; DIGEST]> = Vec::with_capacity(h);
    let mut r0 = 0usize;
    while r0 < h {
        let nr = bh.min(h - r0);
        src.fill_row_block(r0, nr, &mut block[..nr * w]);
        for i in 0..nr {
            layer.push(hash.hash_iter(block[i * w..(i + 1) * w].iter().copied()));
        }
        r0 += nr;
    }

    // Compress pairwise (arity 2) up to the cap. `h` is a power of two, so every layer length is even
    // until it reaches the cap; a tree shorter than the cap clamps to the leaf layer (p3's effective cap).
    let cap_len = (1usize << cap_height).min(layer.len());
    while layer.len() > cap_len {
        layer = layer.chunks_exact(2).map(|c| compress.compress([c[0], c[1]])).collect();
    }
    layer
}

/// A file-backed (mmap'd) store for one `h × w` LDE matrix, held **COLUMN-MAJOR** (element `(row, col)`
/// at `map[col*h + row]`) — the out-of-core substrate that keeps the multi-GB LDE off the anonymous heap.
/// Column-major is what makes both directions ONE sequential pass and dodges the transpose barrier:
/// - **write** a column-tile → each column is a contiguous segment `[(c0+c)*h, (c0+c+1)*h)`, so the whole
///   LDE is written in one forward pass as `c0` advances (independent of the tile width);
/// - **read** for the frontier Merkle → `fill_row_block` reads `w` contiguous column-segments per row-block
///   (w interleaved sequential streams), one pass over the store.
///
/// Access is EXPLICIT and sequential, so the OS streams it (evicts behind the read head) instead of
/// thrashing on p3's blind whole-buffer re-touch (the Phase 2 allocator's failure). Later, FRI opening
/// reads individual rows by `fill_row` (sparse strided seeks — cheap at 96 queries).
pub struct MmapLdeStore {
    map: *mut Val,
    n: usize,
    h: usize,
    w: usize,
    fd: libc::c_int,
}

// SAFETY: `map` is a stable, process-private mmap for the store's lifetime; the streaming commit writes
// each tile BEFORE any read of it, so there is never a concurrent write+read of the same region.
unsafe impl Send for MmapLdeStore {}
unsafe impl Sync for MmapLdeStore {}

static LDE_STORE_SEQ: AtomicU64 = AtomicU64::new(0);

impl MmapLdeStore {
    /// Create a fresh zero-filled `h × w` store in `$LATTICA_SPILL_DIR` (else the temp dir). The file is
    /// unlinked immediately, so it is reclaimed on drop or crash.
    pub fn new(h: usize, w: usize) -> std::io::Result<Self> {
        let n = h.checked_mul(w).expect("store dimensions overflow");
        let bytes = n.checked_mul(size_of::<Val>()).expect("store byte size overflow");
        let dir = std::env::var("LATTICA_SPILL_DIR")
            .ok()
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| std::env::temp_dir().to_string_lossy().into_owned());
        let seq = LDE_STORE_SEQ.fetch_add(1, Ordering::Relaxed);
        let path = format!("{dir}/lat-lde-{}-{seq}.tmp", std::process::id());
        let cpath = CString::new(path).map_err(|_| std::io::Error::from(std::io::ErrorKind::InvalidInput))?;
        // SAFETY: raw file + mmap syscalls with a valid NUL-terminated path and a checked byte length.
        unsafe {
            let fd = libc::open(cpath.as_ptr(), libc::O_RDWR | libc::O_CREAT | libc::O_EXCL, 0o600);
            if fd < 0 {
                return Err(std::io::Error::last_os_error());
            }
            libc::unlink(cpath.as_ptr());
            if libc::ftruncate(fd, bytes as libc::off_t) != 0 {
                let e = std::io::Error::last_os_error();
                libc::close(fd);
                return Err(e);
            }
            let m = libc::mmap(std::ptr::null_mut(), bytes, libc::PROT_READ | libc::PROT_WRITE, libc::MAP_SHARED, fd, 0);
            if m == libc::MAP_FAILED {
                let e = std::io::Error::last_os_error();
                libc::close(fd);
                return Err(e);
            }
            Ok(Self { map: m as *mut Val, n, h, w, fd })
        }
    }

    /// The whole store as a slice (ftruncate-zeroed, then overwritten by the LDE writes).
    #[inline]
    fn slice(&self) -> &[Val] {
        // SAFETY: `map` covers `n` initialized `Val` elements (zeroed at creation) for the store's lifetime.
        unsafe { std::slice::from_raw_parts(self.map, self.n) }
    }

    /// Write a `h × cw` ROW-MAJOR LDE tile (columns `[c0, c0+cw)`, `tile[r*cw + c]`) into the COLUMN-MAJOR
    /// store: column `c0+c` fills the contiguous segment `[(c0+c)*h, (c0+c+1)*h)`. As `c0` advances across
    /// tiles this writes the whole store front-to-back in one sequential pass. The per-column transpose of
    /// the (small, resident) tile is in-RAM; the disk write is sequential.
    pub fn write_col_tile(&self, c0: usize, cw: usize, tile: &[Val]) {
        debug_assert_eq!(tile.len(), self.h * cw, "tile must be h*cw");
        debug_assert!((c0 + cw) * self.h <= self.n, "column tile out of bounds");
        for c in 0..cw {
            // SAFETY: `[(c0+c)*h, +h)` is in-bounds; distinct columns are disjoint; written before any read.
            let dst = unsafe { std::slice::from_raw_parts_mut(self.map.add((c0 + c) * self.h), self.h) };
            for (r, d) in dst.iter_mut().enumerate() {
                *d = tile[r * cw + c];
            }
        }
    }
}

impl Drop for MmapLdeStore {
    fn drop(&mut self) {
        // SAFETY: `map`/`fd` were produced by `mmap`/`open` in `new` and are freed exactly once here.
        unsafe {
            libc::munmap(self.map as *mut libc::c_void, self.n * size_of::<Val>());
            libc::close(self.fd);
        }
    }
}

impl LeafSource for MmapLdeStore {
    fn height(&self) -> usize {
        self.h
    }
    fn width(&self) -> usize {
        self.w
    }
    /// One row by strided gather across the `w` column-segments — for sparse FRI-query reads.
    fn fill_row(&self, row: usize, out: &mut [Val]) {
        let s = self.slice();
        for (c, o) in out.iter_mut().enumerate() {
            *o = s[c * self.h + row];
        }
    }
    /// A block of `nr` rows, read as `w` contiguous column-segments `[c*h + r0, +nr)` (w interleaved
    /// sequential streams over the store) transposed into `out` (row-major `nr × w`) — one streaming pass.
    fn fill_row_block(&self, r0: usize, nr: usize, out: &mut [Val]) {
        let s = self.slice();
        for c in 0..self.w {
            let seg = &s[c * self.h + r0..c * self.h + r0 + nr];
            for i in 0..nr {
                out[i * self.w + c] = seg[i];
            }
        }
    }
}

/// Compute the coset-LDE of `trace` a COLUMN-TILE at a time and write each tile into the COLUMN-MAJOR
/// `store` (via `write_col_tile`), so only one `big × c_block` tile ever resides, never the whole
/// `big × w` LDE, and the store is written FRONT-TO-BACK in ONE sequential pass (each column is a
/// contiguous segment). Byte-identical to `Dft::coset_lde_batch(trace, added_bits, shift)` read
/// row-major: columns are independent polynomials (a column subset yields identical per-column output)
/// and the row bit-reversal is column-independent. `store` must be `big × w` (`big = h << added_bits`).
///
/// Paired with the frontier Merkle's transposed-block read, the whole out-of-core commit is ~2
/// sequential passes over the store, INDEPENDENT of `w` — so it is RAM-bounded AND fast, unlike the
/// row-major-store predecessor (`w/c_block` passes) and the Phase 2 allocator (thrashed under pressure).
pub fn stream_coset_lde_to_store(trace: &RowMajorMatrix<Val>, added_bits: usize, shift: Val, c_block: usize, store: &MmapLdeStore) {
    let (h, w) = (trace.height(), trace.width());
    let big = h << added_bits;
    assert_eq!(store.height(), big, "store height must be the blown-up height");
    assert_eq!(store.width(), w, "store width must match the trace");
    assert!(c_block >= 1, "column block must be >= 1");
    let dft = Dft::default();
    let mut c0 = 0usize;
    while c0 < w {
        let cw = c_block.min(w - c0);
        // gather columns [c0, c0+cw) into a narrow h×cw matrix
        let mut sub = Vec::with_capacity(h * cw);
        for r in 0..h {
            sub.extend_from_slice(&trace.values[r * w + c0..r * w + c0 + cw]);
        }
        // coset-LDE the narrow tile -> big×cw, bit-reversed rows (p3's storage order), then discard it
        let lde = dft.coset_lde_batch(RowMajorMatrix::new(sub, cw), added_bits, shift).to_row_major_matrix();
        store.write_col_tile(c0, cw, &lde.values);
        c0 += cw;
    }
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

    /// Column-tiled LDE written into the mmap store is byte-identical to p3's whole `coset_lde_batch`
    /// (the whole LDE never resides — only one `big × c_block` tile at a time).
    #[test]
    fn stream_lde_matches_p3() {
        let dft = Dft::default();
        let shift = <Val as Field>::GENERATOR;
        for &(log_h, w, added, cblk) in &[(4usize, 3usize, 2usize, 1usize), (8, 5, 3, 2), (10, 49, 4, 8), (12, 53, 4, 16)] {
            let h = 1usize << log_h;
            let vals: Vec<Val> = (0..h * w)
                .map(|i| Val::new((i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) % 0xFFFF_FFFF_0000_0001))
                .collect();
            let mat = RowMajorMatrix::new(vals, w);
            let p3_lde = dft.coset_lde_batch(mat.clone(), added, shift).to_row_major_matrix();
            let big = h << added;
            let store = MmapLdeStore::new(big, w).unwrap();
            stream_coset_lde_to_store(&mat, added, shift, cblk, &store);
            // reconstruct the row-major matrix from the COLUMN-MAJOR store and compare to p3's whole LDE
            let mut got = vec![Val::default(); big * w];
            store.fill_row_block(0, big, &mut got);
            assert_eq!(got, p3_lde.values, "streamed LDE store (row-major view) != p3 at h=2^{log_h} w={w} cblk={cblk}");
        }
    }

    /// End-to-end out-of-core commit: column-tiled LDE into the mmap store + frontier Merkle equals p3's
    /// `coset_lde_batch` + `MerkleTreeMmcs` commitment. Neither the whole LDE nor the whole leaf matrix
    /// ever resides — this is the substrate that actually cuts the prover's RAM.
    #[test]
    fn stream_lde_merkle_matches_p3() {
        let dft = Dft::default();
        let shift = <Val as Field>::GENERATOR;
        let perm = default_goldilocks_poseidon2_8();
        let mmcs = RefMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm), CAP_HEIGHT);
        for &(log_h, w, added, cblk) in &[(7usize, 2usize, 4usize, 1usize), (10, 49, 4, 8), (12, 53, 4, 16)] {
            let h = 1usize << log_h;
            let big = h << added;
            let vals: Vec<Val> = (0..h * w)
                .map(|i| Val::new((i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) % 0xFFFF_FFFF_0000_0001))
                .collect();
            let mat = RowMajorMatrix::new(vals, w);
            let p3_lde = dft.coset_lde_batch(mat.clone(), added, shift).to_row_major_matrix();
            let (p3_commit, _) = mmcs.commit(vec![p3_lde]);
            let store = MmapLdeStore::new(big, w).unwrap();
            stream_coset_lde_to_store(&mat, added, shift, cblk, &store);
            let mine = stream_merkle_cap(&store, CAP_HEIGHT);
            let p3_cap: &[[Val; DIGEST]] = p3_commit.as_ref();
            assert_eq!(p3_cap, mine.as_slice(), "streamed LDE+Merkle != p3 at h=2^{log_h} w={w} cblk={cblk}");
        }
    }

    /// Peak resident set (VmHWM) in MiB, from /proc/self/status.
    fn peak_rss_mib() -> u64 {
        std::fs::read_to_string("/proc/self/status")
            .ok()
            .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM")).map(str::to_string))
            .and_then(|l| l.split_whitespace().nth(1).and_then(|v| v.parse::<u64>().ok()))
            .map(|kb| kb / 1024)
            .unwrap_or(0)
    }

    /// RAM bench: stream a large trace's LDE (blowup 16) into the column-major mmap store and
    /// frontier-Merkle it, entirely out-of-core. The commit's LDE (the multi-GB buffer) lives on disk;
    /// access is EXPLICIT and sequential (one column-major write pass + one transposed-block Merkle read),
    /// so under a cgroup cap it completes with BOUNDED RSS — where the Phase 2 allocator thrashed on p3's
    /// blind whole-buffer re-touch. Run under `systemd-run --user --scope -p MemoryMax=<cap>` on a
    /// nodatacow scratch. Tunables: LATTICA_STREAM_LOGH (18), LATTICA_STREAM_W (53), LATTICA_STREAM_CBLK (4).
    ///
    /// MEASURED: 1.66 GiB LDE (h=2^18, w=53) under a 1 GB HARD cap → RSS 1013 MiB, 41 s — vs 233 s for the
    /// row-major-store predecessor at the same RAM bound (5.6x; ~2 sequential passes, w-independent).
    #[test]
    #[ignore = "bench: out-of-core LDE+Merkle RAM (LATTICA_STREAM_LOGH=<n>, LATTICA_SPILL_DIR=<disk>)"]
    fn stream_commit_ram_bench() {
        let env = |k: &str, d: usize| std::env::var(k).ok().and_then(|s| s.parse().ok()).unwrap_or(d);
        let (log_h, w, cblk, added) = (env("LATTICA_STREAM_LOGH", 18), env("LATTICA_STREAM_W", 53), env("LATTICA_STREAM_CBLK", 4), 4usize);
        let (h, big) = (1usize << log_h, 1usize << (log_h + added));
        let shift = <Val as Field>::GENERATOR;
        // the input trace (h×w) is resident — it is LDE/blowup smaller than the LDE this streams to disk.
        let vals: Vec<Val> = (0..h * w).map(|i| Val::new((i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) % 0xFFFF_FFFF_0000_0001)).collect();
        let mat = RowMajorMatrix::new(vals, w);
        let store = MmapLdeStore::new(big, w).unwrap();
        let t0 = std::time::Instant::now();
        stream_coset_lde_to_store(&mat, added, shift, cblk, &store);
        let cap = stream_merkle_cap(&store, CAP_HEIGHT);
        let secs = t0.elapsed().as_secs_f64();
        assert_eq!(cap.len(), 1usize << CAP_HEIGHT.min(log_h + added), "cap has the expected width");
        println!(
            "STREAM-COMMIT-BENCH log_h={log_h} big=2^{} w={w} cblk={cblk} store={}MiB peak_rss={}MiB commit={secs:.1}s",
            log_h + added,
            (big * w * size_of::<Val>()) / (1 << 20),
            peak_rss_mib(),
        );
    }
}
