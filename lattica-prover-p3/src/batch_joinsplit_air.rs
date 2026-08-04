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
//! The native oracle (`tx_statement_digest`, `dummy_sk`, `batch_root`) is the cross-checked contract:
//! the in-circuit fold is differential-tested against it, and the node's `poseidon2.zig` recompute is
//! KAT-tested against it. The per-tile spend constraints are `joinsplit_air::eval_spend`, reused
//! verbatim (fed the per-tile staging statement + the `P_TILE_LAST` boundary selector).

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::Goldilocks;
use p3_matrix::dense::RowMajorMatrix;
#[cfg(test)]
use p3_uni_stark::prove;

use crate::joinsplit_air::{
    build_trace, eval_spend, merge, periodic, public_values, Input, Output, Witness, DEPTH, DIGEST,
    HEIGHT, M_OUT, N_IN, N_PERIODIC, N_PUBLIC, PI_ANCHOR, PI_FEE, PI_MINT, PI_NF, PI_OUTCM,
    PI_TXBIND, WIDTH,
};
use crate::poseidon2_air::BLOCK;

type Val = Goldilocks;

/// Domain tag for the per-transaction statement digest — the normative table lives in crate::domains.
pub use crate::domains::DOM_TXROOT;

/// Per-transaction statement digest `s_k`: a domain-tagged Merkle–Damgård chain over the public
/// statement. Block 0 = `H(DOM_TXROOT,0,0,0 ‖ anchor)` (a `merge` with the domain in the low half);
/// then merge-shaped blocks absorb each nullifier, each output commitment, `[fee,mint,0,0]`, and
/// `tx_binding` as 4-element chunks. The batch circuit reproduces this exact chain from the per-tile
/// staging columns, so the layout here is the cross-checked contract.
pub fn tx_statement_digest(pv: &[Val]) -> [Val; DIGEST] {
    debug_assert_eq!(pv.len(), N_PUBLIC);
    debug_assert_eq!(PI_TXBIND + DIGEST, N_PUBLIC);
    let chunks = statement_chunks(pv);
    let dom = [Val::from_u64(DOM_TXROOT), Val::ZERO, Val::ZERO, Val::ZERO];
    let mut c = merge(dom, chunks[0]);
    for chunk in &chunks[1..] {
        c = merge(c, *chunk);
    }
    c
}

/// The ordered 4-element statement chunks the s_k fold absorbs, in fold order (anchor, each nullifier,
/// each out_cm, `[fee, mint, 0, 0]`, tx_binding). The SINGLE native source of the consensus chunk
/// order: `tx_statement_digest` folds these, and the trace builder feeds them to the in-circuit fold
/// (`write_fold_blocks`). Must stay in lockstep with the AIR-side chunk table (`fold_chunks`).
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
    v
}

/// The canonical padding tile: a VALID 0-value 2-in/2-out spend (two identical zero notes folding to a
/// shared zero-derived anchor; 0 fee/mint). Using a real valid spend as padding means dummy tiles need
/// no special-case gating — they satisfy every per-tile constraint exactly like a real tile, and their
/// statement is a fixed constant both the prover and the node fold for padding.
pub fn dummy_witness() -> Witness {
    let z4 = [Val::ZERO; DIGEST];
    let inp = Input {
        nk: [0, 0],
        div: Val::ZERO,
        asset: Val::ZERO,
        value: 0,
        rho: [Val::ZERO; 2],
        rcm: [Val::ZERO; 2],
        sib: [z4; DEPTH],
        bits: [false; DEPTH],
    };
    let out = Output {
        recipient: z4,
        asset: Val::ZERO,
        value: 0,
        rho: [Val::ZERO; 2],
        rcm: [Val::ZERO; 2],
    };
    Witness {
        inputs: core::array::from_fn(|_| inp.clone()),
        outputs: [out; M_OUT],
        fee: 0,
        mint: 0,
        tx_binding: z4,
    }
}

/// The statement digest of a padding tile (the canonical `dummy_witness`). A real tx has a non-zero
/// anchor/nullifiers, so a real `s_k` cannot collide with it.
pub fn dummy_sk() -> [Val; DIGEST] {
    tx_statement_digest(&public_values(&dummy_witness()))
}

/// The block **tx-root**: fold each transaction's `s_k` into a running digest (IV = 0), then pad to a
/// power of two with dummy tiles. `root_k = H(root_{k-1} ‖ s_k)`. This is the single public input of the
/// batch proof; the node recomputes it from the block's transactions to verify one proof per block.
pub fn batch_root(ws: &[Witness]) -> [Val; DIGEST] {
    let n_padded = padded_tiles(ws.len());
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

/// The padded tile count — shared batch machinery (re-exported so existing paths keep working).
pub use crate::batch_common::padded_tiles;

// =============================================================================================
// The batch AIR: the join-split spend tiled n times in one trace, proven once. The per-tile
// constraints are the audited `joinsplit_air` constraints made tile-safe (self-containment); the
// periodic columns are reused verbatim from `joinsplit_air::periodic()` (Plonky3 repeats them per
// tile) plus one new boundary selector `P_TILE_LAST`. Each tile's statement bindings point at its
// staging columns, and the in-circuit tx-root fold chains the staged statements to the single
// `batch_root` public input — so DISTINCT transactions verify under one proof.
// =============================================================================================

const TILE_HEIGHT: usize = HEIGHT;
const NUM_BLOCKS: usize = HEIGHT / BLOCK;

// --- batch-only main columns (beyond joinsplit's WIDTH=19) ---
// Staging columns are TILE-PERSISTENT: each holds a field of this tile's public statement, bound to the
// genuinely-computed value at the existing selector row, so the fold can read them anywhere in the tile.
const S_ANCHOR: usize = WIDTH; // 4
const S_NF: usize = S_ANCHOR + DIGEST; // N_IN·4
const S_OUTCM: usize = S_NF + N_IN * DIGEST; // M_OUT·4
const S_FEE: usize = S_OUTCM + M_OUT * DIGEST;
const S_MINT: usize = S_FEE + 1;
const S_TXBIND: usize = S_MINT + 1; // 4 (free; bound transitively via the node's root recompute)
const ROOT: usize = S_TXBIND + DIGEST; // 4 — running tx-root chain (GLOBAL-persistent across tiles)
const BATCH_WIDTH: usize = ROOT + DIGEST;

// --- the in-circuit fold, placed in the free padding at the END of the block space ---
// s_k = MD-chain(DOM_TXROOT ‖ anchor ‖ nf ‖ out_cm ‖ [fee,mint] ‖ tx_binding); then root_k = H(root_{k-1} ‖ s_k).
const FOLD_SK_BLOCKS: usize = 1 + N_IN + M_OUT + 2; // anchor block, then N_IN+M_OUT+2 merge blocks
const FOLD_BLOCKS: usize = FOLD_SK_BLOCKS + 1; // + the root-chain block
const FOLD_BASE: usize = NUM_BLOCKS - FOLD_BLOCKS; // robust: at the very end (joinsplit uses blocks 0..80)
const ROOT_BLOCK: usize = FOLD_BASE + FOLD_SK_BLOCKS;

// The fold-block input/output rows are now computed inside `batch_common::append_batch_selectors`
// (periodic) and `write_fold_blocks` (trace); only the root block's OUTPUT row is still needed here,
// to know where `root_{k-1}` ends when threading the ROOT column.
const fn root_out_row() -> usize {
    ROOT_BLOCK * BLOCK + BLOCK - 1
}
#[cfg(test)]
const fn fold_in_row(bi: usize) -> usize {
    (FOLD_BASE + bi) * BLOCK
}

// --- batch periodic selectors (appended after joinsplit's N_PERIODIC tile-periodic columns) ---
const P_TILE_LAST: usize = N_PERIODIC; // 1 at each tile's last row (self-containment)
const P_FOLD_IN: usize = P_TILE_LAST + 1; // FOLD_SK_BLOCKS one-hots: chunk injection at each s_k block input
const P_SK_LINK: usize = P_FOLD_IN + FOLD_SK_BLOCKS; // s_k block output → next block input lanes 0..4
const P_SK_TO_ROOT: usize = P_SK_LINK + 1; // last s_k block output → root block input lanes 4..8
const P_ROOT_IN: usize = P_SK_TO_ROOT + 1; // root block input lanes 0..4 == ROOT column
const P_ROOT_UPDATE: usize = P_ROOT_IN + 1; // root block output → ROOT column (the per-tile update)
const BATCH_N_PERIODIC: usize = P_ROOT_UPDATE + 1;

/// The AIR-side chunk table the tx-root fold injects, in fold order — the in-circuit twin of the native
/// `statement_chunks` (an auditor checks the two side by side). Each entry is 4 lanes: a staged column
/// `Some(col)` or a 0-pin `None`; the fee/mint block is `[S_FEE, S_MINT, 0, 0]`.
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
    v
}

// FRI / ZK config — the production family from crate::config (single audited source; the trace height
// is runtime, so one config + one AIR proves/verifies every batch size).
#[cfg(test)]
use crate::config::make_config;

/// The tile-periodic columns: joinsplit's `periodic()` (each length `HEIGHT` ⇒ repeated per tile by
/// Plonky3) plus `P_TILE_LAST` = a one-hot at the tile's last row (also repeated per tile).
fn batch_periodic() -> Vec<Vec<Val>> {
    let mut cols = periodic();
    // P_TILE_LAST, the FOLD_SK_BLOCKS chunk-injection one-hots, then s_k-link / s_k→root / root-in /
    // root-update — the order MUST match the P_* indices above (shared machinery, geometry as data).
    crate::batch_common::append_batch_selectors(
        &mut cols,
        TILE_HEIGHT,
        FOLD_SK_BLOCKS,
        FOLD_BASE,
        ROOT_BLOCK,
    );
    cols
}

pub struct JoinSplitBatchAir;

impl BaseAir<Goldilocks> for JoinSplitBatchAir {
    fn width(&self) -> usize {
        BATCH_WIDTH
    }
    fn num_public_values(&self) -> usize {
        DIGEST // the single block tx-root (root_{n-1})
    }
    fn num_periodic_columns(&self) -> usize {
        BATCH_N_PERIODIC
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        batch_periodic()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for JoinSplitBatchAir {
    fn eval(&self, builder: &mut AB) {
        let cur: Vec<AB::Expr> = builder
            .main()
            .current_slice()
            .iter()
            .map(|&x| x.into())
            .collect();
        let nxt: Vec<AB::Expr> = builder
            .main()
            .next_slice()
            .iter()
            .map(|&x| x.into())
            .collect();
        let p: Vec<AB::Expr> = builder
            .periodic_values()
            .iter()
            .map(|&x| x.into())
            .collect();
        let one = AB::Expr::ONE;
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        // 1 at each tile's last row — frees the cross-tile-leaking persistence inside eval_spend.
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

        // 2. the per-tile join-split spend constraints — joinsplit_air's audited body reused verbatim,
        //    fed the staging statement + tile_last (the cur == statement[..] bindings inside eval_spend
        //    double as the staging bindings).
        eval_spend(builder, &statement, tile_last.clone());

        // =====================================================================================
        // Batch: per-tile staging + the in-circuit tx-root fold.
        // =====================================================================================

        // ---- staging columns are TILE-persistent (constant within a tile, free at the tile boundary) ----
        let tile_persist = one.clone() - tile_last.clone();
        let staged: Vec<usize> = {
            let mut v = vec![S_FEE, S_MINT];
            for k in 0..DIGEST {
                v.push(S_ANCHOR + k);
                v.push(S_TXBIND + k);
            }
            for i in 0..N_IN {
                for k in 0..DIGEST {
                    v.push(S_NF + i * DIGEST + k);
                }
            }
            for j in 0..M_OUT {
                for k in 0..DIGEST {
                    v.push(S_OUTCM + j * DIGEST + k);
                }
            }
            v
        };
        crate::batch_common::eval_tile_persistence(builder, &cur, &nxt, tile_persist, &staged);

        // ---- the in-circuit tx-root fold: s_k MD-chain (block 0 = perm([DOM_TXROOT,0,0,0 ‖ anchor]),
        //      blocks 1.. absorb each chunk) then root_k = perm([root_{k-1} ‖ s_k]), ROOT carried across
        //      tiles. Shared emitter; `fold_chunks()` is this circuit's chunk table (checked by eye
        //      against `statement_chunks`) and `ROOT` is the running-root column. ----
        crate::batch_common::eval_txroot_fold(
            builder,
            &cur,
            &nxt,
            &pis,
            &p[P_FOLD_IN..],
            &fold_chunks(),
            ROOT,
        );
    }
}

/// Tile `padded_tiles(ws.len())` single-tile traces into one batch trace, fill each tile's staging
/// columns, run the in-circuit tx-root fold (`batch_common::write_fold_blocks`), and thread the running
/// ROOT across tiles (padded to a power of two with `dummy_witness`). Each tile reuses the audited
/// `joinsplit_air::build_trace`.
pub fn build_batch_trace(ws: &[Witness]) -> RowMajorMatrix<Val> {
    let n = padded_tiles(ws.len());
    let dummy = dummy_witness();
    let mut t = vec![Val::ZERO; n * TILE_HEIGHT * BATCH_WIDTH];
    let mut root = [Val::ZERO; DIGEST]; // IV
    for tile in 0..n {
        let w = if tile < ws.len() { &ws[tile] } else { &dummy };
        let single = build_trace(w); // HEIGHT × WIDTH(19)
        let pv = public_values(w); // the 26-element statement
        let toff = tile * TILE_HEIGHT;

        // 1. copy joinsplit's 19 columns into this tile's first 19 columns
        for r in 0..TILE_HEIGHT {
            let dst = (toff + r) * BATCH_WIDTH;
            let src = r * WIDTH;
            t[dst..dst + WIDTH].copy_from_slice(&single.values[src..src + WIDTH]);
        }
        // 2. staging columns (tile-persistent — filled on every row of the tile)
        for r in 0..TILE_HEIGHT {
            let b = (toff + r) * BATCH_WIDTH;
            t[b + S_ANCHOR..b + S_ANCHOR + DIGEST]
                .copy_from_slice(&pv[PI_ANCHOR..PI_ANCHOR + DIGEST]);
            t[b + S_NF..b + S_NF + N_IN * DIGEST]
                .copy_from_slice(&pv[PI_NF..PI_NF + N_IN * DIGEST]);
            t[b + S_OUTCM..b + S_OUTCM + M_OUT * DIGEST]
                .copy_from_slice(&pv[PI_OUTCM..PI_OUTCM + M_OUT * DIGEST]);
            t[b + S_FEE] = pv[PI_FEE];
            t[b + S_MINT] = pv[PI_MINT];
            t[b + S_TXBIND..b + S_TXBIND + DIGEST]
                .copy_from_slice(&pv[PI_TXBIND..PI_TXBIND + DIGEST]);
        }
        // 3. fold blocks (overwrite the trailing padding blocks): s_k MD-chain, then root chain.
        let new_root = crate::batch_common::write_fold_blocks(
            &mut t,
            toff,
            BATCH_WIDTH,
            &statement_chunks(&pv),
            root,
            FOLD_BASE,
            ROOT_BLOCK,
        );
        // 4. ROOT column: root_{k-1} up to (and incl.) the root block output row, then root_k onward.
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

/// Prove a batch of transactions as one proof. Returns the proof bytes; the block tx-root (the single
/// public input) is `batch_root(ws)`, which the verifier recomputes from the block's statements.
pub fn prove_batch_to_bytes(ws: &[Witness]) -> Vec<u8> {
    assert!(
        padded_tiles(ws.len()) <= MAX_BATCH_TILES,
        "batch exceeds MAX_BATCH_TILES ({MAX_BATCH_TILES}); split the block into multiple batch proofs"
    );
    crate::config::proof_to_bytes(&JoinSplitBatchAir, build_batch_trace(ws), &batch_root(ws))
}

/// The batch tile cap — shared batch machinery (re-exported so existing paths keep working); the
/// ≥100-bit floor at this cap is pinned by `batch_proven_security_floor`.
pub use crate::batch_common::MAX_BATCH_TILES;

/// Proven (UDR) security bits at a batch of `n` transactions (trace height = `padded_tiles(n)·TILE_HEIGHT`).
/// Mirrors `joinsplit_air::measure`'s computation; the batch grows the height ~log(n), slowly lowering the
/// proven floor. The largest size holding ≥100 bits is `MAX_BATCH_TILES`.
pub fn proven_security_bits(n: usize) -> usize {
    crate::config::proven_security_bits(&JoinSplitBatchAir, padded_tiles(n) * TILE_HEIGHT)
}

/// Verify a batch proof against the block tx-root (4 Goldilocks).
pub fn verify_batch_bytes(proof_bytes: &[u8], root: &[Val]) -> bool {
    crate::config::verify_proof_bytes(
        &JoinSplitBatchAir,
        DIGEST,
        MAX_BATCH_TILES * TILE_HEIGHT,
        proof_bytes,
        root,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::joinsplit_air::{demo_witness, ASSET};

    // Distinct, well-formed witnesses (vary tx_binding ⇒ distinct public statements). batch_root only
    // hashes public_values, so the witnesses need not balance for these oracle tests.
    fn variant(tag: u64) -> Witness {
        let mut w = demo_witness();
        w.tx_binding[0] += Val::from_u64(tag);
        w
    }

    // Peak resident set (VmHWM, process-lifetime) in MiB — for the RAM-vs-block-size benchmark.
    fn peak_rss_mib() -> u64 {
        std::fs::read_to_string("/proc/self/status")
            .ok()
            .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM")).map(String::from))
            .and_then(|l| {
                l.split_whitespace()
                    .nth(1)
                    .and_then(|v| v.parse::<u64>().ok())
            })
            .map(|kib| kib / 1024)
            .unwrap_or(0)
    }

    /// RAM-vs-BLOCK-SIZE benchmark for the PRODUCTION batch path (one STARK proof per block). Run ONE N per
    /// process (`LATTICA_BATCH_N=<n>`) so VmHWM (peak RSS) is isolated to that block size. Tiles are valid
    /// balanced 2-in/2-out join-split spends; the trace is `padded_tiles(n)·HEIGHT` rows at the production
    /// config (cap-6, q96/lb4 — ≥100-bit proven up to MAX_BATCH_TILES=64). Reports peak RSS, prove time, and
    /// proof size.
    #[test]
    #[ignore = "bench: batch RAM vs block size (LATTICA_BATCH_N=<n>, one N per process)"]
    fn batch_ram_bench() {
        use p3_matrix::Matrix;
        let n: usize = std::env::var("LATTICA_BATCH_N")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(8)
            .max(1);
        let ws: Vec<Witness> = (0..n).map(|i| variant_asset(1000 + i as u64)).collect();
        let root = batch_root(&ws);
        let trace = build_batch_trace(&ws);
        let (rows, w) = (trace.height(), trace.width());
        let t0 = std::time::Instant::now();
        let proof = prove(&make_config(), &JoinSplitBatchAir, trace, &root);
        let prove_s = t0.elapsed().as_secs_f64();
        let bytes = postcard::to_allocvec(&proof).unwrap();
        assert!(verify_batch_bytes(&bytes, &root), "batch of {n} verifies");
        println!(
            "BATCH-BENCH n={n} padded_tiles={} tile_height={HEIGHT} rows={rows} width={w} peak_rss={}MiB prove={prove_s:.1}s proof={}KiB",
            padded_tiles(n),
            peak_rss_mib(),
            bytes.len() / 1024
        );
    }

    /// Same block-size RAM/time bench, proven on the GPU (`config::gpu::make_config_hiding` = GpuHidingPcs:
    /// device-side LDE + Merkle + quotient randomization). Proof is BYTE-IDENTICAL to CPU and verifies under the
    /// production verifier (asserted). The LDE/NTT device buffers are column-tiled (`gpu.rs::col_block`) to stay
    /// under this GPU's ~3.88 GB CL_DEVICE_MAX_MEM_ALLOC_SIZE, so a full 64-tx block proves on-device (the earlier
    /// ≤ 8-tx CL_INVALID_BUFFER_SIZE ceiling is gone); only total device global memory now bounds the block size.
    #[cfg(feature = "gpu")]
    #[test]
    #[ignore = "bench: batch RAM/time on the GPU (LATTICA_BATCH_N=<n>, one N per process)"]
    fn batch_ram_bench_gpu() {
        use p3_matrix::Matrix;
        let n: usize = std::env::var("LATTICA_BATCH_N")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(8)
            .max(1);
        let ws: Vec<Witness> = (0..n).map(|i| variant_asset(1000 + i as u64)).collect();
        let root = batch_root(&ws);
        let trace = build_batch_trace(&ws);
        let (rows, w) = (trace.height(), trace.width());
        let cfg = crate::config::gpu::make_config_hiding();
        let t0 = std::time::Instant::now();
        let proof = prove(&cfg, &JoinSplitBatchAir, trace, &root);
        let prove_s = t0.elapsed().as_secs_f64();
        let bytes = postcard::to_allocvec(&proof).unwrap();
        assert!(
            verify_batch_bytes(&bytes, &root),
            "batch of {n} verifies (GPU-proven, CPU verifier)"
        );
        println!(
            "BATCH-BENCH-GPU n={n} padded_tiles={} rows={rows} width={w} peak_rss={}MiB prove={prove_s:.1}s proof={}KiB",
            padded_tiles(n),
            peak_rss_mib(),
            bytes.len() / 1024
        );
    }

    /// Same block-size RAM/time bench under the OUT-OF-CORE allocator (`--features stream`): the trace,
    /// quotient, and Merkle-leaf LDE buffers spill to an mmap'd file, so peak RSS is bounded by
    /// page-cache pressure (set a cgroup `memory.high`) instead of the whole LDE living in RAM. The proof
    /// VERIFIES under the production verifier — spilling is byte-transparent (mmap-backed memory holds
    /// identical bytes; the mechanics are pinned byte-exact by `spill_alloc::tests`). Reports peak RSS and
    /// the spill high-water mark. Point `LATTICA_SPILL_DIR` at a disk-backed (ideally `chattr +C`) scratch.
    #[cfg(feature = "stream")]
    #[test]
    #[ignore = "bench: batch RAM/time under the spill allocator (LATTICA_BATCH_N=<n>, LATTICA_SPILL_DIR=<disk>)"]
    fn batch_ram_bench_stream() {
        use p3_matrix::Matrix;
        let n: usize = std::env::var("LATTICA_BATCH_N")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(64)
            .max(1);
        let ws: Vec<Witness> = (0..n).map(|i| variant_asset(1000 + i as u64)).collect();
        let root = batch_root(&ws);
        let trace = build_batch_trace(&ws);
        let (rows, w) = (trace.height(), trace.width());
        crate::spill_alloc::reset_spill_peak();
        let t0 = std::time::Instant::now();
        let bytes = {
            let _g = crate::spill_alloc::SpillScope::arm();
            let proof = prove(&make_config(), &JoinSplitBatchAir, trace, &root);
            postcard::to_allocvec(&proof).unwrap()
        };
        let prove_s = t0.elapsed().as_secs_f64();
        let spill_peak = crate::spill_alloc::spill_peak_bytes();
        assert!(
            verify_batch_bytes(&bytes, &root),
            "batch of {n} verifies (spill-proven)"
        );
        assert!(spill_peak > 0, "the LDE must spill to mmap while armed (n={n}); needs a block whose LDE exceeds the 64 MiB threshold + a writable LATTICA_SPILL_DIR");
        println!(
            "BATCH-BENCH-STREAM n={n} padded_tiles={} rows={rows} width={w} peak_rss={}MiB spill_peak={}MiB prove={prove_s:.1}s proof={}KiB",
            padded_tiles(n),
            peak_rss_mib(),
            spill_peak / (1 << 20),
            bytes.len() / 1024
        );
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

    // ---- Phase 3: distinct tiles bound to the tx-root via staging + the in-circuit fold ----

    #[test]
    fn batch_n1_verifies_under_txroot() {
        let w = variant(1);
        let root = batch_root(std::slice::from_ref(&w));
        assert!(verify_batch_bytes(
            &prove_batch_to_bytes(std::slice::from_ref(&w)),
            &root
        ));
    }

    #[test]
    fn batch_distinct_tiles_verify_and_match_oracle_root() {
        let ws = [variant(1), variant(2)];
        let root = batch_root(&ws);
        assert!(verify_batch_bytes(&prove_batch_to_bytes(&ws), &root));
    }

    #[test]
    fn batch_rejects_wrong_txroot() {
        let ws = [variant(1), variant(2)];
        let proof = prove_batch_to_bytes(&ws);
        let mut bad = batch_root(&ws);
        bad[0] += Val::ONE;
        assert!(!verify_batch_bytes(&proof, &bad));
    }

    #[test]
    #[ignore = "slow: proves a 4-tile batch"]
    fn batch_four_distinct_tiles_verify() {
        let ws: Vec<Witness> = (1..=4).map(variant).collect();
        let root = batch_root(&ws);
        assert!(verify_batch_bytes(&prove_batch_to_bytes(&ws), &root));
    }

    // ---- Phase 4: dummy padding + corrupted-trace / cross-tile isolation (the audit gate) ----

    // A valid balanced spend with a chosen hidden asset. Built on the dummy-witness shape (two IDENTICAL
    // inputs ⇒ a shared anchor trivially), so changing the asset stays self-consistent — unlike
    // demo_witness, whose two inputs use distinct Merkle paths tuned to one anchor.
    fn variant_asset(a: u64) -> Witness {
        let mut w = dummy_witness();
        let av = Val::from_u64(a);
        for inp in w.inputs.iter_mut() {
            inp.asset = av;
        }
        for out in w.outputs.iter_mut() {
            out.asset = av;
        }
        w
    }

    // Prove the (possibly corrupted) trace and verify; true iff rejected (verify=false or prover panics).
    fn corrupt_batch_rejected(trace: RowMajorMatrix<Val>, root: &[Val]) -> bool {
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let proof = prove(&make_config(), &JoinSplitBatchAir, trace, root);
            verify_batch_bytes(&postcard::to_allocvec(&proof).unwrap(), root)
        }));
        matches!(outcome, Ok(false) | Err(_))
    }

    #[test]
    fn batch_kat_dump() {
        // KAT for the Zig node's txStatementDigest/batchRoot fold (poseidon2.zig), seq statement = 1..=N_PUBLIC.
        // PINNED (harvested at HEAD c7e54b1): these are CONSENSUS values — the node recomputes them
        // natively and both sides must agree; a change is a chain fork. Prints kept for cross-language diff.
        use p3_field::PrimeField64;
        let seq: Vec<Val> = (1..=N_PUBLIC as u64).map(Val::from_u64).collect();
        let felts = |x: &[Val; DIGEST]| x.iter().map(|f| f.as_canonical_u64()).collect::<Vec<_>>();
        let s = felts(&tx_statement_digest(&seq));
        let d = felts(&dummy_sk());
        println!("seq_statement_digest = {s:?}");
        println!("dummy_sk = {d:?}");
        assert_eq!(
            s,
            [
                16413833029060099665,
                4880920211288721702,
                16696557975413361240,
                12647866530414313287
            ]
        );
        assert_eq!(
            d,
            [
                10093663321021608916,
                18280800825645272076,
                7712995835321977355,
                5336904204250640364
            ]
        );
    }

    #[test]
    fn batch_proven_security_floor() {
        // n=1 matches the single join-split (103 proven); the floor holds through MAX_BATCH_TILES and
        // 2·MAX_BATCH_TILES is the first size below 100 — pinning N_MAX as exactly the boundary.
        assert_eq!(proven_security_bits(1), 103);
        assert!(
            proven_security_bits(MAX_BATCH_TILES) >= 100,
            "MAX_BATCH_TILES must hold the ≥100-bit floor"
        );
        assert!(
            proven_security_bits(MAX_BATCH_TILES * 2) < 100,
            "MAX_BATCH_TILES is the boundary: 2× drops below the 100-bit floor"
        );
    }

    #[test]
    fn batch_dummy_padding_fold_matches_oracle() {
        // 3 real tiles → padded to 4 with one dummy tile; the in-circuit fold's final output (the trace's
        // last-row root-block output, cols 0..4) must equal the native batch_root (which folds dummy_sk).
        let ws = [variant(1), variant(2), variant(3)];
        let trace = build_batch_trace(&ws);
        let root = batch_root(&ws);
        let h = trace.values.len() / BATCH_WIDTH;
        for k in 0..DIGEST {
            assert_eq!(
                trace.values[(h - 1) * BATCH_WIDTH + k],
                root[k],
                "fold limb {k} != oracle root"
            );
        }
    }

    #[test]
    #[ignore = "slow: proves a 4-tile (3 real + 1 dummy) batch"]
    fn batch_non_power_of_two_verifies() {
        let ws = [variant(1), variant(2), variant(3)];
        let root = batch_root(&ws);
        assert!(verify_batch_bytes(&prove_batch_to_bytes(&ws), &root));
    }

    #[test]
    #[ignore = "slow: proves a 2-tile batch to exercise the verify-side height cap (audit F1)"]
    fn batch_verify_rejects_above_tile_cap() {
        // A valid 2-tile batch verifies; tampering its degree_bits above the 64-tile ceiling (19) makes
        // verify_batch_bytes reject via the height cap BEFORE the expensive verify — so an oversize,
        // below-100-bit-floor batch cannot verify even if a caller forgot to pre-cap. (v3-batch audit F1)
        use crate::config::MyConfig;
        use p3_uni_stark::Proof;
        let ws = [variant(1), variant(2)];
        let root = batch_root(&ws);
        let bytes = prove_batch_to_bytes(&ws);
        assert!(
            verify_batch_bytes(&bytes, &root),
            "the honest 2-tile batch must verify"
        );
        let mut proof: Proof<MyConfig> = postcard::from_bytes(&bytes).unwrap();
        proof.degree_bits = (MAX_BATCH_TILES * TILE_HEIGHT).trailing_zeros() as usize + 2; // one above the cap
        let tampered = postcard::to_allocvec(&proof).unwrap();
        assert!(
            !verify_batch_bytes(&tampered, &root),
            "a proof above the 64-tile height cap must reject"
        );
    }

    #[test]
    #[ignore = "slow: 2-tile prove"]
    fn batch_per_tile_asset_isolation() {
        // two tiles with DIFFERENT hidden assets verify — the per-tile ASSET gate allows it (a global
        // ASSET would force one asset for the whole block).
        let ws = [variant_asset(11), variant_asset(22)];
        let root = batch_root(&ws);
        assert!(verify_batch_bytes(&prove_batch_to_bytes(&ws), &root));
    }

    #[test]
    #[ignore = "slow: corrupted-trace prove"]
    fn batch_corrupted_staged_anchor_is_rejected() {
        let ws = [variant(1), variant(2)];
        let root = batch_root(&ws);
        let mut trace = build_batch_trace(&ws);
        for r in 0..TILE_HEIGHT {
            trace.values[r * BATCH_WIDTH + S_ANCHOR] += Val::ONE; // tile 0's staged anchor
        }
        assert!(corrupt_batch_rejected(trace, &root));
    }

    #[test]
    #[ignore = "slow: corrupted-trace prove"]
    fn batch_corrupted_staged_nullifier_is_rejected() {
        let ws = [variant(1), variant(2)];
        let root = batch_root(&ws);
        let mut trace = build_batch_trace(&ws);
        for r in 0..TILE_HEIGHT {
            trace.values[(TILE_HEIGHT + r) * BATCH_WIDTH + S_NF] += Val::ONE; // tile 1's staged nf
        }
        assert!(corrupt_batch_rejected(trace, &root));
    }

    #[test]
    #[ignore = "slow: corrupted-trace prove"]
    fn batch_within_tile_asset_tamper_is_rejected() {
        // change ASSET at a single mid-tile row ⇒ breaks the per-tile ASSET persistence (cross-tile
        // isolation requires ASSET constant WITHIN a tile, free only at the boundary).
        let ws = [variant(1), variant(2)];
        let root = batch_root(&ws);
        let mut trace = build_batch_trace(&ws);
        trace.values[(TILE_HEIGHT / 2) * BATCH_WIDTH + ASSET] += Val::ONE;
        assert!(corrupt_batch_rejected(trace, &root));
    }

    #[test]
    #[ignore = "slow: corrupted-trace prove"]
    fn batch_corrupted_fold_block_is_rejected() {
        let ws = [variant(1), variant(2)];
        let root = batch_root(&ws);
        let mut trace = build_batch_trace(&ws);
        trace.values[fold_in_row(1) * BATCH_WIDTH + DIGEST] += Val::ONE; // a data lane of an s_k fold block
        assert!(corrupt_batch_rejected(trace, &root));
    }
}
