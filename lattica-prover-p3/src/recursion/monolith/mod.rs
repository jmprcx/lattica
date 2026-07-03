//! Monolith — the in-circuit recursive STARK verifier AIR: the AIR PORT of the validated
//! `native_fri::verify_proof`. One AIR (transcript region + per-query tiles + constraint epilogue) whose
//! trace is satisfiable iff `p3::verify(inner)` accepts. Built phase-by-phase per the approved plan
//! (docs/recursion-verifier-audit.md §10). ⚠️ WORK IN PROGRESS — research, NOT production, NOT audited.
//!
//! Reuses the validated gadgets (`verifier_air`, `fri_merkle`, `fri_fold`, `transcript`) + the
//! `batch_*_air` tiling pattern (periodic selectors + staging + global-persistent columns). Proven with
//! the audited p3 single-AIR `prove`/`verify`; hard 8 GB peak-RSS budget enforced per phase.
//!
//! ## Phase 0 — geometry pin + budget oracle
//! Pins the first-milestone inner proof's shape (arity-2 `ConstAir`, `degree_bits=6`) and confirms the
//! derived monolith trace height fits ≤ 2^18 and proving stays ≤ 8 GB, before any AIR is built. The
//! per-query block budget below is the cost model the per-query tile (Phase 3) must hit.
//!
//! ## Phase 1 — AIR skeleton + transcript preamble (α, ζ)
//! `PreambleAir`: the duplex-sponge transcript preamble, generalizing the validated `TranscriptAir` to
//! the milestone's cap-sized absorbs (instance felts → α, commitment felts → ζ). Validated standalone vs
//! the native challenger (`preamble_challenges`); its eval is composed into the full MonolithAir in Phase 4.
//!
//! ## Module layout (split of the original single-file `monolith.rs`; the module path is unchanged)
//! `air` — the fused `MonolithAir` (struct + runtime geometry + `BaseAir`/`Air::eval` + periodic tables);
//! `build` — `HidingWitness` + `monolith_build_trace` (+ the live `ft_build_trace` transcript filler);
//! `gadgets` — general-arity fold / leaf-hash / arity-4 chain / aggregator-fold gadgets + the live
//! `eval_symbolic_circuit` OOD-epilogue circuit; `lineage` (`#[cfg(test)]`) — the superseded standalone
//! AIRs kept as executable provenance; `tests` — the phase-by-phase validation suite.
//!
//! ## Lineage — which standalone AIR each `MonolithAir` region superseded (all now in `lineage`)
//! - `PreambleAir` (Phase 1) → transcript preamble (instance/commitment absorbs → α, ζ)
//! - `FullTranscriptAir` (Phase 2) → the full transcript region (schedule-driven sponge + challenge binds)
//! - `DeepPointAir` (Phase 3 pt 1) → arith tile: DEEP point x from the index bits
//! - `MroAir` (Phase 3 pt 2) → arith tile: reduced opening (DEEP combination)
//! - `QueryFoldAir` (Phase 3 pts 3+5) → arith tile: bit-aware commit-phase fold chain + final check
//! - `QueryInputTileAir` (Phase 4 pt 1) → arith tile: index → x → ro composition
//! - `QueryTileAir` (Phase 4 pt 2) → super-tile block 0: the full per-query arithmetic
//! - `TiledQueryAir` (Phase 4 pt 4) → the ×K tiled query region
//! - `MonolithSkeletonAir` (Phase 4.0) → the region layout + masks (transcript | query | epilogue)
//! - `CarryBindAir` (Phase 4.A) → the global-persistent challenge carriers
//! - `Phase4AAir` (Phase 4.A fusion) → the fused transcript + tiled-query core
//! - `IndexBindAir` (Phase 4.A #3) → canonical index-bit decomposition per tile
//! - `FoldPointAir` (Phase 4.A #4) → in-circuit fold points s_r per tile
//! - `CapMuxAir` (Phase 4.B #7) → cap-entry selection from the high index bits
//! - `InputMerkleTileAir` (Phase 4.B) → super-tile input-Merkle blocks (leaf hash + merges)
//! - `SuperTileAir` (Phase 4.B) → the super-tile: arith + inline input-Merkle in one period
//! - `CommitMerkleTileAir` (Phase 4.B) → super-tile commit-phase Merkle blocks

mod air;
mod build;
mod gadgets;
#[cfg(test)]
mod lineage;
#[cfg(test)]
mod tests;

pub(crate) use air::*;
#[allow(unused_imports)] // consumed by the test harnesses (native_verify + tests), not the lib pass
pub(crate) use build::*;
pub(crate) use gadgets::*;
#[cfg(test)]
pub(crate) use lineage::*;

// ── Shared sponge / column-layout consts, used by the live AIR (air/build/gadgets) and by the
//    superseded standalone AIRs alike — hoisted here so `lineage` can stay #[cfg(test)]. ──
const RATE: usize = 4;
const CAP_LANE: usize = RATE;
const FT_P_BLOCK_LAST: usize = 11;
const FT_COUNT: usize = 12; // count_b at block b's rows (for the first-row capacity init)
const FT_COUNT_NEXT: usize = 13; // count_{b+1} at block b's rows (for the carry into the next block)
const FT_IS_SQ_NEXT: usize = 14; // 1 if block b+1 is a squeeze (count 0 ⇒ rate carries)
const FT_BIND_START: usize = 15; // one one-hot per bound challenge follows
const MRO_W_EXT: u64 = 7; // F_p² : X² = 7
const QT_E: usize = 0; // fold: running eval
const QT_S: usize = 2; // fold: sibling
const QT_B: usize = 4; // fold: β_r
const QT_BIT: usize = 6; // fold: group-order bit
const QT_SPT: usize = 7; // fold: point s_r
const QT_I2S: usize = 8; // fold: inv(2 s_r)
const QT_DBITS: usize = 9; // DEEP index bits (row 0)
// The db=6 milestone reference cap height (2^6 = 64 entries of 4 felts). `MonolithAir.cap_height` is the
// RUNTIME per-inner value (proof-derivable: log2 of MerkleCap.roots().len()); this const now serves only
// the cfg(test) reference values + the frozen standalone-gadget/lineage tests.
#[cfg(test)]
const CM_CAP_HEIGHT: usize = 6;

// ── Monolith super-tile geometry, DERIVED from the base params so re-pinning the FRI depth is a config change,
//    not a rewrite. Base params: DP_LOG_HEIGHT (= log_global = degree_bits + log_blowup), CM_CAP_HEIGHT (the
//    FRI Merkle-cap height), LOG_BLOWUP (the FRI rate). Every derived value below equals the db=6 milestone
//    literal (guarded by the `geometry_matches_milestone` test). Layout: block 0 arith | input-Merkle |
//    quotient-Merkle | commit-phase Merkle (CM_ROUNDS rounds). ──
const LOG_BLOWUP: usize = 4; // FRI rate (log); log_global = degree_bits + LOG_BLOWUP
// MonolithAir derives these at RUNTIME per-inner (cm_rounds()=nb−3, lg()=cm_rounds()+LOG_BLOWUP); these consts
// are the db=6 milestone reference values, now used only by the guard/aggregator tests.
#[cfg(test)]
const M_DEGREE_BITS: usize = DP_LOG_HEIGHT - LOG_BLOWUP; // inner-trace degree_bits (10 − 4 = 6)
#[cfg(test)]
const CM_ROUNDS: usize = DP_LOG_HEIGHT - LOG_BLOWUP; // FRI commit rounds = folds to the rate floor = degree_bits
#[cfg(test)]
const INPUT_DEPTH: usize = DP_LOG_HEIGHT - CM_CAP_HEIGHT; // input/quotient Merkle path depth to the cap (10 − 6 = 4)
const M_INPUT_LEAF: usize = 1; // first input-leaf block; the leaf spans M_INPUT_LEAF .. +leaf_blocks (runtime)
// HIDING (is_zk=1) width constants — the ZK wrapper's parameters (see native_verify / hiding_commit_layout).
const HIDING_NUM_CW: usize = 4; // HidingFriPcs num_random_codewords added to each committed input matrix
const HIDING_SALT: usize = 4; // MerkleTreeHidingMmcs SALT_ELEMS appended to each leaf preimage
const HIDING_RAND_PUB: usize = 2; // random-round opened value width (one F_p²)
// The LEAF-BLOCK / nqc dimensions of the layout (input-Merkle leaf blocks = ceil(W_inner/RATE), quotient-Merkle
// leaf blocks = ceil(2·nqc/RATE), and everything downstream: M_INPUT_TERM, M_QUOT_LEAF/TERM, CM_LEAF/TERM,
// M_NBLOCKS, M_PERIOD) vary PER INNER, so they are RUNTIME methods on `MonolithAir` (m_input_term()/…/m_period())
// rather than consts — see the geometry methods on the impl. At the milestone (W≤RATE, nqc=1 ⇒ leaf_blocks=1)
// they equal the db=6 literals (guarded by `geometry_matches_milestone`; validated across configs by
// `commit_layout_generalizes`). Only the FRI-depth scalars below stay compile-time (one pinned config).
// commit round r folds the codeword to log-height DP_LOG_HEIGHT−(r+1); its Merkle path is that many levels
// above the cap (0 once the codeword ≤ 2^cap_height). depths at db=6: [3,2,1,0,0,0]. Parameterized by
// (log_global, cap) so the formula is validated at other configs (see `commit_layout_generalizes`).
const fn cm_depth_at(r: usize, log_global: usize, cap: usize) -> usize {
    let h = log_global - (r + 1);
    if h > cap {
        h - cap
    } else {
        0
    }
}
#[cfg(test)]
const fn cm_depth(r: usize) -> usize {
    cm_depth_at(r, DP_LOG_HEIGHT, CM_CAP_HEIGHT)
}

// Runtime twin of the compile-time geometry derivation, parameterized by (log_global, cap_height, log_blowup),
// for the single-block-leaf / nqc=1 baseline. Used only to VALIDATE the derivation matches the consts at db=6
// and generalizes to other depths (see `commit_layout_generalizes`); the monolith itself uses the consts.
#[cfg(test)]
#[allow(clippy::type_complexity)]
fn commit_layout(log_global: usize, cap: usize, log_blowup: usize, leaf_blocks: usize, quot_leaf_blocks: usize) -> (usize, usize, usize, usize, Vec<usize>, Vec<usize>, usize) {
    let cm_rounds = log_global - log_blowup;
    let input_depth = log_global - cap;
    let m_input_term = M_INPUT_LEAF + (leaf_blocks - 1) + input_depth; // multi-block input leaf + path
    let m_quot_leaf = m_input_term + 1;
    let m_quot_term = m_quot_leaf + (quot_leaf_blocks - 1) + input_depth; // multi-block quotient leaf + path
    let (mut leaf, mut term) = (Vec::with_capacity(cm_rounds), Vec::with_capacity(cm_rounds));
    let mut blk = m_quot_term + 1;
    for r in 0..cm_rounds {
        let d = cm_depth_at(r, log_global, cap);
        leaf.push(blk);
        term.push(blk + d);
        blk += d + 1;
    }
    let m_nblocks = term[cm_rounds - 1] + 1;
    (cm_rounds, input_depth, m_input_term, m_quot_term, leaf, term, m_nblocks)
}

/// HIDING (is_zk=1) super-tile layout — the geometry the in-circuit hiding monolith needs (#86 AIR mode).
/// Mirrors `commit_layout` but with THREE input rounds (random, trace, quotient) instead of two, each a
/// SALTED multi-block leaf (preimage = committed_row ‖ salt, absorbed RATE felts/block) + a Merkle path of
/// `input_depth` levels to its cap, then the commit rounds. The random round is structurally a COPY of the
/// trace input-leaf region (prepended). Widths (validated by the native witness): the reduced-opening TERM
/// widths use the MERGED row (public ‖ codewords, NO salt); the LEAF felt widths add SALT_ELEMS; the quotient
/// leaf is the multi-matrix concat over nqc chunks. Returns (m_random_term, m_input_term, m_quot_term, cm_leaf,
/// cm_term, m_nblocks, n_terms, [random_leaf_blocks, trace_leaf_blocks, quot_leaf_blocks]).
#[cfg(test)]
#[allow(clippy::type_complexity)]
fn hiding_commit_layout(
    w_inner: usize,
    nqc: usize,
    log_global: usize,
    cap: usize,
    log_blowup: usize,
) -> (usize, usize, usize, Vec<usize>, Vec<usize>, usize, usize, [usize; 3]) {
    let cm_rounds = log_global - log_blowup;
    let input_depth = log_global - cap;
    // merged widths (public ‖ codewords) = the reduced-opening term widths (NO salt).
    let random_merged = HIDING_RAND_PUB + HIDING_NUM_CW;
    let trace_merged = w_inner + HIDING_NUM_CW;
    let quot_merged = 2 + HIDING_NUM_CW; // per chunk: F_p² (2) + codewords
    // leaf felt widths = committed row ‖ salt; the quotient leaf is the multi-matrix concat over nqc chunks.
    let rlb = (random_merged + HIDING_SALT).div_ceil(RATE);
    let ilb = (trace_merged + HIDING_SALT).div_ceil(RATE);
    let qlb = (nqc * (quot_merged + HIDING_SALT)).div_ceil(RATE);
    // super-tile: block 0 reserved (arith/opened-row setup), then random-leaf, trace-leaf, quot-leaf, each a
    // leaf-hash sponge + `input_depth` path merges; then the commit rounds. is_zk=0 would drop the random region
    // (m_input_leaf back to 1), recovering `commit_layout`.
    let m_random_term = M_INPUT_LEAF + (rlb - 1) + input_depth;
    let m_input_term = (m_random_term + 1) + (ilb - 1) + input_depth;
    let m_quot_term = (m_input_term + 1) + (qlb - 1) + input_depth;
    // the commit phase is ALSO salted (hiding ChallengeMmcs): each round's leaf = MyHash(group ‖ salt) = 8
    // felts ⇒ a 2-block sponge per round (confirmed by hiding_query_commit_merkle_all's (salts, siblings)).
    let cm_leaf_blocks = (4 + HIDING_SALT).div_ceil(RATE);
    let (mut leaf, mut term) = (Vec::with_capacity(cm_rounds), Vec::with_capacity(cm_rounds));
    let mut blk = m_quot_term + 1;
    for r in 0..cm_rounds {
        let d = cm_depth_at(r, log_global, cap);
        leaf.push(blk);
        term.push(blk + (cm_leaf_blocks - 1) + d);
        blk += (cm_leaf_blocks - 1) + d + 1;
    }
    let m_nblocks = term[cm_rounds - 1] + 1;
    // reduced-opening terms: random (×1 point) + trace (×2 points ζ,ζ_next) + quotient (nqc chunks ×1 point).
    let n_terms = random_merged + 2 * trace_merged + nqc * quot_merged;
    (m_random_term, m_input_term, m_quot_term, leaf, term, m_nblocks, n_terms, [rlb, ilb, qlb])
}

/// Max inner proofs the tiled aggregator folds in ONE outer proof, mirroring `batch_joinsplit_air::
/// MAX_BATCH_TILES`. K must be a power of two (the fold's Merkle–Damgård chain pads to pow2, as `batch_root`
/// does); production rounds a short block up to the next pow2 with dummy-proof instances. NOTE: unlike the
/// audited batch, this RESEARCH aggregator runs a reduced-query milestone config (arity-2, ≤32 queries), so
/// it does NOT clear the ≥100-bit proven-security floor — production raises the outer config to the batch's
/// 96-query params (where `proven_security_bits(MAX_BATCH_TILES) ≥ 100`) before this bound is load-bearing.
#[allow(dead_code)]
pub(crate) const MAX_AGG_TILES: usize = 64;
