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

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::Goldilocks;
use p3_matrix::dense::RowMajorMatrix;
use p3_uni_stark::{prove, verify, Proof};

use crate::poseidon2_air::{ext_linear, int_linear, native_permute, native_steps, pow7, BLOCK};
use crate::joinsplit_air::{
    build_trace, merge, periodic, public_values, Input, Output, Witness, ASSET, BIT, DEPTH, DIGEST,
    DOM_CM, DOM_NF, DOM_OWN, HEIGHT, M_OUT, N_IN, N_PERIODIC, NK, NK1, NUM_PUBLIC_INPUTS, PI_ANCHOR, PI_FEE, PI_MINT,
    PI_NF, PI_OUTCM, PI_TXBIND, POSACC, P_CHAIN_LINK, P_COMMIT_A_IN, P_COMMIT_B, P_FEE_IN, P_FINAL, P_MEM_LINK,
    P_MINT_IN, P_NULLOUT, P_NULL_IN, P_OUTOUT, P_OUT_A_IN, P_OWN_IN, P_POS_COEFF, P_RANGE_ACTIVE,
    P_RANGE_CLOSE, P_RANGE_SEED, P_RECIP_LINK, P_REGION_LAST, P_ROOT, P_ROW0, REM, RBIT, RHO, RHO1, VAL,
    VALACC, WIDTH,
};

type Val = Goldilocks;

/// Domain tag for the per-transaction statement digest (1=OWN, 2=CM, 3=NF, 4=HTLC, 5=NF_HTLC).
pub const DOM_TXROOT: u64 = 6;

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
    let out = Output { recipient: z4, asset: Val::ZERO, value: 0, rho: [Val::ZERO; 2], rcm: [Val::ZERO; 2] };
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

// =============================================================================================
// The batch AIR: the join-split spend tiled n times in one trace, proven once. The per-tile
// constraints are the audited `joinsplit_air` constraints made tile-safe (self-containment); the
// periodic columns are reused verbatim from `joinsplit_air::periodic()` (Plonky3 repeats them per
// tile) plus one new boundary selector `P_TILE_LAST`. PHASE 2: still binds each tile to the global
// public inputs, so only IDENTICAL tiles verify — this validates tiling + self-containment. Phase 3
// redirects the per-tile statement bindings to staging columns and adds the in-circuit tx-root fold,
// so DISTINCT transactions verify under the single `batch_root` public input.
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

// --- batch periodic selectors (appended after joinsplit's N_PERIODIC tile-periodic columns) ---
const P_TILE_LAST: usize = N_PERIODIC; // 1 at each tile's last row (self-containment)
const P_FOLD_IN: usize = P_TILE_LAST + 1; // FOLD_SK_BLOCKS one-hots: chunk injection at each s_k block input
const P_SK_LINK: usize = P_FOLD_IN + FOLD_SK_BLOCKS; // s_k block output → next block input lanes 0..4
const P_SK_TO_ROOT: usize = P_SK_LINK + 1; // last s_k block output → root block input lanes 4..8
const P_ROOT_IN: usize = P_SK_TO_ROOT + 1; // root block input lanes 0..4 == ROOT column
const P_ROOT_UPDATE: usize = P_ROOT_IN + 1; // root block output → ROOT column (the per-tile update)
const BATCH_N_PERIODIC: usize = P_ROOT_UPDATE + 1;

/// The 4-element staging column base for fold chunk `ci` (anchor, nf_i, out_cm_j, [fee,mint], tx_binding).
/// Returns None for the fee/mint chunk (handled specially: [S_FEE, S_MINT, 0, 0]).
const fn chunk_stage(ci: usize) -> Option<usize> {
    if ci == 0 {
        Some(S_ANCHOR)
    } else if ci < 1 + N_IN {
        Some(S_NF + (ci - 1) * DIGEST)
    } else if ci < 1 + N_IN + M_OUT {
        Some(S_OUTCM + (ci - 1 - N_IN) * DIGEST)
    } else if ci == 1 + N_IN + M_OUT {
        None // [fee, mint, 0, 0]
    } else {
        Some(S_TXBIND)
    }
}

// FRI / ZK config — the production family from crate::config (single audited source; the trace height
// is runtime, so one config + one AIR proves/verifies every batch size).
use crate::config::{make_config, MyConfig};

/// The tile-periodic columns: joinsplit's `periodic()` (each length `HEIGHT` ⇒ repeated per tile by
/// Plonky3) plus `P_TILE_LAST` = a one-hot at the tile's last row (also repeated per tile).
fn batch_periodic() -> Vec<Vec<Val>> {
    let mut cols = periodic();
    let oh = |rows: &[usize]| {
        let mut c = vec![Val::ZERO; TILE_HEIGHT];
        for &r in rows {
            c[r] = Val::ONE;
        }
        c
    };
    // order MUST match the P_* indices above
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
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let two = AB::Expr::TWO;
        let dom_own = AB::Expr::from(Goldilocks::from_u64(DOM_OWN));
        let dom_cm = AB::Expr::from(Goldilocks::from_u64(DOM_CM));
        let dom_nf = AB::Expr::from(Goldilocks::from_u64(DOM_NF));

        let is_init = p[0].clone();
        let is_full = p[1].clone();
        let is_partial = p[2].clone();
        let rc: Vec<AB::Expr> = (0..8).map(|i| p[3 + i].clone()).collect();
        // TILE EDIT: 1 at each tile's last row — frees the cross-tile-leaking persistence below.
        let tile_last = p[P_TILE_LAST].clone();

        // ---- Poseidon2 round constraints (period-32 schedule; vacuous at every block's last row) ----
        let mut init_s: [AB::Expr; 8] = core::array::from_fn(|i| cur[i].clone());
        ext_linear(&mut init_s);
        let mut full_s: [AB::Expr; 8] = core::array::from_fn(|i| pow7(cur[i].clone() + rc[i].clone()));
        ext_linear(&mut full_s);
        let mut part_s: [AB::Expr; 8] =
            core::array::from_fn(|i| if i == 0 { pow7(cur[0].clone() + rc[0].clone()) } else { cur[i].clone() });
        int_linear(&mut part_s);
        for i in 0..8 {
            let round = is_init.clone() * (nxt[i].clone() - init_s[i].clone())
                + is_full.clone() * (nxt[i].clone() - full_s[i].clone())
                + is_partial.clone() * (nxt[i].clone() - part_s[i].clone());
            builder.when_transition().assert_zero(round);
        }

        // ---- local-persistent columns: constant within a region, free at region AND tile boundaries ----
        // TILE EDIT: subtract `tile_last` so tile k's keys/rho do not bleed into tile k+1's first row.
        let not_last = one.clone() - p[P_REGION_LAST].clone() - tile_last.clone();
        for &c in &[NK, NK1, RHO, RHO1, VAL] {
            builder.when_transition().assert_zero(not_last.clone() * (nxt[c].clone() - cur[c].clone()));
        }
        // TILE EDIT: ASSET is per-TILE-persistent now (each tx its own hidden asset) — gate off at the
        // tile boundary so distinct tiles may carry distinct assets.
        builder
            .when_transition()
            .assert_zero((one.clone() - tile_last.clone()) * (nxt[ASSET].clone() - cur[ASSET].clone()));
        // pos_acc: += bit·2^d at membership links, else constant within the span (A1)
        let bit = nxt[BIT].clone();
        builder.when_transition().assert_zero(
            not_last.clone()
                * (nxt[POSACC].clone() - cur[POSACC].clone() - p[P_MEM_LINK].clone() * (bit.clone() * p[P_POS_COEFF].clone())),
        );
        builder.assert_zero(p[P_OWN_IN].clone() * cur[POSACC].clone());

        // ---- value accumulator: per-tile (P_ROW0/P_FINAL are tile-periodic; acc_delta=0 at boundary) ----
        builder.assert_zero(p[P_ROW0].clone() * cur[VALACC].clone());
        let acc_delta = (p[P_COMMIT_A_IN].clone() + p[P_MINT_IN].clone() - p[P_OUT_A_IN].clone() - p[P_FEE_IN].clone())
            * cur[VAL].clone();
        builder.when_transition().assert_zero(nxt[VALACC].clone() - cur[VALACC].clone() - acc_delta);
        builder.assert_zero(p[P_FINAL].clone() * cur[VALACC].clone());

        // ---- range (A3) ----
        builder.assert_zero(p[P_RANGE_SEED].clone() * (cur[REM].clone() - cur[VAL].clone()));
        let ra = p[P_RANGE_ACTIVE].clone();
        builder
            .when_transition()
            .assert_zero(ra.clone() * (cur[REM].clone() - (two.clone() * nxt[REM].clone() + cur[RBIT].clone())));
        builder.when_transition().assert_zero(ra.clone() * (cur[RBIT].clone() * (one.clone() - cur[RBIT].clone())));
        builder.assert_zero(p[P_RANGE_CLOSE].clone() * cur[REM].clone());

        // ---- ownership input ----
        let own = p[P_OWN_IN].clone();
        builder.assert_zero(own.clone() * (cur[0].clone() - dom_own.clone()));
        builder.assert_zero(own.clone() * (cur[1].clone() - cur[NK].clone()));
        builder.assert_zero(own.clone() * (cur[2].clone() - cur[NK1].clone()));
        for i in 4..8 {
            builder.assert_zero(own.clone() * cur[i].clone());
        }

        // ---- recipient link ----
        let rl = p[P_RECIP_LINK].clone();
        for k in 0..DIGEST {
            builder.when_transition().assert_zero(rl.clone() * (nxt[1 + k].clone() - cur[k].clone()));
        }

        // ---- commit_a input ----
        let ca = p[P_COMMIT_A_IN].clone();
        builder.assert_zero(ca.clone() * (cur[0].clone() - dom_cm.clone()));
        builder.assert_zero(ca.clone() * (cur[1 + DIGEST].clone() - cur[VAL].clone()));
        builder.assert_zero(ca.clone() * (cur[2 + DIGEST].clone() - cur[RHO].clone()));
        builder.assert_zero(ca.clone() * (cur[3 + DIGEST].clone() - cur[RHO1].clone()));

        // ---- chain link ----
        let cl = p[P_CHAIN_LINK].clone();
        for k in 0..DIGEST {
            builder.when_transition().assert_zero(cl.clone() * (nxt[k].clone() - cur[k].clone()));
        }

        // ---- commit_b input ----
        let cb = p[P_COMMIT_B].clone();
        builder.assert_zero(cb.clone() * (cur[DIGEST + 2].clone() - cur[ASSET].clone()));
        builder.assert_zero(cb.clone() * cur[DIGEST + 3].clone());

        // ---- membership links ----
        let ml = p[P_MEM_LINK].clone();
        for k in 0..DIGEST {
            let placed = (one.clone() - bit.clone()) * (nxt[k].clone() - cur[k].clone())
                + bit.clone() * (nxt[DIGEST + k].clone() - cur[k].clone());
            builder.when_transition().assert_zero(ml.clone() * placed);
        }
        builder.when_transition().assert_zero(ml.clone() * (bit.clone() * (one.clone() - bit.clone())));

        // ---- root: each tile folds to its OWN staged anchor (S_ANCHOR) ----
        let pr = p[P_ROOT].clone();
        for k in 0..DIGEST {
            builder.assert_zero(pr.clone() * (cur[k].clone() - cur[S_ANCHOR + k].clone()));
        }

        // ---- nullifier input ----
        let ni = p[P_NULL_IN].clone();
        builder.assert_zero(ni.clone() * (cur[0].clone() - dom_nf.clone()));
        builder.assert_zero(ni.clone() * (cur[1].clone() - cur[NK].clone()));
        builder.assert_zero(ni.clone() * (cur[2].clone() - cur[NK1].clone()));
        builder.assert_zero(ni.clone() * (cur[3].clone() - cur[RHO].clone()));
        builder.assert_zero(ni.clone() * (cur[4].clone() - cur[RHO1].clone()));
        builder.assert_zero(ni.clone() * (cur[5].clone() - cur[POSACC].clone()));
        for i in 6..8 {
            builder.assert_zero(ni.clone() * cur[i].clone());
        }
        for i in 0..N_IN {
            let sel = p[P_NULLOUT + i].clone();
            for k in 0..DIGEST {
                builder.assert_zero(sel.clone() * (cur[k].clone() - cur[S_NF + i * DIGEST + k].clone()));
            }
        }

        // ---- output commitment ----
        let oa = p[P_OUT_A_IN].clone();
        builder.assert_zero(oa.clone() * (cur[0].clone() - dom_cm.clone()));
        builder.assert_zero(oa.clone() * (cur[1 + DIGEST].clone() - cur[VAL].clone()));
        for j in 0..M_OUT {
            let sel = p[P_OUTOUT + j].clone();
            for k in 0..DIGEST {
                builder.assert_zero(sel.clone() * (cur[k].clone() - cur[S_OUTCM + j * DIGEST + k].clone()));
            }
        }

        // ---- fee / mint (bound to the staged values) ----
        builder.assert_zero(p[P_FEE_IN].clone() * (cur[VAL].clone() - cur[S_FEE].clone()));
        builder.assert_zero(p[P_MINT_IN].clone() * (cur[VAL].clone() - cur[S_MINT].clone()));

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
        for &c in &staged {
            builder.when_transition().assert_zero(tile_persist.clone() * (nxt[c].clone() - cur[c].clone()));
        }

        // ---- s_k MD-chain: block 0 = perm([DOM_TXROOT,0,0,0 ‖ anchor]); blocks 1.. absorb each chunk ----
        let dom_txroot = AB::Expr::from(Goldilocks::from_u64(DOM_TXROOT));
        // chunk injection: at fold block bi's input row, lanes 4..8 == the bi-th statement chunk.
        for bi in 0..FOLD_SK_BLOCKS {
            let sel = p[P_FOLD_IN + bi].clone();
            match chunk_stage(bi) {
                Some(base) => {
                    for k in 0..DIGEST {
                        builder.assert_zero(sel.clone() * (cur[DIGEST + k].clone() - cur[base + k].clone()));
                    }
                }
                None => {
                    // the [fee, mint, 0, 0] chunk
                    builder.assert_zero(sel.clone() * (cur[DIGEST].clone() - cur[S_FEE].clone()));
                    builder.assert_zero(sel.clone() * (cur[DIGEST + 1].clone() - cur[S_MINT].clone()));
                    builder.assert_zero(sel.clone() * cur[DIGEST + 2].clone());
                    builder.assert_zero(sel.clone() * cur[DIGEST + 3].clone());
                }
            }
        }
        // block 0 also pins the low lanes to [DOM_TXROOT, 0, 0, 0] (the chain start).
        let sk0 = p[P_FOLD_IN].clone();
        builder.assert_zero(sk0.clone() * (cur[0].clone() - dom_txroot.clone()));
        for k in 1..DIGEST {
            builder.assert_zero(sk0.clone() * cur[k].clone());
        }
        // s_k chain link: block bi output lanes 0..4 → block bi+1 input lanes 0..4.
        let sl = p[P_SK_LINK].clone();
        for k in 0..DIGEST {
            builder.when_transition().assert_zero(sl.clone() * (nxt[k].clone() - cur[k].clone()));
        }
        // last s_k block output (= s_k) → root block input lanes 4..8.
        let s2r = p[P_SK_TO_ROOT].clone();
        for k in 0..DIGEST {
            builder.when_transition().assert_zero(s2r.clone() * (nxt[DIGEST + k].clone() - cur[k].clone()));
        }

        // ---- root chain: root_k = perm([root_{k-1} ‖ s_k]); ROOT carries root across tiles ----
        // root block input lanes 0..4 == the running ROOT column (root_{k-1}).
        let ri = p[P_ROOT_IN].clone();
        for k in 0..DIGEST {
            builder.assert_zero(ri.clone() * (cur[k].clone() - cur[ROOT + k].clone()));
        }
        // IV: ROOT = 0 at the global first row.
        for k in 0..DIGEST {
            builder.when_first_row().assert_zero(cur[ROOT + k].clone());
        }
        // ROOT is constant except across the per-tile update transition (root block output row).
        let ru = p[P_ROOT_UPDATE].clone();
        for k in 0..DIGEST {
            builder
                .when_transition()
                .assert_zero((one.clone() - ru.clone()) * (nxt[ROOT + k].clone() - cur[ROOT + k].clone()));
            // at the update, ROOT becomes the root block's output (lanes 0..4 of root_out_row).
            builder.when_transition().assert_zero(ru.clone() * (nxt[ROOT + k].clone() - cur[k].clone()));
        }
        // The root block is the LAST block, so on the global last row cur[0..4] IS the final tile's root
        // block output (root_{n-1}) — the block tx-root. (The ROOT column's update lands on the *next*
        // row, which doesn't exist for the last tile, so bind the fold output directly.)
        for k in 0..DIGEST {
            builder.when_last_row().assert_zero(cur[k].clone() - pis[k].clone());
        }
    }
}

/// Write the Poseidon2 permutation of `input` into fold `block`'s state columns (cols 0..8), tile `toff`.
fn set_fold_block(t: &mut [Val], toff: usize, block: usize, input: [Val; 8]) {
    let rows = native_steps(input);
    for (r, row) in rows.iter().enumerate() {
        let base = (toff + block * BLOCK + r) * BATCH_WIDTH;
        t[base..base + 8].copy_from_slice(row);
    }
}

/// The 4-element statement chunk absorbed by s_k fold block `bi` (mirrors `chunk_stage` / the oracle's
/// `tx_statement_digest` order: anchor, nf_i, out_cm_j, [fee,mint,0,0], tx_binding).
fn chunk_vals(pv: &[Val], bi: usize) -> [Val; DIGEST] {
    if bi == 0 {
        pv[PI_ANCHOR..PI_ANCHOR + DIGEST].try_into().unwrap()
    } else if bi < 1 + N_IN {
        let i = bi - 1;
        pv[PI_NF + i * DIGEST..PI_NF + (i + 1) * DIGEST].try_into().unwrap()
    } else if bi < 1 + N_IN + M_OUT {
        let j = bi - 1 - N_IN;
        pv[PI_OUTCM + j * DIGEST..PI_OUTCM + (j + 1) * DIGEST].try_into().unwrap()
    } else if bi == 1 + N_IN + M_OUT {
        [pv[PI_FEE], pv[PI_MINT], Val::ZERO, Val::ZERO]
    } else {
        pv[PI_TXBIND..PI_TXBIND + DIGEST].try_into().unwrap()
    }
}

/// Tile `ws.len()` single-tile traces into one batch trace, fill each tile's staging columns, run the
/// in-circuit tx-root fold, and thread the running ROOT across tiles. Power-of-two count for now (dummy
/// tiles arrive in Phase 4). Each tile reuses the audited `joinsplit_air::build_trace`.
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
            t[b + S_ANCHOR..b + S_ANCHOR + DIGEST].copy_from_slice(&pv[PI_ANCHOR..PI_ANCHOR + DIGEST]);
            t[b + S_NF..b + S_NF + N_IN * DIGEST].copy_from_slice(&pv[PI_NF..PI_NF + N_IN * DIGEST]);
            t[b + S_OUTCM..b + S_OUTCM + M_OUT * DIGEST].copy_from_slice(&pv[PI_OUTCM..PI_OUTCM + M_OUT * DIGEST]);
            t[b + S_FEE] = pv[PI_FEE];
            t[b + S_MINT] = pv[PI_MINT];
            t[b + S_TXBIND..b + S_TXBIND + DIGEST].copy_from_slice(&pv[PI_TXBIND..PI_TXBIND + DIGEST]);
        }
        // 3. fold blocks (overwrite the trailing padding blocks): s_k MD-chain, then root chain.
        let mut inp = [Val::ZERO; 8];
        inp[0] = Val::from_u64(DOM_TXROOT);
        inp[DIGEST..].copy_from_slice(&chunk_vals(&pv, 0));
        set_fold_block(&mut t, toff, FOLD_BASE, inp);
        let mut c: [Val; DIGEST] = native_permute(inp)[..DIGEST].try_into().unwrap();
        for bi in 1..FOLD_SK_BLOCKS {
            let mut inp = [Val::ZERO; 8];
            inp[..DIGEST].copy_from_slice(&c);
            inp[DIGEST..].copy_from_slice(&chunk_vals(&pv, bi));
            set_fold_block(&mut t, toff, FOLD_BASE + bi, inp);
            c = native_permute(inp)[..DIGEST].try_into().unwrap();
        }
        // root block: perm([root_{k-1} ‖ s_k])
        let mut rinp = [Val::ZERO; 8];
        rinp[..DIGEST].copy_from_slice(&root);
        rinp[DIGEST..].copy_from_slice(&c);
        set_fold_block(&mut t, toff, ROOT_BLOCK, rinp);
        let new_root: [Val; DIGEST] = native_permute(rinp)[..DIGEST].try_into().unwrap();
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
    let pis = batch_root(ws);
    let proof = prove(&make_config(), &JoinSplitBatchAir, build_batch_trace(ws), &pis);
    postcard::to_allocvec(&proof).expect("proof serialization is infallible")
}

/// The largest batch (in tiles) that holds the ≥100-bit proven-soundness floor: measured 100 bits at
/// n=64 (height 2^18), 99 at n=128. A block needing more transactions emits **multiple** batch proofs of
/// ≤ `MAX_BATCH_TILES` tiles each (or a future config raises `num_queries`). See `batch_proven_security_floor`.
pub const MAX_BATCH_TILES: usize = 64;

/// Proven (UDR) security bits at a batch of `n` transactions (trace height = `padded_tiles(n)·TILE_HEIGHT`).
/// Mirrors `joinsplit_air::measure`'s computation; the batch grows the height ~log(n), slowly lowering the
/// proven floor. The largest size holding ≥100 bits is `MAX_BATCH_TILES`.
pub fn proven_security_bits(n: usize) -> usize {
    crate::config::proven_security_bits(&JoinSplitBatchAir, padded_tiles(n) * TILE_HEIGHT)
}

/// Verify a batch proof against the block tx-root (4 Goldilocks).
pub fn verify_batch_bytes(proof_bytes: &[u8], root: &[Val]) -> bool {
    if root.len() != DIGEST {
        return false;
    }
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), &JoinSplitBatchAir, &proof, root).is_ok()
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

    // ---- Phase 3: distinct tiles bound to the tx-root via staging + the in-circuit fold ----

    #[test]
    fn batch_n1_verifies_under_txroot() {
        let w = variant(1);
        let root = batch_root(std::slice::from_ref(&w));
        assert!(verify_batch_bytes(&prove_batch_to_bytes(std::slice::from_ref(&w)), &root));
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
        // KAT for the Zig node's txStatementDigest/batchRoot fold (poseidon2.zig). seq statement = 1..=26.
        let seq: Vec<Val> = (1..=NUM_PUBLIC_INPUTS as u64).map(Val::from_u64).collect();
        let s = tx_statement_digest(&seq);
        let d = dummy_sk();
        let p = |label: &str, x: &[Val; DIGEST]| {
            use p3_field::PrimeField64;
            println!("{label} = {:?}", x.iter().map(|f| f.as_canonical_u64()).collect::<Vec<_>>());
        };
        p("seq_statement_digest", &s);
        p("dummy_sk", &d);
    }

    #[test]
    fn batch_proven_security_floor() {
        // n=1 matches the single join-split (103 proven); the floor holds through MAX_BATCH_TILES and
        // 2·MAX_BATCH_TILES is the first size below 100 — pinning N_MAX as exactly the boundary.
        assert_eq!(proven_security_bits(1), 103);
        assert!(proven_security_bits(MAX_BATCH_TILES) >= 100, "MAX_BATCH_TILES must hold the ≥100-bit floor");
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
            assert_eq!(trace.values[(h - 1) * BATCH_WIDTH + k], root[k], "fold limb {k} != oracle root");
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
