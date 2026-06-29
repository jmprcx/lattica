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
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{FriParameters, HidingFriPcs};
use p3_goldilocks::{default_goldilocks_poseidon2_8, Goldilocks, Poseidon2Goldilocks};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeHidingMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{prove, verify, Proof, StarkConfig};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use crate::poseidon2_air::{ext_linear, int_linear, pow7};
use crate::joinsplit_air::{
    build_trace, merge, periodic, public_values, Witness, ASSET, BIT, DIGEST, DOM_CM, DOM_NF, DOM_OWN,
    HEIGHT, M_OUT, N_IN, N_PERIODIC, N_PUBLIC, NK, NK1, NUM_PUBLIC_INPUTS, PI_ANCHOR, PI_FEE, PI_MINT,
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

/// The statement digest of a dummy (padding) tile = the digest of the all-zero statement. A real tx has
/// a non-zero anchor and nullifiers, so a real `s_k` can never collide with this.
pub fn dummy_sk() -> [Val; DIGEST] {
    tx_statement_digest(&[Val::ZERO; NUM_PUBLIC_INPUTS])
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
const P_TILE_LAST: usize = N_PERIODIC; // appended after joinsplit's N_PERIODIC columns
const BATCH_N_PERIODIC: usize = N_PERIODIC + 1;

// FRI / ZK config — identical to joinsplit_air's (same production parameters). Copied (not imported) to
// avoid exposing joinsplit_air's private config types; the trace height is runtime, so one config + one
// AIR proves/verifies every batch size.
type Perm = Poseidon2Goldilocks<8>;
type MyHash = PaddingFreeSponge<Perm, 8, 4, 4>;
type MyCompress = TruncatedPermutation<Perm, 2, 4, 8>;
type ValMmcs =
    MerkleTreeHidingMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, ChaCha20Rng, 2, 4, 4>;
type Challenge = BinomialExtensionField<Val, 2>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Challenger = DuplexChallenger<Val, Perm, 8, 4>;
type Dft = Radix2DitParallel<Val>;
type Pcs = HidingFriPcs<Val, Dft, ValMmcs, ChallengeMmcs, ChaCha20Rng>;
type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;

fn make_config() -> MyConfig {
    let perm = default_goldilocks_poseidon2_8();
    let val_mmcs = ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), 6, ChaCha20Rng::from_rng(&mut rand::rng()));
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let fri = FriParameters {
        log_blowup: 4,
        log_final_poly_len: 0,
        max_log_arity: 4,
        num_queries: 96,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 16,
        mmcs: challenge_mmcs,
    };
    let pcs = Pcs::new(Dft::default(), val_mmcs, fri, 4, ChaCha20Rng::from_rng(&mut rand::rng()));
    MyConfig::new(pcs, Challenger::new(perm))
}

/// The tile-periodic columns: joinsplit's `periodic()` (each length `HEIGHT` ⇒ repeated per tile by
/// Plonky3) plus `P_TILE_LAST` = a one-hot at the tile's last row (also repeated per tile).
fn batch_periodic() -> Vec<Vec<Val>> {
    let mut cols = periodic();
    let mut tile_last = vec![Val::ZERO; TILE_HEIGHT];
    tile_last[TILE_HEIGHT - 1] = Val::ONE;
    cols.push(tile_last);
    cols
}

pub struct JoinSplitBatchAir;

impl BaseAir<Goldilocks> for JoinSplitBatchAir {
    fn width(&self) -> usize {
        WIDTH
    }
    fn num_public_values(&self) -> usize {
        N_PUBLIC // PHASE 2: global pis (identical tiles). Phase 3 changes this to the tx-root (DIGEST).
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

        // ---- root: each tile folds to the public anchor (PHASE 2: global pis ⇒ identical tiles) ----
        let pr = p[P_ROOT].clone();
        for k in 0..DIGEST {
            builder.assert_zero(pr.clone() * (cur[k].clone() - pis[PI_ANCHOR + k].clone()));
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
                builder.assert_zero(sel.clone() * (cur[k].clone() - pis[PI_NF + i * DIGEST + k].clone()));
            }
        }

        // ---- output commitment ----
        let oa = p[P_OUT_A_IN].clone();
        builder.assert_zero(oa.clone() * (cur[0].clone() - dom_cm.clone()));
        builder.assert_zero(oa.clone() * (cur[1 + DIGEST].clone() - cur[VAL].clone()));
        for j in 0..M_OUT {
            let sel = p[P_OUTOUT + j].clone();
            for k in 0..DIGEST {
                builder.assert_zero(sel.clone() * (cur[k].clone() - pis[PI_OUTCM + j * DIGEST + k].clone()));
            }
        }

        // ---- fee / mint ----
        builder.assert_zero(p[P_FEE_IN].clone() * (cur[VAL].clone() - pis[PI_FEE].clone()));
        builder.assert_zero(p[P_MINT_IN].clone() * (cur[VAL].clone() - pis[PI_MINT].clone()));
    }
}

/// Tile `ws.len()` single-tile traces into one batch trace. PHASE 2 requires a power-of-two count (no
/// dummy tiles yet — those arrive with the fold in Phase 3). Each tile reuses the audited
/// `joinsplit_air::build_trace`.
pub fn build_batch_trace(ws: &[Witness]) -> RowMajorMatrix<Val> {
    let n = padded_tiles(ws.len());
    assert_eq!(ws.len(), n, "PHASE 2 batch requires a power-of-two tx count (dummy tiles arrive in Phase 3)");
    let mut t = vec![Val::ZERO; n * HEIGHT * WIDTH];
    for (tile, w) in ws.iter().enumerate() {
        let single = build_trace(w);
        let off = tile * HEIGHT * WIDTH;
        t[off..off + HEIGHT * WIDTH].copy_from_slice(&single.values);
    }
    RowMajorMatrix::new(t, WIDTH)
}

/// Prove a batch (PHASE 2: identical tiles; the public inputs are the shared per-tile statement).
pub fn prove_batch_to_bytes(ws: &[Witness], pis: &[Val]) -> Vec<u8> {
    let proof = prove(&make_config(), &JoinSplitBatchAir, build_batch_trace(ws), pis);
    postcard::to_allocvec(&proof).expect("proof serialization is infallible")
}

/// Verify a batch proof against the public inputs.
pub fn verify_batch_bytes(proof_bytes: &[u8], pis: &[Val]) -> bool {
    if pis.len() != N_PUBLIC {
        return false;
    }
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), &JoinSplitBatchAir, &proof, pis).is_ok()
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

    // ---- Phase 2: tiling + self-containment (identical tiles, global pis; real prover) ----

    #[test]
    fn batch_n1_verifies_like_a_single_spend() {
        let w = demo_witness();
        let pis = public_values(&w);
        assert!(verify_batch_bytes(&prove_batch_to_bytes(std::slice::from_ref(&w), &pis), &pis));
    }

    #[test]
    fn batch_two_identical_tiles_verify() {
        let w = demo_witness();
        let pis = public_values(&w);
        let ws = [w.clone(), w];
        assert!(verify_batch_bytes(&prove_batch_to_bytes(&ws, &pis), &pis));
    }

    #[test]
    fn batch_rejects_wrong_public_inputs() {
        let w = demo_witness();
        let proof = prove_batch_to_bytes(&[w.clone(), w.clone()], &public_values(&w));
        let mut bad = public_values(&w);
        bad[PI_ANCHOR] += Val::ONE;
        assert!(!verify_batch_bytes(&proof, &bad));
    }

    #[test]
    #[ignore = "slow: proves a 4-tile batch"]
    fn batch_four_tiles_verify() {
        let w = demo_witness();
        let pis = public_values(&w);
        let ws: Vec<Witness> = (0..4).map(|_| w.clone()).collect();
        assert!(verify_batch_bytes(&prove_batch_to_bytes(&ws, &pis), &pis));
    }
}
