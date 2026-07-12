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

/// **W2-assemble.2 step 3 — the wrap AIR** (`--features recursion`). `WrapAir` reuses the whole monolith
/// constraint system via `MonolithAir::eval_bci`, but supplies `WrapBci` for the B/C/I regions: the OOD
/// epilogue's `c_k` are evaluated by the WITNESSED symbolic-circuit walker (each `Mul` bound to a degree-1
/// column), so the fold degree is capped at ≈ `FOLD_CHUNK+1` INDEPENDENT of the inner's constraint degree —
/// the fix for the self-recursion explosion (inline `c_k` = inner maxdeg → `log_nqc 7` verifying a monolith).
/// The cap-mux (I) delegates to `InlineBci` (degree `cap_height`, already ≤ budget — not the degree crux).
#[cfg(feature = "recursion")]
mod wrap_air {
    use super::Val;
    use crate::recursion::monolith::{arith_point, bind_reduced_opening, InlineBci, MonolithAir, MonolithBci};
    use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
    use p3_field::{Field, PrimeCharacteristicRing, TwoAdicField};
    use p3_goldilocks::Goldilocks;
    use p3_uni_stark::{SymbolicExpr, SymbolicExpression};
    use std::collections::{HashMap, HashSet};
    use std::sync::Arc;

    /// Count the unique `Mul` nodes across a constraint (memoized by `Arc` identity via `seen`) — the number
    /// of witnessed F_p² intermediate columns the wrap allocates. Add/Sub/Neg don't raise degree.
    pub(crate) fn count_mul(e: &SymbolicExpression<Val>, seen: &mut HashSet<usize>) -> usize {
        match e {
            SymbolicExpr::Leaf(_) => 0,
            SymbolicExpr::Neg { x, .. } => count_mul_arc(x, seen),
            SymbolicExpr::Add { x, y, .. } | SymbolicExpr::Sub { x, y, .. } => {
                count_mul_arc(x, seen) + count_mul_arc(y, seen)
            }
            SymbolicExpr::Mul { x, y, .. } => 1 + count_mul_arc(x, seen) + count_mul_arc(y, seen),
        }
    }
    fn count_mul_arc(arc: &Arc<SymbolicExpression<Val>>, seen: &mut HashSet<usize>) -> usize {
        if !seen.insert(Arc::as_ptr(arc) as usize) {
            return 0;
        }
        count_mul(arc, seen)
    }

    /// The WITNESSED symbolic-circuit walker (C's degree fix on the real DAGs): mirrors `eval_symbolic_circuit`
    /// but at each `Mul` witnesses the F_p² product into a degree-1 column pair (`cur[mul_base + 2·i]`), bound
    /// by a degree-2 constraint, so every node's value is degree 1. Shared sub-expressions (by `Arc` identity)
    /// reuse their column. The column count MUST equal `count_mul` (the width `WrapAir` allocated).
    struct Witnesser<'a, AB: AirBuilder<F = Goldilocks>> {
        local: &'a [(AB::Expr, AB::Expr)],
        next: &'a [(AB::Expr, AB::Expr)],
        pubs: &'a [(AB::Expr, AB::Expr)],
        periodic: &'a [(AB::Expr, AB::Expr)],
        is_first: &'a (AB::Expr, AB::Expr),
        is_last: &'a (AB::Expr, AB::Expr),
        is_trans: &'a (AB::Expr, AB::Expr),
        w: &'a AB::Expr,
        cur: &'a [AB::Expr],
        tf: &'a AB::Expr,
        mul_base: usize,
        counter: usize,
        memo: HashMap<usize, (AB::Expr, AB::Expr)>,
    }

    impl<'a, AB: AirBuilder<F = Goldilocks>> Witnesser<'a, AB> {
        fn emul(&self, a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)) -> (AB::Expr, AB::Expr) {
            (
                a.0.clone() * b.0.clone() + self.w.clone() * a.1.clone() * b.1.clone(),
                a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
            )
        }
        fn walk_arc(&mut self, builder: &mut AB, arc: &Arc<SymbolicExpression<Val>>) -> (AB::Expr, AB::Expr) {
            let key = Arc::as_ptr(arc) as usize;
            if let Some(v) = self.memo.get(&key) {
                return v.clone();
            }
            let v = self.walk(builder, arc.as_ref());
            self.memo.insert(key, v.clone());
            v
        }
        fn walk(&mut self, builder: &mut AB, e: &SymbolicExpression<Val>) -> (AB::Expr, AB::Expr) {
            use p3_uni_stark::{BaseEntry, BaseLeaf};
            match e {
                SymbolicExpr::Leaf(leaf) => match leaf {
                    BaseLeaf::Variable(v) => match v.entry {
                        BaseEntry::Main { offset } => {
                            if offset == 0 {
                                self.local[v.index].clone()
                            } else {
                                self.next[v.index].clone()
                            }
                        }
                        BaseEntry::Public => self.pubs[v.index].clone(),
                        BaseEntry::Periodic => self.periodic[v.index].clone(),
                        BaseEntry::Preprocessed { .. } => panic!("preprocessed columns unsupported"),
                    },
                    BaseLeaf::IsFirstRow => self.is_first.clone(),
                    BaseLeaf::IsLastRow => self.is_last.clone(),
                    BaseLeaf::IsTransition => self.is_trans.clone(),
                    BaseLeaf::Constant(c) => (AB::Expr::from(*c), AB::Expr::ZERO),
                },
                SymbolicExpr::Add { x, y, .. } => {
                    let a = self.walk_arc(builder, x);
                    let b = self.walk_arc(builder, y);
                    (a.0 + b.0, a.1 + b.1)
                }
                SymbolicExpr::Sub { x, y, .. } => {
                    let a = self.walk_arc(builder, x);
                    let b = self.walk_arc(builder, y);
                    (a.0 - b.0, a.1 - b.1)
                }
                SymbolicExpr::Neg { x, .. } => {
                    let a = self.walk_arc(builder, x);
                    (AB::Expr::ZERO - a.0, AB::Expr::ZERO - a.1)
                }
                SymbolicExpr::Mul { x, y, .. } => {
                    let a = self.walk_arc(builder, x);
                    let b = self.walk_arc(builder, y);
                    let prod = self.emul(a, b); // degree 2 (a, b are degree-1)
                    let col = self.mul_base + 2 * self.counter;
                    self.counter += 1;
                    let (wl, wh) = (self.cur[col].clone(), self.cur[col + 1].clone());
                    builder.assert_zero(self.tf.clone() * (wl.clone() - prod.0)); // bind: t == a·b
                    builder.assert_zero(self.tf.clone() * (wh.clone() - prod.1));
                    (wl, wh) // c value = the degree-1 witnessed column
                }
            }
        }
    }

    /// The wrap's B/C/I strategy: `emit_epilogue` witnesses `c_k` (degree 1) then folds (the degree fix);
    /// `emit_capmux` delegates to `InlineBci` (not the degree crux).
    pub(crate) struct WrapBci {
        /// The offset where the witnessed `c_k` intermediate columns begin (= `MonolithAir::fused_w()`).
        pub mul_base: usize,
    }

    impl<AB: AirBuilder<F = Goldilocks>> MonolithBci<AB> for WrapBci {
        // The wrap witnesses only the epilogue `c_k` (B/C); the arith tile stays inline (unchanged).
        fn emit_arith(&self, builder: &mut AB, air: &MonolithAir, cur: &[AB::Expr], tf: &AB::Expr, one: &AB::Expr, w: &AB::Expr) {
            InlineBci.emit_arith(builder, air, cur, tf, one, w);
        }

        fn emit_capmux(
            &self,
            builder: &mut AB,
            air: &MonolithAir,
            cur: &[AB::Expr],
            pis: &[AB::Expr],
            one: &AB::Expr,
            tf: &AB::Expr,
            openings: &[(usize, usize, usize, usize)],
        ) {
            InlineBci.emit_capmux(builder, air, cur, pis, one, tf, openings);
        }

        #[allow(clippy::too_many_arguments)]
        fn emit_epilogue(
            &self,
            builder: &mut AB,
            air: &MonolithAir,
            cur: &[AB::Expr],
            tf: &AB::Expr,
            w: &AB::Expr,
            local: &[(AB::Expr, AB::Expr)],
            next: &[(AB::Expr, AB::Expr)],
            pubs: &[(AB::Expr, AB::Expr)],
            periodic: &[(AB::Expr, AB::Expr)],
            is_first: &(AB::Expr, AB::Expr),
            is_last: &(AB::Expr, AB::Expr),
            is_trans: &(AB::Expr, AB::Expr),
            alpha_stark: &(AB::Expr, AB::Expr),
            inv_van: &(AB::Expr, AB::Expr),
            quot: &(AB::Expr, AB::Expr),
        ) {
            let mut wit = Witnesser::<AB> {
                local, next, pubs, periodic, is_first, is_last, is_trans, w, cur, tf,
                mul_base: self.mul_base,
                counter: 0,
                memo: HashMap::new(),
            };
            let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
                (
                    a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(),
                    a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
                )
            };
            let chunked = air.column_window;
            let mut folded = (AB::Expr::ZERO, AB::Expr::ZERO);
            let mut acc_i = 0usize;
            let n_c = air.constraints.len();
            for (k, c) in air.constraints.iter().enumerate() {
                let ci = wit.walk(builder, c); // WITNESSED c_k (degree 1) — the fix
                let fa = emul(folded.clone(), alpha_stark.clone());
                folded = (fa.0 + ci.0, fa.1 + ci.1);
                if chunked && (k + 1) % MonolithAir::FOLD_CHUNK == 0 && k + 1 < n_c {
                    let fac = air.fold_acc(acc_i);
                    let a = (cur[fac].clone(), cur[fac + 1].clone());
                    builder.assert_zero(tf.clone() * (a.0.clone() - folded.0.clone()));
                    builder.assert_zero(tf.clone() * (a.1.clone() - folded.1.clone()));
                    folded = a;
                    acc_i += 1;
                }
            }
            let chk = emul(folded, inv_van.clone());
            builder.assert_zero(tf.clone() * (chk.0 - quot.0.clone()));
            builder.assert_zero(tf.clone() * (chk.1 - quot.1.clone()));
        }
    }

    /// The wrap AIR: the whole monolith constraint system (`eval_bci`) with the B/C/I strategy swapped to
    /// `WrapBci` — the witnessed epilogue caps the fold degree independent of the inner. Trace width =
    /// the monolith's `fused_w` + `2·n_mul` witnessed `c_k` columns.
    pub(crate) struct WrapAir {
        pub(crate) m: MonolithAir,
        pub(crate) n_mul: usize,
    }

    impl WrapAir {
        pub(crate) fn new(m: MonolithAir) -> Self {
            let mut seen = HashSet::new();
            let n_mul: usize = m.constraints.iter().map(|c| count_mul(c, &mut seen)).sum();
            Self { m, n_mul }
        }
    }

    impl BaseAir<Goldilocks> for WrapAir {
        fn width(&self) -> usize {
            self.m.fused_w() + 2 * self.n_mul
        }
        fn num_public_values(&self) -> usize {
            BaseAir::<Goldilocks>::num_public_values(&self.m)
        }
        fn num_periodic_columns(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m)
        }
        fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
            BaseAir::<Goldilocks>::periodic_columns(&self.m)
        }
    }

    impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for WrapAir {
        fn eval(&self, builder: &mut AB) {
            self.m.eval_bci(builder, &WrapBci { mul_base: self.m.fused_w() });
        }
    }

    /// **Brick 5 — the op-table-based epilogue strategy.** Unlike `WrapBci` (which WITNESSES each `c_k` in a
    /// column pair — the 2·n_mul width cost), `OpTableBci` emits NO epilogue columns: the `c_k` evaluation +
    /// α-fold live in the FLATTEN op-table (separate slack rows, `crate::wrap::OpTableF2Air`), and the epilogue
    /// just READS the op-table's `folded` result from a dedicated column (bound to the op-table by the wiring
    /// bus, emitted in the outer AIR) and checks `folded·inv_van == quot(ζ)`. So the epilogue costs O(1) columns
    /// (a 2-felt `folded`) instead of 2·n_mul. Cap-mux delegates to `InlineBci` (as `WrapBci`).
    pub(crate) struct OpTableBci {
        /// The column holding the op-table's `folded` result (F_p² pair at `folded_col`, `folded_col + 1`).
        pub folded_col: usize,
    }

    impl<AB: AirBuilder<F = Goldilocks>> MonolithBci<AB> for OpTableBci {
        // The op-table witnesses only the epilogue `c_k` (B/C); the arith tile stays inline (unchanged).
        fn emit_arith(&self, builder: &mut AB, air: &MonolithAir, cur: &[AB::Expr], tf: &AB::Expr, one: &AB::Expr, w: &AB::Expr) {
            InlineBci.emit_arith(builder, air, cur, tf, one, w);
        }

        fn emit_capmux(
            &self,
            builder: &mut AB,
            air: &MonolithAir,
            cur: &[AB::Expr],
            pis: &[AB::Expr],
            one: &AB::Expr,
            tf: &AB::Expr,
            openings: &[(usize, usize, usize, usize)],
        ) {
            InlineBci.emit_capmux(builder, air, cur, pis, one, tf, openings);
        }

        #[allow(clippy::too_many_arguments)]
        fn emit_epilogue(
            &self,
            builder: &mut AB,
            _air: &MonolithAir,
            cur: &[AB::Expr],
            tf: &AB::Expr,
            w: &AB::Expr,
            _local: &[(AB::Expr, AB::Expr)],
            _next: &[(AB::Expr, AB::Expr)],
            _pubs: &[(AB::Expr, AB::Expr)],
            _periodic: &[(AB::Expr, AB::Expr)],
            _is_first: &(AB::Expr, AB::Expr),
            _is_last: &(AB::Expr, AB::Expr),
            _is_trans: &(AB::Expr, AB::Expr),
            _alpha_stark: &(AB::Expr, AB::Expr),
            inv_van: &(AB::Expr, AB::Expr),
            quot: &(AB::Expr, AB::Expr),
        ) {
            let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
                (
                    a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(),
                    a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
                )
            };
            // The op-table (separate rows) computes `folded`; read it from `folded_col` (bound to the op-table's
            // result by the wiring bus in the outer AIR) and check the epilogue identity — NO `c_k` witnessing,
            // so the epilogue costs O(1) columns.
            let folded = (cur[self.folded_col].clone(), cur[self.folded_col + 1].clone());
            let chk = emul(folded, inv_van.clone());
            builder.assert_zero(tf.clone() * (chk.0 - quot.0.clone()));
            builder.assert_zero(tf.clone() * (chk.1 - quot.1.clone()));
        }
    }

    /// **Brick 5 — the assembled wrap AIR (skeleton, increment 1).** Reuses the ENTIRE monolith constraint
    /// system via `eval_bci` with `OpTableBci`: the reused A–J regions are byte-identical, and the epilogue
    /// reads the op-table's `folded` (O(1) columns) instead of witnessing 2·n_mul `c_k`. This skeleton
    /// establishes the strategy plumbing + measures the epilogue-side width contraction (`fused_w + 2` vs
    /// `WrapAir`'s `fused_w + 2·n_mul`); the op-table REGION (the slack rows computing `folded`) + the wiring
    /// bus (binding `folded_col` + the openings→leaves seam) are the next increments.
    pub(crate) struct AssembledWrapAir {
        pub(crate) m: MonolithAir,
        /// The op-table wiring-bus address holding the `folded` output (set from the op-table build; the arith
        /// head reads `folded_col` from the bus at this address). Any value for pure composition/degree checks.
        pub(crate) folded_addr: u64,
    }

    /// 2c seam binding — wiring-bus base for the committed-opening region (above any op-table wire address).
    pub(crate) const OPEN_BASE: u64 = 1 << 24;

    /// 2c degree fix — the openings' provides are SPLIT across `N_GROUPS` lookup channels (each ≤ ~16 terms ⇒
    /// degree ≤ budget), instead of one ~120-term channel (which was log_nqc 6). An opening's channel is
    /// `open_index % N_GROUPS`; its leaf carries a one-hot `is_ch` selector routing its read to that channel.
    pub(crate) const N_GROUPS: usize = 8;

    /// The canonical `open_id` for an opening, from its `opening_key` `(tag, index)` (tag: 0/1 = Main{0/1} =
    /// local/next, 2 = Public, 3 = Periodic, 4/5/6 = is_first/last/trans, 7 = qwt quotient-recompose weight `i`)
    /// + the inner geometry. Used by BOTH the arith-head provides (AIR) and the op-table opening-leaf seed (trace),
    /// so they address the same opening. (Tag 7 = qwt is distinct from `op_table_f2_trace`'s `opening_key` tag-7 =
    /// Constant: constants are pinned by the epilogue identity, never bus-bound, so they never reach `open_id`.)
    pub(crate) fn open_id(key: (u8, u64), w: u64, np: u64, nper: u64) -> u64 {
        OPEN_BASE
            + match key.0 {
                0 => key.1,
                1 => w + key.1,
                2 => 2 * w + key.1,
                3 => 2 * w + np + key.1,
                4 => 2 * w + np + nper,
                5 => 2 * w + np + nper + 1,
                6 => 2 * w + np + nper + 2,
                7 => 2 * w + np + nper + 3 + key.1, // qwt quotient-recompose weight i (brick 5d.3)
                _ => unreachable!("opening tag in 0..=7"),
            }
    }

    impl AssembledWrapAir {
        /// The `folded` F_p² pair the epilogue reads — appended right after the monolith's fused columns.
        pub(crate) fn folded_col(&self) -> usize {
            self.m.fused_w()
        }
        /// The op-table region's column base (after `folded`): the 13 `OpTableF2Air` columns + `op_sel`.
        pub(crate) fn op_base(&self) -> usize {
            self.m.fused_w() + 2
        }
        pub(crate) fn op_sel(&self) -> usize {
            self.op_base() + 13
        }
        /// Witnessed arith-head marker (= the `tf` periodic selector, bound by a constraint). The `folded` bus
        /// READ is gated by this COLUMN, not by `tf` directly — the lookup prover's aux generation resolves
        /// interaction multiplicities with an empty periodic slice, so periodic must stay out of interactions.
        pub(crate) fn is_head(&self) -> usize {
            self.op_base() + 14
        }
        /// 2c seam binding: `open_id` = the opening-leaf's committed-opening bus address; `is_leaf` = 1 on
        /// opening-leaf rows. The leaf READS its opening at `open_id` and the arith head PROVIDES it from the
        /// monolith's committed `pz`/`sel`/`pis` columns — binding the op-table's trace-opening leaves to the
        /// committed openings (closing the soundness gap).
        pub(crate) fn open_id_col(&self) -> usize {
            self.op_base() + 15
        }
        pub(crate) fn is_leaf_col(&self) -> usize {
            self.op_base() + 16
        }
        /// One-hot channel selector `g` (0..N_GROUPS) — routes an opening-leaf's read to the lookup channel its
        /// opening's provide is on (so the ~120 provides split across N_GROUPS ≤~16-term lookups, keeping degree
        /// within budget).
        pub(crate) fn is_ch_col(&self, g: usize) -> usize {
            self.op_base() + 17 + g
        }
    }

    impl BaseAir<Goldilocks> for AssembledWrapAir {
        fn width(&self) -> usize {
            // folded(2) + op-table(13) + op_sel(1) + is_head(1) + open_id(1) + is_leaf(1) + is_ch(N_GROUPS) — O(1).
            self.m.fused_w() + 2 + 17 + N_GROUPS
        }
        fn num_public_values(&self) -> usize {
            BaseAir::<Goldilocks>::num_public_values(&self.m)
        }
        fn num_periodic_columns(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m)
        }
        fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
            BaseAir::<Goldilocks>::periodic_columns(&self.m)
        }
    }

    impl<AB: AirBuilder<F = Goldilocks> + p3_lookup::InteractionBuilder> Air<AB> for AssembledWrapAir {
        fn eval(&self, builder: &mut AB) {
            // (1) The reused monolith regions + the OpTableBci epilogue (reads `folded_col`, checks vs quot).
            self.m.eval_bci(builder, &OpTableBci { folded_col: self.folded_col() });

            // (2) The op-table REGION — the FLATTEN op-table (`crate::wrap::OpTableF2Air`) inlined and gated by
            // `op_sel`, so it computes the `c_k` + α-fold on the trace's SLACK rows without disturbing the
            // monolith tiles. Reads collected once (borrow released before asserting).
            let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
            let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
            let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
            let ob = self.op_base();
            let (is_mul, is_add, is_sub) = (cur[ob].clone(), cur[ob + 1].clone(), cur[ob + 2].clone());
            let (out_addr, o0, o1) = (cur[ob + 3].clone(), cur[ob + 4].clone(), cur[ob + 5].clone());
            let (a_addr, a0, a1) = (cur[ob + 6].clone(), cur[ob + 7].clone(), cur[ob + 8].clone());
            let (b_addr, b0, b1) = (cur[ob + 9].clone(), cur[ob + 10].clone(), cur[ob + 11].clone());
            let out_mult = cur[ob + 12].clone();
            let op_sel = cur[self.op_sel()].clone();
            let one = AB::Expr::ONE;
            let we = AB::Expr::from(Goldilocks::from_u64(7)); // F_p² : X² = 7

            builder.assert_zero(op_sel.clone() * (op_sel.clone() - one.clone())); // op_sel boolean
            for s in [&is_mul, &is_add, &is_sub] {
                builder.assert_zero(op_sel.clone() * s.clone() * (s.clone() - one.clone()));
            }
            let is_op = is_mul.clone() + is_add.clone() + is_sub.clone();
            builder.assert_zero(op_sel.clone() * is_op.clone() * (is_op.clone() - one.clone()));
            builder.assert_zero(op_sel.clone() * is_mul.clone() * (o0.clone() - (a0.clone() * b0.clone() + we.clone() * a1.clone() * b1.clone())));
            builder.assert_zero(op_sel.clone() * is_mul.clone() * (o1.clone() - (a0.clone() * b1.clone() + a1.clone() * b0.clone())));
            builder.assert_zero(op_sel.clone() * is_add.clone() * (o0.clone() - (a0.clone() + b0.clone())));
            builder.assert_zero(op_sel.clone() * is_add.clone() * (o1.clone() - (a1.clone() + b1.clone())));
            builder.assert_zero(op_sel.clone() * is_sub.clone() * (o0.clone() - (a0.clone() - b0.clone())));
            builder.assert_zero(op_sel.clone() * is_sub.clone() * (o1.clone() - (a1.clone() - b1.clone())));

            // Bind the witnessed arith-head marker `is_head` to the periodic `tf` (a CONSTRAINT, where periodic
            // is available) — so the `folded` bus read below can be gated by the COLUMN `is_head` instead of the
            // periodic `tf` (the lookup prover's aux generation feeds interactions an empty periodic slice).
            let tf = p[self.m.m_tf()].clone();
            let is_head = cur[self.is_head()].clone();
            builder.assert_zero(is_head.clone() - tf);
            // is_leaf boolean + one-hot `is_ch` (each boolean, Σ == is_leaf) — routes each opening-leaf's read to
            // its opening's lookup channel. `is_ch_g ⟹ is_leaf`, so the leaf-read mult `is_ch_g·n_heads` is deg 1.
            let is_leaf = cur[self.is_leaf_col()].clone();
            builder.assert_zero(is_leaf.clone() * (is_leaf.clone() - one.clone()));
            let is_ch: Vec<AB::Expr> = (0..N_GROUPS).map(|g| cur[self.is_ch_col(g)].clone()).collect();
            let mut ch_sum: AB::Expr = AB::Expr::ZERO;
            for c in &is_ch {
                builder.assert_zero(c.clone() * (c.clone() - one.clone()));
                ch_sum = ch_sum + c.clone();
            }
            builder.assert_zero(ch_sum - is_leaf);

            // (3) The wiring bus, SPLIT across channels to keep each lookup's degree within budget. Channel 0 =
            // op-table wiring (reads +op_sel·is_op, define op_sel·out_mult) + the `folded` read (+is_head).
            // Channels 1..=N_GROUPS = the **2c opening binding** groups: each opening is PROVIDED (from the
            // committed pz/pis/sel, mult −is_head) on channel `open_index % N_GROUPS + 1`, and its leaf READS it
            // there (mult is_ch·n_heads). Balance ⇒ every opening-leaf value == the committed column — BOUND.
            let read_mult = op_sel.clone() * is_op;
            let folded = (cur[self.folded_col()].clone(), cur[self.folded_col() + 1].clone());
            let n_heads = AB::Expr::from(Goldilocks::from_u64(self.m.n_queries as u64));
            let neg_head = AB::Expr::ZERO - is_head.clone();
            let (w_in, np, nper) = (self.m.w_inner() as u64, self.m.n_pub() as u64, self.m.n_periodic() as u64);
            let oid = |x: u64| AB::Expr::from(Goldilocks::from_u64(x));
            let mut chans: Vec<Vec<(Vec<AB::Expr>, AB::Expr)>> = vec![Vec::new(); N_GROUPS + 1];
            chans[0].push((vec![a_addr, a0, a1], read_mult.clone()));
            chans[0].push((vec![b_addr, b0, b1], read_mult));
            chans[0].push((vec![out_addr, o0.clone(), o1.clone()], op_sel * out_mult));
            chans[0].push((vec![AB::Expr::from(Goldilocks::from_u64(self.folded_addr)), folded.0, folded.1], is_head));
            let (open_id_v, lo0, lo1) = (cur[self.open_id_col()].clone(), o0, o1);
            for g in 0..N_GROUPS {
                chans[g + 1].push((vec![open_id_v.clone(), lo0.clone(), lo1.clone()], is_ch[g].clone() * n_heads.clone()));
            }
            // Collect every opening's provide `(open_index, value)`, then route to channel `idx % N_GROUPS + 1`.
            let mut prov: Vec<(u64, AB::Expr, AB::Expr)> = Vec::new();
            for c in 0..self.m.w_inner() {
                let (pl, pn) = (self.m.pz(self.m.trm_trace(c)), self.m.pz(self.m.trm_next(c)));
                prov.push((open_id((0, c as u64), w_in, np, nper) - OPEN_BASE, cur[pl].clone(), cur[pl + 1].clone()));
                prov.push((open_id((1, c as u64), w_in, np, nper) - OPEN_BASE, cur[pn].clone(), cur[pn + 1].clone()));
            }
            for i in 0..self.m.n_pub() {
                prov.push((open_id((2, i as u64), w_in, np, nper) - OPEN_BASE, pis[self.m.pub_pi() + i].clone(), AB::Expr::ZERO));
            }
            for i in 0..self.m.n_periodic() {
                let (pb0, pb1) = (self.m.periodic_base() + 2 * i, self.m.periodic_base() + 2 * i + 1);
                prov.push((open_id((3, i as u64), w_in, np, nper) - OPEN_BASE, pis[pb0].clone(), pis[pb1].clone()));
            }
            let (s0, s2) = (self.m.sel(0), self.m.sel(2));
            prov.push((open_id((4, 0), w_in, np, nper) - OPEN_BASE, cur[s0].clone(), cur[s0 + 1].clone()));
            prov.push((open_id((5, 0), w_in, np, nper) - OPEN_BASE, cur[s2].clone(), cur[s2 + 1].clone()));
            let g_inv = AB::Expr::from(Goldilocks::two_adic_generator(self.m.cm_rounds() - self.m.is_zk).inverse());
            prov.push((open_id((6, 0), w_in, np, nper) - OPEN_BASE, pis[2].clone() - g_inv, pis[3].clone()));
            for (idx, v0, v1) in prov {
                chans[(idx as usize % N_GROUPS) + 1].push((vec![oid(OPEN_BASE + idx), v0, v1], neg_head.clone()));
            }
            for ch in chans {
                builder.push_local_interaction(ch);
            }
        }
    }

    /// Native mirror of `Witnesser` (IDENTICAL Arc-memoized DFS order): compute each `Mul` node's F_p² product
    /// from the native OOD openings, so the witnessed `c_k` columns can be filled to satisfy the wrap's
    /// degree-2 binding constraints. Returns the products in the wrap's column-allocation order (`out[i]` →
    /// columns `fused_w + 2·i`).
    pub(crate) fn native_witnessed(
        constraints: &[SymbolicExpression<Val>],
        local: &[crate::config::Challenge],
        next: &[crate::config::Challenge],
        pubs: &[crate::config::Challenge],
        periodic: &[crate::config::Challenge],
        is_first: crate::config::Challenge,
        is_last: crate::config::Challenge,
        is_trans: crate::config::Challenge,
    ) -> Vec<crate::config::Challenge> {
        use crate::config::Challenge;
        struct Ctx<'a> {
            local: &'a [Challenge],
            next: &'a [Challenge],
            pubs: &'a [Challenge],
            periodic: &'a [Challenge],
            is_first: Challenge,
            is_last: Challenge,
            is_trans: Challenge,
            out: Vec<Challenge>,
            memo: HashMap<usize, Challenge>,
        }
        fn walk_arc(arc: &Arc<SymbolicExpression<Val>>, ctx: &mut Ctx) -> Challenge {
            let key = Arc::as_ptr(arc) as usize;
            if let Some(v) = ctx.memo.get(&key) {
                return *v;
            }
            let v = walk(arc.as_ref(), ctx);
            ctx.memo.insert(key, v);
            v
        }
        fn walk(e: &SymbolicExpression<Val>, ctx: &mut Ctx) -> Challenge {
            use p3_uni_stark::{BaseEntry, BaseLeaf};
            match e {
                SymbolicExpr::Leaf(leaf) => match leaf {
                    BaseLeaf::Variable(v) => match v.entry {
                        BaseEntry::Main { offset } => {
                            if offset == 0 {
                                ctx.local[v.index]
                            } else {
                                ctx.next[v.index]
                            }
                        }
                        BaseEntry::Public => ctx.pubs[v.index],
                        BaseEntry::Periodic => ctx.periodic[v.index],
                        BaseEntry::Preprocessed { .. } => panic!("preprocessed columns unsupported"),
                    },
                    BaseLeaf::IsFirstRow => ctx.is_first,
                    BaseLeaf::IsLastRow => ctx.is_last,
                    BaseLeaf::IsTransition => ctx.is_trans,
                    BaseLeaf::Constant(c) => Challenge::from(*c),
                },
                SymbolicExpr::Add { x, y, .. } => walk_arc(x, ctx) + walk_arc(y, ctx),
                SymbolicExpr::Sub { x, y, .. } => walk_arc(x, ctx) - walk_arc(y, ctx),
                SymbolicExpr::Neg { x, .. } => -walk_arc(x, ctx),
                SymbolicExpr::Mul { x, y, .. } => {
                    let a = walk_arc(x, ctx);
                    let b = walk_arc(y, ctx);
                    let p = a * b;
                    ctx.out.push(p); // record in column-allocation order (matches Witnesser's counter)
                    p
                }
            }
        }
        let mut ctx = Ctx {
            local, next, pubs, periodic, is_first, is_last, is_trans,
            out: Vec::new(),
            memo: HashMap::new(),
        };
        for c in constraints {
            let _ = walk(c, &mut ctx); // side effect: pushes each Mul's product in column order
        }
        ctx.out
    }

    /// **Arith-tile assembly (plumbing) — the narrow-tall arith strategy.** Unlike `InlineBci`, whose
    /// `emit_arith` folds the reduced opening in `9·n_terms` COLUMNS (apow/z/pz/px/inv per term — the dominant
    /// inner-scaling width), `DeepFoldBci` keeps the cheap point derivation (`arith_point` — index→x + α_fri
    /// bind, SOUND) but WITNESSES the fold result `ro` from a dedicated column (`ro_col`), binding `QT_E == ro`
    /// (`bind_reduced_opening`). So the arith tile costs O(1) columns; `ro`'s soundness is discharged by the
    /// narrow-tall `DeepFoldAir` region in trace slack (proven faithful on real openings, `cd51eae`) — the
    /// size-fixed-point analog of `OpTableBci` for the epilogue. Cap-mux + epilogue delegate to `InlineBci`.
    pub(crate) struct DeepFoldBci {
        /// The column holding the witnessed reduced opening `ro` (F_p² pair at `ro_col`, `ro_col + 1`).
        pub(crate) ro_col: usize,
    }

    impl<AB: AirBuilder<F = Goldilocks>> MonolithBci<AB> for DeepFoldBci {
        fn emit_arith(&self, builder: &mut AB, air: &MonolithAir, cur: &[AB::Expr], tf: &AB::Expr, one: &AB::Expr, _w: &AB::Expr) {
            // The point stays inline + SOUND (index→x, α_fri bind); only the reduced-opening FOLD is externalized.
            let _ = arith_point(builder, air, cur, tf, one);
            let ro = (cur[self.ro_col].clone(), cur[self.ro_col + 1].clone());
            bind_reduced_opening(builder, cur, tf, ro);
        }

        fn emit_capmux(
            &self,
            builder: &mut AB,
            air: &MonolithAir,
            cur: &[AB::Expr],
            pis: &[AB::Expr],
            one: &AB::Expr,
            tf: &AB::Expr,
            openings: &[(usize, usize, usize, usize)],
        ) {
            InlineBci.emit_capmux(builder, air, cur, pis, one, tf, openings);
        }

        #[allow(clippy::too_many_arguments)]
        fn emit_epilogue(
            &self,
            builder: &mut AB,
            air: &MonolithAir,
            cur: &[AB::Expr],
            tf: &AB::Expr,
            w: &AB::Expr,
            local: &[(AB::Expr, AB::Expr)],
            next: &[(AB::Expr, AB::Expr)],
            pubs: &[(AB::Expr, AB::Expr)],
            periodic: &[(AB::Expr, AB::Expr)],
            is_first: &(AB::Expr, AB::Expr),
            is_last: &(AB::Expr, AB::Expr),
            is_trans: &(AB::Expr, AB::Expr),
            alpha_stark: &(AB::Expr, AB::Expr),
            inv_van: &(AB::Expr, AB::Expr),
            quot: &(AB::Expr, AB::Expr),
        ) {
            InlineBci.emit_epilogue(
                builder, air, cur, tf, w, local, next, pubs, periodic, is_first, is_last, is_trans, alpha_stark,
                inv_van, quot,
            );
        }
    }

    /// The arith-tile wrap AIR: the whole monolith (`eval_bci`) with the arith strategy swapped to `DeepFoldBci`
    /// — the reduced-opening fold externalized to a witnessed `ro` column (at `fused_w`), everything else inline.
    /// Width = `fused_w + 2` (the plumbing step; the narrow-tall `DeepFoldAir` region in slack + the `9·n_terms`
    /// column removal — the actual width win — follow).
    pub(crate) struct ArithWrapAir {
        pub(crate) m: MonolithAir,
    }

    impl BaseAir<Goldilocks> for ArithWrapAir {
        fn width(&self) -> usize {
            self.m.fused_w() + 2
        }
        fn num_public_values(&self) -> usize {
            BaseAir::<Goldilocks>::num_public_values(&self.m)
        }
        fn num_periodic_columns(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m)
        }
        fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
            BaseAir::<Goldilocks>::periodic_columns(&self.m)
        }
    }

    impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for ArithWrapAir {
        fn eval(&self, builder: &mut AB) {
            self.m.eval_bci(builder, &DeepFoldBci { ro_col: self.m.fused_w() });
        }
    }

    /// **Caps assembly (plumbing) — the narrow-tall cap strategy.** The `emit_capmux` analog of [`DeepFoldBci`]:
    /// where [`InlineBci::emit_capmux`] binds each cap carrier `cap_c` to the index-selected committed cap entry
    /// via a degree-`cap_height` product-mux over ALL `2^cap_height` entries (`cap_c[k] = Σ_e (Π_j sel_bit_j(e))·
    /// pis[cbase+e·4+k]` — whose `2^cap_height·4` cap COLUMNS are 85% of the `column_window` fused_w), `CapMuxBci`
    /// EXTERNALIZES it: `emit_capmux` emits NOTHING. `cap_c` already exists as a carrier column and STAYS bound to
    /// the Merkle terminal (`terminal == cap_c`, emitted in `eval_bci`) + held across the super-tile; the missing
    /// binding — `cap_c` == the COMMITTED cap `cap[index>>shift]` — is discharged by a narrow-tall cap-row region
    /// in slack + the wiring bus (the AA-arc, next), exactly as `DeepFoldAir` discharges `ro`. A free binding here
    /// (provable — `cap_c` is bound to the computed Merkle root — but UNSOUND w.r.t. the committed cap until
    /// bus-bound). Arith + epilogue delegate to `InlineBci`. (Plumbing at `column_window=false`, mirroring
    /// `ArithWrapAir`; the `2^cap_height·4` cap-COLUMN removal — the width win — is `column_window`-only, later.)
    pub(crate) struct CapMuxBci;

    impl<AB: AirBuilder<F = Goldilocks>> MonolithBci<AB> for CapMuxBci {
        fn emit_arith(&self, builder: &mut AB, air: &MonolithAir, cur: &[AB::Expr], tf: &AB::Expr, one: &AB::Expr, w: &AB::Expr) {
            InlineBci.emit_arith(builder, air, cur, tf, one, w);
        }

        fn emit_capmux(
            &self,
            _builder: &mut AB,
            _air: &MonolithAir,
            _cur: &[AB::Expr],
            _pis: &[AB::Expr],
            _one: &AB::Expr,
            _tf: &AB::Expr,
            _openings: &[(usize, usize, usize, usize)],
        ) {
            // EXTERNALIZED: no product-mux. `cap_c` is bound to the Merkle terminal (+ held) by `eval_bci`; the
            // narrow-tall cap-row region + bus (next brick) re-bind it to the committed cap `cap[index>>shift]`.
        }

        #[allow(clippy::too_many_arguments)]
        fn emit_epilogue(
            &self,
            builder: &mut AB,
            air: &MonolithAir,
            cur: &[AB::Expr],
            tf: &AB::Expr,
            w: &AB::Expr,
            local: &[(AB::Expr, AB::Expr)],
            next: &[(AB::Expr, AB::Expr)],
            pubs: &[(AB::Expr, AB::Expr)],
            periodic: &[(AB::Expr, AB::Expr)],
            is_first: &(AB::Expr, AB::Expr),
            is_last: &(AB::Expr, AB::Expr),
            is_trans: &(AB::Expr, AB::Expr),
            alpha_stark: &(AB::Expr, AB::Expr),
            inv_van: &(AB::Expr, AB::Expr),
            quot: &(AB::Expr, AB::Expr),
        ) {
            InlineBci.emit_epilogue(
                builder, air, cur, tf, w, local, next, pubs, periodic, is_first, is_last, is_trans, alpha_stark,
                inv_van, quot,
            );
        }
    }

    /// The caps wrap AIR: the whole monolith (`eval_bci`) with the cap-mux strategy swapped to [`CapMuxBci`] — the
    /// `2^cap_height`-entry product-mux externalized, everything else inline. Width = `fused_w` (UNCHANGED: `cap_c`
    /// is a pre-existing carrier, unlike `ArithWrapAir`'s `+2` for the witnessed `ro`). The plumbing step; the
    /// narrow-tall cap-row region in slack + the bus binding + the `column_window` cap-column removal (the width
    /// win) follow — the [`AssembledArithWrapAir`]/AA arc for caps.
    pub(crate) struct CapWrapAir {
        pub(crate) m: MonolithAir,
    }

    impl BaseAir<Goldilocks> for CapWrapAir {
        fn width(&self) -> usize {
            self.m.fused_w()
        }
        fn num_public_values(&self) -> usize {
            BaseAir::<Goldilocks>::num_public_values(&self.m)
        }
        fn num_periodic_columns(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m)
        }
        fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
            BaseAir::<Goldilocks>::periodic_columns(&self.m)
        }
    }

    impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for CapWrapAir {
        fn eval(&self, builder: &mut AB) {
            self.m.eval_bci(builder, &CapMuxBci);
        }
    }

    /// **AA6 — the narrow-openings strategy (DeepFold arith ⊕ OpTable epilogue).** When `narrow_openings` drops the
    /// `2·n_terms` `pz` opening columns, BOTH the arith fold AND the epilogue must externalize their openings —
    /// neither [`DeepFoldBci`] (arith only) nor [`OpTableBci`] (epilogue only) suffices, so this combines them.
    /// `emit_arith` witnesses the reduced-opening fold `ro` from `ro_col` (the point derivation `arith_point` stays
    /// inline + SOUND — reads only the DEEP index bits/α, no `pz`), exactly like [`DeepFoldBci`]. `emit_epilogue`
    /// reads the op-table's `folded` from `folded_col` AND the recomposed `quot` from `quot_col` (the shared
    /// `eval_bci` passes EMPTY local/next + a zero quot when `narrow_openings`, so this strategy is self-contained),
    /// checking `folded·inv_van == quot(ζ)`. `emit_capmux` delegates to [`InlineBci`] (cw=false — caps in `pis`).
    /// The three F_p² columns are FREE witnesses here (the plumbing/compose step, mirroring [`ArithWrapAir`]/
    /// [`CapWrapAir`]); binding `ro`/`folded`/`quot` to the FS-absorbed openings via the sponge-opening bus + the
    /// DeepFold/op-table slack regions is the assembled increment (the [`AssembledCapWrapCwAir`] analog).
    pub(crate) struct OpeningsBci {
        pub(crate) ro_col: usize,
        pub(crate) folded_col: usize,
        pub(crate) quot_col: usize,
    }

    impl<AB: AirBuilder<F = Goldilocks>> MonolithBci<AB> for OpeningsBci {
        fn emit_arith(&self, builder: &mut AB, air: &MonolithAir, cur: &[AB::Expr], tf: &AB::Expr, one: &AB::Expr, _w: &AB::Expr) {
            // Point stays inline + SOUND (index→x, α_fri bind); the reduced-opening FOLD is externalized to `ro_col`.
            let _ = arith_point(builder, air, cur, tf, one);
            let ro = (cur[self.ro_col].clone(), cur[self.ro_col + 1].clone());
            bind_reduced_opening(builder, cur, tf, ro);
        }

        fn emit_capmux(
            &self,
            builder: &mut AB,
            air: &MonolithAir,
            cur: &[AB::Expr],
            pis: &[AB::Expr],
            one: &AB::Expr,
            tf: &AB::Expr,
            openings: &[(usize, usize, usize, usize)],
        ) {
            InlineBci.emit_capmux(builder, air, cur, pis, one, tf, openings);
        }

        #[allow(clippy::too_many_arguments)]
        fn emit_epilogue(
            &self,
            builder: &mut AB,
            _air: &MonolithAir,
            cur: &[AB::Expr],
            tf: &AB::Expr,
            w: &AB::Expr,
            _local: &[(AB::Expr, AB::Expr)],
            _next: &[(AB::Expr, AB::Expr)],
            _pubs: &[(AB::Expr, AB::Expr)],
            _periodic: &[(AB::Expr, AB::Expr)],
            _is_first: &(AB::Expr, AB::Expr),
            _is_last: &(AB::Expr, AB::Expr),
            _is_trans: &(AB::Expr, AB::Expr),
            _alpha_stark: &(AB::Expr, AB::Expr),
            inv_van: &(AB::Expr, AB::Expr),
            _quot: &(AB::Expr, AB::Expr),
        ) {
            let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
                (
                    a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(),
                    a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
                )
            };
            // NARROW-OPENINGS: `folded` (the op-table's α-fold result) + `quot` (recomposed from the chunk-openings)
            // are both bus-bound columns here (the shared eval_bci passed empty/zero openings). Check the epilogue
            // identity `folded·inv_van == quot`. Both columns are FREE witnesses until the sponge-opening bus binds them.
            let folded = (cur[self.folded_col].clone(), cur[self.folded_col + 1].clone());
            let quot = (cur[self.quot_col].clone(), cur[self.quot_col + 1].clone());
            let chk = emul(folded, inv_van.clone());
            builder.assert_zero(tf.clone() * (chk.0 - quot.0));
            builder.assert_zero(tf.clone() * (chk.1 - quot.1));
        }
    }

    /// **Tier-1 width merge — the combined caps ⊕ openings externalization strategy.** The two narrow-tall arcs
    /// externalize DISJOINT parts of the monolith through DISJOINT `MonolithBci` methods: [`CapMuxBci`] the cap-mux
    /// (`emit_capmux` → nothing; `cap_c` re-bound via the SELECT/SPONGE-CAP buses), [`OpeningsBci`] the arith fold +
    /// epilogue (`emit_arith` → `ro_col`, `emit_epilogue` → `folded_col`/`quot_col`). So a monolith with BOTH
    /// `narrow_caps` AND `narrow_openings` needs a strategy that routes `emit_capmux` to `CapMuxBci` and
    /// `emit_arith`/`emit_epilogue` to `OpeningsBci` — a clean delegation (the methods touch disjoint columns/pis).
    /// This is the Bci for the fully-narrowed wrap (`fused_w` 3849 → ~585, the 6.6× width lever); the assembled
    /// merge wires all region buses (caps SELECT+SPONGE-CAP ⊕ openings ro/z-px/pz/sponge ⊕ ov leaf-hash) in one AIR.
    pub(crate) struct CapOpeningsBci {
        pub(crate) ro_col: usize,
        pub(crate) folded_col: usize,
        pub(crate) quot_col: usize,
    }

    impl<AB: AirBuilder<F = Goldilocks>> MonolithBci<AB> for CapOpeningsBci {
        fn emit_arith(&self, builder: &mut AB, air: &MonolithAir, cur: &[AB::Expr], tf: &AB::Expr, one: &AB::Expr, w: &AB::Expr) {
            // openings: the reduced-opening fold `ro` externalized to `ro_col` (point stays inline + sound).
            OpeningsBci { ro_col: self.ro_col, folded_col: self.folded_col, quot_col: self.quot_col }
                .emit_arith(builder, air, cur, tf, one, w);
        }

        fn emit_capmux(
            &self,
            builder: &mut AB,
            air: &MonolithAir,
            cur: &[AB::Expr],
            pis: &[AB::Expr],
            one: &AB::Expr,
            tf: &AB::Expr,
            openings: &[(usize, usize, usize, usize)],
        ) {
            // caps: the product-mux externalized (emit nothing) — `cap_c` re-bound by the SELECT/SPONGE-CAP buses.
            CapMuxBci.emit_capmux(builder, air, cur, pis, one, tf, openings);
        }

        #[allow(clippy::too_many_arguments)]
        fn emit_epilogue(
            &self,
            builder: &mut AB,
            air: &MonolithAir,
            cur: &[AB::Expr],
            tf: &AB::Expr,
            w: &AB::Expr,
            local: &[(AB::Expr, AB::Expr)],
            next: &[(AB::Expr, AB::Expr)],
            pubs: &[(AB::Expr, AB::Expr)],
            periodic: &[(AB::Expr, AB::Expr)],
            is_first: &(AB::Expr, AB::Expr),
            is_last: &(AB::Expr, AB::Expr),
            is_trans: &(AB::Expr, AB::Expr),
            alpha_stark: &(AB::Expr, AB::Expr),
            inv_van: &(AB::Expr, AB::Expr),
            quot: &(AB::Expr, AB::Expr),
        ) {
            // openings: `folded·inv_van == quot` over the bus-bound `folded_col`/`quot_col`.
            OpeningsBci { ro_col: self.ro_col, folded_col: self.folded_col, quot_col: self.quot_col }.emit_epilogue(
                builder, air, cur, tf, w, local, next, pubs, periodic, is_first, is_last, is_trans, alpha_stark,
                inv_van, quot,
            );
        }
    }

    /// **Tier-1 width merge — the bare fully-narrowed verifier (plumbing/compose).** The whole monolith (`eval_bci`)
    /// with ALL FOUR narrow flags (`narrow_arith` + `narrow_caps` + `narrow_openings` + `narrow_ov`) and the combined
    /// [`CapOpeningsBci`] — the cap-mux, the arith fold's `ro`, and the epilogue's `folded`/`quot` all externalized.
    /// Width = `fused_w + 6` at the FULLY-narrowed `fused_w` (the 6.6× win). The `ro`/`folded`/`quot` columns are
    /// FREE witnesses here (provable but UNSOUND until the assembled buses bind them + the caps/openings/ov regions),
    /// exactly like [`CapWrapAir`]/[`NarrowOpeningsWrapAir`] one arc shallower. This brick de-risks the DEGREE: does
    /// the caps externalization coexist with the openings externalization at `log_nqc ≤ 4` in ONE verifier?
    pub(crate) struct CapNarrowWrapAir {
        pub(crate) m: MonolithAir,
    }

    impl CapNarrowWrapAir {
        pub(crate) fn ro_col(&self) -> usize {
            self.m.fused_w()
        }
        pub(crate) fn folded_col(&self) -> usize {
            self.m.fused_w() + 2
        }
        pub(crate) fn quot_col(&self) -> usize {
            self.m.fused_w() + 4
        }
    }

    impl BaseAir<Goldilocks> for CapNarrowWrapAir {
        fn width(&self) -> usize {
            self.m.fused_w() + 6
        }
        fn num_public_values(&self) -> usize {
            BaseAir::<Goldilocks>::num_public_values(&self.m)
        }
        fn num_periodic_columns(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m)
        }
        fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
            BaseAir::<Goldilocks>::periodic_columns(&self.m)
        }
    }

    impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for CapNarrowWrapAir {
        fn eval(&self, builder: &mut AB) {
            self.m.eval_bci(
                builder,
                &CapOpeningsBci { ro_col: self.ro_col(), folded_col: self.folded_col(), quot_col: self.quot_col() },
            );
        }
    }

    /// The narrow-openings wrap AIR (plumbing/compose): the whole monolith (`eval_bci`) with [`OpeningsBci`] — the
    /// arith fold's `ro`, the epilogue's `folded`, and the recomposed `quot` each witnessed in an O(1) slack column
    /// pair (the `2·n_terms` `pz` opening columns GONE, `arith_stride` 0). Width = `fused_w + 6`. The columns are
    /// FREE witnesses (provable but UNSOUND until the sponge-opening bus binds them to the FS-absorbed openings +
    /// the DeepFold/op-table regions — the assembled increment). Mirrors [`ArithWrapAir`]/[`CapWrapAir`].
    pub(crate) struct NarrowOpeningsWrapAir {
        pub(crate) m: MonolithAir,
    }

    impl NarrowOpeningsWrapAir {
        pub(crate) fn ro_col(&self) -> usize {
            self.m.fused_w()
        }
        pub(crate) fn folded_col(&self) -> usize {
            self.m.fused_w() + 2
        }
        pub(crate) fn quot_col(&self) -> usize {
            self.m.fused_w() + 4
        }
    }

    impl BaseAir<Goldilocks> for NarrowOpeningsWrapAir {
        fn width(&self) -> usize {
            self.m.fused_w() + 6
        }
        fn num_public_values(&self) -> usize {
            BaseAir::<Goldilocks>::num_public_values(&self.m)
        }
        fn num_periodic_columns(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m)
        }
        fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
            BaseAir::<Goldilocks>::periodic_columns(&self.m)
        }
    }

    impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for NarrowOpeningsWrapAir {
        fn eval(&self, builder: &mut AB) {
            self.m.eval_bci(
                builder,
                &OpeningsBci { ro_col: self.ro_col(), folded_col: self.folded_col(), quot_col: self.quot_col() },
            );
        }
    }

    /// **Arith-tile assembly — the sound narrow-tall reduced-opening fold** (the [`AssembledWrapAir`] analog one
    /// region deeper). Where [`ArithWrapAir`] externalizes the DEEP fold's `ro` to a FREE witness column
    /// (provable but UNSOUND — a prover can put any `ro`), this AIR discharges `ro`'s soundness through the
    /// LogUp bus. Each query's fold is a narrow-tall [`crate::wrap::DeepFoldAir`] region placed in the trace
    /// SLACK (18 cols overlaid at `df_base`, gated by `df_sel`), carrying `α^k` (`apow`) + the running sum `ro`
    /// down the rows at constant width; the region's LAST row PROVIDES `[x, ro]` on a wiring bus addressed by
    /// the query point `x` (distinct per query), and each arith head READS `[x_head, ro_col]` — so the `ro` the
    /// head binds `QT_E` to is a fold actually computed in slack, not a free witness. The point derivation
    /// (`arith_point`) stays inline + SOUND and `bind_reduced_opening` checks `QT_E == ro_col`.
    ///
    /// **Increment AA1 (this): composes.** The region + the `ro` bus (1 channel, 2 interactions ⇒ low degree —
    /// unlike the op-table's ~120-provide channels the query-input binding will need). AA1 leaves the region's
    /// `z`/`pz`/`px` INPUTS unbound to the committed openings (that 2c-style split-channel binding is AA3); here
    /// `ro` is bound to the slack fold, closing the free-witness gap for the mechanism + fixing the degree.
    pub(crate) struct AssembledArithWrapAir {
        pub(crate) m: MonolithAir,
    }

    impl AssembledArithWrapAir {
        /// The witnessed reduced opening `ro` (F_p² pair) the arith head binds `QT_E` to — appended after the
        /// monolith's fused columns (the slot `DeepFoldBci`/`ArithWrapAir` use).
        pub(crate) fn ro_col(&self) -> usize {
            self.m.fused_w()
        }
        /// The DeepFold region's column base (18 `DeepFoldAir` cols: `[α, x, apow, z, pz, px, inv, t, ro]`).
        pub(crate) fn df_base(&self) -> usize {
            self.m.fused_w() + 2
        }
        /// Region row selector (1 on every DeepFold slack row).
        pub(crate) fn df_sel(&self) -> usize {
            self.df_base() + 18
        }
        /// Region FIRST-row marker (the fold's boundary: `apow = 1`, `ro = t`).
        pub(crate) fn df_first(&self) -> usize {
            self.df_base() + 19
        }
        /// Region LAST-row marker (carries the full `ro`; the bus PROVIDE fires here).
        pub(crate) fn df_end(&self) -> usize {
            self.df_base() + 20
        }
        /// Witnessed arith-head marker (= the periodic `tf` selector, bound by a constraint) — gates the `ro`
        /// bus READ. Periodic must stay out of interactions (the lookup prover's aux gen feeds an empty periodic
        /// slice), so the read is gated by this COLUMN, not `tf` directly.
        pub(crate) fn is_head(&self) -> usize {
            self.df_base() + 21
        }
        /// **AA3** — the region row's term index `k` (a constrained counter: 0 at `df_first`, +1 down `df_trans`).
        /// With the query point `x`, `(x, term_idx)` is the address that ties each region row to its committed
        /// term — the per-query discriminator the op-table's query-independent ζ-opening binding did not need.
        pub(crate) fn term_idx(&self) -> usize {
            self.df_base() + 22
        }
        /// **AA3** — one-hot channel selector `g` for the input-binding read: routes the region row's `(z, pz, px)`
        /// read to the lookup channel its committed term's provide is on (`k % N_GROUPS`). Booleanity + `Σ == df_sel`
        /// pin exactly one channel per region row; the bus balance forces it to be the correct one.
        pub(crate) fn is_ch(&self, g: usize) -> usize {
            self.df_base() + 23 + g
        }
    }

    impl BaseAir<Goldilocks> for AssembledArithWrapAir {
        fn width(&self) -> usize {
            // ro(2) + DeepFoldAir region(18) + df_sel/df_first/df_end/is_head(4) + term_idx(1) + is_ch(N_GROUPS).
            self.m.fused_w() + 2 + 18 + 4 + 1 + N_GROUPS
        }
        fn num_public_values(&self) -> usize {
            BaseAir::<Goldilocks>::num_public_values(&self.m)
        }
        fn num_periodic_columns(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m)
        }
        fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
            BaseAir::<Goldilocks>::periodic_columns(&self.m)
        }
    }

    impl<AB: AirBuilder<F = Goldilocks> + p3_lookup::InteractionBuilder> Air<AB> for AssembledArithWrapAir {
        fn eval(&self, builder: &mut AB) {
            // (1) The reused monolith regions + the `DeepFoldBci` arith strategy: `arith_point` stays inline +
            // SOUND, the reduced-opening fold reads `ro_col` (bound to the slack region below), and
            // `bind_reduced_opening` checks `QT_E == ro_col`. Epilogue + cap-mux delegate to `InlineBci`.
            self.m.eval_bci(builder, &DeepFoldBci { ro_col: self.ro_col() });

            let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
            let nxt: Vec<AB::Expr> = builder.main().next_slice().iter().map(|&x| x.into()).collect();
            let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
            let one = AB::Expr::ONE;
            let we = AB::Expr::from(Goldilocks::from_u64(7)); // F_p² : X² = 7
            let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
                (
                    a.0.clone() * b.0.clone() + we.clone() * a.1.clone() * b.1.clone(),
                    a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
                )
            };
            let db = self.df_base();
            let gg = |r: &[AB::Expr], o: usize| (r[db + o].clone(), r[db + o + 1].clone());

            // (2) Region markers — booleans; `is_head` bound to the periodic `tf` (so the bus READ is gated by
            // the COLUMN, not the periodic). A transition stays WITHIN a region: every region row that is not its
            // last (`df_sel · (1 − df_end)`), so the fold never carries across a region boundary.
            let df_sel = cur[self.df_sel()].clone();
            let df_first = cur[self.df_first()].clone();
            let df_end = cur[self.df_end()].clone();
            let is_head = cur[self.is_head()].clone();
            for m in [&df_sel, &df_first, &df_end, &is_head] {
                builder.assert_zero(m.clone() * (m.clone() - one.clone()));
            }
            builder.assert_zero(is_head.clone() - p[self.m.m_tf()].clone());
            let df_trans = df_sel.clone() * (one.clone() - df_end.clone());

            // (3) The DeepFold region (mirrors `crate::wrap::DeepFoldAir`, gated to the slack rows): each term is
            // a ROW carrying `apow = α^k` + the running sum `ro`, at constant width — the narrow-tall arith tile.
            let (alpha, x) = (gg(&cur, 0), gg(&cur, 2));
            let (apow, z, pz, px, inv, t, ro) = (
                gg(&cur, 4), gg(&cur, 6), gg(&cur, 8), gg(&cur, 10), gg(&cur, 12), gg(&cur, 14), gg(&cur, 16),
            );
            // α, x constant across the fold.
            for i in 0..4 {
                builder.when_transition().assert_zero(df_trans.clone() * (nxt[db + i].clone() - cur[db + i].clone()));
            }
            // apow = α^k (running product), boundary α^0 = 1.
            builder.assert_zero(df_first.clone() * (apow.0.clone() - one.clone()));
            builder.assert_zero(df_first.clone() * apow.1.clone());
            let ap = emul(apow.clone(), alpha);
            builder.when_transition().assert_zero(df_trans.clone() * (gg(&nxt, 4).0 - ap.0));
            builder.when_transition().assert_zero(df_trans.clone() * (gg(&nxt, 4).1 - ap.1));
            // inv = 1/(z − x): inv·(z − x) == 1.
            let chk = emul(inv.clone(), (z.0.clone() - x.0.clone(), z.1.clone() - x.1.clone()));
            builder.assert_zero(df_sel.clone() * (chk.0 - one.clone()));
            builder.assert_zero(df_sel.clone() * chk.1);
            // t = apow · (pz − px) · inv (the term's DEEP contribution).
            let tv = emul(emul(apow, (pz.0.clone() - px.0.clone(), pz.1.clone() - px.1.clone())), inv);
            builder.assert_zero(df_sel.clone() * (t.0.clone() - tv.0));
            builder.assert_zero(df_sel.clone() * (t.1.clone() - tv.1));
            // ro = running sum of t; boundary ro_0 = t_0; transition ro' = ro + t'.
            builder.assert_zero(df_first.clone() * (ro.0.clone() - t.0.clone()));
            builder.assert_zero(df_first.clone() * (ro.1.clone() - t.1.clone()));
            builder.when_transition().assert_zero(df_trans.clone() * (gg(&nxt, 16).0 - (ro.0.clone() + gg(&nxt, 14).0)));
            builder.when_transition().assert_zero(df_trans.clone() * (gg(&nxt, 16).1 - (ro.1.clone() + gg(&nxt, 14).1)));

            // (4) The wiring bus — `N_GROUPS + 1` channels. **Channel 0 = the `ro` bus** (AA1), addressed by the
            // query point `x`: the region's LAST row (`df_end`) PROVIDES `[x, ro]` (mult −1) and each arith head
            // READS `[x_head, ro_col]` (mult +is_head), where `x_head = GEN·qt_acc[lg−1]` is the head's committed
            // query point (imaginary 0). Balance ⇒ `ro_col` at head q == the slack region's fold `ro`.
            //
            // **Channels 1..=N_GROUPS = the AA3 input binding** (the soundness close): each region row's committed
            // inputs `(z, pz, px)` are bound to the arith head's committed columns, so the fold is over the REAL
            // openings — `ro` can no longer be a fold of forged inputs. The head PROVIDES each committed term `k`
            // (address `(x_head, k)`, value `(z(k), pz(k), px(k))`, mult −is_head) on channel `k % N_GROUPS`; the
            // region row READS its bundle (address `(x, term_idx)`, mult +is_ch) on its one-hot channel. Balance
            // forces BOTH the value binding (region `(z,pz,px)` == committed) AND the routing. The per-query `x`
            // in the address is what the op-table's query-independent ζ-opening 2c binding did not need. Bundling
            // `(z,pz,px)` into ONE interaction/term keeps each channel to ~`n_terms/N_GROUPS` provides ⇒ low degree.
            let x_head =
                AB::Expr::from(<Goldilocks as Field>::GENERATOR) * cur[self.m.qt_acc() + self.m.lg() - 1].clone();
            let ro_read = (cur[self.ro_col()].clone(), cur[self.ro_col() + 1].clone());
            let term_idx = cur[self.term_idx()].clone();
            let is_ch: Vec<AB::Expr> = (0..N_GROUPS).map(|g| cur[self.is_ch(g)].clone()).collect();

            // term_idx counter (the per-row discriminator): 0 at df_first, +1 down df_trans.
            builder.assert_zero(df_first.clone() * term_idx.clone());
            builder
                .when_transition()
                .assert_zero(df_trans.clone() * (nxt[self.term_idx()].clone() - term_idx.clone() - one.clone()));
            // is_ch one-hot: boolean + exactly one channel per region row (Σ == df_sel).
            let mut ch_sum = AB::Expr::ZERO;
            for c in &is_ch {
                builder.assert_zero(c.clone() * (c.clone() - one.clone()));
                ch_sum = ch_sum + c.clone();
            }
            builder.assert_zero(ch_sum - df_sel.clone());

            let mut chans: Vec<Vec<(Vec<AB::Expr>, AB::Expr)>> = vec![Vec::new(); N_GROUPS + 1];
            // Channel 0 — the ro bus: region-end PROVIDE [x, ro] (−df_end); head READ [x_head, ro_col] (+is_head).
            chans[0].push((vec![x.0.clone(), x.1.clone(), ro.0.clone(), ro.1.clone()], AB::Expr::ZERO - df_end.clone()));
            chans[0].push((vec![x_head.clone(), AB::Expr::ZERO, ro_read.0, ro_read.1], is_head.clone()));
            // Channels 1..=N_GROUPS — the input binding. Head PROVIDES committed term k on channel k%N_GROUPS.
            // NARROW-ARITH: `z` is not stored — re-derive it (= ζ, or ζ·g_trace for the trace-ζ_next term block)
            // from the committed ζ = `pis[2..4]`, exactly the FULL z-binding's value; FULL: read the stored z(k).
            let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&v| v.into()).collect();
            let g_trace = AB::Expr::from(Goldilocks::two_adic_generator(self.m.cm_rounds() - self.m.is_zk));
            let (zeta0, zeta1) = (pis[2].clone(), pis[3].clone());
            for k in 0..self.m.n_terms {
                let (z0, z1) = if self.m.narrow_arith {
                    if k >= self.m.trm_next_base() && k < self.m.trm_quot_base() {
                        (zeta0.clone() * g_trace.clone(), zeta1.clone() * g_trace.clone())
                    } else {
                        (zeta0.clone(), zeta1.clone())
                    }
                } else {
                    (cur[self.m.z(k)].clone(), cur[self.m.z(k) + 1].clone())
                };
                // NARROW: px is not stored — SOURCE it from the ov/qc carrier it's bound to; FULL: cur[px(k)].
                let px_col = if self.m.narrow_arith { self.m.px_source(k) } else { self.m.px(k) };
                let head_provide = vec![
                    x_head.clone(),
                    AB::Expr::ZERO,
                    AB::Expr::from(Goldilocks::from_u64(k as u64)),
                    z0,
                    z1,
                    cur[self.m.pz(k)].clone(),
                    cur[self.m.pz(k) + 1].clone(),
                    cur[px_col].clone(),
                ];
                chans[k % N_GROUPS + 1].push((head_provide, AB::Expr::ZERO - is_head.clone()));
            }
            // The region row READS its bundle (z at db+6, pz at db+8, px at db+10) on its is_ch channel.
            let region_read = vec![
                x.0.clone(),
                x.1.clone(),
                term_idx,
                cur[db + 6].clone(),
                cur[db + 7].clone(),
                cur[db + 8].clone(),
                cur[db + 9].clone(),
                cur[db + 10].clone(),
            ];
            for g in 0..N_GROUPS {
                chans[g + 1].push((region_read.clone(), is_ch[g].clone()));
            }
            for ch in chans {
                builder.push_local_interaction(ch);
            }
        }
    }

    /// **Caps assembly AA1 — the select bus, `cap_c` bound to a slack cap-row region** (the
    /// [`AssembledArithWrapAir`] analog for caps, the [`CapWrapAir`] soundness close). Where [`CapWrapAir`]
    /// externalizes the product-mux and leaves each cap carrier `cap_c` a FREE witness (bound only to the Merkle
    /// terminal), this AIR discharges the cap SELECTION through the LogUp bus. Each opening's `2^bits` cap entries
    /// become ROWS in the trace SLACK (`[cap_id, entry_idx, digest[4], cap_mult]`, gated by `cap_sel`); the region
    /// PROVIDES each entry `[cap_id, entry_idx, digest]` (mult `cap_mult = −count`), and each arith head READS, per
    /// opening g, `[g, index>>shift_g, cap_c[g]]` (mult `is_head`), `index>>shift_g` decoded from the committed
    /// index bits `sb_b`. Balance ⇒ `cap_c[g]` == the digest of the cap-row the query's index addresses — the
    /// narrow-tall selection, replacing the degree-`cap_height` product-mux over `2^cap_height·4` COLUMNS with
    /// 6-felt ROWS.
    ///
    /// **AA1 (this): composes.** The region + the select bus (one channel, `2 + cm_rounds` reads/head). AA1 leaves
    /// the cap-row digests UNBOUND to the transcript-committed cap (that `pis[cbase + entry_idx·4 + k]` binding is
    /// AA3); here `cap_c` is bound to the slack region, closing the free-witness gap for the SELECTION mechanism +
    /// fixing the degree. `is_head` is a witnessed column bound to the periodic `tf` (periodic must stay out of
    /// interactions — the lookup prover's aux gen feeds an empty periodic slice).
    pub(crate) struct AssembledCapWrapAir {
        pub(crate) m: MonolithAir,
    }

    impl AssembledCapWrapAir {
        /// Cap-row region base (after the monolith's fused columns): `[cap_id, entry_idx, digest[4], cap_mult]`.
        pub(crate) fn cr_base(&self) -> usize {
            self.m.fused_w()
        }
        /// Region row selector (1 on every cap-row slack row; gates the PROVIDE).
        pub(crate) fn cap_sel(&self) -> usize {
            self.cr_base() + 7
        }
        /// Witnessed arith-head marker (= the periodic `tf`, bound by a constraint) — gates the bus READ.
        pub(crate) fn is_head(&self) -> usize {
            self.cr_base() + 8
        }
        /// The openings the head reads: `(cap_id, cg_off, shift, bits)` — trace, quotient, then `cm_rounds` commit
        /// rounds (is_zk=0). `cap_id` distinguishes the caps in the bus tuple; `cg_off` locates `cap_c`; `shift`/
        /// `bits` decode `index>>shift` from `sb_b`. (Mirrors `emit_capmux`'s openings, minus `cbase` — AA1 binds
        /// to the region rows, not the committed pis; that is AA3.)
        pub(crate) fn openings(&self) -> Vec<(usize, usize, usize, usize)> {
            let mut v = vec![
                (0, 0, self.m.input_depth(), self.m.cap_height),
                (1, 4, self.m.input_depth(), self.m.cap_height),
            ];
            for r in 0..self.m.cm_rounds() {
                v.push((2 + r, 8 + 4 * r, self.m.commit_shift(r), self.m.commit_bits(r)));
            }
            v
        }
        /// **AA3** — the openings WITH their committed base `cbase`: `(cap_id, shift, bits, cbase)`. The binding
        /// provider enumerates every committed cap entry `pis[cbase + entry·4 + k]` from this (fixed pis reads).
        pub(crate) fn caps_with_base(&self) -> Vec<(usize, usize, usize, usize)> {
            let mut v = vec![
                (0, self.m.input_depth(), self.m.cap_height, self.m.cap_base()),
                (1, self.m.input_depth(), self.m.cap_height, self.m.qcap_base()),
            ];
            for r in 0..self.m.cm_rounds() {
                v.push((2 + r, self.m.commit_shift(r), self.m.commit_bits(r), self.m.commit_cap_base(r)));
            }
            v
        }
        /// Total committed cap entries to bind (`Σ_openings 2^bits`).
        pub(crate) fn total_entries(&self) -> usize {
            self.caps_with_base().iter().map(|&(_, _, bits, _)| 1usize << bits).sum()
        }
        /// **AA3** max committed-entry provides per binding channel — the LogUp degree scales with provides/channel
        /// (the arith 2c ceiling ~15 for log_nqc ≤ 4); 13 + the 1 cap-row read = 14 terms ⇒ degree 15, comfortable.
        pub(crate) const MAX_PER_CH: usize = 13;
        /// Binding-bus channels: the `total_entries` committed provides split so each channel carries ≤ MAX_PER_CH.
        pub(crate) fn n_bind_ch(&self) -> usize {
            self.total_entries().div_ceil(Self::MAX_PER_CH)
        }
        /// The single binder row's marker (PROVIDES all committed entries once; the bus balance forces exactly one
        /// binder row — 0 ⇒ reads unmatched, ≥2 ⇒ over-provide).
        pub(crate) fn is_binder(&self) -> usize {
            self.cr_base() + 9
        }
        /// Cap-row read-routing one-hot: `is_rd[g] = 1` iff this cap-row READs its committed binding on channel
        /// g+1 (where its entry is provided, `global_index % n_bind_ch`). `Σ_g is_rd == cap_sel`.
        pub(crate) fn is_rd(&self, g: usize) -> usize {
            self.cr_base() + 10 + g
        }
    }

    impl BaseAir<Goldilocks> for AssembledCapWrapAir {
        fn width(&self) -> usize {
            // AA1 region (9: cap_id + entry_idx + digest[4] + cap_mult + cap_sel + is_head) + AA3 binding
            // (is_binder + is_rd[0..n_bind_ch]).
            self.m.fused_w() + 10 + self.n_bind_ch()
        }
        fn num_public_values(&self) -> usize {
            BaseAir::<Goldilocks>::num_public_values(&self.m)
        }
        fn num_periodic_columns(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m)
        }
        fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
            BaseAir::<Goldilocks>::periodic_columns(&self.m)
        }
    }

    impl<AB: AirBuilder<F = Goldilocks> + p3_lookup::InteractionBuilder> Air<AB> for AssembledCapWrapAir {
        fn eval(&self, builder: &mut AB) {
            // (1) The reused monolith regions + the `CapMuxBci` strategy: the product-mux is externalized, so
            // `cap_c` is bound only to the Merkle terminal (+ held) — the select bus below binds it to the region.
            self.m.eval_bci(builder, &CapMuxBci);

            let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
            let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
            let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&v| v.into()).collect();
            let one = AB::Expr::ONE;
            let cr = self.cr_base();
            let n_ch = self.n_bind_ch();

            // (2) Region markers — booleans; `is_head` bound to the periodic `tf` so the bus READ is gated by the
            // COLUMN, not the periodic. Off-region rows carry `cap_mult = 0` (so they PROVIDE nothing). The AA3
            // read-routing one-hot `is_rd` is boolean + sums to `cap_sel` (each cap-row reads on exactly one
            // binding channel; non-cap rows read on none).
            let cap_sel = cur[self.cap_sel()].clone();
            let is_head = cur[self.is_head()].clone();
            let is_binder = cur[self.is_binder()].clone();
            for mk in [&cap_sel, &is_head, &is_binder] {
                builder.assert_zero(mk.clone() * (mk.clone() - one.clone()));
            }
            builder.assert_zero(is_head.clone() - p[self.m.m_tf()].clone());
            builder.assert_zero((one.clone() - cap_sel.clone()) * cur[cr + 6].clone());
            let mut rd_sum = AB::Expr::ZERO;
            for g in 0..n_ch {
                let rd = cur[self.is_rd(g)].clone();
                builder.assert_zero(rd.clone() * (rd.clone() - one.clone()));
                rd_sum = rd_sum + rd;
            }
            builder.assert_zero(rd_sum - cap_sel.clone());

            // Channels: 0 = the SELECT bus; 1..=n_ch = the committed-cap BINDING.
            let mut chans: Vec<Vec<(Vec<AB::Expr>, AB::Expr)>> = vec![Vec::new(); n_ch + 1];

            // The cap-row's own entry `[cap_id, entry_idx, digest]` — PROVIDED to the select bus AND READ from the
            // binding bus (so its digest is forced == the committed cap entry it claims).
            let cap_tuple = vec![
                cur[cr].clone(),
                cur[cr + 1].clone(),
                cur[cr + 2].clone(),
                cur[cr + 3].clone(),
                cur[cr + 4].clone(),
                cur[cr + 5].clone(),
            ];

            // (3) The SELECT bus (channel 0): cap-row PROVIDES its entry (mult `cap_mult` = −count); each arith
            // head READS, per opening g, `[g, index>>shift_g, cap_c[g]]` (mult `is_head`). Balance ⇒ `cap_c[g]` ==
            // the digest of the addressed cap-row.
            chans[0].push((cap_tuple.clone(), cur[cr + 6].clone()));
            for (cap_id, cg_off, shift, bits) in self.openings() {
                let mut sel_idx = AB::Expr::ZERO;
                for j in 0..bits {
                    sel_idx = sel_idx
                        + cur[self.m.sb_b(shift + j)].clone() * AB::Expr::from(Goldilocks::from_u64(1u64 << j));
                }
                let read = vec![
                    AB::Expr::from(Goldilocks::from_u64(cap_id as u64)),
                    sel_idx,
                    cur[self.m.cap_c(cg_off)].clone(),
                    cur[self.m.cap_c(cg_off + 1)].clone(),
                    cur[self.m.cap_c(cg_off + 2)].clone(),
                    cur[self.m.cap_c(cg_off + 3)].clone(),
                ];
                chans[0].push((read, is_head.clone()));
            }

            // (4) The committed-cap BINDING (channels 1..=n_ch — AA3, the soundness close). The single binder row
            // PROVIDES every committed cap entry `[cap_id, entry, pis[cbase + entry·4 + k]]` ONCE (mult −is_binder,
            // routed to channel `global_index % n_ch`); each cap-row READS its own `[cap_id, entry_idx, digest]` on
            // its `is_rd` channel (mult `is_rd[g]`). Balance ⇒ every cap-row's digest == the committed cap entry it
            // claims — so the select bus's `cap_c` is bound to the REAL cap, no longer a free witness. The binder
            // row's provides are FIXED pis reads (`cbase`, `entry` compile-time), split so ≤ MAX_PER_CH per channel.
            let mut gi = 0usize;
            for (cap_id, _shift, bits, cbase) in self.caps_with_base() {
                for e in 0..(1usize << bits) {
                    let ch = gi % n_ch + 1;
                    let tuple = vec![
                        AB::Expr::from(Goldilocks::from_u64(cap_id as u64)),
                        AB::Expr::from(Goldilocks::from_u64(e as u64)),
                        pis[cbase + e * 4].clone(),
                        pis[cbase + e * 4 + 1].clone(),
                        pis[cbase + e * 4 + 2].clone(),
                        pis[cbase + e * 4 + 3].clone(),
                    ];
                    chans[ch].push((tuple, AB::Expr::ZERO - is_binder.clone()));
                    gi += 1;
                }
            }
            for g in 0..n_ch {
                chans[g + 1].push((cap_tuple.clone(), cur[self.is_rd(g)].clone()));
            }

            for ch in chans {
                builder.push_local_interaction(ch);
            }
        }
    }

    /// **Caps AA5 — the cw=true SOUND capstone: `AssembledCapWrapCwAir`.** The [`AssembledCapWrapAir`] sibling one
    /// regime deeper (`column_window=true` + `narrow_caps`): the `2^cap_height·4` cap COLUMNS are DROPPED from the
    /// pis window (the 4.4× width win), so AA3's committed-cap binding (which anchored each cap-row digest to
    /// `pis[cbase]`) is GONE. This re-anchors them to the caps the transcript sponge ACTUALLY absorbed, via the
    /// ordered sponge-cap bus ([`super::SpongeCapBusAir`], proven standalone) — closing the FS⟂auth cap decoupling:
    ///  - **SELECT bus (channel 0, unchanged from AA1):** each arith head READS `[cap_id, index>>shift, cap_c[g]]`;
    ///    the cap-row PROVIDES `[cap_id, entry, digest]` (mult −count). Balance ⇒ `cap_c` == the addressed cap-row.
    ///  - **SPONGE-CAP bus (channel 1, REPLACING AA3):** on the transcript absorb rows, per rate lane `l` a
    ///    periodic-PINNED `(w_gi_l, w_sel_l)` PROVIDES `(w_gi_l, cur[l])` mult −w_sel_l — `cur[l]` the real
    ///    FS-absorbed rate lane, `w_gi_l`/`w_sel_l` bound by constraint to the `sim_cap_positions` cap-tag periodics
    ///    (the FT_BIND pattern, so the order can't be shuffled). Each cap-row READS its 4 digest felts
    ///    `(gi_base+k, digest[k])` mult +cap_sel. Balance on `(gi, value)` ⇒ every cap-row digest == the felt the
    ///    sponge absorbed at that stream position ⇒ the auth cap (`cap_c`, via SELECT) == the FS cap. Sound.
    ///
    /// Width `fused_w + 18` (region 10: `[cap_id, entry, digest[4], cap_mult, cap_sel, is_head, gi_base]` + 2·RATE
    /// witnessed tags); 2 lookup channels. `cap_periodics` = the 2·RATE cap-tag columns (carried; appended to the
    /// monolith periodics). Proven through `prove_lookup` (`cap_wrap_cw_assembled_proves`).
    pub(crate) struct AssembledCapWrapCwAir {
        pub(crate) m: MonolithAir,
        pub(crate) cap_periodics: Vec<Vec<Goldilocks>>,
    }

    impl AssembledCapWrapCwAir {
        /// Cap-absorb rate = DIGEST = the sponge `RATE` (a cap entry is a 4-felt run absorbed into 4 rate lanes).
        pub(crate) const CAP_RATE: usize = 4;
        /// Cap-row region base (after the monolith's fused columns): `[cap_id, entry_idx, digest[4], cap_mult]`.
        pub(crate) fn cr_base(&self) -> usize {
            self.m.fused_w()
        }
        /// Region row selector (1 on every cap-row slack row; gates the digest READ + the PROVIDE).
        pub(crate) fn cap_sel(&self) -> usize {
            self.cr_base() + 7
        }
        /// Witnessed arith-head marker (= the periodic `tf`, bound by a constraint) — gates the select READ.
        pub(crate) fn is_head(&self) -> usize {
            self.cr_base() + 8
        }
        /// The cap-row's `gi` of its `k=0` felt (free witness; the sponge balance FORCES it — the provide multiset
        /// is fixed by the periodic tags + the FS-bound rate lanes, so a wrong `gi_base` can't cancel).
        pub(crate) fn gi_base(&self) -> usize {
            self.cr_base() + 9
        }
        /// Witnessed sponge-cap `gi` tag for rate lane `l` — pinned to the `cap_periodics[2l]` periodic column.
        pub(crate) fn w_gi(&self, l: usize) -> usize {
            self.cr_base() + 10 + 2 * l
        }
        /// Witnessed sponge-cap `sel` tag for rate lane `l` — pinned to `cap_periodics[2l+1]` (1 iff lane `l` of
        /// this transcript block absorbed a cap felt).
        pub(crate) fn w_sel(&self, l: usize) -> usize {
            self.cr_base() + 11 + 2 * l
        }
        /// The periodic index where the appended cap-tag columns begin.
        pub(crate) fn cap_periodic_base(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m)
        }
        /// The SELECT-bus openings (same as [`AssembledCapWrapAir::openings`] — trace, quotient, `cm_rounds`
        /// commit): `(cap_id, cg_off, shift, bits)`.
        pub(crate) fn openings(&self) -> Vec<(usize, usize, usize, usize)> {
            let mut v = vec![
                (0, 0, self.m.input_depth(), self.m.cap_height),
                (1, 4, self.m.input_depth(), self.m.cap_height),
            ];
            for r in 0..self.m.cm_rounds() {
                v.push((2 + r, 8 + 4 * r, self.m.commit_shift(r), self.m.commit_bits(r)));
            }
            v
        }
    }

    impl BaseAir<Goldilocks> for AssembledCapWrapCwAir {
        fn width(&self) -> usize {
            self.m.fused_w() + 10 + 2 * Self::CAP_RATE
        }
        fn num_public_values(&self) -> usize {
            BaseAir::<Goldilocks>::num_public_values(&self.m)
        }
        fn num_periodic_columns(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m) + 2 * Self::CAP_RATE
        }
        fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
            let mut p = BaseAir::<Goldilocks>::periodic_columns(&self.m);
            p.extend(self.cap_periodics.iter().cloned());
            p
        }
    }

    impl<AB: AirBuilder<F = Goldilocks> + p3_lookup::InteractionBuilder> Air<AB> for AssembledCapWrapCwAir {
        fn eval(&self, builder: &mut AB) {
            // (1) The reused monolith regions + the `CapMuxBci` strategy (product-mux externalized); `cap_c` is
            // bound only to the Merkle terminal (+ held) — the SELECT bus binds it to the region below.
            self.m.eval_bci(builder, &CapMuxBci);

            let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
            let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
            let one = AB::Expr::ONE;
            let cr = self.cr_base();
            let pbase = self.cap_periodic_base();
            let rate = Self::CAP_RATE;

            // (2) Region markers — boolean; `is_head` bound to the periodic `tf`, `cap_mult = 0` off-region.
            let cap_sel = cur[self.cap_sel()].clone();
            let is_head = cur[self.is_head()].clone();
            for mk in [&cap_sel, &is_head] {
                builder.assert_zero(mk.clone() * (mk.clone() - one.clone()));
            }
            builder.assert_zero(is_head.clone() - p[self.m.m_tf()].clone());
            builder.assert_zero((one.clone() - cap_sel.clone()) * cur[cr + 6].clone());

            // (3) Sponge-cap tags PINNED to periodic (the periodic-out-of-interactions rule — witness the columns,
            // bind them by constraint, then use the COLUMNS in the bus). `w_sel_l` is thus 0/1 from the periodic.
            for l in 0..rate {
                builder.assert_zero(cur[self.w_gi(l)].clone() - p[pbase + 2 * l].clone());
                builder.assert_zero(cur[self.w_sel(l)].clone() - p[pbase + 2 * l + 1].clone());
            }

            // (4) SELECT bus (channel 0): the cap-row PROVIDES its entry (mult `cap_mult` = −count); each arith
            // head READS, per opening g, `[cap_id, index>>shift_g, cap_c[g]]` (mult `is_head`). Unchanged from AA1.
            let cap_tuple = vec![
                cur[cr].clone(),
                cur[cr + 1].clone(),
                cur[cr + 2].clone(),
                cur[cr + 3].clone(),
                cur[cr + 4].clone(),
                cur[cr + 5].clone(),
            ];
            let mut ch_select: Vec<(Vec<AB::Expr>, AB::Expr)> = vec![(cap_tuple.clone(), cur[cr + 6].clone())];
            for (cap_id, cg_off, shift, bits) in self.openings() {
                let mut sel_idx = AB::Expr::ZERO;
                for j in 0..bits {
                    sel_idx = sel_idx
                        + cur[self.m.sb_b(shift + j)].clone() * AB::Expr::from(Goldilocks::from_u64(1u64 << j));
                }
                ch_select.push((
                    vec![
                        AB::Expr::from(Goldilocks::from_u64(cap_id as u64)),
                        sel_idx,
                        cur[self.m.cap_c(cg_off)].clone(),
                        cur[self.m.cap_c(cg_off + 1)].clone(),
                        cur[self.m.cap_c(cg_off + 2)].clone(),
                        cur[self.m.cap_c(cg_off + 3)].clone(),
                    ],
                    is_head.clone(),
                ));
            }

            // (5) SPONGE-CAP bus (channel 1 — the FS anchor, REPLACING AA3). On the transcript absorb rows, per
            // rate lane `l` PROVIDE `(w_gi_l, cur[l])` mult −w_sel_l (`cur[l]` the real FS-absorbed felt); each
            // cap-row READS its 4 digest felts `(gi_base+k, digest[k])` mult +cap_sel. Balance on `(gi, value)` ⇒
            // every cap-row digest == the felt absorbed at that stream position ⇒ the auth cap == the FS cap.
            let mut ch_sponge: Vec<(Vec<AB::Expr>, AB::Expr)> = Vec::with_capacity(rate + 4);
            for l in 0..rate {
                ch_sponge.push((
                    vec![cur[self.w_gi(l)].clone(), cur[l].clone()],
                    AB::Expr::ZERO - cur[self.w_sel(l)].clone(),
                ));
            }
            for k in 0..4 {
                let gi_k = cur[self.gi_base()].clone() + AB::Expr::from(Goldilocks::from_u64(k as u64));
                ch_sponge.push((vec![gi_k, cur[cr + 2 + k].clone()], cap_sel.clone()));
            }

            builder.push_local_interaction(ch_select);
            builder.push_local_interaction(ch_sponge);
        }
    }

    /// **AA6 brick-3 DE-RISK — does the sponge-opening bus dissolve the 2c degree wall?** The `narrow_openings`
    /// integration hinges on ONE question: binding the epilogue's `n_terms` openings via the ordered sponge bus
    /// (provides SPREAD across transcript rows, reads SPREAD across region rows — never all-on-one-row) keeps
    /// `log_nqc ≤ 4`, unlike the op-table's abandoned 2c binding (the arith HEAD providing ~120 openings on ONE
    /// row ⇒ log_nqc 6, `28df1b2`). This probe answers it: the cw=true narrow monolith (`eval_bci(&CapMuxBci)` —
    /// the caps-narrowed verifier at `log_nqc ≤ 4`) + a SINGLE sponge-opening bus channel (`RATE` provides + 2
    /// reads = 6 tuples/row) binding a 1-opening-per-row region to the FS-absorbed openings. Composes `≤ 4` ⇒ the
    /// sponge bus dissolves the wall (the whole `narrow_openings` integration is de-risked). `op_periodics` = the
    /// 2·RATE opening-tag columns; for `combined_constraint_layout` the VALUES are irrelevant (log_nqc reads the
    /// symbolic constraint STRUCTURE), so the compose probe passes dummies.
    pub(crate) struct OpeningBindCwAir {
        pub(crate) m: MonolithAir,
        pub(crate) op_periodics: Vec<Vec<Goldilocks>>,
    }

    impl OpeningBindCwAir {
        /// Sponge rate = the transcript absorbs RATE felts/block (an opening is a 2-felt F_p² run).
        pub(crate) const RATE: usize = 4;
        pub(crate) fn cr(&self) -> usize {
            self.m.fused_w()
        }
        /// Openings-region row: `[gi_base, val0, val1, op_sel]` (one OOD opening/row; `gi_base` its FS-stream index).
        pub(crate) fn op_sel(&self) -> usize {
            self.cr() + 3
        }
        pub(crate) fn w_gi(&self, l: usize) -> usize {
            self.cr() + 4 + 2 * l
        }
        pub(crate) fn w_sel(&self, l: usize) -> usize {
            self.cr() + 5 + 2 * l
        }
        pub(crate) fn op_periodic_base(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m)
        }
    }

    impl BaseAir<Goldilocks> for OpeningBindCwAir {
        fn width(&self) -> usize {
            self.m.fused_w() + 4 + 2 * Self::RATE
        }
        fn num_public_values(&self) -> usize {
            BaseAir::<Goldilocks>::num_public_values(&self.m)
        }
        fn num_periodic_columns(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m) + 2 * Self::RATE
        }
        fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
            let mut p = BaseAir::<Goldilocks>::periodic_columns(&self.m);
            p.extend(self.op_periodics.iter().cloned());
            p
        }
    }

    impl<AB: AirBuilder<F = Goldilocks> + p3_lookup::InteractionBuilder> Air<AB> for OpeningBindCwAir {
        fn eval(&self, builder: &mut AB) {
            self.m.eval_bci(builder, &CapMuxBci);
            let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
            let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
            let one = AB::Expr::ONE;
            let cr = self.cr();
            let pbase = self.op_periodic_base();
            let rate = Self::RATE;

            let op_sel = cur[self.op_sel()].clone();
            builder.assert_zero(op_sel.clone() * (op_sel.clone() - one.clone()));
            for l in 0..rate {
                builder.assert_zero(cur[self.w_gi(l)].clone() - p[pbase + 2 * l].clone());
                builder.assert_zero(cur[self.w_sel(l)].clone() - p[pbase + 2 * l + 1].clone());
            }

            // ONE sponge-opening bus channel: per lane PROVIDE (w_gi_l, cur[l]) −w_sel_l; the region row READS its
            // opening's 2 F_p² felts (gi_base+k, val_k) +op_sel. 6 tuples/row (vs the 2c head's ~120) — the crux.
            let mut ch: Vec<(Vec<AB::Expr>, AB::Expr)> = Vec::with_capacity(rate + 2);
            for l in 0..rate {
                ch.push((
                    vec![cur[self.w_gi(l)].clone(), cur[l].clone()],
                    AB::Expr::ZERO - cur[self.w_sel(l)].clone(),
                ));
            }
            for k in 0..2 {
                let gi_k = cur[cr].clone() + AB::Expr::from(Goldilocks::from_u64(k as u64));
                ch.push((vec![gi_k, cur[cr + 1 + k].clone()], op_sel.clone()));
            }
            builder.push_local_interaction(ch);
        }
    }

    /// **W3 ov externalization brick 4c (compose de-risk) — the narrow_ov monolith + the SOUND query-keyed leaf-hash→px
    /// bus COMPOSE.** The [`OpeningBindCwAir`] analog for the ov carrier: the narrow_ov monolith ([`OpeningsBci`]; the
    /// ov-carrier reads gated on `!narrow_ov` by brick 4a) + ONE ordered leaf-hash→px bus keyed by **`[lqk, term]`** —
    /// `lqk` the HELD query point `x` (so the bus is query-UNIQUE; a periodic term tag alone REPEATS per query
    /// super-tile ⇒ collides — the resolved crux), `term` the DEEP term index. Each leaf-hash rate lane PROVIDES its
    /// absorbed felt under BOTH shared terms `trm_trace(c)`/`trm_next(c)` (−w_sel); the px-region READS `[lqk, term, px0]`
    /// (+px_sel), reusing the fold's `term_idx`. Confirms the bus + the ov-dropped monolith compose TOGETHER at
    /// `log_nqc ≤ LOG_BLOWUP` — the DEGREE de-risk for the assembled px binding (the balance brick binds `px` to the
    /// real leaf-hash rows, `lqk` HELD+bound to `x_head` there). Additive: does NOT touch the proven wrap. `lqk`/px are
    /// free witnesses here (held/bound in the assembly, as `ro`/`folded`/`quot`/`px` are free in the other de-risks).
    pub(crate) struct NarrowOvBindCwAir {
        pub(crate) m: MonolithAir,
        /// `3·RATE` periodic-pinned tags: per rate lane, the two shared DEEP term ids + the provide-select bit.
        pub(crate) leaf_periodics: Vec<Vec<Goldilocks>>,
    }

    impl NarrowOvBindCwAir {
        pub(crate) const RATE: usize = 4;
        pub(crate) fn ro_col(&self) -> usize {
            self.m.fused_w()
        }
        pub(crate) fn folded_col(&self) -> usize {
            self.m.fused_w() + 2
        }
        pub(crate) fn quot_col(&self) -> usize {
            self.m.fused_w() + 4
        }
        /// The held query key `lqk` = the query point `x` (base-field `GEN^index`; the region's `x1 ≡ 0`), shared by
        /// the leaf-hash PROVIDE and the region READ so the bus address is query-UNIQUE — the crux the periodic tag
        /// alone can't solve (it REPEATS per query super-tile ⇒ collides across queries). A single O(1) slack column
        /// (slope 0 — does NOT reintroduce the w_inner slope); free here, HELD+bound to `x_head` in the assembly.
        pub(crate) fn lqk(&self) -> usize {
            self.m.fused_w() + 6
        }
        /// px-region row: `[term, px0, px_sel]` — reads its trace-term px keyed by `[lqk, term]`; `term` = the DEEP
        /// term index (reused from the fold's `term_idx`, no felt-index map), `px0` the base-field opened felt (`px1≡0`).
        pub(crate) fn term_r(&self) -> usize {
            self.m.fused_w() + 7
        }
        pub(crate) fn px0(&self) -> usize {
            self.m.fused_w() + 8
        }
        pub(crate) fn px_sel(&self) -> usize {
            self.m.fused_w() + 9
        }
        /// leaf-hash provider tags (periodic-pinned): per rate lane, the TWO DEEP terms `trm_trace(c)`/`trm_next(c)`
        /// sharing felt `c = block·RATE+lane` + the select bit (1 iff `c < trm_committed_w` — a felt read as px).
        pub(crate) fn w_t0(&self, l: usize) -> usize {
            self.m.fused_w() + 10 + 3 * l
        }
        pub(crate) fn w_t1(&self, l: usize) -> usize {
            self.m.fused_w() + 11 + 3 * l
        }
        pub(crate) fn w_sel(&self, l: usize) -> usize {
            self.m.fused_w() + 12 + 3 * l
        }
        pub(crate) fn leaf_periodic_base(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m)
        }
    }

    impl BaseAir<Goldilocks> for NarrowOvBindCwAir {
        fn width(&self) -> usize {
            // ro/folded/quot(6) + lqk(1) + px-region [term,px0,px_sel](3) + 3·RATE leaf-hash tags [t0,t1,sel]/lane.
            self.m.fused_w() + 10 + 3 * Self::RATE
        }
        fn num_public_values(&self) -> usize {
            BaseAir::<Goldilocks>::num_public_values(&self.m)
        }
        fn num_periodic_columns(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m) + 3 * Self::RATE
        }
        fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
            let mut p = BaseAir::<Goldilocks>::periodic_columns(&self.m);
            p.extend(self.leaf_periodics.iter().cloned());
            p
        }
    }

    impl<AB: AirBuilder<F = Goldilocks> + p3_lookup::InteractionBuilder> Air<AB> for NarrowOvBindCwAir {
        fn eval(&self, builder: &mut AB) {
            self.m.eval_bci(
                builder,
                &OpeningsBci { ro_col: self.ro_col(), folded_col: self.folded_col(), quot_col: self.quot_col() },
            );
            let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
            let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
            let one = AB::Expr::ONE;
            let pbase = self.leaf_periodic_base();
            let rate = Self::RATE;

            let px_sel = cur[self.px_sel()].clone();
            builder.assert_zero(px_sel.clone() * (px_sel.clone() - one.clone()));
            // term tags + select pinned to the periodics (periodic-out-of-interactions: witness the cols, use the cols).
            for l in 0..rate {
                builder.assert_zero(cur[self.w_t0(l)].clone() - p[pbase + 3 * l].clone());
                builder.assert_zero(cur[self.w_t1(l)].clone() - p[pbase + 3 * l + 1].clone());
                builder.assert_zero(cur[self.w_sel(l)].clone() - p[pbase + 3 * l + 2].clone());
            }

            // ONE leaf-hash→px bus, QUERY-KEYED by `[lqk, term]` (the crux — the SOUND key, not the periodic-only `gi`
            // which repeats per query). Each leaf-hash rate lane `l` (the absorbed opened felt `cur[l]`) PROVIDES its
            // felt under BOTH DEEP terms `trm_trace(c)`/`trm_next(c)` sharing it (−w_sel each); the px-region row READS
            // `[lqk, term, px0]` (+px_sel). The held `lqk` (= x) makes provides/reads query-unique where the term tag
            // alone would collide across queries. TERM-keyed ⇒ the region reuses the fold's `term_idx` (no felt map).
            let lqk = cur[self.lqk()].clone();
            let mut ch: Vec<(Vec<AB::Expr>, AB::Expr)> = Vec::with_capacity(2 * rate + 1);
            for l in 0..rate {
                let neg_sel = AB::Expr::ZERO - cur[self.w_sel(l)].clone();
                ch.push((vec![lqk.clone(), cur[self.w_t0(l)].clone(), cur[l].clone()], neg_sel.clone()));
                ch.push((vec![lqk.clone(), cur[self.w_t1(l)].clone(), cur[l].clone()], neg_sel));
            }
            ch.push((vec![lqk.clone(), cur[self.term_r()].clone(), cur[self.px0()].clone()], px_sel.clone()));
            builder.push_local_interaction(ch);
        }
    }

    /// **AA6 op-table binding brick 5a — the cw=true op-table epilogue COMPOSES** (`--features lookup,recursion`,
    /// cheap). The [`AssembledWrapAir`] op-table region + `folded` binding, ported to `column_window = true` +
    /// `narrow_openings` (the openings-wrap regime) and re-based on [`OpeningsBci`] — the crux the cw=false
    /// `AssembledWrapAir` could NOT reach (its 2c opening-leaf binding reads `pis[..]`, EMPTY at cw=true, and was
    /// degree-infeasible `log_nqc 6`). The epilogue's `folded` is externalized to the FLATTEN op-table
    /// ([`crate::wrap::OpTableF2Air`] relations inlined + gated by `op_sel` on slack rows) and bound to `folded_col`
    /// through the wiring bus (the op-table PROVIDES its `folded` wire at `folded_addr`, the arith head READS
    /// `folded_col` there). De-risks the DEGREE of the op-table region + the folded bus at cw=true BEFORE the full
    /// assembly (the opening LEAVES stay free here — the sponge-opening bus binds them next, mirroring AA1→AA2b);
    /// `ro_col`/`quot_col` are free witnesses (the DeepFold region + the quot recompose bind them). If `log_nqc ≤ 4`
    /// the op-table epilogue integrates at cw=true within budget — the 2c wall is dissolved for the epilogue too.
    pub(crate) struct OpTableBindCwAir {
        pub(crate) m: MonolithAir,
        /// The op-table wiring-bus address of the `folded` output wire (the arith head reads `folded_col` here).
        pub(crate) folded_addr: u64,
    }

    impl OpTableBindCwAir {
        pub(crate) fn ro_col(&self) -> usize {
            self.m.fused_w()
        }
        pub(crate) fn folded_col(&self) -> usize {
            self.m.fused_w() + 2
        }
        pub(crate) fn quot_col(&self) -> usize {
            self.m.fused_w() + 4
        }
        /// The op-table region base (13 `OpTableF2Air` columns), after ro/folded/quot.
        pub(crate) fn op_base(&self) -> usize {
            self.m.fused_w() + 6
        }
        pub(crate) fn op_sel(&self) -> usize {
            self.op_base() + 13
        }
        pub(crate) fn is_head(&self) -> usize {
            self.op_base() + 14
        }
    }

    impl BaseAir<Goldilocks> for OpTableBindCwAir {
        fn width(&self) -> usize {
            // ro/folded/quot(6) + op-table(13) + op_sel(1) + is_head(1).
            self.m.fused_w() + 6 + 13 + 2
        }
        fn num_public_values(&self) -> usize {
            BaseAir::<Goldilocks>::num_public_values(&self.m)
        }
        fn num_periodic_columns(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m)
        }
        fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
            BaseAir::<Goldilocks>::periodic_columns(&self.m)
        }
    }

    impl<AB: AirBuilder<F = Goldilocks> + p3_lookup::InteractionBuilder> Air<AB> for OpTableBindCwAir {
        fn eval(&self, builder: &mut AB) {
            // (1) The narrow cw=true monolith with the OpeningsBci epilogue (reads folded_col/quot_col, checks
            // folded·inv_van == quot_col). ro_col/folded_col/quot_col are free witnesses here.
            self.m.eval_bci(
                builder,
                &OpeningsBci { ro_col: self.ro_col(), folded_col: self.folded_col(), quot_col: self.quot_col() },
            );

            let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
            let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
            let one = AB::Expr::ONE;
            let we = AB::Expr::from(Goldilocks::from_u64(7)); // F_p² : X² = 7
            let ob = self.op_base();

            // (2) The op-table REGION — OpTableF2Air relations inlined + gated by op_sel (slack rows compute the
            // c_k + the α-fold). Mirrors AssembledWrapAir's region, one regime deeper (cw=true).
            let (is_mul, is_add, is_sub) = (cur[ob].clone(), cur[ob + 1].clone(), cur[ob + 2].clone());
            let (out_addr, o0, o1) = (cur[ob + 3].clone(), cur[ob + 4].clone(), cur[ob + 5].clone());
            let (a_addr, a0, a1) = (cur[ob + 6].clone(), cur[ob + 7].clone(), cur[ob + 8].clone());
            let (b_addr, b0, b1) = (cur[ob + 9].clone(), cur[ob + 10].clone(), cur[ob + 11].clone());
            let out_mult = cur[ob + 12].clone();
            let op_sel = cur[self.op_sel()].clone();
            builder.assert_zero(op_sel.clone() * (op_sel.clone() - one.clone()));
            for s in [&is_mul, &is_add, &is_sub] {
                builder.assert_zero(op_sel.clone() * s.clone() * (s.clone() - one.clone()));
            }
            let is_op = is_mul.clone() + is_add.clone() + is_sub.clone();
            builder.assert_zero(op_sel.clone() * is_op.clone() * (is_op.clone() - one.clone()));
            builder.assert_zero(op_sel.clone() * is_mul.clone() * (o0.clone() - (a0.clone() * b0.clone() + we.clone() * a1.clone() * b1.clone())));
            builder.assert_zero(op_sel.clone() * is_mul.clone() * (o1.clone() - (a0.clone() * b1.clone() + a1.clone() * b0.clone())));
            builder.assert_zero(op_sel.clone() * is_add.clone() * (o0.clone() - (a0.clone() + b0.clone())));
            builder.assert_zero(op_sel.clone() * is_add.clone() * (o1.clone() - (a1.clone() + b1.clone())));
            builder.assert_zero(op_sel.clone() * is_sub.clone() * (o0.clone() - (a0.clone() - b0.clone())));
            builder.assert_zero(op_sel.clone() * is_sub.clone() * (o1.clone() - (a1.clone() - b1.clone())));

            // (3) is_head bound to the periodic tf (so the folded bus READ is gated by the COLUMN, not periodic —
            // the lookup prover feeds interactions an empty periodic slice).
            let is_head = cur[self.is_head()].clone();
            builder.assert_zero(is_head.clone() * (is_head.clone() - one.clone()));
            builder.assert_zero(is_head.clone() - p[self.m.m_tf()].clone());

            // (4) The wiring bus (one channel): the op-table reads its 2 operands (+op_sel·is_op) and DEFINES its
            // output (op_sel·out_mult, −fanout INCLUDING the head's folded read); the arith head READS folded_col
            // at folded_addr (+is_head). Balance ⇒ folded_col == the op-table's folded wire. Opening leaves free.
            let read_mult = op_sel.clone() * is_op;
            let folded = (cur[self.folded_col()].clone(), cur[self.folded_col() + 1].clone());
            let ch: Vec<(Vec<AB::Expr>, AB::Expr)> = vec![
                (vec![a_addr, a0, a1], read_mult.clone()),
                (vec![b_addr, b0, b1], read_mult),
                (vec![out_addr, o0, o1], op_sel * out_mult),
                (vec![AB::Expr::from(Goldilocks::from_u64(self.folded_addr)), folded.0, folded.1], is_head),
            ];
            builder.push_local_interaction(ch);
        }
    }

    /// **AA6 op-table binding brick 5b — the op-table + its opening-leaf binding COMPOSES at cw=true** (`--features
    /// lookup,recursion`, cheap). Extends [`OpTableBindCwAir`] with the op-table's OPENING-LEAF binding via the
    /// sponge (the AA2b machinery, with the op-table leaf as the reader instead of the DeepFold): a shared
    /// opening-row region reads each opening's 2 felts from the FS-absorbed sponge stream (channel 2) and
    /// RE-PROVIDES the opening pair to the op-table's opening-leaf rows (channel 1) — so the op-table's `local`/
    /// `next` leaves are BOUND to the real FS openings, SPREAD (one read per op-table leaf row; NEVER the
    /// ~120-provides-on-one-row 2c wall that broke `AssembledWrapAir` at cw=true — and, since the sponge spreads
    /// the provides, no `N_GROUPS` split is needed). With the op-table region + folded bus (channel 0), all THREE
    /// channels compose within budget ⇒ the op-table epilogue — region + fold + sponge-bound leaves — integrates
    /// at cw=true. (pubs/periodic/selector/constant leaves + the DeepFold-region coexistence + trace/prove follow.)
    pub(crate) struct OpTableLeafBindCwAir {
        pub(crate) m: MonolithAir,
        pub(crate) op_periodics: Vec<Vec<Goldilocks>>,
        pub(crate) folded_addr: u64,
        /// When set, ALSO provide the NON-trace opening leaves (pubs/periodic/selectors) from the cw=true
        /// window/sel columns on the arith head (channel 1) — the measurement of whether the ~n_pub+n_periodic+2
        /// non-trace provides fit on ONE row/channel (else they need the `N_GROUPS` split, like AssembledWrapAir).
        pub(crate) bind_window_leaves: bool,
    }

    impl OpTableLeafBindCwAir {
        pub(crate) const RATE: usize = 4;
        pub(crate) fn ro_col(&self) -> usize {
            self.m.fused_w()
        }
        pub(crate) fn folded_col(&self) -> usize {
            self.m.fused_w() + 2
        }
        pub(crate) fn quot_col(&self) -> usize {
            self.m.fused_w() + 4
        }
        pub(crate) fn op_base(&self) -> usize {
            self.m.fused_w() + 6
        }
        pub(crate) fn op_sel(&self) -> usize {
            self.op_base() + 13
        }
        pub(crate) fn is_head(&self) -> usize {
            self.op_base() + 14
        }
        /// Marks an op-table OPENING-leaf row (its `out` value reads the sponge-anchored opening on the op-table bus).
        pub(crate) fn is_leaf(&self) -> usize {
            self.op_base() + 15
        }
        /// The op-table-opening bus address the leaf reads (= the opening's `or_k`; the opening-row provides there).
        pub(crate) fn leaf_key(&self) -> usize {
            self.op_base() + 16
        }
        /// The shared opening-row region: `[gi_base, pz0, pz1, or_sel, or_k, or_mult]` (one DEEP opening/row).
        pub(crate) fn or_base(&self) -> usize {
            self.op_base() + 17
        }
        pub(crate) fn or_gi(&self) -> usize {
            self.or_base()
        }
        pub(crate) fn or_pz(&self) -> usize {
            self.or_base() + 1
        }
        pub(crate) fn or_sel(&self) -> usize {
            self.or_base() + 3
        }
        pub(crate) fn or_k(&self) -> usize {
            self.or_base() + 4
        }
        pub(crate) fn or_mult(&self) -> usize {
            self.or_base() + 5
        }
        pub(crate) fn st_base(&self) -> usize {
            self.or_base() + 6
        }
        pub(crate) fn w_gi(&self, l: usize) -> usize {
            self.st_base() + 2 * l
        }
        pub(crate) fn w_sel(&self, l: usize) -> usize {
            self.st_base() + 2 * l + 1
        }
        pub(crate) fn op_periodic_base(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m)
        }
    }

    impl BaseAir<Goldilocks> for OpTableLeafBindCwAir {
        fn width(&self) -> usize {
            // ro/folded/quot(6) + op-table(13) + op_sel/is_head/is_leaf/leaf_key(4) + opening-row(6) + sponge(2·RATE).
            self.m.fused_w() + 6 + 13 + 4 + 6 + 2 * Self::RATE
        }
        fn num_public_values(&self) -> usize {
            BaseAir::<Goldilocks>::num_public_values(&self.m)
        }
        fn num_periodic_columns(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m) + 2 * Self::RATE
        }
        fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
            let mut p = BaseAir::<Goldilocks>::periodic_columns(&self.m);
            p.extend(self.op_periodics.iter().cloned());
            p
        }
    }

    impl<AB: AirBuilder<F = Goldilocks> + p3_lookup::InteractionBuilder> Air<AB> for OpTableLeafBindCwAir {
        fn eval(&self, builder: &mut AB) {
            self.m.eval_bci(
                builder,
                &OpeningsBci { ro_col: self.ro_col(), folded_col: self.folded_col(), quot_col: self.quot_col() },
            );
            let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
            let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
            let one = AB::Expr::ONE;
            let we = AB::Expr::from(Goldilocks::from_u64(7)); // F_p² : X² = 7
            let ob = self.op_base();

            // (2) The op-table REGION (OpTableF2Air relations, op_sel-gated) — as OpTableBindCwAir.
            let (is_mul, is_add, is_sub) = (cur[ob].clone(), cur[ob + 1].clone(), cur[ob + 2].clone());
            let (out_addr, o0, o1) = (cur[ob + 3].clone(), cur[ob + 4].clone(), cur[ob + 5].clone());
            let (a_addr, a0, a1) = (cur[ob + 6].clone(), cur[ob + 7].clone(), cur[ob + 8].clone());
            let (b_addr, b0, b1) = (cur[ob + 9].clone(), cur[ob + 10].clone(), cur[ob + 11].clone());
            let out_mult = cur[ob + 12].clone();
            let op_sel = cur[self.op_sel()].clone();
            builder.assert_zero(op_sel.clone() * (op_sel.clone() - one.clone()));
            for s in [&is_mul, &is_add, &is_sub] {
                builder.assert_zero(op_sel.clone() * s.clone() * (s.clone() - one.clone()));
            }
            let is_op = is_mul.clone() + is_add.clone() + is_sub.clone();
            builder.assert_zero(op_sel.clone() * is_op.clone() * (is_op.clone() - one.clone()));
            builder.assert_zero(op_sel.clone() * is_mul.clone() * (o0.clone() - (a0.clone() * b0.clone() + we.clone() * a1.clone() * b1.clone())));
            builder.assert_zero(op_sel.clone() * is_mul.clone() * (o1.clone() - (a0.clone() * b1.clone() + a1.clone() * b0.clone())));
            builder.assert_zero(op_sel.clone() * is_add.clone() * (o0.clone() - (a0.clone() + b0.clone())));
            builder.assert_zero(op_sel.clone() * is_add.clone() * (o1.clone() - (a1.clone() + b1.clone())));
            builder.assert_zero(op_sel.clone() * is_sub.clone() * (o0.clone() - (a0.clone() - b0.clone())));
            builder.assert_zero(op_sel.clone() * is_sub.clone() * (o1.clone() - (a1.clone() - b1.clone())));

            // (3) Markers: is_head bound to tf; is_leaf + or_sel boolean; sponge tags pinned to op_periodics.
            let is_head = cur[self.is_head()].clone();
            builder.assert_zero(is_head.clone() * (is_head.clone() - one.clone()));
            builder.assert_zero(is_head.clone() - p[self.m.m_tf()].clone());
            let is_leaf = cur[self.is_leaf()].clone();
            builder.assert_zero(is_leaf.clone() * (is_leaf.clone() - one.clone()));
            let or_sel = cur[self.or_sel()].clone();
            builder.assert_zero(or_sel.clone() * (or_sel.clone() - one.clone()));
            let pbase = self.op_periodic_base();
            for l in 0..Self::RATE {
                builder.assert_zero(cur[self.w_gi(l)].clone() - p[pbase + 2 * l].clone());
                builder.assert_zero(cur[self.w_sel(l)].clone() - p[pbase + 2 * l + 1].clone());
            }

            // Channels: 0 wiring/folded, 1 op-table-opening (sponge-fed trace leaves), 2 sponge FS-anchor; +N_GROUPS
            // for the SPLIT non-trace (pubs/periodic/sel) provides when bind_window_leaves (else they'd concentrate).
            let n_chan = if self.bind_window_leaves { 3 + N_GROUPS } else { 3 };
            let mut chans: Vec<Vec<(Vec<AB::Expr>, AB::Expr)>> = vec![Vec::new(); n_chan];
            // Channel 0 — op-table wiring + the folded read (as OpTableBindCwAir).
            let read_mult = op_sel.clone() * is_op;
            let folded = (cur[self.folded_col()].clone(), cur[self.folded_col() + 1].clone());
            chans[0].push((vec![a_addr, a0, a1], read_mult.clone()));
            chans[0].push((vec![b_addr, b0, b1], read_mult));
            chans[0].push((vec![out_addr, o0.clone(), o1.clone()], op_sel * out_mult));
            chans[0].push((vec![AB::Expr::from(Goldilocks::from_u64(self.folded_addr)), folded.0, folded.1], is_head));
            // Channel 1 — the op-table-opening bus: the opening-row PROVIDES `[or_k, pz]` (or_mult), each op-table
            // opening-leaf READS `[leaf_key, o0, o1]` (+is_leaf). Balance ⇒ the leaf value == the sponge opening.
            chans[1].push((
                vec![cur[self.or_k()].clone(), cur[self.or_pz()].clone(), cur[self.or_pz() + 1].clone()],
                cur[self.or_mult()].clone(),
            ));
            chans[1].push((vec![cur[self.leaf_key()].clone(), o0, o1], is_leaf));
            // The NON-trace opening leaves (pubs/periodic/selectors) are in the TRACE (window/sel columns), not the
            // sponge stream — so the arith head PROVIDES them from cur[pw(..)]/cur[sel(..)] (−is_head). This
            // MEASURES whether the ~n_pub+n_periodic+2 provides fit on channel 1 (else they need the N_GROUPS split).
            if self.bind_window_leaves {
                let neg_head = AB::Expr::ZERO - cur[self.is_head()].clone();
                let oid = |x: u64| AB::Expr::from(Goldilocks::from_u64(x));
                // SPLIT the non-trace provides across N_GROUPS channels (key % N_GROUPS) so each carries ~n/N_GROUPS
                // (≤ budget), NOT all ~61 on one channel (log_nqc 6). The op-table leaf reads on its opening's
                // channel via is_ch in the full assembly; here we measure the PROVIDE degree the split achieves.
                let mut key = 1u64 << 30; // distinct address block for the non-trace openings (compose: any distinct)
                for i in 0..self.m.n_pub() {
                    let g = 3 + (key % N_GROUPS as u64) as usize;
                    chans[g].push((vec![oid(key), cur[self.m.pw(self.m.pub_pi() + i)].clone(), AB::Expr::ZERO], neg_head.clone()));
                    key += 1;
                }
                for i in 0..self.m.n_periodic() {
                    let (g, b) = (3 + (key % N_GROUPS as u64) as usize, self.m.periodic_base() + 2 * i);
                    chans[g].push((vec![oid(key), cur[self.m.pw(b)].clone(), cur[self.m.pw(b + 1)].clone()], neg_head.clone()));
                    key += 1;
                }
                for s in [self.m.sel(0), self.m.sel(2)] {
                    let g = 3 + (key % N_GROUPS as u64) as usize;
                    chans[g].push((vec![oid(key), cur[s].clone(), cur[s + 1].clone()], neg_head.clone()));
                    key += 1;
                }
            }
            // Channel 2 — the sponge FS-anchor: transcript PROVIDES `[w_gi_l, cur[l]]` (−w_sel_l), the opening-row
            // READS its 2 opening felts `[gi_base+i, pz_i]` (+or_sel). (The AA2b sponge bus, one reader over.)
            for l in 0..Self::RATE {
                chans[2].push((
                    vec![cur[self.w_gi(l)].clone(), cur[l].clone()],
                    AB::Expr::ZERO - cur[self.w_sel(l)].clone(),
                ));
            }
            for i in 0..2 {
                let gi_i = cur[self.or_gi()].clone() + AB::Expr::from(Goldilocks::from_u64(i as u64));
                chans[2].push((vec![gi_i, cur[self.or_pz() + i].clone()], or_sel.clone()));
            }
            for ch in chans {
                builder.push_local_interaction(ch);
            }
        }
    }

    /// **AA6 openings assembly AA1 — the cw=true sound reduced-opening fold** (the [`AssembledArithWrapAir`] analog
    /// one regime deeper, at `column_window = true` — the deep-tree fixed-point regime). `narrow_openings` drops the
    /// `2·n_terms` `pz` opening COLUMNS from the arith tile, so the DEEP fold `ro = Σ α^k·(pz − px)/(z − x)` is
    /// externalized to a narrow-tall [`crate::wrap::DeepFoldAir`] region in the trace SLACK (18 cols at `df_base`,
    /// gated by `df_sel`); its LAST row PROVIDES `[x, ro]` on a bus addressed by the query point `x`, and each arith
    /// head READS `[x_head, ro_col]` ([`OpeningsBci`] binds `QT_E == ro_col`). So `ro` is a fold computed in slack,
    /// not a free witness, AT cw=true (where the pz columns are gone — unlike [`AssembledArithWrapAir`], which sourced
    /// `pz` from the committed columns `narrow_arith` kept).
    ///
    /// **AA1 (this): composes** — the region + the `ro` bus (channel 0). AA1 leaves the region's `z`/`pz`/`px` INPUTS
    /// unbound (the sponge-opening FS-anchor + the `pz` re-provide + the `z`/`px` input-binding is the next increment,
    /// mirroring the AA3 arc). `folded_col`/`quot_col` stay free witnesses (the op-table region binds them later).
    pub(crate) struct AssembledOpeningsWrapCwAir {
        pub(crate) m: MonolithAir,
        /// The `2·RATE` opening-tag columns (AA2b): at each transcript absorb row `block·BLOCK` lane `l`, `(gi, sel)`
        /// for the opening felt the FS sponge absorbed there — the `w_gi`/`w_sel` witnessed tags are pinned to these
        /// (the periodic-out-of-interactions rule). Appended after the monolith periodics. (`AssembledCapWrapCwAir`'s
        /// `cap_periodics` analog; compose reads structure, so a dummy suffices.)
        pub(crate) op_periodics: Vec<Vec<Goldilocks>>,
        /// **Brick 5d** — when set, ALSO bind the epilogue: append the op-table region (13 `OpTableF2Air` cols +
        /// `op_sel`) computing `folded`, and a folded wiring bus binding `folded_col` to the op-table's fold. Flag-off
        /// (byte-identical) keeps the proven ro/z/px/pz-only assembly; flag-on adds the op-table epilogue binding.
        pub(crate) bind_optable: bool,
        /// The op-table wiring-bus address of the `folded` output wire (the arith head reads `folded_col` there);
        /// from `op_table_f2_trace` in the assembler, any distinct value for compose. Unused when `!bind_optable`.
        pub(crate) folded_addr: u64,
        /// **Brick 5d.3** — the op-table wiring-bus address of the `quot` output wire (the recomposed quotient(ζ) =
        /// Σ zps_i·chunk_i, appended to the op-table as more rows). The arith head reads `quot_col` here. Unused when
        /// `!bind_optable`.
        pub(crate) quot_addr: u64,
        /// **Brick 4d** — with the monolith's `narrow_ov`, the ov opened-row carrier is externalized: the z/px bus
        /// provides px=0 for TRACE terms (their dropped `px_source→ov_c`), and a leaf-hash→px bus binds each trace
        /// region row's px to the authenticated leaf lane, query-keyed by the held query point `lqk`(=x). Quotient
        /// terms keep px from `qc`. Flag-off byte-identical.
        pub(crate) narrow_ov: bool,
        /// **Brick 4d** — `3·RATE` leaf-hash provide tags (per rate lane: the two shared DEEP term ids
        /// `trm_trace(c)`/`trm_next(c)` + the committed-felt select bit), pinned to periodics. Unused when `!narrow_ov`.
        pub(crate) leaf_periodics: Vec<Vec<Goldilocks>>,
        /// **Tier-1 width merge** — when set, ALSO externalize the Merkle-cap product-mux (the biggest cw=true region):
        /// swap `OpeningsBci`→[`CapOpeningsBci`] (`CapMuxBci` emits nothing, `cap_c` freed), add the cap-row region +
        /// the SELECT bus (`cap_c[g]` == addressed cap-row) + the SPONGE-CAP bus (cap-row digest == FS-absorbed felt),
        /// with the monolith at `narrow_caps` (the `2^cap_height·4` cap COLUMNS gone). Flag-off byte-identical.
        pub(crate) bind_caps: bool,
        /// **Tier-1 width merge** — `2·CAP_RATE` sponge-cap provide tags (per rate lane: the cap digest felt's `gi`
        /// stream index + select bit), pinned to periodics. The `AssembledCapWrapCwAir` `cap_periodics`. Unused when off.
        pub(crate) cap_periodics: Vec<Vec<Goldilocks>>,
    }

    impl AssembledOpeningsWrapCwAir {
        /// Sponge rate = the transcript absorbs `RATE` felts/block; an OOD opening is a 2-felt F_p² run.
        pub(crate) const RATE: usize = 4;
        /// The witnessed reduced opening `ro` (F_p² pair) the arith head binds `QT_E` to (the `OpeningsBci` slot).
        pub(crate) fn ro_col(&self) -> usize {
            self.m.fused_w()
        }
        /// The epilogue α-fold result (free witness here; the op-table region binds it in a later increment).
        pub(crate) fn folded_col(&self) -> usize {
            self.m.fused_w() + 2
        }
        /// The recomposed quotient (free witness here; bound from the chunk-openings in a later increment).
        pub(crate) fn quot_col(&self) -> usize {
            self.m.fused_w() + 4
        }
        /// The DeepFold region's 18-col base (`[α, x, apow, z, pz, px, inv, t, ro]`), after ro/folded/quot.
        pub(crate) fn df_base(&self) -> usize {
            self.m.fused_w() + 6
        }
        /// Region row selector (1 on every DeepFold slack row).
        pub(crate) fn df_sel(&self) -> usize {
            self.df_base() + 18
        }
        /// Region FIRST-row marker (the fold boundary: `apow = 1`, `ro = t`).
        pub(crate) fn df_first(&self) -> usize {
            self.df_base() + 19
        }
        /// Region LAST-row marker (carries the full `ro`; the bus PROVIDE fires here).
        pub(crate) fn df_end(&self) -> usize {
            self.df_base() + 20
        }
        /// Witnessed arith-head marker (= the periodic `tf`, bound by a constraint) — gates the `ro` bus READ.
        pub(crate) fn is_head(&self) -> usize {
            self.df_base() + 21
        }
        /// **AA2** — the region row's term index `k` (a constrained counter: 0 at `df_first`, +1 down `df_trans`).
        /// With the query point `x`, `(x, term_idx)` addresses each region row to its committed term for the
        /// `z`/`px` input-binding (the per-query discriminator the op-table's ζ-opening binding did not need).
        pub(crate) fn term_idx(&self) -> usize {
            self.df_base() + 22
        }
        /// **AA2** — one-hot channel selector `g` routing the region row's `(z, px)` read to the channel its
        /// committed term's provide is on (`k % N_GROUPS`). Booleanity + `Σ == df_sel` pin exactly one per row.
        pub(crate) fn is_ch(&self, g: usize) -> usize {
            self.df_base() + 23 + g
        }
        /// **AA2b** — the SHARED opening-row region base (after the DeepFold region + input-binding router). One row
        /// per DEEP opening (term k): `[gi_base, pz0, pz1, or_sel, or_k, or_mult]`. It READS its opening felt from
        /// the sponge FS-anchor (FS→row, 1:1) and RE-PROVIDES `pz` to the N per-query DeepFold rows (row→folds, 1:N).
        pub(crate) fn or_base(&self) -> usize {
            self.df_base() + 23 + N_GROUPS
        }
        /// The opening-row's `gi` of its `k=0` felt (= `2·term`; the sponge balance forces it).
        pub(crate) fn or_gi(&self) -> usize {
            self.or_base()
        }
        /// The opening-row's `pz` (F_p² pair) — the OOD opening, bound to the FS-absorbed felt + re-provided.
        pub(crate) fn or_pz(&self) -> usize {
            self.or_base() + 1
        }
        /// Opening-row region selector (gates the sponge READ + the pz re-provide).
        pub(crate) fn or_sel(&self) -> usize {
            self.or_base() + 3
        }
        /// The DEEP term index `k` this opening-row represents (the pz-bus address, query-independent).
        pub(crate) fn or_k(&self) -> usize {
            self.or_base() + 4
        }
        /// The pz re-provide multiplicity (−#queries: every query's DeepFold row reads this opening once).
        pub(crate) fn or_mult(&self) -> usize {
            self.or_base() + 5
        }
        /// The sponge-tag region base (after the opening-row region): `2·RATE` witnessed tags pinned to `op_periodics`.
        pub(crate) fn st_base(&self) -> usize {
            self.or_base() + 6
        }
        /// Witnessed sponge `gi` tag for rate lane `l` — pinned to `op_periodics[2l]`.
        pub(crate) fn w_gi(&self, l: usize) -> usize {
            self.st_base() + 2 * l
        }
        /// Witnessed sponge `sel` tag for rate lane `l` — pinned to `op_periodics[2l+1]` (1 iff lane `l` absorbed
        /// an opening felt in this transcript block).
        pub(crate) fn w_sel(&self, l: usize) -> usize {
            self.st_base() + 2 * l + 1
        }
        /// The periodic index where the appended opening-tag columns begin.
        pub(crate) fn op_periodic_base(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m)
        }
        /// **Brick 5d** — the op-table region base (13 `OpTableF2Air` cols + `op_sel`), appended after the sponge
        /// tags (only present when `bind_optable`). Mirrors [`OpTableBindCwAir`]'s region one assembly deeper.
        pub(crate) fn op_base(&self) -> usize {
            self.st_base() + 2 * Self::RATE
        }
        pub(crate) fn op_sel(&self) -> usize {
            self.op_base() + 13
        }
        /// **Brick 5d.2** — marks an op-table TRACE opening leaf (Main{0}/Main{1}): reads its opening at `leaf_key`
        /// (= the DEEP term index) from the shared opening-row's `pz` provide (the pz channel — the same FS-anchored
        /// provide the DeepFold folds), so the leaf value binds to the committed opening. Non-trace leaves use `op_is_ch`.
        pub(crate) fn is_tr_leaf(&self) -> usize {
            self.op_base() + 14
        }
        /// **Brick 5d.2** — the op-table opening-leaf's bus read address: the DEEP term index for a trace leaf, or
        /// the canonical `open_id` for a non-trace leaf.
        pub(crate) fn leaf_key(&self) -> usize {
            self.op_base() + 15
        }
        /// **Brick 5d.2** — one-hot channel selector routing a NON-trace opening leaf's read to the split channel
        /// its committed opening is provided on (`(open_id − OPEN_BASE) % N_GROUPS`); the bus balance forces the match.
        pub(crate) fn op_is_ch(&self, g: usize) -> usize {
            self.op_base() + 16 + g
        }
        /// **Brick 4d** — the narrow_ov column base (after the whole ro/DeepFold/opening/optable layout).
        pub(crate) fn nov_base(&self) -> usize {
            self.m.fused_w() + 6 + 18 + 4 + 1 + N_GROUPS + 6 + 2 * Self::RATE
                + if self.bind_optable { 16 + N_GROUPS } else { 0 }
        }
        /// The HELD query point `lqk`(=x): bound to `x_head` at the arith head + held across the super-tile so the
        /// leaf-hash→px bus keys are query-unique.
        pub(crate) fn held_lqk(&self) -> usize {
            self.nov_base()
        }
        /// On a DeepFold region row: 1 iff its term is a QUOTIENT term (px kept on the z/px bus from `qc`); 0 for a
        /// TRACE term (px=0 on the z/px bus, bound via the leaf-hash bus instead).
        pub(crate) fn df_is_quot(&self) -> usize {
            self.nov_base() + 1
        }
        /// leaf-hash provide tags: per rate lane, the two shared DEEP term ids `trm_trace(c)`/`trm_next(c)` + the
        /// committed-felt select bit (pinned to `leaf_periodics`).
        pub(crate) fn w_term0(&self, l: usize) -> usize {
            self.nov_base() + 2 + 3 * l
        }
        pub(crate) fn w_term1(&self, l: usize) -> usize {
            self.nov_base() + 3 + 3 * l
        }
        pub(crate) fn w_lsel(&self, l: usize) -> usize {
            self.nov_base() + 4 + 3 * l
        }
        /// The periodic index where `leaf_periodics` starts (after the monolith periodics + the `2·RATE` op tags).
        pub(crate) fn leaf_periodic_base(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m) + 2 * Self::RATE
        }

        // --- Tier-1 width merge: the cap-region (bind_caps) — appended after ALL prior regions (incl. ov). ---
        /// Cap-absorb rate = the sponge `RATE` (a cap entry is a 4-felt run absorbed into 4 rate lanes).
        pub(crate) const CAP_RATE: usize = 4;
        /// The cap-region base: the cap-row `[cap_id, entry_idx, digest[4], cap_mult]` (7) + `cap_sel` (1) + `gi_base`
        /// (1) + `2·CAP_RATE` sponge-cap tags. The arith-head marker is REUSED from the openings `is_head` (df_base+21).
        pub(crate) fn cap_base(&self) -> usize {
            self.nov_base() + if self.narrow_ov { 2 + 3 * Self::RATE } else { 0 }
        }
        /// Cap-row region selector (1 on every cap-row slack row; gates the digest READ + the entry PROVIDE).
        pub(crate) fn cap_sel_c(&self) -> usize {
            self.cap_base() + 7
        }
        /// The cap-row's `gi` of its `k=0` digest felt (free witness; the SPONGE-CAP balance forces it).
        pub(crate) fn cap_gi_base(&self) -> usize {
            self.cap_base() + 8
        }
        /// Sponge-cap tags PINNED to `cap_periodics`: per rate lane, the FS-stream `gi` index + the select bit.
        pub(crate) fn cap_w_gi(&self, l: usize) -> usize {
            self.cap_base() + 9 + 2 * l
        }
        pub(crate) fn cap_w_sel(&self, l: usize) -> usize {
            self.cap_base() + 9 + 2 * l + 1
        }
        /// The periodic index where `cap_periodics` starts (after monolith + op tags + [narrow_ov leaf tags]).
        pub(crate) fn cap_periodic_base(&self) -> usize {
            BaseAir::<Goldilocks>::num_periodic_columns(&self.m) + 2 * Self::RATE
                + if self.narrow_ov { 3 * Self::RATE } else { 0 }
        }
        /// The per-opening `(cap_id, cap_c offset, index shift, index bits)` for the SELECT bus (trace, quot, then
        /// each commit round) — the `AssembledCapWrapCwAir::openings` map. `cap_c` is the pre-existing carrier bound
        /// to the Merkle terminal; the SELECT bus re-binds it to the addressed committed cap entry.
        pub(crate) fn cap_openings(&self) -> Vec<(usize, usize, usize, usize)> {
            let mut v = vec![
                (0, 0, self.m.input_depth(), self.m.cap_height),
                (1, 4, self.m.input_depth(), self.m.cap_height),
            ];
            for r in 0..self.m.cm_rounds() {
                v.push((2 + r, 8 + 4 * r, self.m.commit_shift(r), self.m.commit_bits(r)));
            }
            v
        }
    }

    impl BaseAir<Goldilocks> for AssembledOpeningsWrapCwAir {
        fn width(&self) -> usize {
            // ro/folded/quot(6) + DeepFoldAir region(18) + df_sel/df_first/df_end/is_head(4) + term_idx(1)
            // + is_ch(N_GROUPS) + opening-row(6) + 2·RATE sponge tags (+ brick 5d op-table 13 + op_sel + is_tr_leaf
            // + leaf_key + op_is_ch(N_GROUPS)); (+ brick 4d held_lqk + df_is_quot + 3·RATE leaf tags when narrow_ov);
            // (+ Tier-1 merge cap-row 7 + cap_sel + gi_base + 2·CAP_RATE tags when bind_caps).
            self.cap_base() + if self.bind_caps { 9 + 2 * Self::CAP_RATE } else { 0 }
        }
        fn num_public_values(&self) -> usize {
            BaseAir::<Goldilocks>::num_public_values(&self.m)
        }
        fn num_periodic_columns(&self) -> usize {
            self.cap_periodic_base() + if self.bind_caps { 2 * Self::CAP_RATE } else { 0 }
        }
        fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
            let mut p = BaseAir::<Goldilocks>::periodic_columns(&self.m);
            p.extend(self.op_periodics.iter().cloned());
            if self.narrow_ov {
                p.extend(self.leaf_periodics.iter().cloned());
            }
            if self.bind_caps {
                p.extend(self.cap_periodics.iter().cloned());
            }
            p
        }
    }

    impl<AB: AirBuilder<F = Goldilocks> + p3_lookup::InteractionBuilder> Air<AB> for AssembledOpeningsWrapCwAir {
        fn eval(&self, builder: &mut AB) {
            // (1) The narrow monolith: `OpeningsBci` externalizes the arith fold's `ro` (bound below), the epilogue's
            // `folded`, and the recomposed `quot` to slack columns — the `2·n_terms` pz opening columns are GONE. At
            // cw=true `eval_bci` sources the inner-pis from the committed window (`cur[pw(i)]`), so the delegated
            // `InlineBci` cap-mux reads the window, not the empty `public_values()`. Tier-1 merge: when `bind_caps`,
            // `CapOpeningsBci` ALSO externalizes the cap-mux (`cap_c` freed; re-bound by the cap-region buses below).
            let (ro_col, folded_col, quot_col) = (self.ro_col(), self.folded_col(), self.quot_col());
            if self.bind_caps {
                self.m.eval_bci(builder, &CapOpeningsBci { ro_col, folded_col, quot_col });
            } else {
                self.m.eval_bci(builder, &OpeningsBci { ro_col, folded_col, quot_col });
            }

            let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
            let nxt: Vec<AB::Expr> = builder.main().next_slice().iter().map(|&x| x.into()).collect();
            let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
            let one = AB::Expr::ONE;
            let we = AB::Expr::from(Goldilocks::from_u64(7)); // F_p² : X² = 7
            let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
                (
                    a.0.clone() * b.0.clone() + we.clone() * a.1.clone() * b.1.clone(),
                    a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
                )
            };
            let db = self.df_base();
            let gg = |r: &[AB::Expr], o: usize| (r[db + o].clone(), r[db + o + 1].clone());

            // (2) Region markers — booleans; `is_head` bound to the periodic `tf` (so the bus READ is gated by the
            // COLUMN, not the periodic — the lookup prover feeds an empty periodic slice to aux gen). Transitions
            // stay WITHIN a region (`df_sel · (1 − df_end)`), so the fold never carries across a region boundary.
            let df_sel = cur[self.df_sel()].clone();
            let df_first = cur[self.df_first()].clone();
            let df_end = cur[self.df_end()].clone();
            let is_head = cur[self.is_head()].clone();
            for mk in [&df_sel, &df_first, &df_end, &is_head] {
                builder.assert_zero(mk.clone() * (mk.clone() - one.clone()));
            }
            builder.assert_zero(is_head.clone() - p[self.m.m_tf()].clone());
            let df_trans = df_sel.clone() * (one.clone() - df_end.clone());

            // (3) The DeepFold region (mirrors `crate::wrap::DeepFoldAir`, gated to the slack rows): each term is a
            // ROW carrying `apow = α^k` + the running sum `ro`, at constant width. `z`/`pz`/`px` are FREE here (AA1).
            let (alpha, x) = (gg(&cur, 0), gg(&cur, 2));
            let (apow, z, pz, px, inv, t, ro) = (
                gg(&cur, 4), gg(&cur, 6), gg(&cur, 8), gg(&cur, 10), gg(&cur, 12), gg(&cur, 14), gg(&cur, 16),
            );
            // α, x constant across the fold.
            for i in 0..4 {
                builder.when_transition().assert_zero(df_trans.clone() * (nxt[db + i].clone() - cur[db + i].clone()));
            }
            // apow = α^k (running product), boundary α^0 = 1.
            builder.assert_zero(df_first.clone() * (apow.0.clone() - one.clone()));
            builder.assert_zero(df_first.clone() * apow.1.clone());
            let ap = emul(apow.clone(), alpha);
            builder.when_transition().assert_zero(df_trans.clone() * (gg(&nxt, 4).0 - ap.0));
            builder.when_transition().assert_zero(df_trans.clone() * (gg(&nxt, 4).1 - ap.1));
            // inv = 1/(z − x): inv·(z − x) == 1.
            let chk = emul(inv.clone(), (z.0.clone() - x.0.clone(), z.1.clone() - x.1.clone()));
            builder.assert_zero(df_sel.clone() * (chk.0 - one.clone()));
            builder.assert_zero(df_sel.clone() * chk.1);
            // t = apow · (pz − px) · inv (the term's DEEP contribution).
            let tv = emul(emul(apow, (pz.0.clone() - px.0.clone(), pz.1.clone() - px.1.clone())), inv);
            builder.assert_zero(df_sel.clone() * (t.0.clone() - tv.0));
            builder.assert_zero(df_sel.clone() * (t.1.clone() - tv.1));
            // ro = running sum of t; boundary ro_0 = t_0; transition ro' = ro + t'.
            builder.assert_zero(df_first.clone() * (ro.0.clone() - t.0.clone()));
            builder.assert_zero(df_first.clone() * (ro.1.clone() - t.1.clone()));
            builder.when_transition().assert_zero(df_trans.clone() * (gg(&nxt, 16).0 - (ro.0.clone() + gg(&nxt, 14).0)));
            builder.when_transition().assert_zero(df_trans.clone() * (gg(&nxt, 16).1 - (ro.1.clone() + gg(&nxt, 14).1)));

            // (4) term_idx counter (0 at df_first, +1 down df_trans) + is_ch one-hot (the input-binding router).
            let term_idx = cur[self.term_idx()].clone();
            let is_ch: Vec<AB::Expr> = (0..N_GROUPS).map(|g| cur[self.is_ch(g)].clone()).collect();
            builder.assert_zero(df_first.clone() * term_idx.clone());
            builder
                .when_transition()
                .assert_zero(df_trans.clone() * (nxt[self.term_idx()].clone() - term_idx.clone() - one.clone()));
            let mut ch_sum = AB::Expr::ZERO;
            for c in &is_ch {
                builder.assert_zero(c.clone() * (c.clone() - one.clone()));
                ch_sum = ch_sum + c.clone();
            }
            builder.assert_zero(ch_sum - df_sel.clone());

            // (4b) Opening-row markers (AA2b) + the periodic-PINNED sponge tags (the periodic-out-of-interactions
            // rule: witness the columns, bind them by constraint, then use the COLUMNS in the bus). `w_sel_l` is thus
            // 0/1 from the periodic, `w_gi_l` the FS-stream index of the opening felt absorbed at (block, lane l).
            let or_sel = cur[self.or_sel()].clone();
            builder.assert_zero(or_sel.clone() * (or_sel.clone() - one.clone()));
            let pbase = self.op_periodic_base();
            for l in 0..Self::RATE {
                builder.assert_zero(cur[self.w_gi(l)].clone() - p[pbase + 2 * l].clone());
                builder.assert_zero(cur[self.w_sel(l)].clone() - p[pbase + 2 * l + 1].clone());
            }

            // (5) The buses. **Channel 0 = the `ro` bus** (AA1), addressed by the query point `x`: the region's LAST
            // row PROVIDES `[x, ro]` (−df_end), each arith head READS `[x_head, ro_col]` (+is_head), where
            // `x_head = GEN·qt_acc[lg−1]` is the head's committed query point (imaginary 0). Balance ⇒ `ro_col` == the
            // slack fold. **Channels 1..=N_GROUPS = the AA2 `z`/`px` input-binding:** the head PROVIDES its committed
            // `(z, px)` per term k (address `(x_head, k)`, −is_head) on channel `k % N_GROUPS`, the region row READS
            // its bundle (address `(x, term_idx)`, +is_ch) — so the fold's `z`/`px` are the REAL committed values.
            // At cw=true `z` is re-derived from ζ = the committed WINDOW `cur[pw(2)],cur[pw(3)]` (NOT the empty `pis`
            // — the cw=false arith wrap read `pis[2]`): `= ζ` (trace-ζ + quotient terms) or `ζ·g_trace` (the trace-ζ_next
            // block `[trm_next_base, trm_quot_base)`); `px` is SOURCED from the authenticated `ov`/`qc` carrier
            // (`px_source(k)`). `pz` is NOT bound here (it left the tile) — the opening-row region + the pz/sponge
            // buses bind the fold's `pz` to the FS-absorbed opening in the next increment (AA2b).
            let x_head =
                AB::Expr::from(<Goldilocks as Field>::GENERATOR) * cur[self.m.qt_acc() + self.m.lg() - 1].clone();
            let ro_read = (cur[self.ro_col()].clone(), cur[self.ro_col() + 1].clone());
            let g_trace = AB::Expr::from(Goldilocks::two_adic_generator(self.m.cm_rounds() - self.m.is_zk));
            let (zeta0, zeta1) = (cur[self.m.pw(2)].clone(), cur[self.m.pw(3)].clone());

            // Channels: 0 ro, 1..=N_GROUPS z/px, N_GROUPS+1 pz, N_GROUPS+2 sponge; then brick 5d appends the op-table
            // folded wiring bus (N_GROUPS+3) + the N_GROUPS non-trace-leaf split channels (N_GROUPS+4 .. 2·N_GROUPS+4);
            // then the Tier-1 merge caps SELECT + SPONGE-CAP (2), then narrow_ov's leaf-hash (LAST — so `n_chan−1`
            // stays the leaf-hash index regardless of bind_caps). caps base = right after the op-table channels.
            let caps_sel_ch = N_GROUPS + 3 + if self.bind_optable { N_GROUPS + 1 } else { 0 };
            let n_chan = caps_sel_ch + if self.bind_caps { 2 } else { 0 } + if self.narrow_ov { 1 } else { 0 };
            let mut chans: Vec<Vec<(Vec<AB::Expr>, AB::Expr)>> = vec![Vec::new(); n_chan];
            // Channel 0 — the ro bus.
            chans[0].push((vec![x.0.clone(), x.1.clone(), ro.0.clone(), ro.1.clone()], AB::Expr::ZERO - df_end.clone()));
            chans[0].push((vec![x_head.clone(), AB::Expr::ZERO, ro_read.0, ro_read.1], is_head.clone()));
            // Channels 1..=N_GROUPS — the z/px input-binding. Head PROVIDES committed term k on channel k%N_GROUPS.
            for k in 0..self.m.n_terms {
                let (z0, z1) = if k >= self.m.trm_next_base() && k < self.m.trm_quot_base() {
                    (zeta0.clone() * g_trace.clone(), zeta1.clone() * g_trace.clone())
                } else {
                    (zeta0.clone(), zeta1.clone())
                };
                // narrow_ov: TRACE terms (k < trm_quot_base) have their `ov_c` px carrier DROPPED — provide px=0
                // (bound via the leaf-hash bus below); QUOTIENT terms keep px from the `qc` carrier (px_source valid).
                let px_slot = if self.narrow_ov && k < self.m.trm_quot_base() {
                    AB::Expr::ZERO
                } else {
                    cur[self.m.px_source(k)].clone()
                };
                let head_provide = vec![
                    x_head.clone(),
                    AB::Expr::ZERO,
                    AB::Expr::from(Goldilocks::from_u64(k as u64)),
                    z0,
                    z1,
                    px_slot,
                ];
                chans[k % N_GROUPS + 1].push((head_provide, AB::Expr::ZERO - is_head.clone()));
            }
            // The region row READS its (z, px) bundle (region z at db+6, px at db+10) on its is_ch channel.
            // narrow_ov: a TRACE region row (df_is_quot=0) reads px=0 here (its px is bound via the leaf-hash bus);
            // a QUOTIENT region row (df_is_quot=1) reads its real px `cur[db+10]` (bound to `qc` via the head provide).
            let region_px = if self.narrow_ov {
                cur[self.df_is_quot()].clone() * cur[db + 10].clone()
            } else {
                cur[db + 10].clone()
            };
            let region_read = vec![
                x.0.clone(),
                x.1.clone(),
                term_idx.clone(),
                cur[db + 6].clone(),
                cur[db + 7].clone(),
                region_px,
            ];
            for g in 0..N_GROUPS {
                chans[g + 1].push((region_read.clone(), is_ch[g].clone()));
            }

            // **Channel N_GROUPS+1 = the pz bus** (AA2b, query-INDEPENDENT): the shared opening-row PROVIDES `[k, pz]`
            // (mult `or_mult = −#queries`), each per-query DeepFold region row READS `[term_idx, cur[db+8], cur[db+9]]`
            // (mult `df_sel`) — so the fold's `pz` (used at `db+8/9`) is the opening-row's `pz`. The 1:N re-provide (a
            // shared opening folded by every query) that the caps SELECT bus does for a shared cap.
            let or_pz = (cur[self.or_pz()].clone(), cur[self.or_pz() + 1].clone());
            chans[N_GROUPS + 1].push((
                vec![cur[self.or_k()].clone(), or_pz.0.clone(), or_pz.1.clone()],
                cur[self.or_mult()].clone(),
            ));
            chans[N_GROUPS + 1].push((
                vec![term_idx.clone(), cur[db + 8].clone(), cur[db + 9].clone()],
                df_sel.clone(),
            ));

            // **Channel N_GROUPS+2 = the sponge-opening FS-anchor** (AA2b): on each transcript absorb row, per rate
            // lane `l` PROVIDE `[w_gi_l, cur[l]]` (mult −w_sel_l) — `cur[l]` the real FS-absorbed rate lane; the
            // opening-row READS its 2 opening felts `[gi_base+i, pz_i]` (mult +or_sel). Balance on `(gi, value)` ⇒
            // every opening-row `pz` felt == the felt the sponge absorbed at that stream position ⇒ the fold's `pz`
            // (via the pz bus) == the FS opening. Sound. (The `AssembledCapWrapCwAir` sponge-cap bus, one region over.)
            for l in 0..Self::RATE {
                chans[N_GROUPS + 2].push((
                    vec![cur[self.w_gi(l)].clone(), cur[l].clone()],
                    AB::Expr::ZERO - cur[self.w_sel(l)].clone(),
                ));
            }
            for i in 0..2 {
                let gi_i = cur[self.or_gi()].clone() + AB::Expr::from(Goldilocks::from_u64(i as u64));
                chans[N_GROUPS + 2].push((vec![gi_i, cur[self.or_pz() + i].clone()], or_sel.clone()));
            }

            // (6) **Brick 5d — the op-table epilogue binding.** The `OpTableF2Air` region (op_sel-gated) computes
            // `folded` (the α-fold of the constraint values c_k) on slack rows; a folded wiring bus (channel
            // N_GROUPS+3) binds `folded_col` to the op-table's fold wire, so the epilogue's `folded·inv_van == quot`
            // (checked by `OpeningsBci`) reads a fold actually computed in the op-table — not a free witness. The
            // op-table's OPENING LEAVES (its c_k inputs) stay free here (5d.1 compose); the opening-leaf binding
            // (trace leaves at term_idx, non-trace via the N_GROUPS split) + the quot recompose are the next bricks.
            if self.bind_optable {
                let ob = self.op_base();
                let (is_mul, is_add, is_sub) = (cur[ob].clone(), cur[ob + 1].clone(), cur[ob + 2].clone());
                let (out_addr, o0, o1) = (cur[ob + 3].clone(), cur[ob + 4].clone(), cur[ob + 5].clone());
                let (a_addr, a0, a1) = (cur[ob + 6].clone(), cur[ob + 7].clone(), cur[ob + 8].clone());
                let (b_addr, b0, b1) = (cur[ob + 9].clone(), cur[ob + 10].clone(), cur[ob + 11].clone());
                let out_mult = cur[ob + 12].clone();
                let op_sel = cur[self.op_sel()].clone();
                builder.assert_zero(op_sel.clone() * (op_sel.clone() - one.clone()));
                for s in [&is_mul, &is_add, &is_sub] {
                    builder.assert_zero(op_sel.clone() * s.clone() * (s.clone() - one.clone()));
                }
                let is_op = is_mul.clone() + is_add.clone() + is_sub.clone();
                builder.assert_zero(op_sel.clone() * is_op.clone() * (is_op.clone() - one.clone()));
                builder.assert_zero(op_sel.clone() * is_mul.clone() * (o0.clone() - (a0.clone() * b0.clone() + we.clone() * a1.clone() * b1.clone())));
                builder.assert_zero(op_sel.clone() * is_mul.clone() * (o1.clone() - (a0.clone() * b1.clone() + a1.clone() * b0.clone())));
                builder.assert_zero(op_sel.clone() * is_add.clone() * (o0.clone() - (a0.clone() + b0.clone())));
                builder.assert_zero(op_sel.clone() * is_add.clone() * (o1.clone() - (a1.clone() + b1.clone())));
                builder.assert_zero(op_sel.clone() * is_sub.clone() * (o0.clone() - (a0.clone() - b0.clone())));
                builder.assert_zero(op_sel.clone() * is_sub.clone() * (o1.clone() - (a1.clone() - b1.clone())));
                // The folded wiring bus (channel N_GROUPS+3): the op-table reads its 2 operands (+op_sel·is_op) and
                // DEFINES its output (op_sel·out_mult, −fanout INCLUDING the head's folded read); the arith head READS
                // folded_col at folded_addr (+is_head). Balance ⇒ folded_col == the op-table's computed folded wire.
                let read_mult = op_sel.clone() * is_op;
                let folded = (cur[self.folded_col()].clone(), cur[self.folded_col() + 1].clone());
                let wch = N_GROUPS + 3;
                chans[wch].push((vec![a_addr, a0, a1], read_mult.clone()));
                chans[wch].push((vec![b_addr, b0, b1], read_mult));
                chans[wch].push((vec![out_addr, o0, o1], op_sel * out_mult));
                chans[wch].push((
                    vec![AB::Expr::from(Goldilocks::from_u64(self.folded_addr)), folded.0, folded.1],
                    is_head.clone(),
                ));
                // Brick 5d.3: the head ALSO reads quot_col at quot_addr (the op-table's recomposed quotient(ζ) =
                // Σ zps_i·chunk_i output wire, appended to the op-table as more rows). Balance ⇒ quot_col == the
                // op-table's quot, so the epilogue `folded·inv_van == quot` checks a recompose actually computed in
                // the op-table from BOUND quot-chunk openings + qwt weights (not a free witness).
                let quot = (cur[self.quot_col()].clone(), cur[self.quot_col() + 1].clone());
                chans[wch].push((
                    vec![AB::Expr::from(Goldilocks::from_u64(self.quot_addr)), quot.0, quot.1],
                    is_head.clone(),
                ));

                // --- Brick 5d.2: the op-table OPENING-LEAF binding (the op-table's `c_k` inputs bound to the real
                // FS-absorbed openings). Every op-table leaf reads its opening on a bus; the head/opening-row provides
                // force the value. TWO mechanisms, reconciled by address space (term_idx < n_terms ≪ OPEN_BASE):
                //   • TRACE leaves (Main{0}/Main{1}) read `[term_idx, o0, o1]` on the pz channel (N_GROUPS+1) — the
                //     SHARED opening-row's FS-anchored pz provide, the same one the DeepFold folds (no 2nd anchor);
                //   • NON-trace leaves (Public/Periodic/selector) read `[open_id, o0, o1]` on their is_ch split channel;
                //     the arith head PROVIDES each from the cw=true window, SPLIT across N_GROUPS channels (the 5c
                //     pattern) so no single row/channel exceeds the degree budget.
                let leaf_key = cur[self.leaf_key()].clone();
                let (lv0, lv1) = (cur[ob + 4].clone(), cur[ob + 5].clone()); // the leaf's out value (= o0, o1)
                let is_tr_leaf = cur[self.is_tr_leaf()].clone();
                builder.assert_zero(is_tr_leaf.clone() * (is_tr_leaf.clone() - one.clone()));
                chans[N_GROUPS + 1].push((vec![leaf_key.clone(), lv0.clone(), lv1.clone()], is_tr_leaf));

                let nt = N_GROUPS + 4; // the non-trace split channels: nt .. nt+N_GROUPS
                let neg_head = AB::Expr::ZERO - is_head.clone();
                let (wu, npu, nperu) = (self.m.w_inner() as u64, self.m.n_pub() as u64, self.m.n_periodic() as u64);
                let route = |a: u64| ((a - OPEN_BASE) as usize) % N_GROUPS; // an opening's split channel
                let oidv = |x: u64| AB::Expr::from(Goldilocks::from_u64(x));
                for i in 0..self.m.n_pub() {
                    let a = open_id((2, i as u64), wu, npu, nperu);
                    chans[nt + route(a)].push((vec![oidv(a), cur[self.m.pw(self.m.pub_pi() + i)].clone(), AB::Expr::ZERO], neg_head.clone()));
                }
                for i in 0..self.m.n_periodic() {
                    let a = open_id((3, i as u64), wu, npu, nperu);
                    let b = self.m.periodic_base() + 2 * i;
                    chans[nt + route(a)].push((vec![oidv(a), cur[self.m.pw(b)].clone(), cur[self.m.pw(b + 1)].clone()], neg_head.clone()));
                }
                // The selector openings: is_first ← sel(0), is_last ← sel(2) (trace cols), is_trans ← ζ (window pw(2/3)):
                // is_trans(ζ) = ζ − g^{-1} (the AssembledWrapAir formula, ζ from the cw=true window not empty pis).
                for (key, s) in [((4u8, 0u64), self.m.sel(0)), ((5u8, 0u64), self.m.sel(2))] {
                    let a = open_id(key, wu, npu, nperu);
                    chans[nt + route(a)].push((vec![oidv(a), cur[s].clone(), cur[s + 1].clone()], neg_head.clone()));
                }
                let g_inv = AB::Expr::from(Goldilocks::two_adic_generator(self.m.cm_rounds() - self.m.is_zk).inverse());
                let a6 = open_id((6, 0), wu, npu, nperu);
                chans[nt + route(a6)].push((
                    vec![oidv(a6), cur[self.m.pw(2)].clone() - g_inv, cur[self.m.pw(3)].clone()],
                    neg_head.clone(),
                ));
                // Brick 5d.3: the nqc qwt quotient-recompose weights zps_i (window pw(qwt_base+2i)) — non-trace
                // openings the op-table's recompose reads as leaves; provided from the cw=true window, split like the
                // rest. (The quot-chunk openings d0_i/d1_i are TRACE leaves at term_idx = trm_quot(i,j) — the same
                // is_tr_leaf mechanism as the trace openings, bound to the FS-anchored opening-rows.)
                for i in 0..self.m.nqc() {
                    let a = open_id((7, i as u64), wu, npu, nperu);
                    let qb = self.m.qwt_base() + 2 * i;
                    chans[nt + route(a)].push((vec![oidv(a), cur[self.m.pw(qb)].clone(), cur[self.m.pw(qb + 1)].clone()], neg_head.clone()));
                }
                // Non-trace leaf reads: one is_ch-routed read per split channel (gated; only the matching channel
                // fires). The head PROVIDES each non-trace opening once PER head (−is_head, ×n_heads total from the
                // constant window), so the single op-table leaf reads `is_ch·n_heads` to balance (the cw=false
                // `assemble_wrap` scaling). TRACE leaves differ: their opening-row provides ONCE (or_mult absorbs the
                // single op-table read), so the trace-leaf read above is `is_tr_leaf` (unscaled).
                let n_heads = AB::Expr::from(Goldilocks::from_u64(self.m.n_queries as u64));
                for g in 0..N_GROUPS {
                    let ich = cur[self.op_is_ch(g)].clone();
                    builder.assert_zero(ich.clone() * (ich.clone() - one.clone()));
                    chans[nt + g].push((vec![leaf_key.clone(), lv0.clone(), lv1.clone()], ich * n_heads.clone()));
                }
            }

            // **Brick 4d — the leaf-hash→px bus** (last channel, narrow_ov only). The ov opened-row carrier is
            // externalized: each TRACE term's px is bound to the authenticated input-Merkle leaf lane, query-keyed by
            // the held query point `lqk`(=x). Leaf-hash rows PROVIDE `[lqk, term, leaf_lane]` under BOTH shared DEEP
            // terms `trm_trace(c)`/`trm_next(c)` (−w_lsel); each trace region row READS `[x, term_idx, cur[db+10]]`
            // (+df_sel·(1−df_is_quot)). Balance ⇒ every trace region px == the leaf felt at its (query, column). `pz`
            // (bound by the sponge/pz buses) is unchanged; only `px` moves off the dropped `ov` carrier.
            if self.narrow_ov {
                let lhpx = n_chan - 1;
                let rate = Self::RATE;
                let pbase = self.leaf_periodic_base();
                let dq = cur[self.df_is_quot()].clone();
                builder.assert_zero(df_sel.clone() * dq.clone() * (dq.clone() - one.clone()));
                let held = cur[self.held_lqk()].clone();
                builder.assert_zero(is_head.clone() * (held.clone() - x_head.clone()));
                let hold = p[self.m.s_query()].clone() * (one.clone() - p[self.m.p_st_last()].clone());
                builder.when_transition().assert_zero(hold * (nxt[self.held_lqk()].clone() - held.clone()));
                for l in 0..rate {
                    builder.assert_zero(cur[self.w_term0(l)].clone() - p[pbase + 3 * l].clone());
                    builder.assert_zero(cur[self.w_term1(l)].clone() - p[pbase + 3 * l + 1].clone());
                    builder.assert_zero(cur[self.w_lsel(l)].clone() - p[pbase + 3 * l + 2].clone());
                }
                let mut lh: Vec<(Vec<AB::Expr>, AB::Expr)> = Vec::with_capacity(2 * rate + 1);
                for l in 0..rate {
                    let neg_sel = AB::Expr::ZERO - cur[self.w_lsel(l)].clone();
                    lh.push((vec![held.clone(), cur[self.w_term0(l)].clone(), cur[l].clone()], neg_sel.clone()));
                    lh.push((vec![held.clone(), cur[self.w_term1(l)].clone(), cur[l].clone()], neg_sel));
                }
                let df_is_trace = df_sel.clone() * (one.clone() - dq);
                lh.push((vec![x.0.clone(), term_idx.clone(), cur[db + 10].clone()], df_is_trace));
                chans[lhpx] = lh;
            }

            // (Tier-1 width merge) The cap-region + SELECT/SPONGE-CAP buses (bind_caps) — the `AssembledCapWrapCwAir`
            // eval one region deeper. `cap_c` (freed by `CapMuxBci`) is re-bound: SELECT ⇒ `cap_c[g]` == the
            // index-addressed committed cap entry; SPONGE-CAP ⇒ the cap-row digest == the FS-absorbed felt (auth == FS).
            if self.bind_caps {
                let cap_sponge_ch = caps_sel_ch + 1;
                let cr = self.cap_base();
                let cpb = self.cap_periodic_base();
                let caprate = Self::CAP_RATE;
                let cap_sel = cur[self.cap_sel_c()].clone();
                builder.assert_zero(cap_sel.clone() * (cap_sel.clone() - one.clone()));
                builder.assert_zero((one.clone() - cap_sel.clone()) * cur[cr + 6].clone());
                for l in 0..caprate {
                    builder.assert_zero(cur[self.cap_w_gi(l)].clone() - p[cpb + 2 * l].clone());
                    builder.assert_zero(cur[self.cap_w_sel(l)].clone() - p[cpb + 2 * l + 1].clone());
                }
                // SELECT (caps_sel_ch): the cap-row PROVIDES its entry (mult `cap_mult` = −count); each arith head
                // READS, per opening g, `[cap_id, index>>shift_g, cap_c[g]]` (mult `is_head`).
                chans[caps_sel_ch].push((
                    vec![cur[cr].clone(), cur[cr + 1].clone(), cur[cr + 2].clone(), cur[cr + 3].clone(), cur[cr + 4].clone(), cur[cr + 5].clone()],
                    cur[cr + 6].clone(),
                ));
                for (cap_id, cg_off, shift, bits) in self.cap_openings() {
                    let mut sel_idx = AB::Expr::ZERO;
                    for j in 0..bits {
                        sel_idx = sel_idx + cur[self.m.sb_b(shift + j)].clone() * AB::Expr::from(Goldilocks::from_u64(1u64 << j));
                    }
                    chans[caps_sel_ch].push((
                        vec![
                            AB::Expr::from(Goldilocks::from_u64(cap_id as u64)),
                            sel_idx,
                            cur[self.m.cap_c(cg_off)].clone(),
                            cur[self.m.cap_c(cg_off + 1)].clone(),
                            cur[self.m.cap_c(cg_off + 2)].clone(),
                            cur[self.m.cap_c(cg_off + 3)].clone(),
                        ],
                        is_head.clone(),
                    ));
                }
                // SPONGE-CAP (cap_sponge_ch): per rate lane PROVIDE `(gi, cur[l])` mult −sel; each cap-row READS its 4
                // digest felts `(gi_base+k, digest[k])` mult +cap_sel ⇒ the cap-row digest == the FS-absorbed felt.
                for l in 0..caprate {
                    chans[cap_sponge_ch].push((
                        vec![cur[self.cap_w_gi(l)].clone(), cur[l].clone()],
                        AB::Expr::ZERO - cur[self.cap_w_sel(l)].clone(),
                    ));
                }
                for k in 0..4 {
                    let gi_k = cur[self.cap_gi_base()].clone() + AB::Expr::from(Goldilocks::from_u64(k as u64));
                    chans[cap_sponge_ch].push((vec![gi_k, cur[cr + 2 + k].clone()], cap_sel.clone()));
                }
            }

            for ch in chans {
                builder.push_local_interaction(ch);
            }
        }
    }
}

#[cfg(feature = "recursion")]
pub(crate) use wrap_air::{
    native_witnessed, open_id, ArithWrapAir, AssembledArithWrapAir, AssembledCapWrapAir, AssembledCapWrapCwAir,
    AssembledOpeningsWrapCwAir, AssembledWrapAir, CapNarrowWrapAir, CapWrapAir, NarrowOpeningsWrapAir, NarrowOvBindCwAir,
    OpeningBindCwAir, OpTableBindCwAir, OpTableLeafBindCwAir, WrapAir,
    N_GROUPS, OPEN_BASE,
};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{Challenge, LOG_BLOWUP};
    use crate::lookup::prover::{
        combined_constraint_layout, prove_lookup, prove_lookup_lean, verify_lookup, verify_lookup_lean,
        LookupVerifyError,
    };
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
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize, narrow_arith: false, narrow_caps: false, narrow_openings: false, narrow_ov: false };
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

    /// **W2-assemble.2 brick 1 — the reused-region trace builder** (wrap-local; `--features recursion`).
    /// Assembles a REAL join-split inner's full reused-region (A–J) trace + public values via the exposed
    /// witness pipeline (`sim_full` + the `native_fri` extractors + `monolith_build_trace` + the ζ-selector
    /// fill), and SELF-VALIDATES the extracted witness — the pis layout matches `pis_count`, and the native
    /// symbolic OOD fold equals `quotient(ζ)`. This is the foundation the B/C/I-lookup swap builds on: the
    /// reused-region columns are correct; only B/C/I change. Returns `(air, trace, pis)`.
    #[cfg(feature = "recursion")]
    fn wrap_build_reused(
        config: &crate::recursion::native_fri::MyConfig,
        proof: &p3_uni_stark::Proof<crate::recursion::native_fri::MyConfig>,
        pvs: &[Val],
        narrow: bool, // NARROW-ARITH: drop the inline fold's inv/apow (the wrap externalizes the fold)
    ) -> (crate::recursion::monolith::MonolithAir, RowMajorMatrix<Val>, Vec<Val>) {
        use crate::joinsplit_air::{JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::sim_full;
        use crate::recursion::monolith::{monolith_build_trace, MonolithAir};
        use crate::recursion::native_fri::{
            epilogue_openings, eval_symbolic_native, multicol_query_terms, query_commit_merkle_all,
            query_fold_data, query_input_merkle, query_quotient_merkle, quotient_recompose_weights,
        };
        use p3_field::{BasedVectorSpace, PrimeField64};
        use p3_uni_stark::{get_symbolic_constraints, AirLayout};

        let inner = JoinSplitAir;
        let n_queries = proof.opening_proof.query_proofs.len();
        let (block_inputs, counts, binds, chs, index_binds, index_felts) = sim_full(config, proof, pvs);
        let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
        let (mut per_query, mut quot_paths, mut commit_data) = (Vec::new(), Vec::new(), Vec::new());
        let mut final0 = Challenge::ZERO;
        for q in 0..n_queries {
            let (terms, _x, alpha, ro, _w) = multicol_query_terms(config, &inner, proof, pvs, q);
            let (_ro2, rounds, _folded, f0) = query_fold_data(config, proof, pvs, q);
            let (_leaf, path, _ce) = query_input_merkle(config, proof, pvs, q);
            let (_ql, qpath, _qce, _qw) = query_quotient_merkle(config, proof, pvs, q);
            let cm = query_commit_merkle_all(config, proof, pvs, q);
            if q == 0 {
                final0 = f0;
            }
            let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
            per_query.push(((index, terms, alpha, ro, rounds), Val::ZERO, path));
            quot_paths.push(qpath);
            commit_data.push(cm);
        }
        let nqc = proof.opened_values.quotient_chunks.len();
        let constraints = get_symbolic_constraints::<Val, _>(&inner, AirLayout::from_air::<Val>(&inner));
        let air = MonolithAir {
            counts,
            binds,
            index_binds,
            n_queries,
            n_terms: 2 * WIDTH + 2 * nqc,
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
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize, narrow_arith: narrow, narrow_caps: false, narrow_openings: false, narrow_ov: false };
        let (eo_local, eo_next, is_first, is_last, is_trans, inv_van, eo_quot, eo_alpha, _z, eo_periodic) =
            epilogue_openings(config, &inner, proof, pvs);
        let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };

        // pis layout: FS challenges ‖ query indices ‖ final_poly(0) ‖ trace/quotient caps ‖ inner pubs ‖
        // commit-round caps ‖ periodic values at ζ ‖ (quotient-recompose weights if nqc>1).
        let mut pis = Vec::new();
        for ch in &chs {
            pis.extend_from_slice(ch);
        }
        pis.extend_from_slice(&index_felts);
        pis.extend_from_slice(&cc(final0));
        for e in proof.commitments.trace.roots().iter() {
            pis.extend_from_slice(e);
        }
        for e in proof.commitments.quotient_chunks.roots().iter() {
            pis.extend_from_slice(e);
        }
        pis.extend_from_slice(pvs);
        for cm in proof.opening_proof.commit_phase_commits.iter() {
            for e in cm.roots().iter() {
                pis.extend_from_slice(e);
            }
        }
        for pv in &eo_periodic {
            pis.extend_from_slice(&cc(*pv));
        }
        if nqc > 1 {
            for z in &quotient_recompose_weights(config, &inner, proof, pvs) {
                pis.extend_from_slice(&cc(*z));
            }
        }
        assert_eq!(pis.len(), air.pis_count(), "reused-region pis layout matches pis_count");

        // Native pre-check: the symbolic OOD fold on the extracted openings == quotient(ζ) — validates the
        // witness without a full prove (localizes any extraction/wiring bug).
        let pubs: Vec<Challenge> = pvs.iter().map(|&p| Challenge::from(p)).collect();
        let mut folded = Challenge::ZERO;
        for c in &air.constraints {
            folded = folded * eo_alpha
                + eval_symbolic_native(c, &eo_local, &eo_next, &pubs, &eo_periodic, is_first, is_last, is_trans);
        }
        assert_eq!(folded * inv_van, eo_quot, "reused-region PRE-CHECK: symbolic OOD fold == quotient(ζ)");

        // Build the trace + fill the witnessed Lagrange selectors at ζ (is_first/is_last/inv_van).
        let mut trace = monolith_build_trace(
            &air, &block_inputs, &per_query, chs[2], &index_felts, &quot_paths, &commit_data, &[], None,
        );
        let (isf, isl, iv) = (cc(is_first), cc(is_last), cc(inv_van));
        let (fw, sb) = (air.fused_w(), air.sel_base());
        for r in 0..air.height() {
            trace.values[r * fw + sb..r * fw + sb + 2].copy_from_slice(&isf);
            trace.values[r * fw + sb + 2..r * fw + sb + 4].copy_from_slice(&isl);
            trace.values[r * fw + sb + 4..r * fw + sb + 6].copy_from_slice(&iv);
        }
        (air, trace, pis)
    }

    /// **Arith-tile narrow-tall brick 3 — "matches native" on a REAL inner** (`--features recursion`). Build the
    /// monolith trace over a real join-split inner, read its arith-head row (`off = tr + 0·m_period`), and seed
    /// the narrow-tall `DeepFoldAir` with the SAME openings the wide arith tile committed (α, x, and each term's
    /// z/pz/px). The narrow-tall running sum `ro` reproduces the monolith's committed reduced opening `QT_E`
    /// (`= 0`) bit-for-bit — and the real-seeded trace proves. So the `9·n_terms`-COLUMN arith tile has a
    /// narrow-tall replacement faithful on REAL data, not just a synthetic model (the DEEP-fold analog of
    /// `op_table_f2_matches_native_epilogue`).
    #[cfg(feature = "recursion")]
    #[test]
    fn deep_fold_matches_monolith_arith_tile() {
        use crate::config::Challenge;
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use crate::wrap::{deep_fold_trace_from, DeepFoldAir};
        use p3_field::{BasedVectorSpace, Field};
        use p3_goldilocks::Goldilocks;
        use p3_uni_stark::{prove, verify};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (air, tr, _pis) = wrap_build_reused(&config, &proof, &pvs, false);

        // The first query's arith head row carries the entire DEEP reduced-opening fold + its committed QT_E.
        let width = tr.width;
        let off = air.tr(); // q = 0
        let row = |col: usize| tr.values[off * width + col];
        let gv = |col: usize| Challenge::from_basis_coefficients_fn(|i| row(col + i));

        let alpha = gv(air.qt_alpha());
        let x = Challenge::from(<Goldilocks as Field>::GENERATOR * row(air.qt_acc() + air.lg() - 1));
        let qt_e = gv(0); // QT_E = 0: the monolith's committed reduced opening `ro`
        let n = air.n_terms;
        // px is stored base-field (imaginary 0), exactly as the AIR reads `d = (pz − px, pz.1)`.
        let terms: Vec<(Challenge, Challenge, Challenge)> =
            (0..n).map(|k| (gv(air.z(k)), gv(air.pz(k)), Challenge::from(row(air.px(k))))).collect();

        // FAITHFULNESS: the narrow-tall fold's `ro` at the last real term equals the monolith's wide `QT_E`.
        let dft = deep_fold_trace_from(alpha, x, &terms, 0);
        let dw = dft.width;
        let ro_last = Challenge::from_basis_coefficients_fn(|i| dft.values[(n - 1) * dw + 16 + i]);
        assert_eq!(ro_last, qt_e, "narrow-tall DEEP fold `ro` must equal the monolith's committed `QT_E`");

        // …and the real-seeded narrow-tall trace proves through the production prover.
        let pc = crate::config::make_config();
        let dproof = prove(&pc, &DeepFoldAir, dft, &[]);
        assert!(verify(&pc, &DeepFoldAir, &dproof, &[]).is_ok(), "the real-seeded narrow-tall fold must verify");
    }

    /// **Caps narrow-tall brick — the LogUp cap-select MATCHES the monolith product-mux on a REAL inner**
    /// (`--features recursion`). The cap analog of `deep_fold_matches_monolith_arith_tile`, one region over, and
    /// the faithfulness gate for the caps track (the 85%-of-`column_window`-`fused_w` lever). Build the real
    /// join-split monolith trace; read its arith-head cap carriers `cap_c[g]` (the monolith's degree-`cap_height`
    /// product-mux result, `InlineBci::emit_capmux`); and for EVERY opening (trace, quotient, each of the
    /// `cm_rounds` commit rounds) independently select the entry the committed index bits address — `E =
    /// Σ_j bit(shift+j)·2^j`, entry `pis[cbase + E·4 + k]` — the narrow-tall selection. It reproduces `cap_c`
    /// BIT-FOR-BIT across all openings, so the columns→rows swap is faithful on the REAL multi-cap layout (many
    /// caps, real shifts/bits), not just the synthetic `cap_mux_*` model. Then a `CapMuxAir` seeded with the REAL
    /// (flattened) trace cap + the real selected cells PROVES + VERIFIES through the W1 lookup prover — real
    /// committed cap data selects + proves. (Binding the slack rows to the transcript-committed cap + removing the
    /// `2^cap_height·4` cap column-window is the assembly still ahead — the `DeepFoldBci`/AA-arc analog for caps.)
    #[cfg(feature = "recursion")]
    #[test]
    fn cap_mux_matches_monolith() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use crate::wrap::{cap_mux_trace, CapMuxAir};
        use p3_field::PrimeField64;
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (air, tr, pis) = wrap_build_reused(&config, &proof, &pvs, false);

        let width = tr.width;
        let off = air.tr(); // q = 0 arith head — where the cap-mux seeds cap_c
        let row = |col: usize| tr.values[off * width + col];
        // The entry index the committed index bits [shift .. shift+bits) address (the mux's selected `e`).
        let entry = |shift: usize, bits: usize| -> usize {
            (0..bits)
                .map(|j| {
                    let b = row(air.sb_b(shift + j)).as_canonical_u64();
                    assert!(b <= 1, "index bit sb_b({}) must be boolean, got {b}", shift + j);
                    (b as usize) << j
                })
                .sum()
        };

        // Reconstruct the monolith's openings list (the air.rs emit path, is_zk=0): (cg_off, shift, bits, cbase) —
        // trace + quotient at max height (shift = input_depth), then each commit round at its folded height.
        let mut openings = vec![
            (0usize, air.input_depth(), air.cap_height, air.cap_base()),
            (4, air.input_depth(), air.cap_height, air.qcap_base()),
        ];
        for r in 0..air.cm_rounds() {
            openings.push((8 + 4 * r, air.commit_shift(r), air.commit_bits(r), air.commit_cap_base(r)));
        }

        // FAITHFULNESS: for every opening, the index-addressed entry equals the monolith's product-mux carrier.
        for &(cg_off, shift, bits, cbase) in &openings {
            let e = entry(shift, bits);
            for k in 0..4 {
                assert_eq!(
                    row(air.cap_c(cg_off + k)),
                    pis[cbase + e * 4 + k],
                    "opening cg_off={cg_off}: narrow-tall select cap[E={e}][{k}] must equal the product-mux cap_c",
                );
            }
        }

        // …and the REAL cap selects + PROVES through the W1 lookup prover. Flatten the trace cap (2^cap_height
        // entries × 4 felts → scalar cells `cap[e·4+k]`); query the 4 cells of the selected trace entry E.
        let bits = air.cap_height;
        let flat: Vec<Val> = (0..((1usize << bits) * 4)).map(|c| pis[air.cap_base() + c]).collect();
        let e_tr = entry(air.input_depth(), bits);
        let queries: Vec<usize> = (0..4).map(|k| e_tr * 4 + k).collect();
        let cproof = prove_lookup(&CapMuxAir, cap_mux_trace(&flat, &queries), &[]);
        assert!(verify_lookup(&CapMuxAir, &cproof, &[]).is_ok(), "the real-cap LogUp select must verify");
        assert!(openings.len() == 2 + air.cm_rounds() && bits > 0);
    }

    /// **AA5 feasibility (matches-native) — the ordered sponge-cap bus's addressing map.** The FS-anchor that
    /// AA5 needs (bind the narrow-tall cap region to the caps the transcript ACTUALLY absorbed, so removing the
    /// pw cap columns keeps inner-auth non-vacuous) requires addressing each committed cap felt inside the
    /// transcript sponge. This confirms that map on a REAL join-split inner: `sim_cap_positions` records, per
    /// absorbed cap felt, its `(cap_id, entry, k, block, lane)`, and we assert `block_inputs[block][lane]` ==
    /// `roots()[entry][k]` BIT-FOR-BIT for all of them — trace, quotient, and every commit round. Coverage: the
    /// count matches the AIR's cap model (`2·2^cap_height·4 + Σ_r commit_cap_size(r)·4`). And the alignment
    /// finding that makes the in-circuit bus tractable: only the TRACE cap is misaligned (offset by the 3
    /// preamble scalars ⇒ entry 0 lands at rate lane 3 and straddles two blocks), while the quotient/commit caps
    /// each follow a sample-flush and are block-aligned (entry 0 at lane 0). So the ordered bus provides
    /// `cur[lane]` at row `block·BLOCK` with compile-time `(cap_id, entry, k)` tags — the FT_BIND pattern, one
    /// region deeper. (The in-circuit bus + region read is the next brick; this de-risks the addressing.)
    #[cfg(feature = "recursion")]
    #[test]
    fn cap_absorb_stream_matches_committed_caps() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::monolith::tests::sim_cap_positions;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (block_inputs, positions) = sim_cap_positions(&config, &proof, &pvs);

        // The committed cap felt for (cap_id, entry, k): trace (0), quotient (1), commit round r (2+r).
        let committed = |cap_id: usize, entry: usize, k: usize| -> Val {
            match cap_id {
                0 => proof.commitments.trace.roots()[entry][k],
                1 => proof.commitments.quotient_chunks.roots()[entry][k],
                _ => proof.opening_proof.commit_phase_commits[cap_id - 2].roots()[entry][k],
            }
        };

        // FAITHFULNESS: every absorbed cap felt sits at its recorded sponge (block, lane), == the committed
        // cap entry. This is exactly what the in-circuit ordered bus provides from `cur[lane]` at row `block·BLOCK`.
        for &(cap_id, entry, k, block, lane) in &positions {
            assert!(lane < 4, "cap felt must land in a rate lane (0..RATE)");
            assert_eq!(
                block_inputs[block][lane],
                committed(cap_id, entry, k),
                "cap_id={cap_id} entry={entry} k={k}: sponge block {block} lane {lane} != committed cap",
            );
        }

        // COVERAGE: the mapped felts are exactly the AIR's cap model — trace + quotient at full 2^cap_height,
        // plus each commit round at its folded height. Cross-checks the AIR model vs the real proof caps.
        let (air, _tr, _pis) = wrap_build_reused(&config, &proof, &pvs, false);
        let expected: usize = 2 * (1usize << air.cap_height) * 4
            + (0..air.cm_rounds()).map(|r| air.commit_cap_size(r) * 4).sum::<usize>();
        assert_eq!(positions.len(), expected, "every commit-absorbed cap felt mapped exactly once");

        // ALIGNMENT: only the trace cap is misaligned (lane 3, straddling blocks); quotient is block-aligned.
        let tr0 = positions.iter().find(|&&(c, e, k, ..)| (c, e, k) == (0, 0, 0)).expect("trace cap entry 0");
        let q0 = positions.iter().find(|&&(c, e, k, ..)| (c, e, k) == (1, 0, 0)).expect("quotient cap entry 0");
        assert_eq!(tr0.4, 3, "trace cap felt 0 lands at rate lane 3 (after the 3 preamble scalars)");
        assert_eq!(q0.4, 0, "quotient cap felt 0 is block-aligned (lane 0) after the α flush");
        println!(
            "AA5 feasibility: {} FS-absorbed cap felts bind sponge (block,lane) → committed cap bit-for-bit \
             (trace misaligned @lane 3; quotient/commit block-aligned)",
            positions.len()
        );
    }

    /// **AA6 arith-openings feasibility — the OOD openings are FS-absorbed bit-for-bit** (`--features recursion`,
    /// ~30s). The [`cap_absorb_stream_matches_committed_caps`] analog for the arith tile: the DEEP fold's `pz` (the
    /// inner's `opened_values`, the `2·n_terms`-COLUMN arith tile = the dominant inner-scaling WIDTH region, ~4 of
    /// the marginal-5 self-composition B) is absorbed into the transcript sponge right after ζ. On a REAL
    /// join-split inner, `sim_opening_positions` records each opening felt's `(opening_id, k, block, lane)`, and
    /// this asserts `block_inputs[block][lane] == the committed opening felt` for EVERY one (trace_local +
    /// trace_next + quotient_chunks, ×2 for F_p²). ⇒ the arith tile can be re-anchored to the FS-absorbed openings
    /// by the SAME ordered sponge bus the caps used — the columns→rows swap that drops it from `fused_w` (marginal
    /// 5 → ~1). The addressing brick of the AA6 arc (mirrors the caps `743f5b7` feasibility brick).
    #[cfg(feature = "recursion")]
    #[test]
    fn opening_absorb_stream_matches_committed_openings() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::monolith::tests::sim_opening_positions;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (block_inputs, positions, committed) = sim_opening_positions(&config, &proof, &pvs);

        assert_eq!(positions.len(), committed.len(), "positions and committed openings are index-aligned");
        for (gi, &(oid, k, block, lane)) in positions.iter().enumerate() {
            assert_eq!(
                block_inputs[block][lane], committed[gi],
                "opening felt (oid {oid}, k {k}) must == its FS-absorbed rate lane at (block {block}, lane {lane})"
            );
        }
        // coverage: 2 felts per opening; openings = trace_local + trace_next + Σ quotient_chunks.
        let n_openings = proof.opened_values.trace_local.len()
            + proof.opened_values.trace_next.as_ref().map_or(0, |t| t.len())
            + proof.opened_values.quotient_chunks.iter().map(|c| c.len()).sum::<usize>();
        assert_eq!(positions.len(), 2 * n_openings, "every opening's 2 F_p² felts are recorded");
        println!(
            "AA6 feasibility: {} OOD opening felts ({n_openings} openings × 2) FS-absorbed bit-for-bit at their \
             (block,lane) — the arith tile (2·n_terms pz cols) can be sponge-anchored like the caps, dropping the \
             dominant inner-scaling WIDTH region from fused_w.",
            positions.len()
        );
    }

    /// **AA5 — the in-circuit ordered sponge-cap bus COMPOSES + BALANCES** (`--features lookup,recursion`, cheap).
    /// The FS-anchor mechanism the cw=true width win needs: bind the narrow-tall cap region to the caps the
    /// transcript sponge ACTUALLY absorbed. Builds [`SpongeCapBusAir`]'s trace from the REAL join-split absorb
    /// stream (`sim_cap_positions`) — SPONGE rows provide each cap felt from its rate lane keyed by the
    /// enumeration index `gi`, REGION rows read `(gi, committed_cap_felt)` — and (1) COMPOSES `log_nqc ≤ 4`
    /// (one channel, `RATE+1` tuples/row), (2) BALANCES natively (every `(gi, value)` nets to zero ⇒ committed
    /// region felt == FS-absorbed felt). The end-to-end proof + tamper-reject is [`sponge_cap_bus_proves`]. So
    /// the ordered binding — the AA5 FS-anchor — is well-formed + balanced. (Tags are witnessed here; the
    /// assembly PINS them to periodic per `(block,lane)`, the FT_BIND pattern — that pinning + the cw=true pw-cap
    /// removal is the next brick.)
    #[cfg(feature = "recursion")]
    #[test]
    fn sponge_cap_bus_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::lookup::prover::combined_constraint_layout;
        use crate::recursion::monolith::tests::sim_cap_positions;
        use crate::recursion::native_fri::make_config;
        use crate::wrap::{sponge_cap_bus_trace, SpongeCapBusAir};
        use p3_field::PrimeField64;
        use p3_lookup::Lookups;
        use p3_uni_stark::prove;
        use std::collections::BTreeMap;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (block_inputs, positions) = sim_cap_positions(&config, &proof, &pvs);

        // Committed cap felt per position (index-aligned with `positions` = the enumeration index gi).
        let committed: Vec<Val> = positions
            .iter()
            .map(|&(cap_id, entry, k, _, _)| match cap_id {
                0 => proof.commitments.trace.roots()[entry][k],
                1 => proof.commitments.quotient_chunks.roots()[entry][k],
                _ => proof.opening_proof.commit_phase_commits[cap_id - 2].roots()[entry][k],
            })
            .collect();

        let trace = sponge_cap_bus_trace(&block_inputs, &positions, &committed);
        let (width, height) = (trace.width, trace.values.len() / trace.width);

        // (1) COMPOSE: one LogUp channel, RATE+1 tuples/row, low degree.
        let air = SpongeCapBusAir;
        let lookups = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        assert_eq!(lookups.len(), 1, "one ordered-bus channel");
        assert!(log_nqc <= LOG_BLOWUP, "the ordered sponge-cap bus must compose within budget (got {log_nqc})");

        // (2) BALANCE (native, from the built trace): sponge provides (gi, lane) −sel, region reads (gi, rval)
        // +is_region; every (gi, value) nets to zero ⇒ each committed region felt == the FS-absorbed sponge felt.
        let g = |r: usize, c: usize| trace.values[r * width + c].as_canonical_u64();
        let (rate, is_reg, rgi, rval) = (4usize, 3 * 4 + 2, 3 * 4, 3 * 4 + 1);
        let mut bus: BTreeMap<(u64, u64), i64> = BTreeMap::new();
        for r in 0..height {
            for l in 0..rate {
                if trace.values[r * width + 2 * rate + l] == Val::ONE {
                    *bus.entry((g(r, rate + l), g(r, l))).or_insert(0) -= 1; // provide
                }
            }
            if trace.values[r * width + is_reg] == Val::ONE {
                *bus.entry((g(r, rgi), g(r, rval))).or_insert(0) += 1; // read
            }
        }
        let nonzero = bus.values().filter(|&&v| v != 0).count();
        assert_eq!(nonzero, 0, "ordered sponge-cap bus must net to zero ({nonzero} imbalanced (gi,value) tuples)");
        assert_eq!(bus.len(), positions.len(), "one balanced (gi,value) tuple per absorbed cap felt");

        println!(
            "AA5 ordered sponge-cap bus: {} cap felts, width {width}, {height} rows, log_nqc {log_nqc} — \
             COMPOSES + BALANCES natively (the FS-anchor multiset; proof in sponge_cap_bus_proves)",
            positions.len()
        );
    }

    /// **AA6 brick 2 — the ordered sponge bus binds the OPENINGS too** (`--features lookup,recursion`, cheap). The
    /// arith tile's FS-anchor REUSES the proven [`SpongeCapBusAir`]/`sponge_cap_bus_trace` verbatim (the bus is
    /// generic over the `(gi, value)` enumeration — only `(block,lane)` per felt matters). Fed the OPENING stream
    /// (`sim_opening_positions`) it COMPOSES `log_nqc ≤ 4` + BALANCES natively (every `(gi, opening felt)` nets to
    /// zero ⇒ each region opening == the FS-absorbed opening). So the same SOUND FS-anchor (proven end-to-end in
    /// [`sponge_cap_bus_proves`]) drops the arith tile — no new bus mechanism needed, just a new feed.
    #[cfg(feature = "recursion")]
    #[test]
    fn sponge_opening_bus_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::lookup::prover::combined_constraint_layout;
        use crate::recursion::monolith::tests::sim_opening_positions;
        use crate::recursion::native_fri::make_config;
        use crate::wrap::{sponge_cap_bus_trace, SpongeCapBusAir};
        use p3_field::PrimeField64;
        use p3_lookup::Lookups;
        use p3_uni_stark::prove;
        use std::collections::BTreeMap;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (block_inputs, opos, committed) = sim_opening_positions(&config, &proof, &pvs);
        // the ordered bus only reads (block,lane) per felt; carry the opening tags in the (ignored) cap-id/entry slots.
        let positions: Vec<(usize, usize, usize, usize, usize)> =
            opos.iter().map(|&(oid, k, b, l)| (0, oid, k, b, l)).collect();

        let trace = sponge_cap_bus_trace(&block_inputs, &positions, &committed);
        let (width, height) = (trace.width, trace.values.len() / trace.width);

        let air = SpongeCapBusAir;
        let lookups = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        assert_eq!(lookups.len(), 1, "one ordered-bus channel");
        assert!(log_nqc <= LOG_BLOWUP, "the ordered sponge-opening bus must compose within budget (got {log_nqc})");

        let g = |r: usize, c: usize| trace.values[r * width + c].as_canonical_u64();
        let (rate, is_reg, rgi, rval) = (4usize, 3 * 4 + 2, 3 * 4, 3 * 4 + 1);
        let mut bus: BTreeMap<(u64, u64), i64> = BTreeMap::new();
        for r in 0..height {
            for l in 0..rate {
                if trace.values[r * width + 2 * rate + l] == Val::ONE {
                    *bus.entry((g(r, rate + l), g(r, l))).or_insert(0) -= 1; // provide
                }
            }
            if trace.values[r * width + is_reg] == Val::ONE {
                *bus.entry((g(r, rgi), g(r, rval))).or_insert(0) += 1; // read
            }
        }
        let nonzero = bus.values().filter(|&&v| v != 0).count();
        assert_eq!(nonzero, 0, "ordered sponge-opening bus must net to zero ({nonzero} imbalanced (gi,value) tuples)");
        assert_eq!(bus.len(), positions.len(), "one balanced (gi,value) tuple per absorbed opening felt");
        println!(
            "AA6 sponge-OPENING bus: {} opening felts, width {width}, {height} rows, log_nqc {log_nqc} — COMPOSES \
             + BALANCES (reuses the proven SpongeCapBusAir; the arith-tile FS-anchor holds exactly like the caps).",
            positions.len()
        );
    }

    /// **AA5 — the ordered sponge-cap bus PROVES + tamper-rejects** (`--release --ignored`). The heavy half of
    /// [`sponge_cap_bus_composes`]: the same real-absorb-stream trace PROVES + verifies through `prove_lookup`,
    /// and a corrupted committed felt (≠ the FS-absorbed felt) is REJECTED (the bus unbalances). So the FS-anchor
    /// binding — region cap == the caps the sponge absorbed — holds as a SOUND STARK.
    #[cfg(feature = "recursion")]
    #[test]
    #[ignore = "heavy: proves SpongeCapBusAir through prove_lookup (~5min); run `--release --features lookup,recursion -- --ignored`"]
    fn sponge_cap_bus_proves() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::lookup::prover::{prove_lookup, verify_lookup};
        use crate::recursion::monolith::tests::sim_cap_positions;
        use crate::recursion::native_fri::make_config;
        use crate::wrap::{sponge_cap_bus_trace, SpongeCapBusAir};
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (block_inputs, positions) = sim_cap_positions(&config, &proof, &pvs);
        let committed: Vec<Val> = positions
            .iter()
            .map(|&(cap_id, entry, k, _, _)| match cap_id {
                0 => proof.commitments.trace.roots()[entry][k],
                1 => proof.commitments.quotient_chunks.roots()[entry][k],
                _ => proof.opening_proof.commit_phase_commits[cap_id - 2].roots()[entry][k],
            })
            .collect();
        let air = SpongeCapBusAir;

        let trace = sponge_cap_bus_trace(&block_inputs, &positions, &committed);
        let lproof = prove_lookup(&air, trace, &[]);
        assert!(verify_lookup(&air, &lproof, &[]).is_ok(), "the ordered sponge-cap bus must prove + verify");

        // REJECT: corrupt one committed felt ⇒ its region read no longer matches its sponge provide ⇒ imbalance.
        let mut bad = committed.clone();
        bad[0] += Val::ONE;
        let bad_trace = sponge_cap_bus_trace(&block_inputs, &positions, &bad);
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let p = prove_lookup(&air, bad_trace, &[]);
            verify_lookup(&air, &p, &[]).is_err()
        }))
        .unwrap_or(true);
        std::panic::set_hook(hook);
        assert!(rejected, "a committed cap felt ≠ the FS-absorbed felt must not produce a valid proof");
    }

    /// **AA5 — `narrow_caps` shrinks the cw=true pw window (the width-win geometry, cheap).** The foundational
    /// geometry change: flipping `MonolithAir.narrow_caps` DROPS the Merkle-cap slice from the inner-proof `pis`
    /// window, so at `column_window=true` the pw window (and thus `fused_w`) shrinks by exactly the cap felts
    /// (`2·cap_stride + commit_caps_len`, is_zk=0). Builds a real join-split inner's cw=true monolith at
    /// `narrow_caps` false vs true and asserts the exact reduction — the ~85%-of-`fused_w` cap columns leave the
    /// trace. Flag-OFF is byte-identical (`pinned_constraint_fingerprints` guards it); this measures the ON win.
    /// (The caps still enter FS via the sponge + anchor the region via [`crate::wrap::SpongeCapBusAir`]; wiring
    /// that into the assembled cap-wrap + proving is the next brick.)
    #[cfg(feature = "recursion")]
    #[test]
    fn narrow_caps_shrinks_pis_window() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::sim_full;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::{make_config, multicol_query_terms};
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (_bi, counts, binds, _chs, index_binds, index_felts) = sim_full(&config, &proof, &pvs);
        let (terms, _x, _a, _ro, _wt) = multicol_query_terms(&config, &JoinSplitAir, &proof, &pvs, 0);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let mk = |narrow_caps: bool| MonolithAir {
            counts: counts.clone(),
            binds: binds.clone(),
            index_binds: index_binds.clone(),
            n_queries: index_felts.len(),
            n_terms: terms.len(),
            inner_counter: false,
            column_window: true,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints: constraints.clone(),
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: false,
            narrow_caps,
            narrow_openings: false, narrow_ov: false,
        };
        let (full, narrow) = (mk(false), mk(true));
        let cap_felts = 2 * full.cap_stride() + full.commit_caps_len(); // trace + quot + commit caps (is_zk=0)

        assert_eq!(narrow.pis_count(), full.pis_count() - cap_felts, "narrow_caps drops the pis cap slice");
        assert_eq!(narrow.fused_w(), full.fused_w() - cap_felts, "the pw cap columns leave fused_w (cw=true)");
        // downstream pis regions shift down by the dropped trace+quot caps (then further by the commit caps).
        assert_eq!(narrow.pub_pi(), full.pub_pi() - 2 * full.cap_stride(), "pub_pi shifts past the dropped trace+quot caps");
        assert_eq!(narrow.pis_cap_stride(), 0, "narrow: no pis cap slice");
        assert_eq!(full.pis_cap_stride(), full.cap_stride(), "full: the real cap slice");
        assert!(cap_felts > 0 && narrow.fused_w() < full.fused_w());

        // CONSTRAINT-COMPATIBILITY: the narrow_caps geometry works with CapMuxBci (the cap-mux externalized ⇒
        // nothing reads the dropped pis cap slice). CapWrapAir { m: narrow } builds its symbolic layout with NO
        // out-of-bounds pis read and COMPOSES within budget, at the reduced width (fused_w 963, cap columns gone).
        // This is the assembly foundation — the plain monolith (InlineBci) CAN'T (its emit_capmux would read the
        // collapsed slice); only the cap-mux-externalized wrap can drop the caps.
        use p3_uni_stark::get_log_num_quotient_chunks;
        let wrap_narrow = CapWrapAir { m: mk(true) };
        assert_eq!(BaseAir::<Val>::width(&wrap_narrow), narrow.fused_w(), "CapWrapAir width == narrow fused_w (cap cols gone)");
        let nlayout = AirLayout::from_air::<Val>(&wrap_narrow); // panics if the collapsed pis layout causes a bad read
        let log_nqc = get_log_num_quotient_chunks::<Val, _>(&wrap_narrow, nlayout, 0);
        assert!(log_nqc <= LOG_BLOWUP, "narrow_caps CapWrapAir must compose within budget (log_nqc {log_nqc})");
        println!(
            "narrow_caps (cap_height {}): pis_count {} → {} (−{cap_felts}), fused_w {} → {} (the cw=true pw \
             cap columns removed; the caps now live in the FS sponge + the narrow-tall region)",
            full.cap_height,
            full.pis_count(),
            narrow.pis_count(),
            full.fused_w(),
            narrow.fused_w()
        );
    }

    /// **AA6 — `narrow_openings` shrinks the arith tile to its header (the deep-tree B-lever geometry).** Extends
    /// `narrow_arith`: the LAST inner-scaling arith columns — the `2·n_terms` per-term OOD openings `pz` (the
    /// inner proof's `opened_values`) — leave the tile (`arith_stride` 2 → 0), to be re-sourced from the
    /// FS-absorbed opening stream via the ordered sponge-opening bus ([`crate::wrap::SpongeCapBusAir`]). This
    /// measures the raw column win against the `narrow_arith` baseline, holding everything else equal: the arith
    /// tile collapses to `qt_terms` (its DEEP index-bits + acc-chain + α header) and `fused_w` drops by exactly
    /// `2·n_terms`. Flag-OFF is byte-identical (`pinned_constraint_fingerprints` guards it); this measures the ON
    /// geometry. (Re-sourcing the openings from the bus + proving the assembled openings-wrap is the next brick.)
    #[cfg(feature = "recursion")]
    #[test]
    fn narrow_openings_shrinks_arith_tile() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::sim_full;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::{make_config, multicol_query_terms};
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (_bi, counts, binds, _chs, index_binds, index_felts) = sim_full(&config, &proof, &pvs);
        let (terms, _x, _a, _ro, _wt) = multicol_query_terms(&config, &JoinSplitAir, &proof, &pvs, 0);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        // `narrow_arith` is the baseline (`[pz]` only, stride 2); `narrow_openings` extends it (stride 0). Hold
        // everything else equal so the ONLY delta is the pz opening columns.
        let mk = |narrow_openings: bool| MonolithAir {
            counts: counts.clone(),
            binds: binds.clone(),
            index_binds: index_binds.clone(),
            n_queries: index_felts.len(),
            n_terms: terms.len(),
            inner_counter: false,
            column_window: false,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints: constraints.clone(),
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: true,
            narrow_caps: false,
            narrow_openings,
            narrow_ov: false,
        };
        let (base, narrow) = (mk(false), mk(true));
        let n_terms = terms.len();

        // stride: narrow_arith keeps pz (2 felts/term); narrow_openings drops it (0).
        assert_eq!(base.arith_stride(), 2, "narrow_arith baseline keeps pz (stride 2)");
        assert_eq!(narrow.arith_stride(), 0, "narrow_openings drops pz too (stride 0)");
        // the arith tile collapses to its header (qt_terms: DEEP index bits + acc chain + α), no per-term columns.
        assert_eq!(narrow.tile_w(), narrow.qt_terms(), "narrow_openings: the arith tile is just its header");
        assert_eq!(base.tile_w(), base.qt_terms() + 2 * n_terms, "narrow_arith: header + 2·n_terms pz felts");
        // fused_w drops by exactly the pz columns (2 felts × n_terms); everything downstream shifts down.
        assert_eq!(narrow.fused_w(), base.fused_w() - 2 * n_terms, "the pz opening columns leave fused_w");
        assert!(2 * n_terms > 0 && narrow.fused_w() < base.fused_w());
        println!(
            "narrow_openings (n_terms {n_terms}): arith tile {} → {} cols, fused_w {} → {} (−{} pz felts; the \
             last inner-scaling arith columns externalized to the sponge-opening bus)",
            base.tile_w(),
            narrow.tile_w(),
            base.fused_w(),
            narrow.fused_w(),
            2 * n_terms,
        );
    }

    /// **W3 — `narrow_ov` shrinks the OPENED-ROW carrier to rows (the B<1-completing geometry).** After
    /// `narrow_openings` the LAST region still scaling with the inner width is the `ov` opened-row carrier
    /// (`input_leaf_felts = w_inner`, the authenticated input-Merkle LEAF PREIMAGE) — it holds the marginal
    /// self-composition B at EXACTLY 1.00 (`self_composition_b_narrowed`). `narrow_ov` drops its `w_inner` felts
    /// from the carrier region (`ov_carrier_w() → 0` in `carriers_base`/`qc`), to be re-sourced narrow-tall from the
    /// input-Merkle leaf hash + `px_source` (the sound-brick work). This measures the raw column win vs the
    /// `narrow_openings` baseline: `fused_w` drops by EXACTLY `input_leaf_felts` (= `w_inner`) — the last
    /// inner-scaling region — while the leaf-HASH width (`leaf_blocks`) is unchanged (only the carrier columns move).
    /// Flag-OFF is byte-identical (`pinned_constraint_fingerprints` guards it); ⇒ the projected marginal B → 0
    /// (`self_composition_b_narrowed`) is realized by this geometry (a strict contraction ⇒ an attracting `W*`).
    #[cfg(feature = "recursion")]
    #[test]
    fn narrow_ov_shrinks_carrier() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::sim_full;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::{make_config, multicol_query_terms};
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (_bi, counts, binds, _chs, index_binds, index_felts) = sim_full(&config, &proof, &pvs);
        let (terms, _x, _a, _ro, _wt) = multicol_query_terms(&config, &JoinSplitAir, &proof, &pvs, 0);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        // baseline = narrow_openings (the ov carrier still WIDE); narrow_ov extends it (ov carrier → rows).
        let mk = |narrow_ov: bool| MonolithAir {
            counts: counts.clone(),
            binds: binds.clone(),
            index_binds: index_binds.clone(),
            n_queries: index_felts.len(),
            n_terms: terms.len(),
            inner_counter: false,
            column_window: false,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints: constraints.clone(),
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: true,
            narrow_caps: false,
            narrow_openings: true,
            narrow_ov,
        };
        let (base, narrow) = (mk(false), mk(true));

        // the ov opened-row carrier: input_leaf_felts (= w_inner) felts → 0 columns.
        assert_eq!(base.input_leaf_felts(), WIDTH, "is_zk=0: the ov carrier is the w_inner opened trace row");
        assert_eq!(base.ov_carrier_w(), base.input_leaf_felts(), "narrow_openings baseline keeps the ov carrier WIDE");
        assert_eq!(narrow.ov_carrier_w(), 0, "narrow_ov externalizes the ov opened-row carrier (0 columns)");
        // fused_w drops by EXACTLY input_leaf_felts (= w_inner) — the LAST inner-scaling region.
        assert_eq!(narrow.fused_w(), base.fused_w() - base.input_leaf_felts(), "the ov opened-row carrier leaves fused_w");
        // the leaf-HASH width is UNCHANGED — only the carrier COLUMNS move to rows (the preimage is still hashed).
        assert_eq!(narrow.leaf_blocks(), base.leaf_blocks(), "the leaf-hash preimage width is unchanged (only the carrier columns move)");
        assert!(narrow.fused_w() < base.fused_w());
        println!(
            "narrow_ov (w_inner {WIDTH}): ov opened-row carrier {} → 0 cols, fused_w {} → {} (−{} = w_inner; the LAST \
             inner-scaling region externalized ⇒ marginal self-composition B 1.00 → 0, a strict contraction). The \
             leaf-hash width (leaf_blocks {}) is unchanged — only the carrier columns move to rows.",
            base.ov_carrier_w(),
            base.fused_w(),
            narrow.fused_w(),
            base.input_leaf_felts(),
            base.leaf_blocks(),
        );
    }

    /// **W3 ov externalization brick 2 — the ov carrier IS the input-Merkle leaf-hash preimage** (`--features
    /// recursion`, cheap; the addressing brick, mirrors the caps `743f5b7` / openings `opening_absorb_stream…`
    /// feasibility bricks). The `ov` opened-row carrier (`ov_c(c)`) is bound to the input-Merkle leaf hash by
    /// `eval_bci` (air.rs ~1728/1740: `cur[c%RATE] == cur[ov_c(c)]` at each leaf absorb block, gated `m_leaf`/`ia_in`),
    /// so the w_inner felts already live in the leaf-hash Poseidon input lanes. This confirms, on a REAL join-split
    /// inner (w_inner 19, 5 leaf blocks — the multi-block case) built by `build_symbolic_inner_window`, that for
    /// every query `q` and felt `c`, the carrier value `ov_c(c)` EQUALS the leaf-hash lane at super-tile row
    /// `tr + q·m_period() + (m_input_leaf()+c/RATE)·BLOCK`, lane `c%RATE`. ⇒ the ov carrier COPY is redundant: the
    /// sound narrow_ov re-sources `px` (`px_source→ov_c`) from the leaf-hash rows via a LogUp bus (the leaf hash is
    /// the FS-anchor, Merkle-authenticated → trace cap), eliminating the carrier — the openings sponge-bus pattern
    /// one region over. (The bus compose + assembled binding + balance/prove are the next bricks.)
    #[cfg(feature = "recursion")]
    #[test]
    fn ov_carrier_matches_leaf_hash() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::poseidon2_air::BLOCK;
        use crate::recursion::monolith::tests::build_symbolic_inner_window;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        // FULL geometry (narrow_arith:false ⇒ px stored + ov carrier bound to it + the leaf-hash binding present).
        let (tr, counts, binds, index_binds, n_terms, _pv0) =
            build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, false, false, false, false);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let m = MonolithAir {
            counts,
            binds,
            index_binds,
            n_queries: proof.opening_proof.query_proofs.len(),
            n_terms,
            inner_counter: false,
            column_window: true,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints,
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: false,
            narrow_caps: false,
            narrow_openings: false,
            narrow_ov: false,
        };
        let fw = m.fused_w();
        let h = tr.len() / fw;
        let rate = 4usize; // RATE
        let mut checked = 0usize;
        for q in 0..m.n_queries {
            let off = m.tr() + q * m.m_period(); // query q's super-tile start
            for c in 0..WIDTH {
                // ov carrier value (held constant across the super-tile — read at the first row).
                let ov_val = tr[off * fw + m.ov_c(c)];
                // leaf-hash Poseidon input lane: block (m_input_leaf + c/RATE), lane c%RATE.
                let leaf_row = off + (m.m_input_leaf() + c / rate) * BLOCK;
                assert!(leaf_row < h, "leaf-hash row in bounds");
                let leaf_val = tr[leaf_row * fw + (c % rate)];
                assert_eq!(
                    ov_val, leaf_val,
                    "query {q} felt {c}: ov_c({}) must == the leaf-hash lane at block {} lane {}",
                    m.ov_c(c),
                    m.m_input_leaf() + c / rate,
                    c % rate
                );
                checked += 1;
            }
        }
        assert_eq!(checked, m.n_queries * WIDTH, "every (query, opened-row felt) pair checked");
        println!(
            "W3 ov brick 2: {checked} (query, felt) pairs — ov_c(c) == the input-Merkle leaf-hash Poseidon input lane \
             at (tr + q·m_period() + (m_input_leaf+c/RATE)·BLOCK, c%RATE), on a real join-split inner (w_inner {WIDTH}, \
             {} leaf blocks). ⇒ px can be re-sourced from the leaf hash via a bus, eliminating the ov carrier copy \
             (the leaf hash is the Merkle-authenticated FS-anchor — the openings sponge-bus pattern one region over).",
            m.leaf_blocks()
        );
    }

    /// **W3 ov externalization brick 4b — the narrow_ov TRACE matches native** (`--features recursion`, cheap; NO
    /// prove). The trace builder (`build_symbolic_inner_window` → `monolith_build_trace`) now threads `narrow_ov`:
    /// with it on, the ov opened-row carrier fill is skipped (`monolith/build.rs`, gated on `!narrow_ov`) while the
    /// leaf-preimage still feeds `leaf_hash`. This confirms, byte-for-byte on a real join-split inner, that the
    /// narrow_ov trace EQUALS the baseline (narrow_openings) trace with EXACTLY the ov-carrier column block
    /// `[ov() .. ov()+input_leaf_felts())` excised — every other column (the leaf-hash Poseidon lanes, the Merkle
    /// merges, the qc/commit carriers, the pis window) is identical. ⇒ the narrowing DROPS the carrier and nothing
    /// else: the input-Merkle leaf/cap are unchanged (still authenticated), so the narrow_ov trace satisfies the
    /// narrow_ov AIR (whose only delta is the gated-off ov reads, brick 4a). The prerequisite the assembled px
    /// binding (brick 4d) needs: a real narrowed trace whose px is re-sourced from the (unchanged) leaf-hash lanes.
    #[cfg(feature = "recursion")]
    #[test]
    fn narrow_ov_trace_matches_native() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::build_symbolic_inner_window;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        // the assembler's regime: narrow_arith + narrow_openings on, caps in the window; toggle ONLY narrow_ov.
        let mk = |narrow_ov: bool| -> (Vec<Val>, MonolithAir) {
            let (tr, counts, binds, index_binds, n_terms, _pv0) = build_symbolic_inner_window(
                &config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, false, true, true, narrow_ov,
            );
            let m = MonolithAir {
                counts,
                binds,
                index_binds,
                n_queries: proof.opening_proof.query_proofs.len(),
                n_terms,
                inner_counter: false,
                column_window: true,
                k_instances: 1,
                fold: false,
                fold_txstmt: false,
                constraints: constraints.clone(),
                w_inner_f: WIDTH,
                n_pub_f: N_PUBLIC,
                n_periodic_f: N_PERIODIC,
                is_zk: 0,
                cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
                narrow_arith: true,
                narrow_caps: false,
                narrow_openings: true,
                narrow_ov,
            };
            (tr, m)
        };
        let (base_tr, base) = mk(false);
        let (narrow_tr, narrow) = mk(true);
        let (bfw, nfw) = (base.fused_w(), narrow.fused_w());
        let ilf = base.input_leaf_felts();
        let p = base.ov(); // the ov-carrier block start (== narrow.ov(): only its WIDTH changes)
        assert_eq!(base.ov(), narrow.ov(), "the ov-carrier block start is unchanged (only its width → 0)");
        assert_eq!(nfw, bfw - ilf, "narrow_ov drops exactly input_leaf_felts (= w_inner) columns");
        let h = base_tr.len() / bfw;
        assert_eq!(narrow_tr.len() / nfw, h, "same height");

        // byte-for-byte: narrow[r][c] == base[r][c] for c < p; == base[r][c+ilf] for c ≥ p (the block excised).
        let mut checked = 0usize;
        for r in 0..h {
            for c in 0..nfw {
                let base_c = if c < p { c } else { c + ilf };
                assert_eq!(
                    narrow_tr[r * nfw + c],
                    base_tr[r * bfw + base_c],
                    "row {r} narrow col {c} must equal baseline col {base_c} (ov block [{p}..{}) excised)",
                    p + ilf
                );
                checked += 1;
            }
        }
        // and the excised block in the baseline is exactly the held ov carrier (== the leaf-hash lanes, brick 2) —
        // so what we dropped is the redundant copy, not any authenticating data.
        println!(
            "W3 ov brick 4b: narrow_ov trace matches native — {checked} cells byte-identical to the baseline with the \
             {ilf}-col ov carrier [{p}..{}) excised (fused_w {bfw} → {nfw}). The leaf-hash lanes + Merkle merges + \
             qc/commit carriers + pis window are UNCHANGED (only the redundant opened-row copy is gone), so the \
             narrow_ov trace satisfies the narrow_ov AIR. Ready for the assembled px re-source (brick 4d).",
            p + ilf
        );
    }

    /// **W3 ov externalization brick 3 — the leaf-hash→px bus COMPOSES + BALANCES** (`--features lookup,recursion`,
    /// cheap; the `sponge_opening_bus_composes` analog, one region over). Brick 2 showed the ov carrier felts already
    /// sit in the input-Merkle leaf-hash Poseidon input lanes. This confirms the proven [`crate::wrap::SpongeCapBusAir`]
    /// (the generic ordered `(gi, value)` bus the caps + openings reuse) binds them VERBATIM: lay each query's opened
    /// trace row (= the leaf preimage = `px`) out `RATE` felts/leaf-block as the bus's provide lanes, read `px` on the
    /// region side, and (1) COMPOSE `log_nqc ≤ LOG_BLOWUP` (one channel), (2) BALANCE natively (every `(gi, value)`
    /// nets to zero ⇒ each `px` == its leaf-hash preimage lane). ⇒ the sound `narrow_ov` sources `px` from the leaf
    /// hash via this bus, eliminating the `ov` carrier — the leaf hash is the Merkle-authenticated FS-anchor. (The
    /// ASSEMBLED binding — the narrow_ov monolith reading `px` from the real leaf-hash rows through the bus + the
    /// heavy prove — is the next brick; the assembled prove OOMs this 62 GB box, like the brick-5d prove.)
    #[cfg(feature = "recursion")]
    #[test]
    fn leaf_hash_px_bus_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::lookup::prover::combined_constraint_layout;
        use crate::poseidon2_air::W as PW;
        use crate::recursion::native_fri::make_config;
        use crate::wrap::{sponge_cap_bus_trace, SpongeCapBusAir};
        use p3_field::PrimeField64;
        use p3_lookup::Lookups;
        use p3_uni_stark::prove;
        use std::collections::BTreeMap;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let rate = 4usize;
        let n_q = proof.opening_proof.query_proofs.len();
        // per query: the opened trace row (the leaf preimage = px). Lay it out RATE felts/leaf-block into synthetic
        // "block_inputs" = the leaf-hash Poseidon input lanes SpongeCapBusAir provides; the region side reads px.
        let mut block_inputs: Vec<[Val; PW]> = Vec::new();
        let mut positions: Vec<(usize, usize, usize, usize, usize)> = Vec::new();
        let mut committed: Vec<Val> = Vec::new();
        for q in 0..n_q {
            let row = &proof.opening_proof.query_proofs[q].input_proof[0].opened_values[0];
            let w_inner = row.len();
            let block_base = block_inputs.len();
            for b in 0..w_inner.div_ceil(rate) {
                let clen = core::cmp::min(rate, w_inner - b * rate);
                let mut blk = [Val::ZERO; PW];
                blk[..clen].copy_from_slice(&row[b * rate..b * rate + clen]);
                block_inputs.push(blk);
            }
            for c in 0..w_inner {
                positions.push((0, q, c, block_base + c / rate, c % rate));
                committed.push(row[c]); // px = the opened-row felt = the leaf-hash preimage lane
            }
        }
        let trace = sponge_cap_bus_trace(&block_inputs, &positions, &committed);
        let (width, height) = (trace.width, trace.values.len() / trace.width);

        // (1) COMPOSE (reuses the proven SpongeCapBusAir — same AIR the caps/openings bind through).
        let air = SpongeCapBusAir;
        let lookups = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        assert_eq!(lookups.len(), 1, "one ordered-bus channel");
        assert!(log_nqc <= LOG_BLOWUP, "the leaf-hash→px bus must compose within budget (got {log_nqc})");

        // (2) BALANCE: sponge provides (gi, lane) −sel, region reads (gi, px) +is_region ⇒ px == the leaf preimage.
        let g = |r: usize, c: usize| trace.values[r * width + c].as_canonical_u64();
        let (is_reg, rgi, rval) = (3 * 4 + 2, 3 * 4, 3 * 4 + 1);
        let mut bus: BTreeMap<(u64, u64), i64> = BTreeMap::new();
        for r in 0..height {
            for l in 0..rate {
                if trace.values[r * width + 2 * rate + l] == Val::ONE {
                    *bus.entry((g(r, rate + l), g(r, l))).or_insert(0) -= 1;
                }
            }
            if trace.values[r * width + is_reg] == Val::ONE {
                *bus.entry((g(r, rgi), g(r, rval))).or_insert(0) += 1;
            }
        }
        let nonzero = bus.values().filter(|&&v| v != 0).count();
        assert_eq!(nonzero, 0, "leaf-hash→px bus must net to zero ({nonzero} imbalanced (gi,value) tuples)");
        assert_eq!(bus.len(), positions.len(), "one balanced (gi,value) tuple per opened-row felt");
        println!(
            "W3 ov brick 3: {} opened-row felts ({n_q} queries), width {width}, {height} rows, log_nqc {log_nqc} — \
             the leaf-hash→px bus COMPOSES + BALANCES (reuses the proven SpongeCapBusAir, the openings pattern one \
             region over: the leaf hash provides px, so the ov carrier copy is eliminated). The assembled narrow_ov \
             binding (px sourced from the real leaf-hash rows) + prove are next (the assembled prove OOMs this box).",
            positions.len()
        );
    }

    /// **AA6 — the narrow_openings wrap COMPOSES (the plumbing/compose step).** The narrow_openings monolith
    /// (`arith_stride` 0 — the `pz` opening columns GONE) + [`OpeningsBci`] (DeepFold arith ⊕ OpTable epilogue,
    /// `ro`/`folded`/`quot` as FREE witnesses) builds its symbolic layout with NO degenerate `pz` read and composes
    /// at `log_nqc ≤ LOG_BLOWUP`, width `fused_w + 6`. The shared `eval_bci` `pz` recompose is gated OFF for
    /// `narrow_openings` (local/next empty, quot zero — the strategy self-sources from its columns) so nothing
    /// reads the dropped openings. This is the strategy-plumbing foundation (mirrors `CapWrapAir`); binding the
    /// three columns to the FS-absorbed openings via the sponge-opening bus + the DeepFold/op-table regions is next.
    #[cfg(feature = "recursion")]
    #[test]
    fn narrow_openings_wrap_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::sim_full;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::{make_config, multicol_query_terms};
        use p3_uni_stark::{get_log_num_quotient_chunks, get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (_bi, counts, binds, _chs, index_binds, index_felts) = sim_full(&config, &proof, &pvs);
        let (terms, _x, _a, _ro, _wt) = multicol_query_terms(&config, &JoinSplitAir, &proof, &pvs, 0);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let m = MonolithAir {
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
            narrow_arith: true,
            narrow_caps: false,
            narrow_openings: true, narrow_ov: false,
        };
        let fused = m.fused_w();
        let wrap = NarrowOpeningsWrapAir { m };
        assert_eq!(BaseAir::<Val>::width(&wrap), fused + 6, "ro + folded + quot free-witness pairs (pz columns gone)");
        let layout = AirLayout::from_air::<Val>(&wrap); // panics if the narrow_openings layout causes a bad read
        let log_nqc = get_log_num_quotient_chunks::<Val, _>(&wrap, layout, 0);
        assert!(log_nqc <= LOG_BLOWUP, "narrow_openings wrap must compose within budget (log_nqc {log_nqc})");
        println!("narrow_openings wrap composes: log_nqc {log_nqc}, width fused_w {fused} + 6 (the pz opening columns externalized)");
    }

    /// **W3 ov externalization brick 4b — the narrow_ov monolith COMPOSES (plumbing).** With brick 4a gating the
    /// ov-carrier reads on `!narrow_ov`, and [`OpeningsBci`] externalizing the fold (so the monolith itself reads no
    /// `px`), the narrow_ov monolith — the `ov` opened-row carrier DROPPED (`fused_w` smaller by `w_inner`) —
    /// composes through the EXISTING [`NarrowOpeningsWrapAir`] at `log_nqc ≤ LOG_BLOWUP`, width `fused_w + 6`. `px` is
    /// a free witness here (the leaf-hash→px bus binds it in the assembled brick, brick 4c). Additive: does NOT touch
    /// the proven `AssembledOpeningsWrapCwAir`. So the ov-dropped verifier layout is well-formed + low-degree — the
    /// plumbing step (mirrors `narrow_openings_wrap_composes` / the `ArithWrapAir`/`CapWrapAir` free-witness compose).
    #[cfg(feature = "recursion")]
    #[test]
    fn narrow_ov_wrap_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::sim_full;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::{make_config, multicol_query_terms};
        use p3_uni_stark::{get_log_num_quotient_chunks, get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (_bi, counts, binds, _chs, index_binds, index_felts) = sim_full(&config, &proof, &pvs);
        let (terms, _x, _a, _ro, _wt) = multicol_query_terms(&config, &JoinSplitAir, &proof, &pvs, 0);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let mk = |narrow_ov: bool| MonolithAir {
            counts: counts.clone(),
            binds: binds.clone(),
            index_binds: index_binds.clone(),
            n_queries: index_felts.len(),
            n_terms: terms.len(),
            inner_counter: false,
            column_window: false,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints: constraints.clone(),
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: true,
            narrow_caps: false,
            narrow_openings: true,
            narrow_ov,
        };
        let (m_open, m_ov) = (mk(false), mk(true));
        let (open_fused, ov_fused) = (m_open.fused_w(), m_ov.fused_w());
        // the ov opened-row carrier (w_inner felts) leaves fused_w.
        assert_eq!(ov_fused, open_fused - WIDTH, "narrow_ov drops the w_inner ov carrier from fused_w");
        let wrap = NarrowOpeningsWrapAir { m: m_ov };
        assert_eq!(BaseAir::<Val>::width(&wrap), ov_fused + 6, "ro/folded/quot free-witness pairs; the ov carrier gone");
        let layout = AirLayout::from_air::<Val>(&wrap); // panics if the narrow_ov layout causes a dropped-column read
        let log_nqc = get_log_num_quotient_chunks::<Val, _>(&wrap, layout, 0);
        assert!(log_nqc <= LOG_BLOWUP, "the narrow_ov wrap must compose within budget (log_nqc {log_nqc})");
        println!(
            "W3 ov brick 4b: the narrow_ov monolith COMPOSES — log_nqc {log_nqc}, fused_w {ov_fused} (−w_inner {WIDTH} \
             vs narrow_openings {open_fused}), width {} = fused_w + 6. The ov opened-row carrier externalized, px a \
             free witness (bound via the leaf-hash→px bus in the assembled brick 4c). Additive: the proven \
             AssembledOpeningsWrapCwAir is untouched.",
            ov_fused + 6
        );
    }

    /// **W3 ov externalization brick 4c (compose) — the narrow_ov monolith + the leaf-hash→px bus COMPOSE together**
    /// (`--features lookup,recursion`, cheap). The [`OpeningBindCwAir`] analog for px: [`NarrowOvBindCwAir`] = the
    /// narrow_ov monolith (`OpeningsBci`) + ONE leaf-hash→px bus (same generic FS-anchor shape as the sponge-opening
    /// bus). Confirms both compose TOGETHER at `log_nqc ≤ LOG_BLOWUP` — the DEGREE de-risk for the assembled px
    /// binding (the query-keyed leaf-hash provider + native-balance is the next brick). Additive: proven wrap untouched.
    #[cfg(feature = "recursion")]
    #[test]
    fn narrow_ov_bind_cw_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::build_symbolic_inner_window;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (_tr, counts, binds, index_binds, n_terms, _pv0) =
            build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, false, true, true, false);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let m = MonolithAir {
            counts,
            binds,
            index_binds,
            n_queries: proof.opening_proof.query_proofs.len(),
            n_terms,
            inner_counter: false,
            column_window: true,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints,
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: true,
            narrow_caps: false,
            narrow_openings: true,
            narrow_ov: true,
        };
        let h = m.height();
        // 3·RATE periodics: per lane the two shared DEEP term ids (trm_trace/trm_next) + the select bit (dummy for
        // compose — the VALUES don't affect degree; the ASSEMBLED balance fills them from the real leaf geometry).
        let leaf_periodics = vec![vec![Val::ZERO; h]; 3 * NarrowOvBindCwAir::RATE];
        let air = NarrowOvBindCwAir { m, leaf_periodics };
        let width = <NarrowOvBindCwAir as BaseAir<Val>>::width(&air);
        let lookups = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        assert_eq!(lookups.len(), 1, "one leaf-hash→px bus channel");
        assert!(log_nqc <= LOG_BLOWUP, "the narrow_ov monolith + query-keyed leaf-hash→px bus must compose (got {log_nqc})");
        println!(
            "W3 ov brick 4c (compose): NarrowOvBindCwAir (narrow_ov monolith + ONE leaf-hash→px bus, SOUND \
             query-key [lqk, term]) width {width}, {} channel, log_nqc {log_nqc} ≤ {LOG_BLOWUP} — the bus + the \
             ov-dropped monolith compose TOGETHER (the OpeningBindCwAir analog for px). The held lqk (= x) makes the \
             bus query-unique (the periodic term tag alone repeats per query); each leaf lane provides under both \
             shared DEEP terms trm_trace/trm_next, the region reads [lqk, term_idx, px0]. Assembled balance next.",
            lookups.len()
        );
    }

    /// **W3 ov externalization brick 4c (soundness rationale) — the held query key is NECESSARY** (`--features
    /// recursion`, trivial; pure multiset arithmetic, NO AIR/prove). Proves WHY the leaf-hash→px bus must be keyed by
    /// `[lqk, felt]` (lqk = the per-query point) and not the periodic-only `[felt]` tag: because px is
    /// QUERY-DEPENDENT (each query opens a DIFFERENT row), but the leaf-hash provider rows are TILED (the periodic
    /// felt-tag REPEATS every query super-tile). A negative control on a synthetic 2-query, 2-felt multiset:
    /// a COLUMN-SWAP attack (query 0 reads query 1's authenticated felt at the same felt index, and vice-versa) is
    /// INVISIBLE to the periodic-only `[felt]` bus (the swapped reads are the SAME signed multiset ⇒ still nets zero
    /// ⇒ the fold binds px to the WRONG query's opening, unsound), but is CAUGHT by the sound `[lqk, felt]` bus (no
    /// provider exists at `(this-query, felt)` with the other query's value ⇒ the multiset does NOT net zero). ⇒ the
    /// resolved crux — `lqk` HELD = x — is exactly what makes the ov externalization sound; brick 4c's compose proves
    /// that key's degree, this proves its necessity.
    #[cfg(feature = "recursion")]
    #[test]
    fn narrow_ov_query_key_is_necessary() {
        use std::collections::BTreeMap;
        // 2 queries, 2 committed felts each: query q's opened row = [q·10, q·10+1] (distinct per query).
        let px = |q: u64, c: u64| q * 10 + c;
        // The signed bus multiset over tuples (key, felt, value): providers −1 (each query's leaf-hash row provides
        // its AUTHENTICATED px(q,c)), readers +1 (each query's fold reads the value it USES). `key` = q for the sound
        // [lqk,felt] bus, or a SENTINEL (query dropped) for the unsound periodic-only [felt] bus (the tiled tag).
        // HONEST: the reader uses its own px(q,c). ATTACK (query/column swap): query q's fold uses px(1-q,c) — the
        // OTHER query's authenticated opening — a real soundness break the bus must catch.
        let net = |keyed_by_query: bool, attack: bool| -> usize {
            let mut bus: BTreeMap<(u64, u64, u64), i64> = BTreeMap::new();
            let kq = |q: u64| if keyed_by_query { q } else { u64::MAX };
            for q in 0..2u64 {
                for c in 0..2u64 {
                    *bus.entry((kq(q), c, px(q, c))).or_insert(0) -= 1; // provider: authenticated px(q,c)
                }
            }
            for q in 0..2u64 {
                for c in 0..2u64 {
                    let src = if attack { 1 - q } else { q }; // attack: fold the OTHER query's felt value
                    *bus.entry((kq(q), c, px(src, c))).or_insert(0) += 1; // reader: the value the fold uses
                }
            }
            bus.values().filter(|&&v| v != 0).count()
        };
        // HONEST: both keys balance (a correct proof passes either way).
        assert_eq!(net(true, false), 0, "sound [lqk,felt] key: honest reads balance");
        assert_eq!(net(false, false), 0, "periodic-only [felt] key: honest reads balance");
        // ATTACK (column/query swap): the sound key CATCHES it (nonzero), the periodic-only key MISSES it (zero).
        assert_eq!(net(false, true), 0, "periodic-only [felt] key: the query-SWAP attack is INVISIBLE (unsound) — the \
             tiled periodic tag can't tell the queries apart, so the swapped reads net to zero");
        assert!(net(true, true) > 0, "sound [lqk,felt] key: the query-SWAP attack is CAUGHT — no provider exists at \
             (this-query, felt) with the other query's value, so the multiset does NOT net zero");
        println!(
            "W3 ov brick 4c (soundness rationale): the held query key `lqk` is NECESSARY — a query-swap attack on the \
             leaf-hash→px bus is INVISIBLE to the periodic-only [felt] key (net 0, unsound: px binds to the WRONG \
             query's opening) but CAUGHT by the sound [lqk, felt] key (net {} ≠ 0). ⇒ the resolved crux (lqk HELD = x) \
             is exactly what makes the ov externalization sound.",
            net(true, true)
        );
    }

    /// **W3 ov externalization brick 4d — the query-keyed leaf-hash→px bus BALANCES on the REAL narrow_ov trace**
    /// (`--features recursion`, cheap; native multiset, NO prove — the brick-5d soundness bar). On a real join-split
    /// inner's narrow_ov monolith trace (`narrow_ov` on ⇒ the ov carrier DROPPED, `px` sourced from the leaf-hash
    /// lanes), replicate the sound `[lqk, term]` leaf-hash→px bus and confirm it nets to zero. The two sides derive
    /// their tuples INDEPENDENTLY and must meet at each committed felt: **providers** walk the PHYSICAL leaf-hash
    /// blocks (row `off + (m_input_leaf + b)·BLOCK`, lane `l` ⇒ felt `c = b·RATE + l`) and provide the absorbed lane
    /// value under BOTH shared DEEP terms `trm_trace(c)`/`trm_next(c)` (−1 each, gated `c < trm_committed_w` = the
    /// w_sel selector); **readers** walk the FOLD's TRACE terms `k` (mapping `k → c` via the trace/next ranges) and
    /// read px keyed by `(x_q, k)`. Balance ⇒ the physical leaf layout, the w_sel range, the term↔felt map, the query
    /// key (`x_q = GEN·qt_acc[lg−1]`), and the 2×/felt multiplicity are all mutually consistent on the real geometry
    /// (w_inner 19, 5 leaf blocks) — a bug in any would imbalance it (as the native balances localized the brick-5d
    /// pz/quot bugs before the heavy prove). This validates the addressing/multiplicity/query-keying STRUCTURE on the
    /// real trace (the value comes from the one authenticated leaf cell — the in-circuit px BINDING is closed by the
    /// AIR eval + the heavy prove, which OOMs this 62 GB box like brick 5d); the AIR-eval wiring is the follow-on.
    #[cfg(feature = "recursion")]
    #[test]
    fn narrow_ov_leaf_px_bus_balances_on_real_trace() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::poseidon2_air::BLOCK;
        use crate::recursion::monolith::tests::build_symbolic_inner_window;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::make_config;
        use p3_field::{Field, PrimeField64};
        use p3_goldilocks::Goldilocks;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};
        use std::collections::BTreeMap;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        // narrow_ov trace (brick 4b): ov carrier dropped, leaf-hash lanes still filled.
        let (tr, counts, binds, index_binds, n_terms, _pv0) =
            build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, false, true, true, true);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let m = MonolithAir {
            counts, binds, index_binds,
            n_queries: proof.opening_proof.query_proofs.len(),
            n_terms, inner_counter: false, column_window: true, k_instances: 1,
            fold: false, fold_txstmt: false, constraints,
            w_inner_f: WIDTH, n_pub_f: N_PUBLIC, n_periodic_f: N_PERIODIC, is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: true, narrow_caps: false, narrow_openings: true, narrow_ov: true,
        };
        let (fw, rate) = (m.fused_w(), 4usize);
        let h = tr.len() / fw;
        // arith heads (tf rows) ⇒ the per-query point x_q = GEN·qt_acc[lg−1] = the held lqk.
        let tf_col = BaseAir::<Val>::periodic_columns(&m)[m.m_tf()].clone();
        let heads: Vec<usize> = (0..h).filter(|&r| tf_col[r % tf_col.len()] == Val::ONE).collect();
        assert_eq!(heads.len(), m.n_queries, "one arith head per query");

        let g = |v: Val| v.as_canonical_u64();
        let (cw, tb, nb, lb) = (m.trm_committed_w(), m.trm_trace_base(), m.trm_next_base(), m.leaf_blocks());
        let mut bus: BTreeMap<(u64, u64, u64), i64> = BTreeMap::new();
        for (q, &head) in heads.iter().enumerate() {
            let off = m.tr() + q * m.m_period();
            let x_q = g(<Goldilocks as Field>::GENERATOR * tr[head * fw + m.qt_acc() + m.lg() - 1]);
            // PROVIDER — walk the PHYSICAL leaf-hash blocks; felt c = b·RATE + l, value = the absorbed rate lane.
            for b in 0..lb {
                for l in 0..rate {
                    let c = b * rate + l;
                    if c >= cw {
                        continue; // w_sel: only committed felts (c < trm_committed_w) are read as px
                    }
                    let v = g(tr[(off + (m.m_input_leaf() + b) * BLOCK) * fw + l]);
                    *bus.entry((x_q, (tb + c) as u64, v)).or_insert(0) -= 1; // shared term trm_trace(c)
                    *bus.entry((x_q, (nb + c) as u64, v)).or_insert(0) -= 1; // shared term trm_next(c)
                }
            }
            // READER — walk the FOLD's TRACE terms; k → felt c(k) via the trace/next ranges; read px at (x_q, k).
            for k in 0..n_terms {
                let c = if k >= tb && k < tb + cw {
                    k - tb
                } else if k >= nb && k < nb + cw {
                    k - nb
                } else {
                    continue; // quotient term — px from the `qc` carrier on the z/px bus, not the leaf-hash bus
                };
                let v = g(tr[(off + (m.m_input_leaf() + c / rate) * BLOCK) * fw + (c % rate)]);
                *bus.entry((x_q, k as u64, v)).or_insert(0) += 1;
            }
        }
        let nonzero = bus.values().filter(|&&v| v != 0).count();
        assert_eq!(nonzero, 0, "the query-keyed leaf-hash→px bus must net to zero ({nonzero} imbalanced tuples)");
        assert_eq!(bus.len(), 2 * cw * m.n_queries, "one balanced tuple per (query, committed felt, term-role trace|next)");
        println!(
            "W3 ov brick 4d: the query-keyed [lqk, term] leaf-hash→px bus BALANCES on the REAL narrow_ov trace — \
             {} tuples net-zero ({} committed felts × 2 shared terms × {} queries), providers walked the physical \
             leaf blocks (w_inner {WIDTH}, {lb} blocks), readers the fold's trace terms, meeting at every felt. \
             Validates the physical leaf layout + w_sel + term↔felt map + query key (x_q) + 2×/felt multiplicity are \
             mutually consistent on the real geometry (the addressing/structure the assembler must reproduce); the \
             in-circuit px binding (AIR eval, compose de-risked by brick 4c) + the heavy prove (OOMs, like 5d) close it.",
            bus.len(), cw, m.n_queries
        );
    }

    /// **Step 5 (W5 GATE 2) — the self-composition marginal B < 1 with narrow_ov, MEASURED cheaply** (`--features
    /// recursion`, cheap; NO inner-monolith prove — `fused_w` is a deterministic width function, so the SLOPE is
    /// inner-independent). The make-or-break SIZE gate: does the fully-narrowed (arith + caps + openings + ov)
    /// self-composing verifier CONTRACT (marginal `B = d(fused_w)/d(w_inner) < 1`) so the recursion tree converges to
    /// an attracting fixed point `W* = A/(1−B)` instead of exploding (the R5 44× blow-up)? Builds the OUTER's
    /// structural params over a real join-split inner (cheap prove), then reads `fused_w` at synthetic widths and
    /// measures the marginal at the four geometries. Asserts the +ov point (brick 4b — the REAL narrow_ov geometry,
    /// not a projection) crosses strictly below 1. The heavy end-to-end prove of the canonical wrap OOMs this box
    /// (`self_composition_b_narrowed`, `#[ignore]`, the R5-authentic cross-check); this is the CHEAP, CI-runnable gate.
    #[cfg(feature = "recursion")]
    #[test]
    fn w5_gate_narrow_ov_marginal_b_below_one() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::build_symbolic_inner_window;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        // the OUTER verifying this inner — its structural params (counts/binds/n_terms) drive fused_w.
        let (_tr, counts, binds, index_binds, n_terms, _pv0) =
            build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, false, false, false, false);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let cap_h = proof.commitments.trace.roots().len().trailing_zeros() as usize;
        // narrow toggles arith(9→2)+caps; nopen ADDS openings (arith_stride→0); nov ADDS the ov carrier (brick 4b).
        let mk = |w_inner: usize, nt: usize, narrow: bool, nopen: bool, nov: bool| MonolithAir {
            counts: counts.clone(), binds: binds.clone(), index_binds: index_binds.clone(),
            n_queries: proof.opening_proof.query_proofs.len(), n_terms: nt,
            inner_counter: false, column_window: true, k_instances: 1, fold: false, fold_txstmt: false,
            constraints: constraints.clone(), w_inner_f: w_inner, n_pub_f: N_PUBLIC, n_periodic_f: N_PERIODIC, is_zk: 0,
            cap_height: cap_h, narrow_arith: narrow || nopen, narrow_caps: narrow, narrow_openings: nopen, narrow_ov: nov };
        let (w0, nt0, d) = (WIDTH, n_terms, 256usize);
        // scale the w_inner-coupled inputs (w_inner + the 2·w_inner trace-ζ/ζ_next terms) by Δ; hold the FRI
        // structure (nqc/cap_height/n_binds — they scale only ~log with the inner size).
        let marg = |narrow: bool, nopen: bool, nov: bool| {
            (mk(w0 + d, nt0 + 2 * d, narrow, nopen, nov).fused_w() - mk(w0, nt0, narrow, nopen, nov).fused_w()) as f64
                / d as f64
        };
        let (mb_full, mb_narrow, mb_open, mb_ov) =
            (marg(false, false, false), marg(true, false, false), marg(true, true, false), marg(true, true, true));
        // the attracting fixed point W* = A/(1−B) exists iff B < 1 (a contraction).
        let (a_ov, w_star) = {
            let wlo = mk(w0, nt0, true, true, true).fused_w() as f64;
            let a = wlo - mb_ov * w0 as f64;
            (a, a / (1.0 - mb_ov))
        };
        println!(
            "W5 GATE (cheap, MEASURED): self-composition marginal B = d(fused_w)/d(w_inner): FULL {mb_full:.2} → \
             arith+caps {mb_narrow:.2} → +openings {mb_open:.2} → +ov {mb_ov:.2} cols/col. The ov externalization \
             (brick 4b) drops the LAST inner-scaling +1 ⇒ B < 1 ⇒ a STRICT CONTRACTION ⇒ the self-composition \
             W_out = {a_ov:.0} + {mb_ov:.2}·W_in converges to an attracting fixed point W* = {w_star:.0} (no \
             explosion). The heavy end-to-end prove OOMs this 62 GB box; the SIZE gate is met by MEASUREMENT.",
        );
        assert!(mb_full > 1.0, "the FULL (un-narrowed) self-composition must be an expansion (B = {mb_full:.2} > 1) — the R5 explosion");
        assert!(mb_open > mb_ov, "the ov externalization must reduce the marginal B ({mb_open:.2} → {mb_ov:.2})");
        assert!(mb_ov < 1.0, "W5 GATE: the narrow_ov marginal B must be strictly < 1 (got {mb_ov:.2}) ⇒ an attracting fixed point W* exists");
    }

    /// **AA5 — the cw=true narrow_caps TRACE builds (openings correct).** `build_symbolic_inner_window` gained a
    /// `narrow_caps` flag that skips the trace/quotient/commit cap felts from the pis window. At `true` it builds
    /// a valid cw=true trace with the cap slice DROPPED — and its internal diagnostics still pass: the native
    /// α-fold == quot(ζ) AND the window holds α/pub/periodic/qwt at the COLLAPSED offsets (`pub_pi`/`periodic_base`
    /// /`qwt_base` shifted down past the gone caps). So the narrow window openings land correctly and the trace
    /// has the reduced `fused_w` (963, cap columns gone). This is the trace-side of the width win; proving the
    /// caps-dropped verifier + wiring the sponge-cap FS-anchor is the remaining assembly.
    #[cfg(feature = "recursion")]
    #[test]
    fn narrow_caps_cw_trace_builds() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::build_symbolic_inner_window;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);

        // narrow_caps=true: the internal α-fold + window (α/pub/periodic/qwt) pre-checks assert INSIDE the builder,
        // so a successful return means the collapsed-window openings are correct.
        let (tr, counts, binds, index_binds, n_terms, _pv0) =
            build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, true, false, false, false);

        // reconstruct the narrow air the trace was built for; the trace width == its (reduced) fused_w.
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let air = MonolithAir {
            counts,
            binds,
            index_binds,
            n_queries: proof.opening_proof.query_proofs.len(),
            n_terms,
            inner_counter: false,
            column_window: true,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints,
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: false,
            narrow_caps: true, narrow_openings: false, narrow_ov: false,
        };
        let fw = air.fused_w();
        assert_eq!(tr.len(), air.height() * fw, "narrow cw=true trace has the reduced fused_w width (caps dropped)");
        assert!(fw < 1200, "narrow fused_w {fw} ≈ 963 (cap columns removed)");
        println!(
            "narrow_caps cw=true trace: 2^{} rows × fused_w {fw} — the α-fold + window pre-checks passed (the \
             collapsed-window openings are correct; caps dropped)",
            air.height().trailing_zeros()
        );
    }

    /// **AA5 — the caps-dropped cw=true verifier PROVES** (`--release --ignored`, heavy). Builds the narrow_caps
    /// cw=true trace (width 963, the ~85% cap columns GONE) and proves + verifies `CapWrapAir { m: narrow }`
    /// through the standard prover — the cap-mux externalized (`CapMuxBci`) so nothing reads the dropped pis caps;
    /// `cap_c` stays a free carrier bound only to the Merkle terminal (the sponge-cap FS-anchor that binds it to
    /// the transcript-absorbed caps is the remaining assembly). So the width win HOLDS AS A REAL STARK — the
    /// cw=true verifier proves at fused_w 963, not just composes. (Mirrors `cap_wrap_externalized_proves`, cw=true.)
    #[cfg(feature = "recursion")]
    #[test]
    #[ignore = "heavy (CONFIRMED ~55s, 2 runs): proves the caps-dropped cw=true verifier (width 963); run `--release --features lookup,recursion -j1 -- --ignored`"]
    fn narrow_caps_cw_verifier_proves() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::build_symbolic_inner_window;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::make_config;
        use p3_matrix::dense::RowMajorMatrix;
        use p3_uni_stark::{get_symbolic_constraints, prove, verify, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (tr, counts, binds, index_binds, n_terms, _pv0) =
            build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, true, false, false, false);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let air = MonolithAir {
            counts,
            binds,
            index_binds,
            n_queries: proof.opening_proof.query_proofs.len(),
            n_terms,
            inner_counter: false,
            column_window: true,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints,
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: false,
            narrow_caps: true, narrow_openings: false, narrow_ov: false,
        };
        let fw = air.fused_w();
        let wrap = CapWrapAir { m: air };
        let prf = prove(&config, &wrap, RowMajorMatrix::new(tr, fw), &[]);
        assert!(verify(&config, &wrap, &prf, &[]).is_ok(), "the caps-dropped cw=true verifier must prove + verify (width {fw})");
    }

    /// **Caps AA5 — build the cw=true assembled cap-wrap trace** (`narrow_caps`: the cap COLUMNS dropped from the
    /// pis window). Mirrors `assemble_cap_wrap` one regime deeper: build the narrow cw=true monolith trace
    /// (`build_symbolic_inner_window(.., true)`, as `narrow_caps_cw_verifier_proves`); widen it for the cap-row
    /// region + the 2·RATE sponge-cap tags; seed each cap entry's row (digest = the FS-absorbed felt
    /// `block_inputs[block][lane]` == the committed cap, `gi_base` = its stream index, `cap_mult` = −#heads
    /// selecting it) and the transcript absorb rows' periodic-pinned tags (`w_gi_l = gi`, `w_sel_l = 1` at each cap
    /// felt's `(block·BLOCK, lane)`). Returns `(air, trace, pis)`; `pis` empty (cw=true — inner pis live in the
    /// witness window). `cap_periodics` = the 2·RATE cap-tag columns the tags are pinned to.
    #[cfg(feature = "recursion")]
    fn assemble_cap_wrap_cw(
        config: &crate::recursion::native_fri::MyConfig,
        proof: &p3_uni_stark::Proof<crate::recursion::native_fri::MyConfig>,
        pvs: &[Val],
    ) -> (AssembledCapWrapCwAir, RowMajorMatrix<Val>, Vec<Val>) {
        use crate::joinsplit_air::{JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::poseidon2_air::BLOCK;
        use crate::recursion::monolith::tests::{build_symbolic_inner_window, sim_cap_positions};
        use crate::recursion::monolith::MonolithAir;
        use p3_matrix::dense::RowMajorMatrix;
        use p3_uni_stark::{get_symbolic_constraints, AirLayout};
        use std::collections::BTreeMap;

        // narrow cw=true monolith trace + air (identical setup to narrow_caps_cw_verifier_proves).
        let (mono_tr, counts, binds, index_binds, n_terms, _pv0) =
            build_symbolic_inner_window(config, &JoinSplitAir, proof, pvs, WIDTH, N_PUBLIC, N_PERIODIC, true, false, false, false);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let m = MonolithAir {
            counts,
            binds,
            index_binds,
            n_queries: proof.opening_proof.query_proofs.len(),
            n_terms,
            inner_counter: false,
            column_window: true,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints,
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: false,
            narrow_caps: true, narrow_openings: false, narrow_ov: false,
        };
        let (fw, h) = (m.fused_w(), m.height());
        let rate = AssembledCapWrapCwAir::CAP_RATE;
        let width = fw + 10 + 2 * rate;
        let (cr, cap_sel_c, is_head_c, gi_base_c) = (fw, fw + 7, fw + 8, fw + 9);
        let w_gi = |l: usize| fw + 10 + 2 * l;
        let w_sel = |l: usize| fw + 11 + 2 * l;

        // The FS-absorbed cap stream: positions[gi] = (cap_id, entry, k, block, lane); the committed felt is the
        // absorbed rate lane block_inputs[block][lane] (== roots()[entry][k], per cap_absorb_stream_matches_committed_caps).
        let (block_inputs, positions) = sim_cap_positions(config, proof, pvs);

        // cap-tag periodics (2·RATE full-height cols): mark each cap felt's (block·BLOCK row, lane) with its gi+sel.
        let mut cap_periodics = vec![vec![Val::ZERO; h]; 2 * rate];
        for (gi, &(_cap_id, _entry, _k, block, lane)) in positions.iter().enumerate() {
            let row = block * BLOCK;
            cap_periodics[2 * lane][row] = Val::from_u64(gi as u64);
            cap_periodics[2 * lane + 1][row] = Val::ONE;
        }

        // group the stream by (cap_id, entry): gi_base (k=0's gi) + the 4 digest felts (the FS-absorbed cap).
        let mut entry_gi: BTreeMap<(usize, usize), usize> = BTreeMap::new();
        let mut entry_dig: BTreeMap<(usize, usize), [Val; 4]> = BTreeMap::new();
        for (gi, &(cap_id, entry, k, block, lane)) in positions.iter().enumerate() {
            if k == 0 {
                entry_gi.insert((cap_id, entry), gi);
            }
            entry_dig.entry((cap_id, entry)).or_insert([Val::ZERO; 4])[k] = block_inputs[block][lane];
        }

        // arith heads (m_tf rows) + the caps with their (shift, bits) for the select-bus count.
        let tf_col = BaseAir::<Val>::periodic_columns(&m)[m.m_tf()].clone();
        let heads: Vec<usize> = (0..h).filter(|&r| tf_col[r % tf_col.len()] == Val::ONE).collect();
        assert_eq!(heads.len(), m.n_queries, "one arith head per query");
        let caps: Vec<(usize, usize, usize)> = {
            let mut v = vec![(0, m.input_depth(), m.cap_height), (1, m.input_depth(), m.cap_height)];
            for r in 0..m.cm_rounds() {
                v.push((2 + r, m.commit_shift(r), m.commit_bits(r)));
            }
            v
        };
        let n_entries: usize = caps.iter().map(|&(_, _, bits)| 1usize << bits).sum();
        let used = m.tr() + m.n_queries * m.m_period();
        assert!(used + n_entries <= h, "cap region ({n_entries}) must fit the slack ({})", h - used);

        let mut wide = vec![Val::ZERO; h * width];
        for r in 0..h {
            wide[r * width..r * width + fw].copy_from_slice(&mono_tr[r * fw..(r + 1) * fw]);
        }
        for &head in &heads {
            wide[head * width + is_head_c] = Val::ONE;
        }
        // the periodic-pinned tag COLUMNS in the trace (MUST equal cap_periodics — the AIR binds them).
        for (gi, &(_cap_id, _entry, _k, block, lane)) in positions.iter().enumerate() {
            let row = block * BLOCK;
            wide[row * width + w_gi(lane)] = Val::from_u64(gi as u64);
            wide[row * width + w_sel(lane)] = Val::ONE;
        }
        // cap-row region: one row per (cap, entry), in the trace slack.
        let mut dst = used;
        for &(cap_id, shift, bits) in &caps {
            let n = 1usize << bits;
            let mut count = vec![0u64; n];
            for &head in &heads {
                let mut e = 0usize;
                for j in 0..bits {
                    if mono_tr[head * fw + m.sb_b(shift + j)] == Val::ONE {
                        e += 1 << j;
                    }
                }
                count[e] += 1;
            }
            for e in 0..n {
                let b = dst * width;
                let dig = entry_dig[&(cap_id, e)];
                wide[b + cr] = Val::from_u64(cap_id as u64);
                wide[b + cr + 1] = Val::from_u64(e as u64);
                for k in 0..4 {
                    wide[b + cr + 2 + k] = dig[k];
                }
                wide[b + cr + 6] = Val::ZERO - Val::from_u64(count[e]); // cap_mult = −count
                wide[b + cap_sel_c] = Val::ONE;
                wide[b + gi_base_c] = Val::from_u64(entry_gi[&(cap_id, e)] as u64);
                dst += 1;
            }
        }

        (AssembledCapWrapCwAir { m, cap_periodics }, RowMajorMatrix::new(wide, width), Vec::new())
    }

    /// **Caps AA5 cw=true — the SOUND capstone composes as a LookupAir** (`--features recursion`). The
    /// [`AssembledCapWrapCwAir`] sibling of `cap_wrap_assembled_composes`: at `column_window=true` + `narrow_caps`
    /// the `2^cap_height` cap columns are DROPPED (the 4.4× fused_w win), and the two buses — the SELECT bus
    /// (`cap_c` ↔ cap-row) and the sponge-cap FS-anchor bus (cap-row digest ↔ the transcript-absorbed cap) —
    /// compose within the degree budget (`log_nqc ≤ LOG_BLOWUP`) at the reduced width.
    #[cfg(feature = "recursion")]
    #[test]
    fn cap_wrap_cw_assembled_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, _trace, _pis) = assemble_cap_wrap_cw(&config, &proof, &pvs);

        let fw = asm.m.fused_w();
        let width = <AssembledCapWrapCwAir as BaseAir<Val>>::width(&asm);
        let n_open = asm.openings().len();
        let lookups = Lookups::from_air::<Challenge, _>(&asm);
        let (_layout, log_nqc) = combined_constraint_layout(&asm, &lookups, 1);
        println!(
            "cap AA5 cw=true: width {width} = fused_w {fw} + 10 + 2·RATE (cap-row region 10 + sponge tags); {} \
             lookup channel(s) (select + sponge-cap FS-anchor), {n_open} select reads/head, log_nqc {log_nqc} ≤ \
             {LOG_BLOWUP}. The caps are DROPPED from the pis window (4.4× win); the sponge-cap bus re-anchors each \
             cap-row digest to the FS-absorbed cap (replacing AA3's now-gone pis anchor).",
            lookups.len()
        );
        assert!(fw < 1200, "narrow cw=true fused_w {fw} ≈ 963 (cap columns dropped)");
        assert_eq!(width, fw + 10 + 2 * AssembledCapWrapCwAir::CAP_RATE, "region 10 + 2·RATE sponge tags");
        assert_eq!(lookups.len(), 2, "2 channels: the select bus + the sponge-cap FS-anchor bus");
        assert!(log_nqc <= LOG_BLOWUP, "cap AA5 cw=true must compose within the degree budget (got {log_nqc})");
    }

    /// **AA6 brick-3 DE-RISK — the sponge-opening bus DISSOLVES the 2c degree wall** (`--features lookup,recursion`,
    /// cheap). The `narrow_openings` integration's crux: binding the epilogue's openings via the ordered sponge bus
    /// must keep `log_nqc ≤ 4` in the ASSEMBLED context, where the op-table's 2c binding (the arith head providing
    /// ~120 openings on ONE row) blew up to `log_nqc 6` (`28df1b2`). Builds [`OpeningBindCwAir`] — the cw=true
    /// narrow monolith + ONE sponge-opening bus (6 tuples/row, SPREAD) — and measures `log_nqc` via
    /// `combined_constraint_layout` (compose-only; the periodics' VALUES don't affect degree, so dummies suffice).
    /// If ≤ 4, the sponge bus's spread provides/reads dissolve the wall ⇒ the whole `narrow_openings` build (arith
    /// fold + op-table epilogue + sponge bus, dropping the 2·n_terms pz cols) is de-risked.
    #[cfg(feature = "recursion")]
    #[test]
    fn opening_bind_cw_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::build_symbolic_inner_window;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (_tr, counts, binds, index_binds, n_terms, _pv0) =
            build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, true, false, false, false);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let m = MonolithAir {
            counts,
            binds,
            index_binds,
            n_queries: proof.opening_proof.query_proofs.len(),
            n_terms,
            inner_counter: false,
            column_window: true,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints,
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: false,
            narrow_caps: true, narrow_openings: false, narrow_ov: false,
        };
        let h = m.height();
        // dummy op_periodics: log_nqc reads the symbolic constraint STRUCTURE (tuple counts/degrees), not the values.
        let op_periodics = vec![vec![Val::ZERO; h]; 2 * OpeningBindCwAir::RATE];
        let air = OpeningBindCwAir { m, op_periodics };
        let width = <OpeningBindCwAir as BaseAir<Val>>::width(&air);
        let lookups = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        println!(
            "AA6 brick-3 DE-RISK: OpeningBindCwAir (cw=true monolith + ONE sponge-opening bus, {} tuples/row) width \
             {width}, {} channel, log_nqc {log_nqc}. The op-table 2c binding (arith head provides ~120 openings on \
             ONE row) hit log_nqc 6; the sponge bus's SPREAD provides/reads stay ≤ {LOG_BLOWUP} ⇒ the sponge bus \
             DISSOLVES the 2c degree wall — the narrow_openings integration is de-risked.",
            OpeningBindCwAir::RATE + 2,
            lookups.len()
        );
        assert_eq!(lookups.len(), 1, "one sponge-opening bus channel");
        assert!(
            log_nqc <= LOG_BLOWUP,
            "the sponge-opening binding must compose ≤ budget in the assembled context (got {log_nqc}) — else the \
             2c wall is NOT dissolved and the narrow_openings approach needs a rethink"
        );
    }

    /// **AA6 op-table binding brick 5a — the cw=true op-table epilogue COMPOSES within budget** (`--features
    /// lookup,recursion`, cheap). [`OpTableBindCwAir`]: the narrow cw=true monolith (`OpeningsBci` epilogue) + the
    /// FLATTEN op-table region (`OpTableF2Air` relations, `op_sel`-gated) + the folded wiring bus binding
    /// `folded_col`. The cw=true sibling of the `AssembledWrapAir` op-table epilogue — which it could NOT reach,
    /// because that AIR's 2c opening-leaf binding provided ~120 openings on the arith head (`log_nqc 6`) AND read
    /// the now-empty `pis`. Routing `folded` through the op-table + wiring bus (SPREAD across slack rows), the
    /// epilogue integrates at cw=true within budget (`log_nqc ≤ LOG_BLOWUP`) — the last epilogue piece before the
    /// full assembly (which binds the opening leaves via the sponge bus + recomposes `quot_col`).
    #[cfg(feature = "recursion")]
    #[test]
    fn optable_bind_cw_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::build_symbolic_inner_window;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (_tr, counts, binds, index_binds, n_terms, _pv0) =
            build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, false, true, true, false);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let m = MonolithAir {
            counts,
            binds,
            index_binds,
            n_queries: proof.opening_proof.query_proofs.len(),
            n_terms,
            inner_counter: false,
            column_window: true,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints,
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: true,
            narrow_caps: false,
            narrow_openings: true, narrow_ov: false,
        };
        let air = OpTableBindCwAir { m, folded_addr: 1 << 20 };
        let fw = air.m.fused_w();
        let width = <OpTableBindCwAir as BaseAir<Val>>::width(&air);
        let lookups = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        println!(
            "AA6 op-table binding brick 5a: OpTableBindCwAir (cw=true narrow monolith + OpeningsBci epilogue + the \
             op-table region [OpTableF2Air relations] + the folded wiring bus) width {width} = fused_w {fw} + 21 \
             (ro/folded/quot 6 + op-table 13 + op_sel + is_head), {} channel(s), log_nqc {log_nqc} ≤ {LOG_BLOWUP} — \
             the epilogue's folded externalized to the op-table + bound to folded_col at cw=true, the 2c wall \
             (AssembledWrapAir's log_nqc 6 / empty-pis) DISSOLVED for the epilogue.",
            lookups.len()
        );
        assert_eq!(width, fw + 6 + 13 + 2, "ro/folded/quot 6 + op-table 13 + op_sel + is_head");
        assert_eq!(lookups.len(), 1, "one op-table wiring + folded bus channel");
        assert!(log_nqc <= LOG_BLOWUP, "the cw=true op-table epilogue must compose within the degree budget (got {log_nqc})");
    }

    /// **AA6 op-table binding brick 5b — the op-table + its sponge-bound opening leaves COMPOSE at cw=true**
    /// (`--features lookup,recursion`, cheap). [`OpTableLeafBindCwAir`]: brick 5a's op-table region + folded bus
    /// PLUS the opening-leaf binding via the sponge (the AA2b machinery, op-table leaf as the reader) — a shared
    /// opening-row reads each opening's felts from the FS-absorbed sponge (channel 2) and re-provides the pair to
    /// the op-table's opening-leaf rows (channel 1). Confirms all THREE channels compose within budget at cw=true
    /// (`log_nqc ≤ LOG_BLOWUP`) — so the op-table epilogue's `local`/`next` leaves bind to the real FS openings
    /// SPREAD (no 2c wall), the last epilogue degree question before the full assembly.
    #[cfg(feature = "recursion")]
    #[test]
    fn optable_leaf_bind_cw_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::build_symbolic_inner_window;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (_tr, counts, binds, index_binds, n_terms, _pv0) =
            build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, false, true, true, false);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let m = MonolithAir {
            counts,
            binds,
            index_binds,
            n_queries: proof.opening_proof.query_proofs.len(),
            n_terms,
            inner_counter: false,
            column_window: true,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints,
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: true,
            narrow_caps: false,
            narrow_openings: true, narrow_ov: false,
        };
        let h = m.height();
        // dummy op_periodics: compose reads the symbolic constraint STRUCTURE, not the values.
        let op_periodics = vec![vec![Val::ZERO; h]; 2 * OpTableLeafBindCwAir::RATE];
        let air = OpTableLeafBindCwAir { m, op_periodics, folded_addr: 1 << 20, bind_window_leaves: false };
        let fw = air.m.fused_w();
        let width = <OpTableLeafBindCwAir as BaseAir<Val>>::width(&air);
        let lookups = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        println!(
            "AA6 op-table binding brick 5b: OpTableLeafBindCwAir (op-table region + folded bus + the op-table-opening \
             bus + the sponge FS-anchor) width {width} = fused_w {fw} + 29 + 2·RATE, {} channels (wiring/folded + \
             op-table-opening + sponge), log_nqc {log_nqc} ≤ {LOG_BLOWUP} — the op-table's local/next leaves bind to \
             the FS openings SPREAD (no 2c wall), so the whole op-table epilogue integrates at cw=true.",
            lookups.len()
        );
        assert_eq!(width, fw + 6 + 13 + 4 + 6 + 2 * OpTableLeafBindCwAir::RATE, "op-table + markers + opening-row + sponge");
        assert_eq!(lookups.len(), 3, "wiring/folded + op-table-opening + sponge FS-anchor");
        assert!(log_nqc <= LOG_BLOWUP, "the cw=true op-table + leaf binding must compose within the degree budget (got {log_nqc})");
    }

    /// **AA6 op-table binding brick 5c — the NON-trace leaves bind via the N_GROUPS split at cw=true** (`--features
    /// lookup,recursion`, cheap). Extends the 5b [`OpTableLeafBindCwAir`] with `bind_window_leaves`: the pubs/
    /// periodic/selector opening leaves are in the TRACE (cw=true window/sel columns), NOT the sponge stream, so
    /// the arith head PROVIDES them reading `cur[pw(..)]`/`cur[sel(..)]` (−is_head). Measured: all 61 (n_pub 26 +
    /// n_periodic 33 + 2 sel) on ONE channel → `log_nqc 6` (the 2c wall recurs — the AssembledWrapAir problem);
    /// SPLIT across `N_GROUPS` channels (~8/channel) → `log_nqc 4`. So the sponge spreads the ~108 TRACE openings
    /// (brick 5b) and the `N_GROUPS` split handles the 61 NON-trace ⇒ the WHOLE op-table opening-leaf binding
    /// composes cw=true within budget. (The op-table leaf's `is_ch` read-routing + the exact `open_id` addressing
    /// land in the full assembly.)
    #[cfg(feature = "recursion")]
    #[test]
    fn optable_window_leaves_split_cw_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::build_symbolic_inner_window;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (_tr, counts, binds, index_binds, n_terms, _pv0) =
            build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, false, true, true, false);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let m = MonolithAir {
            counts,
            binds,
            index_binds,
            n_queries: proof.opening_proof.query_proofs.len(),
            n_terms,
            inner_counter: false,
            column_window: true,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints,
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: true,
            narrow_caps: false,
            narrow_openings: true, narrow_ov: false,
        };
        let (h, n_pub, n_periodic) = (m.height(), m.n_pub(), m.n_periodic());
        let op_periodics = vec![vec![Val::ZERO; h]; 2 * OpTableLeafBindCwAir::RATE];
        let air = OpTableLeafBindCwAir { m, op_periodics, folded_addr: 1 << 20, bind_window_leaves: true };
        let lookups = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        println!(
            "AA6 op-table binding brick 5c: the {} non-trace openings (n_pub {n_pub} + n_periodic {n_periodic} + 2 \
             selectors) — which on ONE channel hit log_nqc 6 (the 2c wall) — SPLIT across N_GROUPS={N_GROUPS} \
             channels (~{}/channel) ⇒ {} channels, log_nqc {log_nqc} ≤ {LOG_BLOWUP}. So the sponge spreads the ~108 \
             TRACE openings (brick 5b) and the N_GROUPS split handles the {} NON-trace ⇒ the WHOLE op-table \
             opening-leaf binding composes at cw=true.",
            n_pub + n_periodic + 2,
            (n_pub + n_periodic + 2).div_ceil(N_GROUPS),
            lookups.len(),
            n_pub + n_periodic + 2,
        );
        assert_eq!(lookups.len(), 3 + N_GROUPS, "wiring/folded + op-table-opening + sponge + N_GROUPS non-trace split");
        assert!(log_nqc <= LOG_BLOWUP, "the N_GROUPS-split non-trace leaf provides must compose within budget (got {log_nqc})");
    }

    /// **AA6 openings AA1+AA2+AA2b cw=true — the FULLY-BOUND reduced-opening fold COMPOSES** (`--features
    /// lookup,recursion`, cheap). The [`AssembledOpeningsWrapCwAir`] compose milestone and the
    /// [`AssembledArithWrapAir`] `arith_wrap_assembled_composes` sibling one regime deeper: at `column_window = true`
    /// + `narrow_openings` (the `2·n_terms` pz opening columns DROPPED) the DEEP fold `ro` is externalized to a
    /// narrow-tall DeepFold region + bound to the arith head via the `ro` bus (AA1, channel 0); the fold's `z`/`px`
    /// INPUTS are bound to the committed columns (AA2, channels 1..=N_GROUPS) — `z` re-derived from ζ = the cw=true
    /// WINDOW `cur[pw(2)]` (NOT the empty pis), `px` from `px_source`; and the fold's `pz` is bound (AA2b) through a
    /// SHARED opening-row region (2-level offline memory) — FS-anchored to the sponge-absorbed opening (channel
    /// N_GROUPS+2) and re-provided 1:N to the per-query folds (the pz bus, channel N_GROUPS+1). Confirms all
    /// N_GROUPS+3 channels compose within the degree budget (`log_nqc ≤ LOG_BLOWUP`) at cw=true — so the reduced
    /// opening is a fold over the REAL FS-absorbed z/pz/px, with the pz COLUMNS gone. `folded_col`/`quot_col` stay
    /// free (the op-table region binds the epilogue next).
    #[cfg(feature = "recursion")]
    #[test]
    fn openings_wrap_cw_assembled_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::build_symbolic_inner_window;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        // narrow_caps = false: the caps stay in the pis window (isolating the openings work); build the window to match.
        let (_tr, counts, binds, index_binds, n_terms, _pv0) =
            build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, false, false, false, false);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let m = MonolithAir {
            counts,
            binds,
            index_binds,
            n_queries: proof.opening_proof.query_proofs.len(),
            n_terms,
            inner_counter: false,
            column_window: true,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints,
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: true,
            narrow_caps: false,
            narrow_openings: true, narrow_ov: false,
        };
        let h = m.height();
        // dummy op_periodics: compose reads the symbolic constraint STRUCTURE, not the values (like opening_bind_cw_composes).
        let op_periodics = vec![vec![Val::ZERO; h]; 2 * AssembledOpeningsWrapCwAir::RATE];
        let air = AssembledOpeningsWrapCwAir { m, op_periodics, bind_optable: false, folded_addr: 0, quot_addr: 0, narrow_ov: false, leaf_periodics: vec![], bind_caps: false, cap_periodics: vec![] };
        let fw = air.m.fused_w();
        let width = <AssembledOpeningsWrapCwAir as BaseAir<Val>>::width(&air);
        let lookups = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        println!(
            "AA6 openings AA1+AA2+AA2b cw=true: width {width} = fused_w {fw} + 35 + N_GROUPS + 2·RATE (ro/folded/quot \
             6 + DeepFold 18 + markers 4 + term_idx 1 + is_ch {N_GROUPS} + opening-row 6 + sponge tags 8); {} channels \
             (ro + {N_GROUPS} z/px input-binding + pz bus + sponge FS-anchor), log_nqc {log_nqc} ≤ {LOG_BLOWUP}. The pz \
             columns are DROPPED (narrow_openings); the fold's z/px/pz ALL bound — z from the cw=true window ζ=pw(2), \
             px from px_source, pz via the shared opening-row (FS-anchored to the sponge-absorbed opening + re-provided \
             1:N). folded_col/quot_col stay free (the op-table region binds them next).",
            lookups.len()
        );
        assert_eq!(
            width,
            fw + 6 + 18 + 4 + 1 + N_GROUPS + 6 + 2 * AssembledOpeningsWrapCwAir::RATE,
            "ro/folded/quot 6 + DeepFold 18 + markers 4 + term_idx 1 + is_ch N_GROUPS + opening-row 6 + sponge tags 2·RATE"
        );
        assert_eq!(lookups.len(), N_GROUPS + 3, "ro + N_GROUPS z/px input-binding + pz bus + sponge FS-anchor");
        assert!(log_nqc <= LOG_BLOWUP, "openings AA1+AA2+AA2b cw=true must compose within the degree budget (got {log_nqc})");
    }

    /// **AA6 brick 5d.1+5d.2+5d.3 — the op-table folded + opening-leaf + quot binding COEXIST with the openings fold
    /// at cw=true** (`--features lookup,recursion`, cheap). Extends `openings_wrap_cw_assembled_composes` with
    /// `bind_optable`: the
    /// [`AssembledOpeningsWrapCwAir`] now ALSO appends the op-table region ([`OpTableF2Air`] relations, op_sel-gated)
    /// computing `folded` + a folded wiring bus (channel N_GROUPS+3) binding `folded_col` to the op-table's fold — so
    /// the epilogue `folded·inv_van == quot` ([`OpeningsBci`]) reads a fold actually computed in slack, not a free
    /// witness (5d.1). **5d.2** binds the op-table's opening LEAVES (its `c_k` inputs) to the real FS-absorbed openings:
    /// TRACE leaves (Main{0}/Main{1}) read at `term_idx` off the SHARED opening-row's pz provide (the same FS-anchored
    /// value the DeepFold folds — no second sponge anchor); NON-trace leaves (Public/Periodic/selector) read at their
    /// canonical `open_id` off the arith head's cw=true-window provide, SPLIT across N_GROUPS channels (the brick-5c
    /// pattern — all ~62 on one channel would recur the 2c wall). Confirms the DeepFold arith region + the op-table
    /// region + the opening-leaf buses + all 2·N_GROUPS+4 channels COEXIST within the degree budget (`log_nqc ≤
    /// LOG_BLOWUP`) at cw=true — the DeepFold/op-table coexistence the handoff flagged as the key open question.
    /// **5d.3** binds `quot_col` too: the quotient recompose `quot(ζ) = Σ zps_i·(d0_i + X·d1_i)` is appended to the
    /// op-table as more rows (X·d1 = emul((0,1),d1), all mul/add), so the head reads `quot_col` at `quot_addr` on the
    /// wiring bus; the quot-chunk openings d0/d1 are TRACE leaves at `term_idx = trm_quot(i,j)`, the nqc qwt weights
    /// zps_i are non-trace leaves off the cw=true window (`pw(qwt_base+2i)`). So BOTH free witnesses (`folded_col`,
    /// `quot_col`) that made the epilogue vacuous are now bound — the AIR is complete; the trace/balance/prove follow.
    #[cfg(feature = "recursion")]
    #[test]
    fn optable_openings_wrap_cw_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::build_symbolic_inner_window;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        // narrow_caps = false: the caps stay in the pis window (isolating the openings work); build the window to match.
        let (_tr, counts, binds, index_binds, n_terms, _pv0) =
            build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, false, false, false, false);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let m = MonolithAir {
            counts,
            binds,
            index_binds,
            n_queries: proof.opening_proof.query_proofs.len(),
            n_terms,
            inner_counter: false,
            column_window: true,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints,
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: true,
            narrow_caps: false,
            narrow_openings: true, narrow_ov: false,
        };
        let h = m.height();
        // dummy op_periodics: compose reads the symbolic constraint STRUCTURE, not the values.
        let op_periodics = vec![vec![Val::ZERO; h]; 2 * AssembledOpeningsWrapCwAir::RATE];
        let air = AssembledOpeningsWrapCwAir { m, op_periodics, bind_optable: true, folded_addr: 1 << 20, quot_addr: 1 << 21, narrow_ov: false, leaf_periodics: vec![], bind_caps: false, cap_periodics: vec![] };
        let fw = air.m.fused_w();
        let width = <AssembledOpeningsWrapCwAir as BaseAir<Val>>::width(&air);
        let lookups = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        println!(
            "AA6 brick 5d.1+5d.2+5d.3 (op-table folded + opening-leaf + quot binding): width {width} = fused_w {fw} \
             + 35 + N_GROUPS + 2·RATE + 16 + N_GROUPS (op-table 13 + op_sel + is_tr_leaf + leaf_key + op_is_ch \
             N_GROUPS); {} channels (ro + {N_GROUPS} z/px + pz + sponge + folded/quot wiring + {N_GROUPS} non-trace \
             split), log_nqc {log_nqc} ≤ {LOG_BLOWUP}. The DeepFold arith region + the op-table region COEXIST; \
             folded_col AND quot_col bound to the op-table's fold/recompose; trace + quot-chunk leaves read at \
             term_idx (shared pz provide), non-trace + qwt weights via the N_GROUPS split. Trace/balance/prove next.",
            lookups.len()
        );
        assert_eq!(
            width,
            fw + 6 + 18 + 4 + 1 + N_GROUPS + 6 + 2 * AssembledOpeningsWrapCwAir::RATE + 16 + N_GROUPS,
            "base openings width + op-table 13 + op_sel + is_tr_leaf + leaf_key + op_is_ch(N_GROUPS)"
        );
        assert_eq!(
            lookups.len(),
            2 * N_GROUPS + 4,
            "ro + N_GROUPS z/px + pz + sponge + op-table folded wiring + N_GROUPS non-trace-leaf split"
        );
        assert!(log_nqc <= LOG_BLOWUP, "brick 5d op-table + openings coexistence must compose within budget (got {log_nqc})");
    }

    /// **Brick 4d (compose) — the narrow_ov openings-wrap composes.** The full assembled openings-wrap (DeepFold + ro
    /// + z/px + pz + sponge) with `narrow_ov`: the ov opened-row carrier DROPPED, the z/px bus provides px=0 for TRACE
    /// terms, and the leaf-hash→px bus (held `lqk` + `[lqk, term]` key + 2-provides/lane) binds trace px to the
    /// authenticated leaf lane. Composes at `log_nqc ≤ LOG_BLOWUP` — the DEGREE de-risk for the assembled narrow_ov
    /// prove (balance + prove next). Additive; flag-off byte-identical (the proven openings/optable compose untouched).
    #[cfg(feature = "recursion")]
    #[test]
    fn narrow_ov_openings_wrap_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::build_symbolic_inner_window;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (_tr, counts, binds, index_binds, n_terms, _pv0) =
            build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, false, true, true, true);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let m = MonolithAir {
            counts, binds, index_binds,
            n_queries: proof.opening_proof.query_proofs.len(), n_terms,
            inner_counter: false, column_window: true, k_instances: 1, fold: false, fold_txstmt: false,
            constraints, w_inner_f: WIDTH, n_pub_f: N_PUBLIC, n_periodic_f: N_PERIODIC, is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: true, narrow_caps: false, narrow_openings: true, narrow_ov: true,
        };
        let h = m.height();
        let op_periodics = vec![vec![Val::ZERO; h]; 2 * AssembledOpeningsWrapCwAir::RATE];
        let leaf_periodics = vec![vec![Val::ZERO; h]; 3 * AssembledOpeningsWrapCwAir::RATE];
        let air = AssembledOpeningsWrapCwAir {
            m, op_periodics, bind_optable: false, folded_addr: 0, quot_addr: 0, narrow_ov: true, leaf_periodics,
            bind_caps: false, cap_periodics: vec![],
        };
        let width = <AssembledOpeningsWrapCwAir as BaseAir<Val>>::width(&air);
        let lookups = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        println!(
            "Brick 4d (compose): narrow_ov openings-wrap width {width}, {} channels (+ leaf-hash→px), log_nqc \
             {log_nqc} ≤ {LOG_BLOWUP} — the ov carrier externalized (px=0 for trace on the z/px bus, bound via the \
             leaf-hash bus keyed by held lqk=x).",
            lookups.len()
        );
        assert_eq!(lookups.len(), N_GROUPS + 4, "ro + N_GROUPS z/px + pz + sponge + leaf-hash→px");
        assert!(log_nqc <= LOG_BLOWUP, "the narrow_ov openings-wrap must compose within budget (got {log_nqc})");
    }

    /// **Tier-1 width merge M1b — the ASSEMBLED caps ⊕ openings wrap composes.** The full assembled AIR with
    /// `bind_caps` (the `narrow_caps` monolith + [`CapOpeningsBci`] + the cap-row region + the SELECT and SPONGE-CAP
    /// buses) COMBINED with the openings externalization (DeepFold `ro` + z/px + pz + sponge) — the assembled-eval
    /// integration of the 9.2× width merge. `narrow_ov` stays off here (it enters via the leaf-hash bus, LAST channel,
    /// separately). Composes at `log_nqc ≤ LOG_BLOWUP` with `N_GROUPS+5` channels (openings `N_GROUPS+3` + caps SELECT
    /// + SPONGE-CAP), so the cap-mux externalization (cap COLUMNS gone) bus-binds in the SAME AIR as the openings.
    #[cfg(feature = "recursion")]
    #[test]
    fn cap_merge_openings_wrap_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::build_symbolic_inner_window;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        // narrow_caps + narrow_arith + narrow_openings (narrow_ov off — bind_caps ⊕ openings merge only).
        let (_tr, counts, binds, index_binds, n_terms, _pv0) =
            build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, true, true, true, false);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let m = MonolithAir {
            counts, binds, index_binds,
            n_queries: proof.opening_proof.query_proofs.len(), n_terms,
            inner_counter: false, column_window: true, k_instances: 1, fold: false, fold_txstmt: false,
            constraints, w_inner_f: WIDTH, n_pub_f: N_PUBLIC, n_periodic_f: N_PERIODIC, is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: true, narrow_caps: true, narrow_openings: true, narrow_ov: false,
        };
        let h = m.height();
        let op_periodics = vec![vec![Val::ZERO; h]; 2 * AssembledOpeningsWrapCwAir::RATE];
        let cap_periodics = vec![vec![Val::ZERO; h]; 2 * AssembledOpeningsWrapCwAir::CAP_RATE];
        let air = AssembledOpeningsWrapCwAir {
            m, op_periodics, bind_optable: false, folded_addr: 0, quot_addr: 0, narrow_ov: false, leaf_periodics: vec![],
            bind_caps: true, cap_periodics,
        };
        let width = <AssembledOpeningsWrapCwAir as BaseAir<Val>>::width(&air);
        let lookups = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        println!(
            "Tier-1 MERGE M1b (assembled compose): caps ⊕ openings wrap width {width}, {} channels (openings + caps \
             SELECT + SPONGE-CAP), log_nqc {log_nqc} ≤ {LOG_BLOWUP} — the cap-mux externalized (narrow_caps, cap \
             COLUMNS gone) AND bus-bound in the SAME assembled AIR as the openings externalization.",
            lookups.len()
        );
        assert_eq!(lookups.len(), N_GROUPS + 5, "openings (ro + N_GROUPS z/px + pz + sponge) + caps SELECT + SPONGE-CAP");
        assert!(log_nqc <= LOG_BLOWUP, "the assembled caps ⊕ openings merge must compose within budget (got {log_nqc})");
    }

    /// **Tier-1 width merge M1a — the caps ⊕ openings externalizations coexist under budget.** The combined
    /// [`CapOpeningsBci`] externalizes BOTH the cap-mux (`CapMuxBci`) AND the arith fold + epilogue (`OpeningsBci`)
    /// in ONE bare verifier (`narrow_caps` + `narrow_arith` + `narrow_openings`). This is the DEGREE de-risk for the
    /// 6.6× width merge — the NEW risk being whether the two externalizations coexist at `log_nqc ≤ LOG_BLOWUP`
    /// (narrow_ov's coexistence with openings was already proven this session). `narrow_ov` is NOT a free-witness bare
    /// verifier (its `px` has no source without the leaf-hash bus), so it enters only in the assembled merge — but its
    /// `fused_w` contribution is pure column arithmetic, so the FULL 4-flag width win (the ~585 number vs ~3849) is
    /// measured here regardless. `ro`/`folded`/`quot` are FREE columns (bound in the assembled merge next).
    #[cfg(feature = "recursion")]
    #[test]
    fn cap_narrow_wrap_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::build_symbolic_inner_window;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::make_config;
        use p3_lookup::InteractionSymbolicBuilder;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        // Only counts/binds/n_terms (the symbolic shape) matter for log_nqc + fused_w. `full` (no flags) is the
        // un-narrowed baseline; the 4-flag combo gives the fully-narrowed width (bus-independent column arithmetic).
        let mk = |ncaps: bool, narith: bool, nopen: bool, nov: bool| {
            let (_tr, counts, binds, index_binds, n_terms, _pv0) = build_symbolic_inner_window(
                &config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, ncaps, narith, nopen, nov,
            );
            MonolithAir {
                counts, binds, index_binds,
                n_queries: proof.opening_proof.query_proofs.len(), n_terms,
                inner_counter: false, column_window: true, k_instances: 1, fold: false, fold_txstmt: false,
                constraints: constraints.clone(), w_inner_f: WIDTH, n_pub_f: N_PUBLIC, n_periodic_f: N_PERIODIC, is_zk: 0,
                cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
                narrow_arith: narith, narrow_caps: ncaps, narrow_openings: nopen, narrow_ov: nov,
            }
        };
        let fw_full = mk(false, false, false, false).fused_w();
        let fw_4flag = mk(true, true, true, true).fused_w(); // the full merge target (~585) — pure width, bus-independent
        // The caps ⊕ openings bare verifier (narrow_ov off — it needs the assembled bus, not a free witness). A bare
        // verifier pushes NO interactions, so `combined_constraint_layout`'s eval_all (which assumes ≥1 lookup)
        // doesn't apply; measure the BASE-constraint degree directly via the symbolic builder — the real degree
        // de-risk (do the two externalized checks combine above budget?). The per-channel bus degrees were already
        // proven ≤ budget for caps and openings SEPARATELY, and log_nqc = max(base, bus) over disjoint constraints.
        let air = CapNarrowWrapAir { m: mk(true, true, true, false) };
        let width = <CapNarrowWrapAir as BaseAir<Val>>::width(&air);
        let mut isb = InteractionSymbolicBuilder::<Val, Challenge>::new(AirLayout::from_air(&air));
        air.eval(&mut isb);
        let max_deg = isb
            .base_constraints()
            .iter()
            .map(|c| c.degree_multiple())
            .chain(isb.extension_constraints().iter().map(|c| c.degree_multiple()))
            .max()
            .unwrap_or(0);
        let log_nqc = (max_deg.max(2) - 1).next_power_of_two().ilog2() as usize;
        println!(
            "Tier-1 MERGE (compose): fused_w FULL {fw_full} → 4-flag NARROW {fw_4flag} ({:.1}× width win). The caps ⊕ \
             openings bare verifier (AIR width {width}) has base-constraint degree {max_deg} ⇒ log_nqc {log_nqc} ≤ \
             {LOG_BLOWUP} — the cap-mux AND the arith fold/epilogue externalizations coexist in ONE verifier under \
             budget (ro/folded/quot free, bound in the assembled merge; narrow_ov enters there via the leaf-hash bus).",
            fw_full as f64 / fw_4flag as f64
        );
        assert!(log_nqc <= LOG_BLOWUP, "caps ⊕ openings base constraints must stay within budget (got log_nqc {log_nqc})");
        assert!(fw_4flag * 4 < fw_full, "the merge must be a large width win (got FULL {fw_full} → 4-flag {fw_4flag})");
    }

    /// **AA6 openings AA3 — assemble the cw=true narrow-openings wrap trace** (the [`AssembledOpeningsWrapCwAir`]
    /// companion of `assemble_arith_wrap` one regime deeper, borrowing `assemble_cap_wrap_cw`'s sponge machinery).
    /// Builds the narrow cw=true monolith (`narrow_arith` + `narrow_openings`: the `9·n_terms` arith tile GONE),
    /// then widens it with (a) a per-query DeepFold slack region — `α`/`x` from the head's committed columns, `z`
    /// re-derived from the window ζ (= `pw(2)`, NOT pis), `px` from `px_source`, `pz` from the FS-absorbed committed
    /// opening (the tile no longer stores it); (b) the shared opening-row region (one row per DEEP opening term)
    /// carrying that `pz`, FS-anchored to the sponge + re-provided `−n_queries`; (c) the `2·RATE` periodic-pinned
    /// sponge tags marking each opening felt's `(block, lane)` with its stream index. A per-query assert that the
    /// DeepFold `ro` reproduces the committed reduced opening (`QT_E`) validates the z/px/pz sourcing + the
    /// term↔stream ordering at assembly time (before the heavy prove).
    #[cfg(feature = "recursion")]
    fn assemble_openings_wrap_cw(
        config: &crate::recursion::native_fri::MyConfig,
        proof: &p3_uni_stark::Proof<crate::recursion::native_fri::MyConfig>,
        pvs: &[Val],
        bind_optable: bool,
        narrow_ov: bool,
        bind_caps: bool,
    ) -> (AssembledOpeningsWrapCwAir, RowMajorMatrix<Val>, Vec<Val>) {
        use crate::config::Challenge;
        use crate::joinsplit_air::{JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::poseidon2_air::BLOCK;
        use crate::recursion::monolith::tests::{build_symbolic_inner_window, sim_cap_positions, sim_opening_positions};
        use crate::recursion::monolith::MonolithAir;
        use crate::wrap::deep_fold_trace_from;
        use p3_field::{BasedVectorSpace, Field, TwoAdicField};
        use p3_goldilocks::Goldilocks;
        use p3_matrix::dense::RowMajorMatrix;
        use p3_uni_stark::{get_symbolic_constraints, AirLayout};
        use std::collections::BTreeMap;

        // narrow cw=true monolith trace + air (narrow_arith + narrow_openings [+ narrow_caps when bind_caps]).
        let (mono_tr, counts, binds, index_binds, n_terms, _pv0) = build_symbolic_inner_window(
            config, &JoinSplitAir, proof, pvs, WIDTH, N_PUBLIC, N_PERIODIC, bind_caps, true, true, narrow_ov,
        );
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let m = MonolithAir {
            counts,
            binds,
            index_binds,
            n_queries: proof.opening_proof.query_proofs.len(),
            n_terms,
            inner_counter: false,
            column_window: true,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints,
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: true,
            narrow_caps: bind_caps,
            narrow_openings: true, narrow_ov,
        };
        let (fw, h) = (m.fused_w(), m.height());
        let rate = AssembledOpeningsWrapCwAir::RATE;
        let caprate = AssembledOpeningsWrapCwAir::CAP_RATE;

        // Column bases — MUST match `AssembledOpeningsWrapCwAir`'s accessors.
        let ro_col = fw;
        let db = fw + 6; // after ro/folded/quot (6)
        let (df_sel, df_first, df_end, is_head, term_idx, is_ch0) =
            (db + 18, db + 19, db + 20, db + 21, db + 22, db + 23);
        let or_base = db + 23 + N_GROUPS;
        let (or_gi, or_pz, or_sel, or_k, or_mult) = (or_base, or_base + 1, or_base + 3, or_base + 4, or_base + 5);
        let st_base = or_base + 6;
        let w_gi = |l: usize| st_base + 2 * l;
        let w_sel = |l: usize| st_base + 2 * l + 1;
        // brick 4d narrow_ov column bases (after the whole ro/DeepFold/opening(/optable) layout).
        let nov_base = fw + 6 + 18 + 4 + 1 + N_GROUPS + 6 + 2 * rate + if bind_optable { 16 + N_GROUPS } else { 0 };
        let (held_lqk, df_is_quot) = (nov_base, nov_base + 1);
        let w_term0 = |l: usize| nov_base + 2 + 3 * l;
        let w_term1 = |l: usize| nov_base + 3 + 3 * l;
        let w_lsel = |l: usize| nov_base + 4 + 3 * l;
        // Tier-1 merge: the cap-region base (after nov + narrow_ov cols) — cap-row(7) + cap_sel + gi_base + 2·caprate.
        let cap_base = nov_base + if narrow_ov { 2 + 3 * rate } else { 0 };
        let (cr, cap_sel_c, cap_gi_base) = (cap_base, cap_base + 7, cap_base + 8);
        let cap_w_gi = |l: usize| cap_base + 9 + 2 * l;
        let cap_w_sel = |l: usize| cap_base + 9 + 2 * l + 1;
        let width = cap_base + if bind_caps { 9 + 2 * caprate } else { 0 };

        // The FS-absorbed opening stream: positions[gi] = (oid, coeff, block, lane); committed[gi] = the felt
        // (== block_inputs[block][lane], the absorbed rate lane). A DEEP term k's F_p² opening is the pair
        // (committed[2k], committed[2k+1]) at stream indices (2k, 2k+1) — the `or_gi = 2·term` correspondence.
        let (_block_inputs, positions, committed) = sim_opening_positions(config, proof, pvs);
        assert_eq!(committed.len(), 2 * n_terms, "each DEEP term is one F_p² opening (2 felts) in stream order");

        // op_periodics (2·RATE full-height cols): mark each opening felt's (block·BLOCK row, lane) with its gi+sel.
        let mut op_periodics = vec![vec![Val::ZERO; h]; 2 * rate];
        for (gi, &(_oid, _coeff, block, lane)) in positions.iter().enumerate() {
            op_periodics[2 * lane][block * BLOCK] = Val::from_u64(gi as u64);
            op_periodics[2 * lane + 1][block * BLOCK] = Val::ONE;
        }
        // brick 4d leaf_periodics (3·RATE full-height cols): per query's leaf-hash block row, lane l ⇒ the two shared
        // DEEP term ids trm_trace(c)/trm_next(c) + select (c = b·RATE+l committed) — the AIR pins the tag COLUMNS to
        // these. Same values every query (the felt→term map + super-tile leaf offset repeat), matching the trace fill.
        let mut leaf_periodics = vec![vec![Val::ZERO; h]; 3 * rate];
        if narrow_ov {
            for q in 0..m.n_queries {
                let off = m.tr() + q * m.m_period();
                for b in 0..m.leaf_blocks() {
                    let lrow = off + (m.m_input_leaf() + b) * BLOCK;
                    for l in 0..rate {
                        let c = b * rate + l;
                        if c >= m.trm_committed_w() {
                            continue;
                        }
                        leaf_periodics[3 * l][lrow] = Val::from_u64(m.trm_trace(c) as u64);
                        leaf_periodics[3 * l + 1][lrow] = Val::from_u64(m.trm_next(c) as u64);
                        leaf_periodics[3 * l + 2][lrow] = Val::ONE;
                    }
                }
            }
        }

        // arith heads (m_tf rows) — one DeepFold region per query, then the shared opening-row region.
        let tf_col = BaseAir::<Val>::periodic_columns(&m)[m.m_tf()].clone();
        let heads: Vec<usize> = (0..h).filter(|&r| tf_col[r % tf_col.len()] == Val::ONE).collect();
        assert_eq!(heads.len(), m.n_queries, "one arith head per query");
        let used = m.tr() + m.n_queries * m.m_period();
        // Tier-1 merge: the cap-region (bind_caps) takes 2·2^cap_height (trace+quot) + Σ 2^commit_bits(r) slack rows
        // AFTER the DeepFold regions + opening-rows.
        let n_cap_rows = if bind_caps {
            let mut n = 2 * (1usize << m.cap_height);
            for r in 0..m.cm_rounds() {
                n += 1usize << m.commit_bits(r);
            }
            n
        } else {
            0
        };
        assert!(
            used + n_terms * m.n_queries + n_terms + n_cap_rows <= h,
            "DeepFold regions + opening-rows + cap-region ({}) must fit the monolith slack ({})",
            n_terms * m.n_queries + n_terms + n_cap_rows,
            h - used
        );

        let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
        let mut wide = vec![Val::ZERO; h * width];
        for r in 0..h {
            wide[r * width..r * width + fw].copy_from_slice(&mono_tr[r * fw..(r + 1) * fw]);
        }
        // the periodic-pinned tag COLUMNS in the trace (MUST equal op_periodics — the AIR binds them).
        for (gi, &(_oid, _coeff, block, lane)) in positions.iter().enumerate() {
            let row = block * BLOCK;
            wide[row * width + w_gi(lane)] = Val::from_u64(gi as u64);
            wide[row * width + w_sel(lane)] = Val::ONE;
        }

        let g_trace = Goldilocks::two_adic_generator(m.cm_rounds() - m.is_zk);
        for (q, &head) in heads.iter().enumerate() {
            let row = |col: usize| mono_tr[head * fw + col];
            let alpha = Challenge::from_basis_coefficients_fn(|i| row(m.qt_alpha() + i));
            let x = Challenge::from(<Goldilocks as Field>::GENERATOR * row(m.qt_acc() + m.lg() - 1));
            // cw=true: ζ from the committed WINDOW pw(2), NOT pis (empty at cw=true).
            let zeta = Challenge::from_basis_coefficients_fn(|i| row(m.pw(2 + i)));
            let off = m.tr() + q * m.m_period(); // query q's super-tile start
            let terms: Vec<(Challenge, Challenge, Challenge)> = (0..n_terms)
                .map(|k| {
                    let z = if k >= m.trm_next_base() && k < m.trm_quot_base() { zeta * g_trace } else { zeta };
                    let pz = Challenge::from_basis_coefficients_fn(|i| committed[2 * k + i]);
                    // narrow_ov: a TRACE term's px `ov_c` carrier is dropped — source it from the authenticated leaf
                    // lane (felt c → leaf-hash block c/RATE lane c%RATE). Quotient terms keep px from `qc` (px_source).
                    let px = if narrow_ov && k < m.trm_quot_base() {
                        let c = if k >= m.trm_trace_base() && k < m.trm_trace_base() + m.trm_committed_w() {
                            k - m.trm_trace_base()
                        } else {
                            k - m.trm_next_base()
                        };
                        Challenge::from(mono_tr[(off + (m.m_input_leaf() + c / rate) * BLOCK) * fw + (c % rate)])
                    } else {
                        Challenge::from(row(m.px_source(k)))
                    };
                    (z, pz, px)
                })
                .collect();
            let region = deep_fold_trace_from(alpha, x, &terms, 0);
            let dw = region.width; // 18
            let ro_last = Challenge::from_basis_coefficients_fn(|i| region.values[(n_terms - 1) * dw + 16 + i]);
            // The fold ro MUST reproduce the committed reduced opening at QT_E (= column 0) — validates z/px/pz
            // sourcing AND the term↔stream ordering before the heavy prove.
            assert_eq!(
                ro_last,
                Challenge::from_basis_coefficients_fn(|i| row(i)),
                "query {q}: DeepFold ro must equal the committed reduced opening (QT_E = col 0)"
            );
            wide[head * width + ro_col..head * width + ro_col + 2].copy_from_slice(&cc(ro_last));
            wide[head * width + is_head] = Val::ONE;

            for k in 0..n_terms {
                let dst = used + q * n_terms + k;
                wide[dst * width + db..dst * width + db + 18].copy_from_slice(&region.values[k * dw..k * dw + 18]);
                wide[dst * width + df_sel] = Val::ONE;
                wide[dst * width + term_idx] = Val::from_u64(k as u64);
                wide[dst * width + is_ch0 + k % N_GROUPS] = Val::ONE; // route the read to the term's channel k%N_GROUPS
                if k == 0 {
                    wide[dst * width + df_first] = Val::ONE;
                }
                if k == n_terms - 1 {
                    wide[dst * width + df_end] = Val::ONE;
                }
                // narrow_ov: a QUOTIENT region row keeps its px on the z/px bus (df_is_quot=1); a TRACE row binds px
                // via the leaf-hash bus (df_is_quot=0 ⇒ z/px px=0, leaf-hash read active).
                if narrow_ov {
                    wide[dst * width + df_is_quot] = if k >= m.trm_quot_base() { Val::ONE } else { Val::ZERO };
                }
            }
            // narrow_ov: HELD lqk = x (the query point base felt) across the super-tile; the leaf-hash provide + the
            // region read key on it (query-unique). `x`'s base felt = GEN·qt_acc[lg−1] (== the region rows' `x.0`).
            if narrow_ov {
                let x_felt = <Goldilocks as Field>::GENERATOR * row(m.qt_acc() + m.lg() - 1);
                for r in off..off + m.m_period() {
                    wide[r * width + held_lqk] = x_felt;
                }
                // leaf-hash provide tags: per leaf-hash block row, rate lane l, felt c = b·RATE+l ⇒ the two shared
                // DEEP terms trm_trace(c)/trm_next(c) + select (c committed). Set the trace COLUMNS (the periodic below
                // must match — the AIR pins the columns to the periodic).
                for b in 0..m.leaf_blocks() {
                    let lrow = off + (m.m_input_leaf() + b) * BLOCK;
                    for l in 0..rate {
                        let c = b * rate + l;
                        if c >= m.trm_committed_w() {
                            continue;
                        }
                        wide[lrow * width + w_term0(l)] = Val::from_u64(m.trm_trace(c) as u64);
                        wide[lrow * width + w_term1(l)] = Val::from_u64(m.trm_next(c) as u64);
                        wide[lrow * width + w_lsel(l)] = Val::ONE;
                    }
                }
            }
        }

        // the SHARED opening-row region: one row per DEEP opening term k — FS-anchored to the sponge (reads its 2
        // opening felts) and re-provided `−n_queries` to every query's DeepFold row via the pz bus.
        let or_start = used + n_terms * m.n_queries;
        for k in 0..n_terms {
            let b = (or_start + k) * width;
            wide[b + or_gi] = Val::from_u64(2 * k as u64);
            wide[b + or_pz] = committed[2 * k];
            wide[b + or_pz + 1] = committed[2 * k + 1];
            wide[b + or_sel] = Val::ONE;
            wide[b + or_k] = Val::from_u64(k as u64);
            // Each term is provided once to the DeepFold (−n_queries reads); when bind_optable the op-table ALSO
            // reads every term once (trace via a preseed leaf, quot via the recompose), so or_mult absorbs the +1.
            wide[b + or_mult] = Val::ZERO - Val::from_u64(m.n_queries as u64 + if bind_optable { 1 } else { 0 });
        }

        // Tier-1 merge — the cap-region (bind_caps): mirror `assemble_cap_wrap_cw`, placed in the slack AFTER the
        // opening-rows. `cap_c` (freed by `CapMuxBci`) is re-bound by the SELECT + SPONGE-CAP buses. `is_head` is
        // SHARED with the openings region (already set at head rows), so only the cap-row region + tags are filled.
        let mut cap_periodics: Vec<Vec<Val>> = Vec::new();
        if bind_caps {
            let (block_inputs, positions) = sim_cap_positions(config, proof, pvs);
            cap_periodics = vec![vec![Val::ZERO; h]; 2 * caprate];
            for (gi, &(_cap_id, _entry, _k, block, lane)) in positions.iter().enumerate() {
                let row = block * BLOCK;
                cap_periodics[2 * lane][row] = Val::from_u64(gi as u64);
                cap_periodics[2 * lane + 1][row] = Val::ONE;
                // the periodic-pinned tag COLUMNS in the trace (MUST equal cap_periodics — the AIR binds them).
                wide[row * width + cap_w_gi(lane)] = Val::from_u64(gi as u64);
                wide[row * width + cap_w_sel(lane)] = Val::ONE;
            }
            // group the stream by (cap_id, entry): gi_base (k=0's gi) + the 4 digest felts (the FS-absorbed cap).
            let mut entry_gi: BTreeMap<(usize, usize), usize> = BTreeMap::new();
            let mut entry_dig: BTreeMap<(usize, usize), [Val; 4]> = BTreeMap::new();
            for (gi, &(cap_id, entry, k, block, lane)) in positions.iter().enumerate() {
                if k == 0 {
                    entry_gi.insert((cap_id, entry), gi);
                }
                entry_dig.entry((cap_id, entry)).or_insert([Val::ZERO; 4])[k] = block_inputs[block][lane];
            }
            let caps: Vec<(usize, usize, usize)> = {
                let mut v = vec![(0, m.input_depth(), m.cap_height), (1, m.input_depth(), m.cap_height)];
                for r in 0..m.cm_rounds() {
                    v.push((2 + r, m.commit_shift(r), m.commit_bits(r)));
                }
                v
            };
            // cap-row region: one row per (cap, entry), in the slack AFTER the opening-rows.
            let mut dst = or_start + n_terms;
            for &(cap_id, shift, bits) in &caps {
                let n = 1usize << bits;
                let mut count = vec![0u64; n];
                for &head in &heads {
                    let mut e = 0usize;
                    for j in 0..bits {
                        if mono_tr[head * fw + m.sb_b(shift + j)] == Val::ONE {
                            e += 1 << j;
                        }
                    }
                    count[e] += 1;
                }
                for e in 0..n {
                    let b = dst * width;
                    let dig = entry_dig[&(cap_id, e)];
                    wide[b + cr] = Val::from_u64(cap_id as u64);
                    wide[b + cr + 1] = Val::from_u64(e as u64);
                    for k in 0..4 {
                        wide[b + cr + 2 + k] = dig[k];
                    }
                    wide[b + cr + 6] = Val::ZERO - Val::from_u64(count[e]); // cap_mult = −count
                    wide[b + cap_sel_c] = Val::ONE;
                    wide[b + cap_gi_base] = Val::from_u64(entry_gi[&(cap_id, e)] as u64);
                    dst += 1;
                }
            }
        }

        // Brick 5d.4 — the op-table epilogue region (bind_optable): computes `folded` (the α-fold of the constraint
        // c_k) + `quot` (Σ zps_i·chunk_i), both bound to folded_col/quot_col via the wiring bus; its opening leaves
        // bound to the FS opening-rows (trace/quot, at term_idx) or the head's window provide (non-trace/qwt).
        let (mut folded_addr, mut quot_addr) = (0u64, 0u64);
        if bind_optable {
            use crate::recursion::native_fri::{epilogue_openings, quotient_recompose_weights};
            use crate::wrap::{op_table_f2_trace, QuotChunk};
            use p3_uni_stark::{BaseEntry, BaseLeaf};

            let op_base = st_base + 2 * rate;
            let (op_sel_c, is_tr_leaf_c, leaf_key_c) = (op_base + 13, op_base + 14, op_base + 15);
            let op_is_ch = |g: usize| op_base + 16 + g;
            let cs = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
            let (wu, npu, nperu) = (m.w_inner() as u64, m.n_pub() as u64, m.n_periodic() as u64);

            // Native OOD openings at ζ (the leaf values) + the nqc quotient-recompose weights zps_i.
            let (_eo_local, _eo_next, is_first, is_last, is_trans, _iv, _eo_quot, eo_alpha, _z, eo_periodic) =
                epilogue_openings(config, &JoinSplitAir, proof, pvs);
            let zps = quotient_recompose_weights(config, &JoinSplitAir, proof, pvs);
            let pubs: Vec<Challenge> = pvs.iter().map(|&p| Challenge::from(p)).collect();
            let opening = |term: usize| Challenge::from_basis_coefficients_fn(|i| committed[2 * term + i]);

            // seed: TRACE openings sourced from `committed` (== the opening-rows' pz, so the trace-leaf reads
            // balance bit-for-bit); non-trace from the native epilogue (== the head's window provides).
            let seed = |l: &BaseLeaf<Val>| -> Challenge {
                match l {
                    BaseLeaf::Constant(c) => Challenge::from(*c),
                    BaseLeaf::Variable(v) => match v.entry {
                        BaseEntry::Main { offset } => {
                            opening(if offset == 0 { m.trm_trace(v.index) } else { m.trm_next(v.index) })
                        }
                        BaseEntry::Public => pubs[v.index],
                        BaseEntry::Periodic => eo_periodic[v.index],
                        BaseEntry::Preprocessed { .. } => panic!("preprocessed columns unsupported"),
                    },
                    BaseLeaf::IsFirstRow => is_first,
                    BaseLeaf::IsLastRow => is_last,
                    BaseLeaf::IsTransition => is_trans,
                }
            };

            // preseed: TRACE openings at term_idx (open_id = the DEEP term index — a trace leaf bound to the
            // opening-row); NON-trace at their canonical OPEN_BASE open_id (bound to the head's window provide).
            let mut preseed: Vec<((u8, u64), Challenge, u64)> = Vec::new();
            for c in 0..m.w_inner() {
                let (lt, nt) = (m.trm_trace(c), m.trm_next(c));
                preseed.push(((0, c as u64), opening(lt), lt as u64));
                preseed.push(((1, c as u64), opening(nt), nt as u64));
            }
            for i in 0..m.n_pub() {
                preseed.push(((2, i as u64), pubs[i], open_id((2, i as u64), wu, npu, nperu)));
            }
            for i in 0..m.n_periodic() {
                preseed.push(((3, i as u64), eo_periodic[i], open_id((3, i as u64), wu, npu, nperu)));
            }
            preseed.push(((4, 0), is_first, open_id((4, 0), wu, npu, nperu)));
            preseed.push(((5, 0), is_last, open_id((5, 0), wu, npu, nperu)));
            preseed.push(((6, 0), is_trans, open_id((6, 0), wu, npu, nperu)));

            // quot recompose chunks: d0_i/d1_i from `committed` at trm_quot(i,0/1) (TRACE leaves at term_idx);
            // zps_i the weight (NON-trace leaf at open_id((7,i))).
            let chunks: Vec<QuotChunk> = (0..m.nqc())
                .map(|i| {
                    let (t0, t1) = (m.trm_quot(i, 0), m.trm_quot(i, 1));
                    QuotChunk {
                        d0: opening(t0),
                        d0_oid: t0 as u64,
                        d1: opening(t1),
                        d1_oid: t1 as u64,
                        zps: zps[i],
                        zps_oid: open_id((7, i as u64), wu, npu, nperu),
                    }
                })
                .collect();

            let (op_matrix, _roots, folded, leaf_bindings, quot) =
                op_table_f2_trace(&cs, seed, Some(eo_alpha), &preseed, Some(&chunks));
            let (folded_val, faddr) = folded.expect("the join-split epilogue folds to a value");
            let (quot_val, qaddr) = quot.expect("the quot recompose returns a value");
            folded_addr = faddr;
            quot_addr = qaddr;

            // Place the op-table in the slack AFTER the opening-rows; the folded/quot output wires are read n_heads
            // times by the arith heads (not internally), so override their out_mult to −n_heads.
            let op_start = or_start + n_terms;
            let op_h = op_matrix.values.len() / 13;
            assert!(
                op_start + op_h <= h,
                "op-table rows ({op_h}) must fit the slack after DeepFold+opening-rows ({})",
                h.saturating_sub(op_start)
            );
            let nheads = m.n_queries as u64;
            for i in 0..op_h {
                let dst = op_start + i;
                let mut cols: [Val; 13] = op_matrix.values[i * 13..i * 13 + 13].try_into().unwrap();
                if cols[3] == Val::from_u64(folded_addr) || cols[3] == Val::from_u64(quot_addr) {
                    cols[12] = Val::ZERO - Val::from_u64(nheads);
                }
                wide[dst * width + op_base..dst * width + op_base + 13].copy_from_slice(&cols);
                wide[dst * width + op_sel_c] = Val::ONE;
            }
            // Mark the opening-leaf rows: TRACE leaves (open_id < OPEN_BASE = the term index) read at leaf_key on the
            // pz channel (is_tr_leaf); NON-trace leaves (open_id ≥ OPEN_BASE) read at leaf_key on their split channel.
            for &(row, oid) in &leaf_bindings {
                let dst = op_start + row;
                wide[dst * width + leaf_key_c] = Val::from_u64(oid);
                if oid < OPEN_BASE {
                    wide[dst * width + is_tr_leaf_c] = Val::ONE;
                } else {
                    wide[dst * width + op_is_ch(((oid - OPEN_BASE) as usize) % N_GROUPS)] = Val::ONE;
                }
            }
            // Fill folded_col (fw+2) / quot_col (fw+4) at the arith heads (read from the wiring bus).
            for &head in &heads {
                wide[head * width + fw + 2..head * width + fw + 4].copy_from_slice(&cc(folded_val));
                wide[head * width + fw + 4..head * width + fw + 6].copy_from_slice(&cc(quot_val));
            }
        }

        (
            AssembledOpeningsWrapCwAir { m, op_periodics, bind_optable, folded_addr, quot_addr, narrow_ov, leaf_periodics, bind_caps, cap_periodics },
            RowMajorMatrix::new(wide, width),
            Vec::new(),
        )
    }

    /// **AA6 openings AA3 — all `N_GROUPS+3` channels balance** (native, cheap — NO prove). Assemble the cw=true
    /// narrow-openings trace and confirm each bus channel nets to zero as a signed multiset: channel 0 (RO) ⇒ every
    /// head's `ro_col` == its region's fold `ro`; channels `1..=N_GROUPS` (z/px input-binding) ⇒ each region row's
    /// `(z, px)` == the committed `(ζ / ζ·g, px_source)` per term; channel `N_GROUPS+1` (pz) ⇒ every region `pz`
    /// == the shared opening-row's `pz` (provided `−n_queries`, read `+1` per query); channel `N_GROUPS+2`
    /// (sponge FS-anchor) ⇒ every opening-row felt `(2k+i, pz_i)` cancels the transcript provide `(w_gi_l, cur[l])`
    /// at its stream position — i.e. the fold's `pz` == the FS-absorbed opening. Localizes any address / placement /
    /// multiplicity / ordering bug before the heavy `prove_lookup` (as the arith/cap balances did one regime up).
    #[cfg(feature = "recursion")]
    #[test]
    fn openings_wrap_cw_assembled_bus_balances() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_field::{Field, PrimeField64, TwoAdicField};
        use p3_goldilocks::Goldilocks;
        use p3_uni_stark::prove;
        use std::collections::HashMap;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, _pis) = assemble_openings_wrap_cw(&config, &proof, &pvs, false, false, false);

        let m = &asm.m;
        let (fw, h) = (m.fused_w(), m.height());
        let rate = AssembledOpeningsWrapCwAir::RATE;
        let width = fw + 6 + 18 + 4 + 1 + N_GROUPS + 6 + 2 * rate;
        let (ro_col, db) = (fw, fw + 6);
        let (df_sel, df_end, is_head, term_idx, is_ch0) = (db + 18, db + 20, db + 21, db + 22, db + 23);
        let or_base = db + 23 + N_GROUPS;
        let (or_gi, or_pz, or_sel, or_k, or_mult) = (or_base, or_base + 1, or_base + 3, or_base + 4, or_base + 5);
        let st_base = or_base + 6;
        let (w_gi, w_sel) = (|l: usize| st_base + 2 * l, |l: usize| st_base + 2 * l + 1);
        let ku = |v: Val| v.as_canonical_u64();
        let g_trace = Goldilocks::two_adic_generator(m.cm_rounds() - m.is_zk);

        // Field-valued signed multiset per (channel, tuple) — mirrors the eval's field mults exactly (the pz
        // provide is `−n_queries`, not `±1`, so accumulate in Val like `cap_wrap_cw_assembled_bus_balances`).
        let mut bus: HashMap<(usize, Vec<u64>), Val> = HashMap::new();
        let neg1 = Val::ZERO - Val::ONE;
        for r in 0..h {
            let b = r * width;
            let g = |c: usize| trace.values[b + c];
            // channel 0 — the ro bus: region END provides [x, ro] (−1); head reads [x_head, 0, ro_col] (+1).
            if g(df_end) == Val::ONE {
                *bus.entry((0, vec![ku(g(db + 2)), ku(g(db + 3)), ku(g(db + 16)), ku(g(db + 17))])).or_insert(Val::ZERO) += neg1;
            }
            if g(is_head) == Val::ONE {
                let x_head = <Goldilocks as Field>::GENERATOR * g(m.qt_acc() + m.lg() - 1);
                *bus.entry((0, vec![ku(x_head), 0, ku(g(ro_col)), ku(g(ro_col + 1))])).or_insert(Val::ZERO) += Val::ONE;
                // channels 1..=N_GROUPS — head PROVIDES committed term k (−1) on channel k%N_GROUPS+1: (x_head, 0,
                // k, z0, z1, px). cw=true: z from the window ζ (= g(pw(2))); px from px_source.
                let (z0f, z1f) = (g(m.pw(2)), g(m.pw(3)));
                for k in 0..m.n_terms {
                    let (z0, z1) = if k >= m.trm_next_base() && k < m.trm_quot_base() {
                        (z0f * g_trace, z1f * g_trace)
                    } else {
                        (z0f, z1f)
                    };
                    let tuple = vec![ku(x_head), 0, k as u64, ku(z0), ku(z1), ku(g(m.px_source(k)))];
                    *bus.entry((k % N_GROUPS + 1, tuple)).or_insert(Val::ZERO) += neg1;
                }
            }
            // region row READS its (z, px) bundle (+1) on its one-hot is_ch channel AND its pz (+1) on the pz bus.
            if g(df_sel) == Val::ONE {
                let gch = (0..N_GROUPS).find(|&gc| g(is_ch0 + gc) == Val::ONE).expect("a region row routes to one channel");
                let tuple = vec![ku(g(db + 2)), ku(g(db + 3)), ku(g(term_idx)), ku(g(db + 6)), ku(g(db + 7)), ku(g(db + 10))];
                *bus.entry((gch + 1, tuple)).or_insert(Val::ZERO) += Val::ONE;
                *bus.entry((N_GROUPS + 1, vec![ku(g(term_idx)), ku(g(db + 8)), ku(g(db + 9))])).or_insert(Val::ZERO) += Val::ONE;
            }
            // opening-row — pz bus PROVIDE [or_k, pz] (mult or_mult = −n_queries) + sponge READ [2k+i, pz_i] (+1).
            if g(or_sel) == Val::ONE {
                *bus.entry((N_GROUPS + 1, vec![ku(g(or_k)), ku(g(or_pz)), ku(g(or_pz + 1))])).or_insert(Val::ZERO) += g(or_mult);
                for i in 0..2u64 {
                    *bus.entry((N_GROUPS + 2, vec![ku(g(or_gi)) + i, ku(g(or_pz + i as usize))])).or_insert(Val::ZERO) += Val::ONE;
                }
            }
            // channel N_GROUPS+2 — each transcript rate lane with an opening felt PROVIDES (w_gi_l, cur[l]) (−1).
            for l in 0..rate {
                if g(w_sel(l)) == Val::ONE {
                    *bus.entry((N_GROUPS + 2, vec![ku(g(w_gi(l))), ku(g(l))])).or_insert(Val::ZERO) += neg1;
                }
            }
        }
        let nonzero = bus.values().filter(|&&v| v != Val::ZERO).count();
        let bad: Vec<_> = bus.iter().filter(|(_, &v)| v != Val::ZERO).take(8).collect();
        assert!(bad.is_empty(), "every (channel, tuple) must net to zero; {nonzero} nonzero, e.g. {bad:?}");
        println!(
            "openings cw=true buses ({} channels: ro + {} z/px input-binding + pz + sponge FS-anchor): {} distinct \
             entries, all net-zero — the DEEP fold's ro/z/px/pz are ALL bound to the committed columns + the \
             FS-absorbed opening, with the pz COLUMNS dropped (narrow_openings).",
            N_GROUPS + 3,
            N_GROUPS,
            bus.len()
        );
    }

    /// **AA6 brick 5d.4 — the op-table + openings assembled trace balances ALL 2·N_GROUPS+4 channels** (native,
    /// cheap — NO prove). Assemble with `bind_optable`: the op-table region computes `folded` (α-fold of the c_k) +
    /// `quot` (Σ zps_i·chunk_i) and its opening leaves bind to the FS opening-rows (trace/quot) / the head's window
    /// provides (non-trace/qwt). Confirms every bus channel nets to zero as a signed multiset — the openings channels
    /// (ro/z/px/pz/sponge, as `openings_wrap_cw_assembled_bus_balances`, but with `or_mult = −(n_queries+1)` now
    /// absorbing the op-table's per-term read), PLUS: the folded/quot wiring bus (op-table wires define/read + the
    /// heads read folded_col/quot_col), the pz channel's op-table trace-leaf reads, and the N_GROUPS non-trace split
    /// (head provides pub/periodic/sel/is_trans/qwt, op-table leaves read `is_ch·n_heads`). Localizes any addressing /
    /// multiplicity / leaf-marking / recompose bug before the heavy `prove_lookup`.
    #[cfg(feature = "recursion")]
    #[test]
    fn optable_openings_wrap_cw_bus_balances() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_field::{Field, PrimeField64, TwoAdicField};
        use p3_goldilocks::Goldilocks;
        use p3_uni_stark::prove;
        use std::collections::HashMap;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, _pis) = assemble_openings_wrap_cw(&config, &proof, &pvs, true, false, false);

        let m = &asm.m;
        let (fw, h) = (m.fused_w(), m.height());
        let rate = AssembledOpeningsWrapCwAir::RATE;
        let width = <AssembledOpeningsWrapCwAir as BaseAir<Val>>::width(&asm);
        let (ro_col, db) = (fw, fw + 6);
        let (df_sel, df_end, is_head, term_idx, is_ch0) = (db + 18, db + 20, db + 21, db + 22, db + 23);
        let or_base = db + 23 + N_GROUPS;
        let (or_gi, or_pz, or_sel, or_k, or_mult) = (or_base, or_base + 1, or_base + 3, or_base + 4, or_base + 5);
        let st_base = or_base + 6;
        let (w_gi, w_sel) = (|l: usize| st_base + 2 * l, |l: usize| st_base + 2 * l + 1);
        // op-table columns.
        let op_base = st_base + 2 * rate;
        let (op_sel_c, is_tr_leaf_c, leaf_key_c) = (op_base + 13, op_base + 14, op_base + 15);
        let op_is_ch = |g: usize| op_base + 16 + g;
        let (folded_col, quot_col) = (fw + 2, fw + 4);
        let (wch, nt) = (N_GROUPS + 3, N_GROUPS + 4);
        let ku = |v: Val| v.as_canonical_u64();
        let g_trace = Goldilocks::two_adic_generator(m.cm_rounds() - m.is_zk);
        let g_inv = Goldilocks::two_adic_generator(m.cm_rounds() - m.is_zk).inverse();
        let nheads = Val::from_u64(m.n_queries as u64);
        let (wu, npu, nperu) = (m.w_inner() as u64, m.n_pub() as u64, m.n_periodic() as u64);
        let route = |a: u64| ((a - OPEN_BASE) as usize) % N_GROUPS;

        let mut bus: HashMap<(usize, Vec<u64>), Val> = HashMap::new();
        let neg1 = Val::ZERO - Val::ONE;
        for r in 0..h {
            let b = r * width;
            let g = |c: usize| trace.values[b + c];
            // ---- openings channels (as openings_wrap_cw_assembled_bus_balances) ----
            if g(df_end) == Val::ONE {
                *bus.entry((0, vec![ku(g(db + 2)), ku(g(db + 3)), ku(g(db + 16)), ku(g(db + 17))])).or_insert(Val::ZERO) += neg1;
            }
            if g(is_head) == Val::ONE {
                let x_head = <Goldilocks as Field>::GENERATOR * g(m.qt_acc() + m.lg() - 1);
                *bus.entry((0, vec![ku(x_head), 0, ku(g(ro_col)), ku(g(ro_col + 1))])).or_insert(Val::ZERO) += Val::ONE;
                let (z0f, z1f) = (g(m.pw(2)), g(m.pw(3)));
                for k in 0..m.n_terms {
                    let (z0, z1) = if k >= m.trm_next_base() && k < m.trm_quot_base() { (z0f * g_trace, z1f * g_trace) } else { (z0f, z1f) };
                    let tuple = vec![ku(x_head), 0, k as u64, ku(z0), ku(z1), ku(g(m.px_source(k)))];
                    *bus.entry((k % N_GROUPS + 1, tuple)).or_insert(Val::ZERO) += neg1;
                }
                // wiring reads (folded/quot) + the non-trace provides.
                *bus.entry((wch, vec![asm.folded_addr, ku(g(folded_col)), ku(g(folded_col + 1))])).or_insert(Val::ZERO) += Val::ONE;
                *bus.entry((wch, vec![asm.quot_addr, ku(g(quot_col)), ku(g(quot_col + 1))])).or_insert(Val::ZERO) += Val::ONE;
                for i in 0..m.n_pub() {
                    let a = open_id((2, i as u64), wu, npu, nperu);
                    *bus.entry((nt + route(a), vec![a, ku(g(m.pw(m.pub_pi() + i))), 0])).or_insert(Val::ZERO) += neg1;
                }
                for i in 0..m.n_periodic() {
                    let (a, bb) = (open_id((3, i as u64), wu, npu, nperu), m.periodic_base() + 2 * i);
                    *bus.entry((nt + route(a), vec![a, ku(g(m.pw(bb))), ku(g(m.pw(bb + 1)))])).or_insert(Val::ZERO) += neg1;
                }
                for (key, s) in [((4u8, 0u64), m.sel(0)), ((5u8, 0u64), m.sel(2))] {
                    let a = open_id(key, wu, npu, nperu);
                    *bus.entry((nt + route(a), vec![a, ku(g(s)), ku(g(s + 1))])).or_insert(Val::ZERO) += neg1;
                }
                let a6 = open_id((6, 0), wu, npu, nperu);
                *bus.entry((nt + route(a6), vec![a6, ku(g(m.pw(2)) - g_inv), ku(g(m.pw(3)))])).or_insert(Val::ZERO) += neg1;
                for i in 0..m.nqc() {
                    let (a, qb) = (open_id((7, i as u64), wu, npu, nperu), m.qwt_base() + 2 * i);
                    *bus.entry((nt + route(a), vec![a, ku(g(m.pw(qb))), ku(g(m.pw(qb + 1)))])).or_insert(Val::ZERO) += neg1;
                }
            }
            if g(df_sel) == Val::ONE {
                let gch = (0..N_GROUPS).find(|&gc| g(is_ch0 + gc) == Val::ONE).expect("a region row routes to one channel");
                let tuple = vec![ku(g(db + 2)), ku(g(db + 3)), ku(g(term_idx)), ku(g(db + 6)), ku(g(db + 7)), ku(g(db + 10))];
                *bus.entry((gch + 1, tuple)).or_insert(Val::ZERO) += Val::ONE;
                *bus.entry((N_GROUPS + 1, vec![ku(g(term_idx)), ku(g(db + 8)), ku(g(db + 9))])).or_insert(Val::ZERO) += Val::ONE;
            }
            if g(or_sel) == Val::ONE {
                *bus.entry((N_GROUPS + 1, vec![ku(g(or_k)), ku(g(or_pz)), ku(g(or_pz + 1))])).or_insert(Val::ZERO) += g(or_mult);
                for i in 0..2u64 {
                    *bus.entry((N_GROUPS + 2, vec![ku(g(or_gi)) + i, ku(g(or_pz + i as usize))])).or_insert(Val::ZERO) += Val::ONE;
                }
            }
            for l in 0..rate {
                if g(w_sel(l)) == Val::ONE {
                    *bus.entry((N_GROUPS + 2, vec![ku(g(w_gi(l))), ku(g(l))])).or_insert(Val::ZERO) += neg1;
                }
            }
            // ---- op-table channels (bind_optable) ----
            if g(op_sel_c) == Val::ONE {
                let is_op = g(op_base) + g(op_base + 1) + g(op_base + 2); // is_mul+is_add+is_sub (0/1)
                *bus.entry((wch, vec![ku(g(op_base + 6)), ku(g(op_base + 7)), ku(g(op_base + 8))])).or_insert(Val::ZERO) += is_op; // read a
                *bus.entry((wch, vec![ku(g(op_base + 9)), ku(g(op_base + 10)), ku(g(op_base + 11))])).or_insert(Val::ZERO) += is_op; // read b
                *bus.entry((wch, vec![ku(g(op_base + 3)), ku(g(op_base + 4)), ku(g(op_base + 5))])).or_insert(Val::ZERO) += g(op_base + 12); // define out
                let (lk, lv0, lv1) = (ku(g(leaf_key_c)), ku(g(op_base + 4)), ku(g(op_base + 5)));
                if g(is_tr_leaf_c) == Val::ONE {
                    *bus.entry((N_GROUPS + 1, vec![lk, lv0, lv1])).or_insert(Val::ZERO) += Val::ONE; // trace leaf reads on pz
                }
                for gc in 0..N_GROUPS {
                    if g(op_is_ch(gc)) == Val::ONE {
                        *bus.entry((nt + gc, vec![lk, lv0, lv1])).or_insert(Val::ZERO) += nheads; // non-trace leaf reads
                    }
                }
            }
        }
        let nonzero = bus.values().filter(|&&v| v != Val::ZERO).count();
        let bad: Vec<_> = bus.iter().filter(|(_, &v)| v != Val::ZERO).take(8).collect();
        assert!(bad.is_empty(), "every (channel, tuple) must net to zero; {nonzero} nonzero, e.g. {bad:?}");
        println!(
            "op-table + openings cw=true buses ({} channels): {} distinct entries, all net-zero — folded_col + \
             quot_col bound to the op-table's fold/recompose, its opening leaves bound to the FS opening-rows (trace/\
             quot) + the window (non-trace/qwt). The epilogue folded·inv_van == quot is now over BOUND values.",
            2 * N_GROUPS + 4,
            bus.len()
        );
    }

    /// **Brick 4d (balance) — the narrow_ov openings-wrap buses balance** (native, cheap — NO prove). Assemble the
    /// cw=true narrow_ov trace and confirm each channel nets to zero as a signed multiset: the ro/pz/sponge channels
    /// are unchanged from the proven openings-wrap; the z/px channels carry `px=0` for TRACE terms (their px moved off
    /// the dropped `ov` carrier); and the NEW leaf-hash→px channel (N_GROUPS+3) balances iff every trace region px ==
    /// the authenticated input-Merkle leaf lane at its (query, column), keyed by the held query point `lqk`. Localizes
    /// any held-lqk / term-tag / leaf-lane bug before the heavy prove (as the AA2/AA3 balances did for arith/caps).
    #[cfg(feature = "recursion")]
    #[test]
    fn narrow_ov_openings_wrap_bus_balances() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_field::{Field, PrimeField64, TwoAdicField};
        use p3_goldilocks::Goldilocks;
        use p3_uni_stark::prove;
        use std::collections::HashMap;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, _pis) = assemble_openings_wrap_cw(&config, &proof, &pvs, false, true, false);

        let m = &asm.m;
        let (fw, h) = (m.fused_w(), m.height());
        let rate = AssembledOpeningsWrapCwAir::RATE;
        let width = <AssembledOpeningsWrapCwAir as BaseAir<Val>>::width(&asm);
        let (ro_col, db) = (fw, fw + 6);
        let (df_sel, df_end, is_head, term_idx, is_ch0) = (db + 18, db + 20, db + 21, db + 22, db + 23);
        let or_base = db + 23 + N_GROUPS;
        let (or_gi, or_pz, or_sel, or_k, or_mult) = (or_base, or_base + 1, or_base + 3, or_base + 4, or_base + 5);
        let st_base = or_base + 6;
        let (w_gi, w_sel) = (|l: usize| st_base + 2 * l, |l: usize| st_base + 2 * l + 1);
        // narrow_ov columns start where the op-table columns would (bind_optable=false ⇒ none): nov_base.
        let nov = st_base + 2 * rate;
        let (held_lqk, dq) = (nov, nov + 1);
        let (wt0, wt1, wls) =
            (|l: usize| nov + 2 + 3 * l, |l: usize| nov + 3 + 3 * l, |l: usize| nov + 4 + 3 * l);
        let lhpx = N_GROUPS + 3; // n_chan − 1 (bind_optable=false, narrow_ov=true ⇒ n_chan = N_GROUPS+4)
        let ku = |v: Val| v.as_canonical_u64();
        let g_trace = Goldilocks::two_adic_generator(m.cm_rounds() - m.is_zk);

        let mut bus: HashMap<(usize, Vec<u64>), Val> = HashMap::new();
        let neg1 = Val::ZERO - Val::ONE;
        for r in 0..h {
            let b = r * width;
            let g = |c: usize| trace.values[b + c];
            // ---- ro bus (channel 0) — unchanged ----
            if g(df_end) == Val::ONE {
                *bus.entry((0, vec![ku(g(db + 2)), ku(g(db + 3)), ku(g(db + 16)), ku(g(db + 17))])).or_insert(Val::ZERO) += neg1;
            }
            if g(is_head) == Val::ONE {
                let x_head = <Goldilocks as Field>::GENERATOR * g(m.qt_acc() + m.lg() - 1);
                *bus.entry((0, vec![ku(x_head), 0, ku(g(ro_col)), ku(g(ro_col + 1))])).or_insert(Val::ZERO) += Val::ONE;
                let (z0f, z1f) = (g(m.pw(2)), g(m.pw(3)));
                for k in 0..m.n_terms {
                    let (z0, z1) = if k >= m.trm_next_base() && k < m.trm_quot_base() { (z0f * g_trace, z1f * g_trace) } else { (z0f, z1f) };
                    // narrow_ov: TRACE terms provide px=0 (bound via the leaf-hash bus); QUOTIENT terms keep px.
                    let px = if k < m.trm_quot_base() { Val::ZERO } else { g(m.px_source(k)) };
                    let tuple = vec![ku(x_head), 0, k as u64, ku(z0), ku(z1), ku(px)];
                    *bus.entry((k % N_GROUPS + 1, tuple)).or_insert(Val::ZERO) += neg1;
                }
            }
            if g(df_sel) == Val::ONE {
                let gch = (0..N_GROUPS).find(|&gc| g(is_ch0 + gc) == Val::ONE).expect("a region row routes to one channel");
                // narrow_ov region px = df_is_quot · cur[db+10] (0 for trace terms; bound via the leaf-hash bus).
                let region_px = if g(dq) == Val::ONE { g(db + 10) } else { Val::ZERO };
                let tuple = vec![ku(g(db + 2)), ku(g(db + 3)), ku(g(term_idx)), ku(g(db + 6)), ku(g(db + 7)), ku(region_px)];
                *bus.entry((gch + 1, tuple)).or_insert(Val::ZERO) += Val::ONE;
                *bus.entry((N_GROUPS + 1, vec![ku(g(term_idx)), ku(g(db + 8)), ku(g(db + 9))])).or_insert(Val::ZERO) += Val::ONE;
                // leaf-hash READ (trace terms only): [x.0, term_idx, cur[db+10]] (+df_sel·(1−df_is_quot)).
                if g(dq) == Val::ZERO {
                    *bus.entry((lhpx, vec![ku(g(db + 2)), ku(g(term_idx)), ku(g(db + 10))])).or_insert(Val::ZERO) += Val::ONE;
                }
            }
            if g(or_sel) == Val::ONE {
                *bus.entry((N_GROUPS + 1, vec![ku(g(or_k)), ku(g(or_pz)), ku(g(or_pz + 1))])).or_insert(Val::ZERO) += g(or_mult);
                for i in 0..2u64 {
                    *bus.entry((N_GROUPS + 2, vec![ku(g(or_gi)) + i, ku(g(or_pz + i as usize))])).or_insert(Val::ZERO) += Val::ONE;
                }
            }
            for l in 0..rate {
                if g(w_sel(l)) == Val::ONE {
                    *bus.entry((N_GROUPS + 2, vec![ku(g(w_gi(l))), ku(g(l))])).or_insert(Val::ZERO) += neg1;
                }
                // leaf-hash PROVIDES (two term-tags per lane: trm_trace/trm_next): [held, w_term, leaf_lane] (−w_lsel).
                if g(wls(l)) == Val::ONE {
                    *bus.entry((lhpx, vec![ku(g(held_lqk)), ku(g(wt0(l))), ku(g(l))])).or_insert(Val::ZERO) += neg1;
                    *bus.entry((lhpx, vec![ku(g(held_lqk)), ku(g(wt1(l))), ku(g(l))])).or_insert(Val::ZERO) += neg1;
                }
            }
        }
        let nonzero = bus.values().filter(|&&v| v != Val::ZERO).count();
        let bad: Vec<_> = bus.iter().filter(|(_, &v)| v != Val::ZERO).take(8).collect();
        assert!(bad.is_empty(), "every (channel, tuple) must net to zero; {nonzero} nonzero, e.g. {bad:?}");
        println!(
            "narrow_ov openings-wrap cw=true buses ({} channels): {} distinct entries, all net-zero — the ov opened-row \
             carrier externalized, every trace region px bound to the authenticated leaf lane via the held-lqk leaf-hash bus.",
            N_GROUPS + 4,
            bus.len()
        );
    }

    /// **Brick 4d (prove) — the narrow_ov openings-wrap PROVES through the LEAN prover.** The definitive soundness
    /// check for the ov externalization (the `openings_wrap_cw_assembled_proves` analog with `narrow_ov` on): build
    /// the cw=true narrow_ov trace (the `ov` opened-row carrier GONE, every trace px re-sourced from the authenticated
    /// input-Merkle leaf lane via the held-lqk leaf-hash bus) and prove + verify end-to-end. So the deep-tree B lever's
    /// final residual — the +1 `ov` trace-leaf carrier (`input_leaf_felts = w_inner`) — is externalized narrow-tall as
    /// a SOUND STARK, driving marginal B to 0. A corrupted region px (its leaf-hash read no longer matches any provide)
    /// is rejected. Heavy (LEAN, ~32 GB / -j1); `--release --features lookup,recursion -j1 -- --ignored`.
    #[cfg(feature = "recursion")]
    #[test]
    #[ignore = "heavy (LEAN, -j1): proves the cw=true narrow_ov openings-wrap through prove_lookup + tamper-rejects a corrupted trace px; run `--release --features lookup,recursion -j1 -- --ignored`"]
    fn narrow_ov_openings_wrap_proves() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, pis) = assemble_openings_wrap_cw(&config, &proof, &pvs, false, true, false);
        let width = <AssembledOpeningsWrapCwAir as BaseAir<Val>>::width(&asm);
        println!(
            "proving cw=true narrow_ov openings-wrap (ro + {} z/px + pz + sponge + leaf-hash→px): width {width}, {} \
             rows, {} channels — the ov opened-row carrier externalized, trace px bound to the authenticated leaf lane",
            N_GROUPS,
            asm.m.height(),
            N_GROUPS + 4
        );
        // LEAN (non-hiding, is_zk=0) prover ⇒ the quotient-domain LDE (the OOM term) ~2× smaller than the hiding path.
        let lproof = prove_lookup_lean(&asm, trace, &pis);
        assert!(
            verify_lookup_lean(&asm, &lproof, &pis).is_ok(),
            "the cw=true narrow_ov openings-wrap must prove + verify through the LEAN prover (width {width})"
        );

        // Corrupt a TRACE region's px (cur[db+10] on a df_sel row with df_is_quot=0) ⇒ its leaf-hash read no longer
        // matches the authenticated-leaf provide ⇒ the leaf-hash bus unbalances (and the fold ro breaks) ⇒ rejected.
        let (asm2, mut bad, pis2) = assemble_openings_wrap_cw(&config, &proof, &pvs, false, true, false);
        let db = asm2.m.fused_w() + 6;
        let (df_sel, dq) = (db + 18, asm2.df_is_quot());
        let row = (0..asm2.m.height())
            .find(|&r| bad.values[r * width + df_sel] == Val::ONE && bad.values[r * width + dq] == Val::ZERO)
            .expect("a trace region row (df_sel=1, df_is_quot=0)");
        bad.values[row * width + db + 10] += Val::ONE; // trace region px.0
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let lp = prove_lookup_lean(&asm2, bad, &pis2);
            verify_lookup_lean(&asm2, &lp, &pis2).is_err()
        }))
        .unwrap_or(true);
        std::panic::set_hook(hook);
        assert!(rejected, "a corrupted trace region px must be rejected (leaf-hash bus unbalances)");
    }

    /// **AA6 openings AA4 — the assembled openings-wrap PROVES through `prove_lookup`.** The definitive soundness
    /// check (the `arith_wrap_assembled_proves` / `cap_wrap_cw_assembled_proves` analog for the OPENINGS tile):
    /// build the cw=true narrow-openings trace (the `2·n_terms` pz opening COLUMNS gone) and prove + verify it
    /// end-to-end through the W1 lookup prover. So the reduced-opening fold holds as a SOUND STARK with the fold's
    /// `pz` re-sourced from the FS-absorbed opening (the shared opening-row + the sponge FS-anchor bus + the pz
    /// re-provide) rather than a committed column — the deep-tree B lever's openings arc, sound. A corrupted
    /// opening-row `pz` is rejected (the sponge FS-anchor + the pz bus both unbalance). Heavy;
    /// `--release --features lookup,recursion -j1 -- --ignored`.
    #[cfg(feature = "recursion")]
    #[test]
    #[ignore = "heavy (-j1): proves the cw=true assembled openings-wrap through prove_lookup + tamper-rejects a corrupted opening-row pz; run `--release --features lookup,recursion -j1 -- --ignored`"]
    fn openings_wrap_cw_assembled_proves() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, pis) = assemble_openings_wrap_cw(&config, &proof, &pvs, false, false, false);
        let width = <AssembledOpeningsWrapCwAir as BaseAir<Val>>::width(&asm);
        println!(
            "proving cw=true assembled openings-wrap (ro + {} z/px + pz + sponge FS-anchor): width {width}, {} rows, \
             {} channels — the 2·n_terms pz opening columns externalized",
            N_GROUPS,
            asm.m.height(),
            N_GROUPS + 3
        );
        // LEAN (non-hiding, is_zk=0) prover ⇒ the quotient-domain LDE (the OOM term) is ~2× smaller than the hiding
        // path — this wide openings-wrap (width 3792) is exactly the Brick-4d/Step-6 prove that OOMs under hiding.
        let lproof = prove_lookup_lean(&asm, trace, &pis);
        assert!(
            verify_lookup_lean(&asm, &lproof, &pis).is_ok(),
            "the cw=true assembled openings-wrap must prove + verify through the LEAN prover (width {width})"
        );

        // Corrupt the first opening-row's pz ⇒ BOTH the sponge FS-anchor bus (pz ≠ the FS-absorbed felt) and the pz
        // re-provide bus (opening-row pz ≠ the regions' pz) unbalance ⇒ the corrupted trace must not verify.
        let (asm2, mut bad, pis2) = assemble_openings_wrap_cw(&config, &proof, &pvs, false, false, false);
        let fw = asm2.m.fused_w();
        let or_pz = (fw + 6) + 23 + N_GROUPS + 1; // db(fw+6) + 23 + N_GROUPS = or_base; or_pz = or_base + 1
        let used = asm2.m.tr() + asm2.m.n_queries * asm2.m.m_period();
        let or_start = used + asm2.m.n_terms * asm2.m.n_queries;
        bad.values[or_start * width + or_pz] += Val::ONE; // opening-row 0's pz.0
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let lp = prove_lookup_lean(&asm2, bad, &pis2);
            verify_lookup_lean(&asm2, &lp, &pis2).is_err()
        }))
        .unwrap_or(true);
        std::panic::set_hook(hook);
        assert!(rejected, "a corrupted opening-row pz must be rejected (sponge FS-anchor + pz buses unbalance)");
    }

    /// **AA6 brick 5d.5 — the op-table + openings assembled wrap PROVES through `prove_lookup`.** The definitive
    /// soundness check for the COMPLETE cw=true narrow-openings epilogue: build the `bind_optable` trace (the op-table
    /// region computes `folded` = α-fold of the c_k + `quot` = Σ zps_i·chunk_i; its opening leaves bound to the FS
    /// opening-rows (trace/quot at term_idx) + the head window (non-trace/qwt); the wiring bus binds folded_col +
    /// quot_col) and prove + verify it end-to-end through the W1 lookup prover. So the epilogue identity
    /// `folded·inv_van == quot` now holds over BOUND values — the last two free witnesses that made it vacuous are
    /// gone, at cw=true, with the `2·n_terms` pz opening COLUMNS externalized. A corrupted `folded_col` at a head is
    /// rejected (the folded wiring bus unbalances AND the epilogue identity breaks). Heavy (~97min);
    /// `--release --features lookup,recursion -j1 -- --ignored`.
    #[cfg(feature = "recursion")]
    #[test]
    #[ignore = "heavy (-j1, ~97min): proves the cw=true op-table+openings assembled wrap through prove_lookup + tamper-rejects a corrupted folded_col; run `--release --features lookup,recursion -j1 -- --ignored`"]
    fn optable_openings_wrap_cw_proves() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, pis) = assemble_openings_wrap_cw(&config, &proof, &pvs, true, false, false);
        let width = <AssembledOpeningsWrapCwAir as BaseAir<Val>>::width(&asm);
        println!(
            "proving cw=true op-table+openings assembled wrap (ro + {} z/px + pz + sponge + folded/quot wiring + {} \
             non-trace split): width {width}, {} rows, {} channels — folded_col + quot_col bound to the op-table, the \
             epilogue folded·inv_van == quot over BOUND values, the 2·n_terms pz opening columns externalized",
            N_GROUPS,
            N_GROUPS,
            asm.m.height(),
            2 * N_GROUPS + 4
        );
        let lproof = prove_lookup_lean(&asm, trace, &pis);
        assert!(
            verify_lookup_lean(&asm, &lproof, &pis).is_ok(),
            "the cw=true op-table+openings assembled wrap must prove + verify through prove_lookup (width {width})"
        );

        // Corrupt folded_col at an arith head ⇒ the folded wiring bus (head's folded_col read ≠ the op-table's folded
        // provide) unbalances AND the epilogue folded·inv_van == quot breaks ⇒ the corrupted trace must not verify.
        let (asm2, mut bad, pis2) = assemble_openings_wrap_cw(&config, &proof, &pvs, true, false, false);
        let fw = asm2.m.fused_w();
        let is_head = (fw + 6) + 21; // db(fw+6) + 21
        let head = (0..asm2.m.height())
            .find(|&r| bad.values[r * width + is_head] == Val::ONE)
            .expect("an arith head row");
        bad.values[head * width + fw + 2] += Val::ONE; // folded_col.0
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let lp = prove_lookup_lean(&asm2, bad, &pis2);
            verify_lookup_lean(&asm2, &lp, &pis2).is_err()
        }))
        .unwrap_or(true);
        std::panic::set_hook(hook);
        assert!(rejected, "a corrupted folded_col must be rejected (folded wiring bus unbalances + epilogue identity breaks)");
    }

    /// **Caps AA5 cw=true — both buses balance** (native, cheap — NO prove). Assemble the cw=true trace and confirm
    /// each channel nets to zero as a signed multiset: channel 0 (SELECT) ⇒ every head's `cap_c[g]` == the
    /// addressed cap-row digest; channel 1 (SPONGE-CAP) ⇒ every cap-row digest felt `(gi_base+k, digest[k])` cancels
    /// the transcript provide `(w_gi_l, cur[l])` at its stream position — i.e. the cap-row digest == the FS-absorbed
    /// felt. Localizes any tag/gi/digest/count/alignment bug before the heavy prove (as the AA2 balance did).
    #[cfg(feature = "recursion")]
    #[test]
    fn cap_wrap_cw_assembled_bus_balances() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_field::PrimeField64;
        use p3_uni_stark::prove;
        use std::collections::HashMap;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, _pis) = assemble_cap_wrap_cw(&config, &proof, &pvs);

        let (fw, h) = (asm.m.fused_w(), asm.m.height());
        let rate = AssembledCapWrapCwAir::CAP_RATE;
        let width = fw + 10 + 2 * rate;
        let (cr, cap_sel, is_head, gi_base) = (fw, fw + 7, fw + 8, fw + 9);
        let m = &asm.m;
        let ku = |v: Val| v.as_canonical_u64();
        let openings = asm.openings();

        let mut bus: HashMap<(usize, Vec<u64>), Val> = HashMap::new();
        for r in 0..h {
            let b = r * width;
            let g = |c: usize| trace.values[b + c];
            // channel 0 (SELECT): cap-row PROVIDES its entry (mult cap_mult); each head READS its openings (+1).
            if g(cap_sel) == Val::ONE {
                let key = vec![ku(g(cr)), ku(g(cr + 1)), ku(g(cr + 2)), ku(g(cr + 3)), ku(g(cr + 4)), ku(g(cr + 5))];
                *bus.entry((0, key)).or_insert(Val::ZERO) += g(cr + 6);
                // channel 1 (SPONGE): the cap-row READS its 4 digest felts (gi_base+k, digest[k]) (+1).
                for k in 0..4u64 {
                    let sk = vec![ku(g(gi_base)) + k, ku(g(cr + 2 + k as usize))];
                    *bus.entry((1, sk)).or_insert(Val::ZERO) += Val::ONE;
                }
            }
            if g(is_head) == Val::ONE {
                for &(cap_id, cg_off, shift, bits) in &openings {
                    let mut sel_idx = 0u64;
                    for j in 0..bits {
                        if g(m.sb_b(shift + j)) == Val::ONE {
                            sel_idx += 1 << j;
                        }
                    }
                    let key = vec![
                        cap_id as u64,
                        sel_idx,
                        ku(g(m.cap_c(cg_off))),
                        ku(g(m.cap_c(cg_off + 1))),
                        ku(g(m.cap_c(cg_off + 2))),
                        ku(g(m.cap_c(cg_off + 3))),
                    ];
                    *bus.entry((0, key)).or_insert(Val::ZERO) += Val::ONE;
                }
            }
            // channel 1 (SPONGE): each transcript rate lane with a cap felt PROVIDES (w_gi_l, cur[l]) (−1).
            for l in 0..rate {
                if g(fw + 11 + 2 * l) == Val::ONE {
                    let sk = vec![ku(g(fw + 10 + 2 * l)), ku(g(l))];
                    *bus.entry((1, sk)).or_insert(Val::ZERO) -= Val::ONE;
                }
            }
        }
        let nonzero = bus.values().filter(|&&v| v != Val::ZERO).count();
        let bad: Vec<_> = bus.iter().filter(|(_, &v)| v != Val::ZERO).take(8).collect();
        assert!(bad.is_empty(), "every (channel, tuple) must net to zero; {nonzero} nonzero, e.g. {bad:?}");
        println!(
            "cap cw=true buses (2 channels: select + sponge-cap FS-anchor): {} distinct entries, all net-zero — \
             cap_c bound to the cap-row (select) AND each cap-row digest to the FS-absorbed sponge cap (sponge) ⇒ \
             the width-win cap-select is SOUND (auth == FS).",
            bus.len()
        );
    }

    /// **Caps AA5 cw=true — the SOUND capstone PROVES through `prove_lookup`.** The definitive check: build the
    /// cw=true assembled cap-wrap (caps dropped from the pis window, the select bus + the sponge-cap FS-anchor bus)
    /// and prove + verify it end-to-end through the W1 lookup prover. So the width win (fused_w ≈ 963) holds as a
    /// SOUND STARK with `cap_c` bound to the FS-absorbed cap — the deep-tree cap bottleneck's B≤1 lever, sound. A
    /// corrupted cap-row digest is rejected (both buses unbalance). Heavy; `--release --features lookup,recursion -j1`.
    #[cfg(feature = "recursion")]
    #[test]
    #[ignore = "heavy (CONFIRMED ~422s, -j1): proves the cw=true assembled cap-wrap (width 981, 2 channels) through prove_lookup + tamper-rejects a corrupted cap-row digest; run `--release --features lookup,recursion -j1 -- --ignored`"]
    fn cap_wrap_cw_assembled_proves() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, pis) = assemble_cap_wrap_cw(&config, &proof, &pvs);
        let width = <AssembledCapWrapCwAir as BaseAir<Val>>::width(&asm);
        println!(
            "proving cw=true assembled cap-wrap (select + sponge-cap FS-anchor): width {width}, {} rows, 2 channels",
            asm.m.height()
        );
        let lproof = prove_lookup(&asm, trace, &pis);
        assert!(
            verify_lookup(&asm, &lproof, &pis).is_ok(),
            "the cw=true assembled cap-wrap must prove + verify through prove_lookup (width {width})"
        );

        // Corrupt the first cap-row's digest ⇒ BOTH the select bus (digest ≠ cap_c) and the sponge bus (digest ≠
        // the FS felt) unbalance ⇒ the corrupted trace must not verify.
        let (asm2, mut bad, pis2) = assemble_cap_wrap_cw(&config, &proof, &pvs);
        let used = asm2.m.tr() + asm2.m.n_queries * asm2.m.m_period();
        let cr = asm2.m.fused_w();
        bad.values[used * width + cr + 2] += Val::ONE; // digest[0] of the first cap-row
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let lp = prove_lookup(&asm2, bad, &pis2);
            verify_lookup(&asm2, &lp, &pis2).is_err()
        }))
        .unwrap_or(true);
        std::panic::set_hook(hook);
        assert!(rejected, "a corrupted cap-row digest must be rejected (select + sponge buses unbalance)");
    }

    /// **Tier-1 RAM+GPU (integrated) — the caps-narrowed wrap PROVES on the GPU under the lean config, RSS measured.**
    /// The dominant width lever (caps ≈ 85% of the un-narrowed cw=true `fused_w`) proven end-to-end through the
    /// GPU-accelerated LEAN lookup prover: assemble the cw=true cap-wrap (width 981, the `2^cap_height` cap COLUMNS
    /// gone), prove via [`prove_lookup_lean_gpu`] (`GpuDft` LDE + `is_zk=0`), and verify under the CPU lean verifier
    /// (wire-compatible). Reports peak RSS (VmHWM) — the caps narrowing + lean + GPU stack, the "reduce RAM with GPU
    /// support" demonstration on the biggest single lever. Heavy; `--release --features gpu,lookup,recursion -j1`.
    #[cfg(all(feature = "gpu", feature = "recursion"))]
    #[test]
    #[ignore = "heavy (GPU-lean): proves the caps-narrowed cw=true wrap (width 981) on the GPU + reports peak RSS; run `--release --features gpu,lookup,recursion -j1 -- --ignored`"]
    fn cap_wrap_cw_assembled_proves_gpu() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::lookup::prover::prove_lookup_lean_gpu;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::prove;

        let peak_rss_mib = || -> u64 {
            std::fs::read_to_string("/proc/self/status")
                .ok()
                .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM")).map(String::from))
                .and_then(|l| l.split_whitespace().nth(1).and_then(|v| v.parse::<u64>().ok()))
                .map(|kib| kib / 1024)
                .unwrap_or(0)
        };

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, pis) = assemble_cap_wrap_cw(&config, &proof, &pvs);
        let width = <AssembledCapWrapCwAir as BaseAir<Val>>::width(&asm);
        let lproof = prove_lookup_lean_gpu(&asm, trace, &pis);
        assert!(
            verify_lookup_lean(&asm, &lproof, &pis).is_ok(),
            "the caps-narrowed cw=true wrap must prove on the GPU (lean) + verify under the CPU lean verifier (width {width})"
        );
        println!(
            "Tier-1 RAM+GPU: caps-narrowed cw=true wrap (width {width}, {} rows) PROVED via prove_lookup_lean_gpu \
             (GpuDft LDE + is_zk=0) + CPU-lean-verified. Peak RSS {} MiB — the caps narrowing (85% lever) + lean + GPU.",
            asm.m.height(),
            peak_rss_mib()
        );
    }

    /// **Tier-1 merge M1c (assemble) — the merged caps ⊕ openings trace assembles.** `assemble_openings_wrap_cw` with
    /// `bind_caps`: the `narrow_caps` monolith window + the openings fill (its internal ro-assert validates the
    /// z/px/pz sourcing at the COLLAPSED offsets, so narrow_caps + narrow_openings coexist) + the cap-region fill
    /// (SELECT/SPONGE-CAP) in the slack AFTER the opening-rows. A successful assemble (no offset panic) + the expected
    /// width + populated cap-rows confirm the fill; the prove is `cap_merge_assembled_proves`.
    #[cfg(feature = "recursion")]
    #[test]
    fn cap_merge_assembled_builds() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, _pis) = assemble_openings_wrap_cw(&config, &proof, &pvs, false, false, true);
        let width = <AssembledOpeningsWrapCwAir as BaseAir<Val>>::width(&asm);
        assert_eq!(trace.values.len(), asm.m.height() * width, "the merged trace has the assembled width");
        let cap_sel_c = asm.cap_sel_c();
        let n_cap_rows = (0..asm.m.height()).filter(|&r| trace.values[r * width + cap_sel_c] == Val::ONE).count();
        assert!(n_cap_rows > 0, "the cap-region must be filled (cap_sel rows)");
        println!(
            "Tier-1 MERGE M1c (assemble): merged caps ⊕ openings trace width {width} (narrow_caps fused_w {} + \
             regions), {n_cap_rows} cap-rows — the openings fill (ro-assert passed) + the cap-region coexist in one trace.",
            asm.m.fused_w()
        );
    }

    /// **Tier-1 FULL 4-way merge (assemble) — caps ⊕ openings ⊕ ov in ONE trace.** `assemble_openings_wrap_cw` with
    /// BOTH `bind_caps` AND `narrow_ov`: the cap COLUMNS + the `2·n_terms` pz opening COLUMNS + the ov opened-row
    /// carrier ALL externalized (width 545 → ~458). The narrow_ov leaf-hash fill + the cap-region fill coexist (caps
    /// in the slack after the opening-rows; the leaf-hash + sponge-cap tags on transcript rows, disjoint columns; the
    /// caps channels ordered BEFORE narrow_ov's last-channel leaf-hash), and the leaf lanes are sourced at the
    /// narrow_caps COLLAPSED offsets — the internal ro-assert validates the whole fill at assembly time.
    #[cfg(feature = "recursion")]
    #[test]
    fn cap_merge_full_builds() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, _pis) = assemble_openings_wrap_cw(&config, &proof, &pvs, false, true, true);
        let width = <AssembledOpeningsWrapCwAir as BaseAir<Val>>::width(&asm);
        assert_eq!(trace.values.len(), asm.m.height() * width, "the full-merge trace has the assembled width");
        let n_cap_rows = (0..asm.m.height()).filter(|&r| trace.values[r * width + asm.cap_sel_c()] == Val::ONE).count();
        assert!(n_cap_rows > 0 && asm.narrow_ov && asm.bind_caps, "all four externalizations on + the cap-region filled");
        println!(
            "Tier-1 FULL 4-way MERGE (assemble): caps ⊕ openings ⊕ ov trace width {width} (narrow_caps+openings+ov \
             fused_w {} + regions), {n_cap_rows} cap-rows — all four externalizations coexist in one trace (ro-assert passed).",
            asm.m.fused_w()
        );
    }

    /// **Tier-1 FULL 4-way merge — the caps ⊕ openings ⊕ ov wrap PROVES (lean).** The COMPLETE width merge as a SOUND
    /// STARK: the cap COLUMNS + the pz opening COLUMNS + the ov trace-leaf carrier ALL gone (width ~458 vs the
    /// caps-un-narrowed 3792, ~8× less quotient-domain LDE). Prove + verify + tamper-reject a corrupted cap-row
    /// digest. Heavy; `--release --features lookup,recursion -j1` (or `gpu,lookup,recursion` for the GPU path).
    #[cfg(feature = "recursion")]
    #[test]
    #[ignore = "heavy (LEAN, -j1): proves the FULL 4-way merged wrap (width ~458) + tamper-rejects; run `--release --features lookup,recursion -j1 -- --ignored`"]
    fn cap_merge_full_proves() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, pis) = assemble_openings_wrap_cw(&config, &proof, &pvs, false, true, true);
        let width = <AssembledOpeningsWrapCwAir as BaseAir<Val>>::width(&asm);
        println!("proving the FULL 4-way merged wrap: width {width}, {} rows", asm.m.height());
        let lproof = prove_lookup_lean(&asm, trace, &pis);
        assert!(
            verify_lookup_lean(&asm, &lproof, &pis).is_ok(),
            "the full 4-way merged wrap must prove + verify through the LEAN prover (width {width})"
        );

        // Corrupt the first cap-row's digest ⇒ the SELECT + SPONGE-CAP buses unbalance ⇒ rejected.
        let (asm2, mut bad, pis2) = assemble_openings_wrap_cw(&config, &proof, &pvs, false, true, true);
        let used = asm2.m.tr() + asm2.m.n_queries * asm2.m.m_period();
        let cap_start = used + asm2.m.n_terms * asm2.m.n_queries + asm2.m.n_terms;
        let cr = asm2.cap_base();
        bad.values[cap_start * width + cr + 2] += Val::ONE;
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let lp = prove_lookup_lean(&asm2, bad, &pis2);
            verify_lookup_lean(&asm2, &lp, &pis2).is_err()
        }))
        .unwrap_or(true);
        std::panic::set_hook(hook);
        assert!(rejected, "a corrupted cap-row digest must be rejected in the full 4-way merge");
    }

    /// **Tier-1 merge M1c/M3 — the merged caps ⊕ openings wrap PROVES (lean).** The 9.2× width merge as a SOUND
    /// STARK: assemble the `narrow_caps` + `narrow_openings` + `narrow_arith` wrap (width ~545 — BOTH the
    /// `2^cap_height` cap COLUMNS and the `2·n_terms` pz opening columns GONE) and prove + verify end-to-end through
    /// the LEAN prover — the host-RAM win (width ~545 vs the caps-un-narrowed 3792, ~7× less quotient-domain LDE). A
    /// corrupted cap-row digest is rejected (the SELECT + SPONGE-CAP buses unbalance). Heavy; `--release -j1`.
    #[cfg(feature = "recursion")]
    #[test]
    #[ignore = "heavy (LEAN, -j1): proves the merged caps⊕openings wrap (width ~545) + tamper-rejects; run `--release --features lookup,recursion -j1 -- --ignored`"]
    fn cap_merge_assembled_proves() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, pis) = assemble_openings_wrap_cw(&config, &proof, &pvs, false, false, true);
        let width = <AssembledOpeningsWrapCwAir as BaseAir<Val>>::width(&asm);
        println!("proving the merged caps ⊕ openings wrap: width {width}, {} rows", asm.m.height());
        let lproof = prove_lookup_lean(&asm, trace, &pis);
        assert!(
            verify_lookup_lean(&asm, &lproof, &pis).is_ok(),
            "the merged caps ⊕ openings wrap must prove + verify through the LEAN prover (width {width})"
        );

        // Corrupt the first cap-row's digest ⇒ the SELECT + SPONGE-CAP buses unbalance ⇒ rejected.
        let (asm2, mut bad, pis2) = assemble_openings_wrap_cw(&config, &proof, &pvs, false, false, true);
        let used = asm2.m.tr() + asm2.m.n_queries * asm2.m.m_period();
        let cap_start = used + asm2.m.n_terms * asm2.m.n_queries + asm2.m.n_terms; // after DeepFold regions + opening-rows
        let cr = asm2.cap_base();
        bad.values[cap_start * width + cr + 2] += Val::ONE; // digest[0] of the first cap-row
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let lp = prove_lookup_lean(&asm2, bad, &pis2);
            verify_lookup_lean(&asm2, &lp, &pis2).is_err()
        }))
        .unwrap_or(true);
        std::panic::set_hook(hook);
        assert!(rejected, "a corrupted cap-row digest must be rejected (SELECT + SPONGE-CAP buses unbalance)");
    }

    /// **Tier-1 CAPSTONE — the merged caps ⊕ openings wrap PROVES on the GPU (width 545).** The full integrated
    /// Tier-1 result: the width-merged wrap (BOTH the `2^cap_height` cap COLUMNS and the `2·n_terms` pz opening
    /// columns gone — width 545 vs the caps-un-narrowed 3792, ~7× less LDE) proven end-to-end through the
    /// GPU-accelerated LEAN prover (`GpuDft` LDE + `is_zk=0`) + CPU-lean-verified (wire-compatible). The RAM win
    /// (width merge) × the speed win (GPU) in one prove — "reduce RAM with GPU support" on the fully-narrowed wrap.
    /// Reports peak RSS. Heavy; `--release --features gpu,lookup,recursion -j1`.
    #[cfg(all(feature = "gpu", feature = "recursion"))]
    #[test]
    #[ignore = "heavy (GPU-lean): proves the merged caps⊕openings wrap (width 545) on the GPU + reports peak RSS; run `--release --features gpu,lookup,recursion -j1 -- --ignored`"]
    fn cap_merge_assembled_proves_gpu() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::lookup::prover::prove_lookup_lean_gpu;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::prove;

        let peak_rss_mib = || -> u64 {
            std::fs::read_to_string("/proc/self/status")
                .ok()
                .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM")).map(String::from))
                .and_then(|l| l.split_whitespace().nth(1).and_then(|v| v.parse::<u64>().ok()))
                .map(|kib| kib / 1024)
                .unwrap_or(0)
        };

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, pis) = assemble_openings_wrap_cw(&config, &proof, &pvs, false, false, true);
        let width = <AssembledOpeningsWrapCwAir as BaseAir<Val>>::width(&asm);
        let lproof = prove_lookup_lean_gpu(&asm, trace, &pis);
        assert!(
            verify_lookup_lean(&asm, &lproof, &pis).is_ok(),
            "the merged caps ⊕ openings wrap must prove on the GPU (lean) + verify under the CPU lean verifier (width {width})"
        );
        println!(
            "Tier-1 CAPSTONE: merged caps ⊕ openings wrap (width {width}, {} rows — cap COLUMNS + pz COLUMNS gone) \
             PROVED via prove_lookup_lean_gpu + CPU-lean-verified. Peak RSS {} MiB — the width merge (~7×) × GPU.",
            asm.m.height(),
            peak_rss_mib()
        );
    }

    /// **Caps plumbing brick — `CapWrapAir` composes with the product-mux externalized** (`--features recursion`).
    /// The cheap half of the `CapMuxBci` plumbing (the `ArithWrapAir` analog): swapping the cap-mux strategy to
    /// `CapMuxBci` (`emit_capmux` → nothing) drops the `openings·4` product-mux constraints (and their `2^cap_height`
    /// entry reads) while keeping width at `fused_w` (cap_c is a pre-existing carrier) and NOT raising the degree
    /// (removing constraints can't). Confirms the externalized AIR is well-formed + a strict constraint SUBSET of
    /// the monolith; `cap_wrap_externalized_proves` is the heavy end-to-end confirmation.
    #[cfg(feature = "recursion")]
    #[test]
    fn cap_wrap_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (air, _tr, _pis) = wrap_build_reused(&config, &proof, &pvs, false);
        let fw = air.fused_w();

        // The full monolith's constraints (InlineBci product-mux included), for the subset + degree comparison.
        let mono_cs = get_symbolic_constraints::<Val, _>(&air, AirLayout::from_air::<Val>(&air));
        let mono_deg = mono_cs.iter().map(|c| c.degree_multiple()).max().unwrap();

        let wrap = CapWrapAir { m: air };
        assert_eq!(BaseAir::<Val>::width(&wrap), fw, "CapWrapAir adds no columns (cap_c is a pre-existing carrier)");
        let cs = get_symbolic_constraints::<Val, _>(&wrap, AirLayout::from_air::<Val>(&wrap));
        let deg = cs.iter().map(|c| c.degree_multiple()).max().unwrap();
        println!(
            "CapWrapAir: width {fw} (== fused_w, NO cap cols added), {} constraints (monolith {}, −{} product-mux), \
             max degree {deg} (monolith {mono_deg}). Product-mux externalized; cap_c stays bound to the Merkle terminal.",
            cs.len(),
            mono_cs.len(),
            mono_cs.len() - cs.len()
        );
        assert!(deg <= mono_deg, "externalizing the product-mux must not raise the constraint degree");
        assert!(cs.len() < mono_cs.len(), "CapWrapAir must be a strict constraint subset (product-mux dropped)");
    }

    /// **Caps AA1 — `AssembledCapWrapAir` composes as a LookupAir** (`--features recursion`). The sibling of
    /// `arith_wrap_assembled_composes` for caps: the reused monolith (`eval_bci(&CapMuxBci)`, product-mux
    /// externalized) + the narrow-tall cap-row region + the select bus form ONE lookup-carrying AIR that composes
    /// WITHIN the degree budget. `cap_c` is now bound to the slack cap-row region via the bus (not a free witness);
    /// the region→committed-cap binding (AA3) + the trace + native bus-balance (AA2) + the prove (AA4) follow.
    #[cfg(feature = "recursion")]
    #[test]
    fn cap_wrap_assembled_composes() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_lookup::Lookups;
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (air, _tr, _pis) = wrap_build_reused(&config, &proof, &pvs, false);

        let asm = AssembledCapWrapAir { m: air };
        let fw = asm.m.fused_w();
        let width = <AssembledCapWrapAir as BaseAir<Val>>::width(&asm);
        let (n_open, n_ch, n_ent) = (asm.openings().len(), asm.n_bind_ch(), asm.total_entries());
        let lookups = Lookups::from_air::<Challenge, _>(&asm);
        let (_layout, log_nqc) = combined_constraint_layout(&asm, &lookups, 1);
        println!(
            "cap AA1+AA3: width {width} = fused_w {fw} + 10 + n_bind_ch {n_ch} (cap-row region 9 + is_binder + \
             is_rd[{n_ch}]); {} lookup channel(s) (1 select + {n_ch} binding), {n_open} reads/head, {n_ent} \
             committed entries bound (≤{} /channel), log_nqc {log_nqc} ≤ {LOG_BLOWUP}. Select bus binds cap_c to \
             the cap-row region; the AA3 binding bus binds each cap-row digest to the committed cap pis.",
            lookups.len(),
            AssembledCapWrapAir::MAX_PER_CH
        );
        assert_eq!(width, fw + 10 + n_ch, "AA1 region (10) + AA3 is_rd one-hot (n_bind_ch)");
        assert_eq!(n_open, 2 + asm.m.cm_rounds(), "one read per opening (trace + quot + cm_rounds)");
        assert_eq!(lookups.len(), n_ch + 1, "1 select channel + n_bind_ch binding channels");
        assert!(log_nqc <= LOG_BLOWUP, "cap AA1+AA3 must compose within the degree budget (got {log_nqc})");
    }

    /// **Caps assembly AA2 — build the assembled cap-wrap trace.** Widen the monolith trace to `fused_w + 9`; mark
    /// each arith head (`is_head = 1`, the `m_tf` rows); and seed the cap-row region in the trace SLACK — for every
    /// opening's cap, one ROW per entry `[cap_id, entry_idx, digest = pis[cbase + entry·4 + k], cap_mult = −count]`,
    /// where `count` = how many heads select that entry (decoded from the committed index bits `sb_b`, exactly the
    /// AIR's `index>>shift`). The select bus then binds each head's `cap_c[g]` to the addressed cap-row. Returns
    /// `(air, trace, pis)`. Mirrors `assemble_arith_wrap`, one region over (base-field tuples, no fold recurrence).
    #[cfg(feature = "recursion")]
    fn assemble_cap_wrap(
        config: &crate::recursion::native_fri::MyConfig,
        proof: &p3_uni_stark::Proof<crate::recursion::native_fri::MyConfig>,
        pvs: &[Val],
    ) -> (AssembledCapWrapAir, RowMajorMatrix<Val>, Vec<Val>) {
        use p3_matrix::dense::RowMajorMatrix;

        let (air, mono_trace, pis) = wrap_build_reused(config, proof, pvs, false);
        let (fw, h) = (air.fused_w(), air.height());
        let n_q = air.n_queries;
        let (cr, cap_sel, is_head_col) = (fw, fw + 7, fw + 8);
        let (is_binder_col, is_rd_base) = (fw + 9, fw + 10);

        // The caps WITH their committed base `cbase` (openings() drops it; the trace reads the digest from pis).
        let caps: Vec<(usize, usize, usize, usize)> = {
            // (cap_id, shift, bits, cbase)
            let m = &air;
            let mut v = vec![
                (0, m.input_depth(), m.cap_height, m.cap_base()),
                (1, m.input_depth(), m.cap_height, m.qcap_base()),
            ];
            for r in 0..m.cm_rounds() {
                v.push((2 + r, m.commit_shift(r), m.commit_bits(r), m.commit_cap_base(r)));
            }
            v
        };
        let total_rows: usize = caps.iter().map(|&(_, _, bits, _)| 1usize << bits).sum();
        let n_ch = total_rows.div_ceil(AssembledCapWrapAir::MAX_PER_CH); // AA3 binding channels
        let width = fw + 10 + n_ch;

        // Arith heads = the rows where `m_tf` fires (one per query), same as `assemble_arith_wrap`.
        let tf_col = BaseAir::<Val>::periodic_columns(&air)[air.m_tf()].clone();
        let heads: Vec<usize> = (0..h).filter(|&r| tf_col[r % tf_col.len()] == Val::ONE).collect();
        assert_eq!(heads.len(), n_q, "one arith head per query");
        let used = air.tr() + n_q * air.m_period();
        // cap-rows [used, used+total_rows) + one binder row after them.
        assert!(used + total_rows + 1 <= h, "cap region + binder ({}) must fit the slack ({})", total_rows + 1, h - used);

        let mut wide = vec![Val::ZERO; h * width];
        for r in 0..h {
            wide[r * width..r * width + fw].copy_from_slice(&mono_trace.values[r * fw..(r + 1) * fw]);
        }
        for &head in &heads {
            wide[head * width + is_head_col] = Val::ONE;
        }

        // Seed the cap-row region: one ROW per (cap, entry) in enumeration order (global index `gi`); digest from
        // the committed cap, `cap_mult = −(heads selecting it)`, `is_rd` routing the AA3 binding read to channel
        // `gi % n_ch` (where the binder provides this entry).
        let mut dst = used;
        let mut gi = 0usize;
        for &(cap_id, shift, bits, cbase) in &caps {
            let n_entries = 1usize << bits;
            let mut count = vec![0u64; n_entries];
            for &head in &heads {
                let mut e = 0usize;
                for j in 0..bits {
                    if mono_trace.values[head * fw + air.sb_b(shift + j)] == Val::ONE {
                        e += 1 << j;
                    }
                }
                count[e] += 1;
            }
            for e in 0..n_entries {
                let b = dst * width;
                wide[b + cr] = Val::from_u64(cap_id as u64);
                wide[b + cr + 1] = Val::from_u64(e as u64);
                for k in 0..4 {
                    wide[b + cr + 2 + k] = pis[cbase + e * 4 + k];
                }
                wide[b + cr + 6] = Val::ZERO - Val::from_u64(count[e]); // cap_mult = −count
                wide[b + cap_sel] = Val::ONE;
                wide[b + is_rd_base + gi % n_ch] = Val::ONE; // AA3 read routing
                dst += 1;
                gi += 1;
            }
        }
        // The single binder row (PROVIDES every committed entry once, in the AIR), right after the cap-rows.
        wide[dst * width + is_binder_col] = Val::ONE;

        (AssembledCapWrapAir { m: air }, RowMajorMatrix::new(wide, width), pis)
    }

    /// **Caps assembly AA2 — the assembled cap-wrap's select bus balances** (native, cheap — NO prove). Assemble
    /// the trace and confirm the select bus balances as a signed multiset: each cap-row PROVIDES its entry (mult
    /// −count), each arith head READS its `2 + cm_rounds` index-selected entries (+1); they cancel iff every head's
    /// `cap_c[g]` == the committed cap-row the query's index addresses. Localizes any address / digest / count bug
    /// before the heavy prove (as `arith_wrap_assembled_bus_balances` did for the `ro` bus).
    #[cfg(feature = "recursion")]
    #[test]
    fn cap_wrap_assembled_bus_balances() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_field::PrimeField64;
        use p3_uni_stark::prove;
        use std::collections::HashMap;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, pis) = assemble_cap_wrap(&config, &proof, &pvs);

        let (fw, h) = (asm.m.fused_w(), asm.m.height());
        let n_ch = asm.n_bind_ch();
        let width = fw + 10 + n_ch;
        let (cr, cap_sel, is_head, is_binder, is_rd_base) = (fw, fw + 7, fw + 8, fw + 9, fw + 10);
        let m = &asm.m;
        let ku = |v: Val| v.as_canonical_u64();
        let openings = asm.openings();
        let caps = asm.caps_with_base();

        // Key by (CHANNEL, tuple): channel 0 = the SELECT bus (cap_c ↔ cap-row); 1..=n_ch = the committed-cap
        // BINDING (cap-row digest ↔ pis). Each channel must net to Val::ZERO independently (counts ≪ p ⇒
        // field-zero == int-zero), so a mis-routed binding read is caught, not just a value mismatch.
        let mut bus: HashMap<(usize, Vec<u64>), Val> = HashMap::new();
        for r in 0..h {
            let b = r * width;
            let g = |c: usize| trace.values[b + c];
            if g(cap_sel) == Val::ONE {
                let key = vec![ku(g(cr)), ku(g(cr + 1)), ku(g(cr + 2)), ku(g(cr + 3)), ku(g(cr + 4)), ku(g(cr + 5))];
                // Channel 0: the cap-row PROVIDES its entry to the select bus (mult cap_mult = −count).
                *bus.entry((0, key.clone())).or_insert(Val::ZERO) += g(cr + 6);
                // Channels 1..=n_ch: the cap-row READS its committed binding (+1) on its is_rd channel.
                let rd = (0..n_ch).find(|&gc| g(is_rd_base + gc) == Val::ONE).expect("cap-row routes to one channel");
                *bus.entry((rd + 1, key)).or_insert(Val::ZERO) += Val::ONE;
            }
            if g(is_head) == Val::ONE {
                for &(cap_id, cg_off, shift, bits) in &openings {
                    let mut sel_idx = 0u64;
                    for j in 0..bits {
                        if g(m.sb_b(shift + j)) == Val::ONE {
                            sel_idx += 1 << j;
                        }
                    }
                    let key = vec![
                        cap_id as u64,
                        sel_idx,
                        ku(g(m.cap_c(cg_off))),
                        ku(g(m.cap_c(cg_off + 1))),
                        ku(g(m.cap_c(cg_off + 2))),
                        ku(g(m.cap_c(cg_off + 3))),
                    ];
                    *bus.entry((0, key)).or_insert(Val::ZERO) += Val::ONE; // + select read
                }
            }
            if g(is_binder) == Val::ONE {
                // The binder PROVIDES every committed entry (−1) on channel (global_index % n_ch) + 1.
                let mut gi = 0usize;
                for &(cap_id, _shift, bits, cbase) in &caps {
                    for e in 0..(1usize << bits) {
                        let key = vec![
                            cap_id as u64,
                            e as u64,
                            ku(pis[cbase + e * 4]),
                            ku(pis[cbase + e * 4 + 1]),
                            ku(pis[cbase + e * 4 + 2]),
                            ku(pis[cbase + e * 4 + 3]),
                        ];
                        *bus.entry((gi % n_ch + 1, key)).or_insert(Val::ZERO) -= Val::ONE;
                        gi += 1;
                    }
                }
            }
        }
        let nonzero = bus.values().filter(|&&v| v != Val::ZERO).count();
        let bad: Vec<_> = bus.iter().filter(|(_, &v)| v != Val::ZERO).take(8).collect();
        assert!(bad.is_empty(), "every (channel, tuple) must net to zero; {nonzero} nonzero, e.g. {bad:?}");
        println!(
            "cap buses ({} channels: 1 select + {n_ch} binding): {} distinct (channel, tuple) entries, all \
             net-zero — cap_c bound to the cap-row (select) AND each cap-row digest to the committed cap pis \
             (binding) ⇒ the cap-select is SOUND at cw=false.",
            n_ch + 1,
            bus.len()
        );
    }

    /// **Caps assembly AA4 — the assembled cap-wrap PROVES through `prove_lookup`.** The definitive soundness
    /// check (the `arith_wrap_assembled_proves` analog for caps): build the full trace (reused monolith with the
    /// product-mux externalized + the narrow-tall cap-row region + the select bus + the AA3 committed-cap binding
    /// across `n_bind_ch` channels) and prove + verify it end-to-end through the W1 lookup prover (outer is_zk=1).
    /// Confirms the SOUND cap-select holds under a REAL prove — the monolith A–J constraints, the select bus
    /// (`cap_c` ↔ cap-row), and the binding bus (each cap-row digest ↔ the committed cap pis) all hold together as
    /// a SOUND STARK, replacing the degree-`cap_height` product-mux over `2^cap_height·4` COLUMNS with slack ROWS.
    /// A corrupted cap-row digest is rejected (the binding bus unbalances). Heavy (64 channels); `--release --ignored`.
    #[cfg(feature = "recursion")]
    #[test]
    #[ignore = "heavy: proves the assembled cap-wrap (2^16 rows, 64 channels) through prove_lookup; run `--release --features lookup,recursion -j2 -- --ignored`"]
    fn cap_wrap_assembled_proves() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::lookup::prover::{prove_lookup, verify_lookup};
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, pis) = assemble_cap_wrap(&config, &proof, &pvs);
        let width = <AssembledCapWrapAir as BaseAir<Val>>::width(&asm);
        println!(
            "proving assembled cap-wrap (select bus + committed-cap binding): width {width}, {} rows, {} channels",
            asm.m.height(),
            asm.n_bind_ch() + 1
        );
        let lproof = prove_lookup(&asm, trace, &pis);
        assert!(
            verify_lookup(&asm, &lproof, &pis).is_ok(),
            "the assembled cap-wrap must prove + verify through prove_lookup"
        );

        // Corrupt the first cap-row's digest ⇒ its committed-cap binding read (digest ≠ pis) unbalances the binding
        // bus ⇒ the corrupted trace must not verify.
        let (asm2, mut bad, pis2) = assemble_cap_wrap(&config, &proof, &pvs);
        let used = asm2.m.tr() + asm2.m.n_queries * asm2.m.m_period();
        let cr = asm2.m.fused_w();
        bad.values[used * width + cr + 2] += Val::ONE; // digest[0] of the first cap-row
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let p = prove_lookup(&asm2, bad, &pis2);
            verify_lookup(&asm2, &p, &pis2).is_err()
        }))
        .unwrap_or(true);
        std::panic::set_hook(hook);
        assert!(rejected, "a corrupted cap-row digest (≠ committed cap) must not produce a valid proof");
    }

    /// **Caps plumbing brick — `CapWrapAir` proves with the product-mux externalized** (`--release --ignored`).
    /// The heavy end-to-end half: the monolith trace already satisfies the full monolith ⊇ `CapWrapAir`
    /// (product-mux dropped), so `CapWrapAir` proves it DIRECTLY (no widening — cap_c is a pre-existing carrier,
    /// bound to the Merkle terminal + held). And corrupting a cap_c at an arith head is rejected (the remaining
    /// cap_c binding — hold + terminal — still fires). So the `emit_capmux` externalization is trace-faithful end
    /// to end; the cap_c→committed-cap binding (the removed product-mux) is the next brick (the bus). Mirrors
    /// `arith_wrap_witnessed_ro_proves`.
    #[cfg(feature = "recursion")]
    #[test]
    #[ignore = "heavy: proves CapWrapAir (2^16 rows); run `--release --features lookup,recursion -- --ignored`"]
    fn cap_wrap_externalized_proves() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::{prove, verify};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (air, mono_trace, pis) = wrap_build_reused(&config, &proof, &pvs, false);
        let (tr, width, cap0) = (air.tr(), air.fused_w(), air.cap_c(0));
        let wrap = CapWrapAir { m: air };

        let prf = prove(&config, &wrap, mono_trace.clone(), &pis);
        assert!(verify(&config, &wrap, &prf, &pis).is_ok(), "CapWrapAir must verify with the product-mux externalized");

        // Corrupt cap_c[0] at the first arith head ⇒ the remaining cap_c constraints (hold + Merkle terminal) break.
        let mut bad = mono_trace;
        bad.values[tr * width + cap0] += Val::ONE;
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let p = prove(&config, &wrap, bad, &pis);
            verify(&config, &wrap, &p, &pis).is_err()
        }))
        .unwrap_or(true);
        std::panic::set_hook(hook);
        assert!(rejected, "a corrupted cap_c must not produce a valid CapWrapAir proof");
    }

    /// **Brick 5 increment 2b — assemble the full wrap trace** (`--features recursion`). Widen the reused
    /// monolith trace to `fused_w + 16`; seed the FLATTEN op-table with the REAL ζ-openings + fold; place its
    /// rows in the trace SLACK (`op_sel = 1`); fill `folded_col` at each arith head (`tf = 1` rows) with the
    /// op-table's `folded` value; and override the `folded` wire's `out_mult` to `−n_heads` (it is read once per
    /// arith head, not internally). Returns `(AssembledWrapAir, trace, pis)`.
    #[cfg(feature = "recursion")]
    fn assemble_wrap(
        config: &crate::recursion::native_fri::MyConfig,
        proof: &p3_uni_stark::Proof<crate::recursion::native_fri::MyConfig>,
        pvs: &[Val],
    ) -> (AssembledWrapAir, RowMajorMatrix<Val>, Vec<Val>) {
        use crate::config::Challenge;
        use crate::joinsplit_air::JoinSplitAir;
        use crate::recursion::native_fri::epilogue_openings;
        use crate::wrap::op_table_f2_trace;
        use p3_field::BasedVectorSpace;
        use p3_uni_stark::{get_symbolic_constraints, AirLayout, BaseEntry, BaseLeaf};

        let (air, mono_trace, pis) = wrap_build_reused(config, proof, pvs, false);
        let (eo_local, eo_next, is_first, is_last, is_trans, _iv, _eq, eo_alpha, _z, eo_periodic) =
            epilogue_openings(config, &JoinSplitAir, proof, pvs);
        let pubs: Vec<Challenge> = pvs.iter().map(|&p| Challenge::from(p)).collect();
        let seed = |l: &BaseLeaf<Val>| -> Challenge {
            match l {
                BaseLeaf::Constant(c) => Challenge::from(*c),
                BaseLeaf::Variable(v) => match v.entry {
                    BaseEntry::Main { offset } => {
                        if offset == 0 {
                            eo_local[v.index]
                        } else {
                            eo_next[v.index]
                        }
                    }
                    BaseEntry::Public => pubs[v.index],
                    BaseEntry::Periodic => eo_periodic[v.index],
                    BaseEntry::Preprocessed { .. } => panic!("preprocessed columns unsupported"),
                },
                BaseLeaf::IsFirstRow => is_first,
                BaseLeaf::IsLastRow => is_last,
                BaseLeaf::IsTransition => is_trans,
            }
        };
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));

        // 2c preseed: every ζ-opening as a leaf `(key, value, open_id)`, so each arith-head provide has a
        // reader. Values from `epilogue_openings`; `open_id` from the canonical scheme (shared with the AIR).
        let (w, np, nper) = (air.w_inner(), air.n_pub(), air.n_periodic());
        let (wu, npu, nperu) = (w as u64, np as u64, nper as u64);
        let mut preseed: Vec<((u8, u64), Challenge, u64)> = Vec::new();
        for c in 0..w {
            preseed.push(((0, c as u64), eo_local[c], open_id((0, c as u64), wu, npu, nperu)));
            preseed.push(((1, c as u64), eo_next[c], open_id((1, c as u64), wu, npu, nperu)));
        }
        for i in 0..np {
            preseed.push(((2, i as u64), pubs[i], open_id((2, i as u64), wu, npu, nperu)));
        }
        for i in 0..nper {
            preseed.push(((3, i as u64), eo_periodic[i], open_id((3, i as u64), wu, npu, nperu)));
        }
        preseed.push(((4, 0), is_first, open_id((4, 0), wu, npu, nperu)));
        preseed.push(((5, 0), is_last, open_id((5, 0), wu, npu, nperu)));
        preseed.push(((6, 0), is_trans, open_id((6, 0), wu, npu, nperu)));

        let (op_matrix, _roots, folded, leaf_bindings, _quot) =
            op_table_f2_trace(&constraints, seed, Some(eo_alpha), &preseed, None);
        let (folded_val, folded_addr) = folded.expect("the join-split epilogue folds to a value");

        let (fw, h) = (air.fused_w(), air.height());
        let used = air.tr() + air.n_queries * air.m_period();
        let op_h = op_matrix.values.len() / 13;
        let width = fw + 19 + N_GROUPS;
        assert!(used + op_h <= h, "op-table rows ({op_h}) must fit in the monolith slack ({})", h - used);

        // The arith heads = the rows where the epilogue selector `tf` (= m_tf periodic) fires.
        let tf_col = BaseAir::<Val>::periodic_columns(&air)[air.m_tf()].clone();
        let heads: Vec<usize> = (0..h).filter(|&r| tf_col[r % tf_col.len()] == Val::ONE).collect();

        let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
        let mut wide = vec![Val::ZERO; h * width];
        for r in 0..h {
            wide[r * width..r * width + fw].copy_from_slice(&mono_trace.values[r * fw..(r + 1) * fw]);
        }
        let fc = cc(folded_val);
        for &head in &heads {
            wide[head * width + fw..head * width + fw + 2].copy_from_slice(&fc); // folded_col at arith heads
            wide[head * width + fw + 16] = Val::ONE; // is_head (= tf) — gates the folded/provide bus terms
        }
        let ob = fw + 2;
        for i in 0..op_h {
            let dst = used + i;
            let mut cols: [Val; 13] = op_matrix.values[i * 13..i * 13 + 13].try_into().unwrap();
            if cols[3] == Val::from_u64(folded_addr) {
                cols[12] = -Val::from_u64(heads.len() as u64); // folded read once per arith head, not internally
            }
            wide[dst * width + ob..dst * width + ob + 13].copy_from_slice(&cols);
            wide[dst * width + fw + 15] = Val::ONE; // op_sel
        }
        // 2c binding: mark the opening-leaf rows with their `open_id` + `is_leaf`, so each reads its committed
        // opening from the arith head's provide (binding leaf value == the committed pz/pis/sel column).
        for &(row, oid) in &leaf_bindings {
            let dst = used + row;
            wide[dst * width + fw + 17] = Val::from_u64(oid); // open_id
            wide[dst * width + fw + 18] = Val::ONE; // is_leaf
            let ch = ((oid - OPEN_BASE) as usize) % N_GROUPS; // one-hot channel = open_index % N_GROUPS
            wide[dst * width + fw + 19 + ch] = Val::ONE; // is_ch[ch]
        }
        (AssembledWrapAir { m: air, folded_addr }, RowMajorMatrix::new(wide, width), pis)
    }

    /// **Brick 5 increment 2b — the assembled wrap trace's wiring bus balances** (native, cheap — NO heavy
    /// prove). Assemble the full wrap trace and confirm the LogUp wiring bus balances as a signed multiset:
    /// every op-table wire's provide (`−fanout`, or `−n_heads` for `folded`) is matched by its reads (`+1`
    /// each), and the arith heads' `folded` reads match the op-table's `folded` provide. Localizes any
    /// addressing / multiplicity / placement bug before `prove_lookup`.
    #[cfg(feature = "recursion")]
    #[test]
    fn wrap_assembled_bus_balances() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_field::{Field, PrimeField64, TwoAdicField};
        use p3_goldilocks::Goldilocks;
        use p3_uni_stark::prove;
        use std::collections::HashMap;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, pis) = assemble_wrap(&config, &proof, &pvs);

        let (fw, h) = (asm.m.fused_w(), asm.m.height());
        let (width, ob) = (fw + 19 + N_GROUPS, fw + 2);
        let tf_col = BaseAir::<Val>::periodic_columns(&asm.m)[asm.m.m_tf()].clone();
        let n_heads = (0..h).filter(|&r| tf_col[r % tf_col.len()] == Val::ONE).count() as i128;
        let (wu, npu, nperu) = (asm.m.w_inner() as u64, asm.m.n_pub() as u64, asm.m.n_periodic() as u64);
        let g_inv = Goldilocks::two_adic_generator(asm.m.cm_rounds() - asm.m.is_zk).inverse();
        const P: u64 = 0xFFFF_FFFF_0000_0001; // Goldilocks order
        let sgn = |v: Val| -> i128 {
            let u = v.as_canonical_u64();
            if u > P / 2 { u as i128 - P as i128 } else { u as i128 }
        };
        let ku = |v: Val| v.as_canonical_u64();
        let chan = |oid: u64| ((oid - OPEN_BASE) as usize % N_GROUPS) + 1; // an opening's lookup channel

        // Key by (CHANNEL, addr, v0, v1) — each LogUp channel must balance INDEPENDENTLY (so a mis-routed
        // leaf-read is caught, not just a value mismatch).
        let mut bus: HashMap<(usize, u64, u64, u64), i128> = HashMap::new();
        for r in 0..h {
            let b = r * width;
            let g = |c: usize| trace.values[b + c];
            let op_sel = sgn(g(fw + 15));
            let is_op = sgn(g(ob)) + sgn(g(ob + 1)) + sgn(g(ob + 2));
            let read = op_sel * is_op;
            *bus.entry((0, ku(g(ob + 6)), ku(g(ob + 7)), ku(g(ob + 8)))).or_default() += read; // read a (ch 0)
            *bus.entry((0, ku(g(ob + 9)), ku(g(ob + 10)), ku(g(ob + 11)))).or_default() += read; // read b
            *bus.entry((0, ku(g(ob + 3)), ku(g(ob + 4)), ku(g(ob + 5)))).or_default() += op_sel * sgn(g(ob + 12)); // def
            let is_head = sgn(g(fw + 16));
            *bus.entry((0, asm.folded_addr, ku(g(fw)), ku(g(fw + 1)))).or_default() += is_head; // folded read (ch 0)
            for gc in 0..N_GROUPS {
                let is_ch = sgn(g(fw + 19 + gc));
                *bus.entry((gc + 1, ku(g(fw + 17)), ku(g(ob + 4)), ku(g(ob + 5)))).or_default() += is_ch * n_heads; // leaf read → its channel
            }
            if is_head != 0 {
                let mut prov = |oid: u64, v0: u64, v1: u64| *bus.entry((chan(oid), oid, v0, v1)).or_default() -= is_head;
                for c in 0..asm.m.w_inner() {
                    let (pl, pn) = (asm.m.pz(asm.m.trm_trace(c)), asm.m.pz(asm.m.trm_next(c)));
                    prov(open_id((0, c as u64), wu, npu, nperu), ku(g(pl)), ku(g(pl + 1)));
                    prov(open_id((1, c as u64), wu, npu, nperu), ku(g(pn)), ku(g(pn + 1)));
                }
                for i in 0..asm.m.n_pub() {
                    prov(open_id((2, i as u64), wu, npu, nperu), ku(pis[asm.m.pub_pi() + i]), 0);
                }
                for i in 0..asm.m.n_periodic() {
                    let (pb0, pb1) = (asm.m.periodic_base() + 2 * i, asm.m.periodic_base() + 2 * i + 1);
                    prov(open_id((3, i as u64), wu, npu, nperu), ku(pis[pb0]), ku(pis[pb1]));
                }
                let (s0, s2) = (asm.m.sel(0), asm.m.sel(2));
                prov(open_id((4, 0), wu, npu, nperu), ku(g(s0)), ku(g(s0 + 1)));
                prov(open_id((5, 0), wu, npu, nperu), ku(g(s2)), ku(g(s2 + 1)));
                prov(open_id((6, 0), wu, npu, nperu), ku(pis[2] - g_inv), ku(pis[3]));
            }
        }
        let bad: Vec<_> = bus.iter().filter(|(_, &m)| m != 0).take(8).collect();
        assert!(bad.is_empty(), "each lookup channel must balance; {} nonzero net entries, e.g. {bad:?}", bus.values().filter(|&&m| m != 0).count());
        println!("assembled wrap bus (2c binding, SPLIT into {} channels): {} distinct (channel,addr,val) entries, all net-zero — the opening leaves are BOUND, per-channel", N_GROUPS + 1, bus.len());
    }

    /// **Brick 5 increment 2b-ii — the assembled wrap PROVES through `prove_lookup`.** The definitive
    /// soundness check: build the full assembled wrap trace (reused monolith regions + the op-table region +
    /// the wiring bus) and prove + verify it end-to-end through the W1 lookup prover (outer is_zk=1). This
    /// confirms the op-table-based wrap is a SOUND STARK — the monolith A–J constraints, the op-table's local
    /// op relations, the wiring bus (binding `folded_col` to the op-table's computed fold), and the
    /// `OpTableBci` epilogue (`folded·inv_van == quot`) all hold together — at width `fused_w + 16` (O(1)),
    /// not `fused_w + 2·n_mul`. Heavy (2^16 → 2^17 hiding commit); `--release --ignored`.
    #[cfg(feature = "recursion")]
    #[test]
    #[ignore = "heavy: proves the assembled wrap (2^16 rows) through prove_lookup; run `--release --features lookup,recursion -- --ignored`"]
    fn wrap_assembled_proves() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::lookup::prover::{prove_lookup, verify_lookup};
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, pis) = assemble_wrap(&config, &proof, &pvs);
        let width = <AssembledWrapAir as BaseAir<Val>>::width(&asm);
        println!("proving assembled wrap (op-table + 2c opening binding, split): width {width}, {} rows", asm.m.height());
        let lproof = prove_lookup(&asm, trace, &pis);
        assert!(
            verify_lookup(&asm, &lproof, &pis).is_ok(),
            "the assembled op-table-based wrap must prove + verify through prove_lookup"
        );
    }

    /// **Cheap always-on validation of the reused-region epilogue witness (B/H).** The same pre-check
    /// `wrap_build_reused` runs, standalone (no heavy trace build): extract the OOD openings for a REAL
    /// join-split inner and confirm the native symbolic fold equals `quotient(ζ)` — the identity the wrap's
    /// B/C epilogue (lookup form) must reproduce. Localizes any extraction/wiring bug in the fast suite.
    #[cfg(feature = "recursion")]
    #[test]
    fn wrap_reused_ood_identity() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::{epilogue_openings, eval_symbolic_native, make_config};
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};
        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (eo_local, eo_next, is_first, is_last, is_trans, inv_van, eo_quot, eo_alpha, _z, eo_periodic) =
            epilogue_openings(&config, &JoinSplitAir, &proof, &pvs);
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let pubs: Vec<Challenge> = pvs.iter().map(|&p| Challenge::from(p)).collect();
        let mut folded = Challenge::ZERO;
        for c in &constraints {
            folded = folded * eo_alpha
                + eval_symbolic_native(c, &eo_local, &eo_next, &pubs, &eo_periodic, is_first, is_last, is_trans);
        }
        assert_eq!(folded * inv_van, eo_quot, "reused-region OOD identity: symbolic fold == quotient(ζ)");
    }

    /// The heavy end-to-end: the reused-region AIR, built from the wrap side, PROVES + VERIFIES over a real
    /// inner and rejects a tampered inner public — the wrap-side trace builder is correct, not just
    /// well-shaped. Ignored by default (2^16 rows, ~GBs); run with `--ignored`.
    #[cfg(feature = "recursion")]
    #[test]
    #[ignore = "heavy: proves the full reused-region monolith (2^16 rows, ~7 GB); run with `--release \
                --features lookup,recursion -- --ignored` (debug is ~100× slower)"]
    fn wrap_reused_trace_proves() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::{prove, verify};
        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (air, trace, pis) = wrap_build_reused(&config, &proof, &pvs, false);
        let prf = prove(&config, &air, trace, &pis);
        assert!(verify(&config, &air, &prf, &pis).is_ok(), "the reused-region monolith must verify");
        let mut bad = pis.clone();
        bad[air.pub_pi()] += Val::ONE;
        assert!(verify(&config, &air, &prf, &bad).is_err(), "a tampered inner pub must be rejected");
    }

    /// **W2-measure — the assembled wrap.** Build a real join-split `MonolithAir`, wrap it (`WrapAir` reuses
    /// the whole constraint system via `eval_bci`, with the WITNESSED epilogue + cap-mux delegated), and
    /// measure the wrap's `log_nqc ≤ 4` at the production is_zk = 1. The witnessed `c_k` cap the epilogue fold
    /// degree independent of the inner — so the assembled wrap (the refactor's payoff, `eval_bci` + `WrapBci`)
    /// composes within budget.
    #[cfg(feature = "recursion")]
    #[test]
    fn wrap_air_within_budget() {
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
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize, narrow_arith: false, narrow_caps: false, narrow_openings: false, narrow_ov: false };
        let wrap = WrapAir::new(air);
        let width = <WrapAir as p3_air::BaseAir<Val>>::width(&wrap);
        let layout = AirLayout::from_air::<Val>(&wrap);
        let log_nqc = get_log_num_quotient_chunks::<Val, WrapAir>(&wrap, layout, 1);
        println!(
            "WrapAir (join-split inner, witnessed epilogue): width {width} (+{} c_k cols), log_nqc {log_nqc} (budget {LOG_BLOWUP})",
            2 * wrap.n_mul
        );
        assert!(log_nqc <= LOG_BLOWUP, "the assembled wrap must be within the degree budget");
    }

    /// **Brick 5 increment 2 — the assembled wrap AIR (op-table region + wiring bus) composes as a LookupAir.**
    /// Build a real join-split `MonolithAir`, wrap it in `AssembledWrapAir` = the reused monolith regions
    /// (`eval_bci` + `OpTableBci`, epilogue reads `folded`) + the FLATTEN op-table region (gated by `op_sel`) +
    /// the wiring bus (op wiring + the arith head reading `folded` at `FOLDED_ADDR`). Measured through the W1
    /// lookup prover's OWN layout (`combined_constraint_layout`, since it now carries the bus lookup): its width
    /// is `fused_w + 16` (folded 2 + op-table 13 + op_sel 1 — **O(1) over fused_w**, vs `WrapAir`'s
    /// `fused_w + 2·n_mul`) and it composes within budget at is_zk=1. So `eval_bci` (the whole monolith
    /// constraint system) THREADS the interaction builders — the assembly is a valid, in-budget lookup AIR. The
    /// trace builder + prove through `prove_lookup`, then the openings→leaves seam, are the next increments.
    #[cfg(feature = "recursion")]
    #[test]
    fn wrap_assembled_composes() {
        use crate::joinsplit_air::{
            build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH,
        };
        use crate::lookup::prover::combined_constraint_layout;
        use crate::recursion::monolith::tests::sim_full;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::{make_config, multicol_query_terms};
        use p3_lookup::Lookups;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
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
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize, narrow_arith: false, narrow_caps: false, narrow_openings: false, narrow_ov: false };
        let fused_w = air.fused_w();
        let asm = AssembledWrapAir { m: air, folded_addr: 0 }; // any address for the pure composition check
        let width = <AssembledWrapAir as p3_air::BaseAir<Val>>::width(&asm);
        let lookups = Lookups::from_air::<Challenge, _>(&asm);
        let (_layout, log_nqc) = combined_constraint_layout(&asm, &lookups, 1);
        println!(
            "AssembledWrapAir (op-table + bus + 2c binding, SPLIT): width {width} = fused_w {fused_w} + {} (folded \
             2 + op-table 13 + op_sel 1 + is_head 1 + open_id 1 + is_leaf 1 + is_ch {N_GROUPS}), {} lookup(s), \
             log_nqc {log_nqc} (budget {LOG_BLOWUP}) — O(1) over fused_w vs WrapAir's fused_w + 2·n_mul",
            19 + N_GROUPS,
            lookups.len()
        );
        assert_eq!(width, fused_w + 19 + N_GROUPS, "the assembled wrap adds only O(1) cols (op-table + binding + routing)");
        // The 2c opening binding's ~120 provides are SPLIT across N_GROUPS+1 lookup channels (each ≤ ~16 terms),
        // so the assembled wrap composes WITHIN the degree budget again (was log_nqc 6 on one channel; now 4).
        assert!(log_nqc <= LOG_BLOWUP, "the assembled wrap (split binding) must compose within the degree budget");

        // **W5 fixed-point situation after W3 (measured).** W3's op-table removed the `2·n_mul` c_k COLUMNS, but
        // the outer width still scales with the INNER width via the super-tile ARITH TILE (`9·n_terms`, with
        // `n_terms ≈ 2·w_inner` — the reduced-opening/DEEP terms laid out in COLUMNS, `z(k)=qt_terms+9k`). So the
        // B factor (outer width / inner width) is still ≫ 1 — NOT yet the fixed point (`W_out ≤ W_in`). This is
        // the honest gap the `tree/mod.rs` model currently ASSUMES away ("size-stable by construction IF
        // canonical fixed-shape"): the arith tile + the caps (`2^cap_height`) + `n_terms` must be made
        // inner-independent (narrow-tall columns→rows, like the op-table did for `c_k`, + canonicalization).
        let (n_terms, w_inner) = (asm.m.n_terms, asm.m.w_inner());
        let arith_tile = 9 * n_terms; // the DEEP reduced-opening columns (z(n_terms) − qt_terms)
        println!(
            "W5 fixed-point GAP (post-W3): assembled wrap width {width} verifying a w_inner={w_inner} inner ⇒ B = \
             {}× (needs ≤ 1). The ARITH TILE = 9·n_terms = {arith_tile} ({}% of fused_w {fused_w}, n_terms={n_terms} \
             ≈ 2·w_inner) is the DOMINANT inner-scaling term — the NEXT narrow-tall target. W3 removed the c_k \
             COLUMNS; the arith tile + caps + canonicalization remain for the size fixed point.",
            width / w_inner,
            arith_tile * 100 / fused_w
        );

        // **The arith-tile narrow-tall WIN, projected + feasibility-checked (post-`ffe9f47`).** With `DeepFoldBci`
        // the `9·n_terms` inline arith COLUMNS are externalized (ArithWrapAir today: `ro` witnessed, columns still
        // present). The completed swap places the narrow-tall `DeepFoldAir` (n_terms ROWS per query, width 18) in
        // trace SLACK and removes the columns. Grounded on THIS real inner: (1) the region FITS the slack, and
        // (2) the width contracts — the concrete size-fixed-point lever.
        let (n_q, hgt) = (asm.m.n_queries, asm.m.height());
        let (used, region_rows) = (asm.m.tr() + n_q * asm.m.m_period(), n_terms * n_q);
        assert!(region_rows <= hgt - used, "narrow-tall region ({region_rows} rows) must fit the slack ({})", hgt - used);
        let swapped_w = fused_w - arith_tile + 18 + 2; // −9·n_terms cols, +DeepFoldAir region (18) + ro_col (2)
        println!(
            "  → ARITH-TILE narrow-tall projection: region {region_rows} rows ≤ slack {} ✓; width fused_w {fused_w} \
             → SWAPPED {swapped_w} (−{arith_tile} arith cols + 20 O(1)) ⇒ B {}→{} (outer/inner). The 9·n_terms \
             COLUMNS are the removed inner-scaling term; caps + canonicalization + Tip5 then drive B → ≤ 1.",
            hgt - used,
            width / w_inner,
            swapped_w / w_inner
        );
        assert!(swapped_w < fused_w, "the narrow-tall arith swap must strictly shrink the monolith width");
    }

    /// **Arith-tile assembly increment AA1 — `AssembledArithWrapAir` composes as a LookupAir.** The sibling of
    /// `wrap_assembled_composes` for the arith tile: the reused monolith regions (`eval_bci` + `DeepFoldBci`) +
    /// the narrow-tall `DeepFoldAir` region (gated to slack) + the `ro` wiring bus form ONE lookup-carrying AIR
    /// that composes WITHIN the degree budget. `ro` is now bound to the slack region's fold via the bus (not a
    /// free witness); the query-input (`z`/`pz`/`px`) binding + the trace + the prove are AA2–AA4. Cheap (no
    /// prove) — mirrors the op-table's first assembly increment (`wrap_assembled_composes`).
    #[cfg(feature = "recursion")]
    #[test]
    fn arith_wrap_assembled_composes() {
        use crate::joinsplit_air::{
            build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH,
        };
        use crate::lookup::prover::combined_constraint_layout;
        use crate::recursion::monolith::tests::sim_full;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::{make_config, multicol_query_terms};
        use p3_lookup::Lookups;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (_bi, counts, binds, _chs, index_binds, index_felts) = sim_full(&config, &proof, &pvs);
        let (terms, _x, _a, _ro, _wt) = multicol_query_terms(&config, &JoinSplitAir, &proof, &pvs, 0);
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        // Build the same monolith at FULL vs NARROW arith to MEASURE the AA5.2 width harvest. Narrow drops the
        // inline fold's `inv`+`apow` (4 felts/term); `[z, pz, px]` stay (the wrap externalizes only the fold).
        let mk = |narrow: bool| MonolithAir {
            counts: counts.clone(),
            binds: binds.clone(),
            index_binds: index_binds.clone(),
            n_queries: index_felts.len(),
            n_terms: terms.len(),
            inner_counter: false,
            column_window: false,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints: constraints.clone(),
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: narrow, narrow_caps: false, narrow_openings: false, narrow_ov: false,
        };
        let full = mk(false);
        let (full_fused_w, n_terms, w_inner) = (full.fused_w(), full.n_terms, full.w_inner());
        let air = mk(true); // NARROW: z+px+inv/apow gone (stride 9→2), fold externalized, z re-derived, px sourced
        let fused_w = air.fused_w();
        assert_eq!(fused_w, full_fused_w - 7 * n_terms, "narrow_arith drops z+px+inv+apow (7 felts/term) from fused_w");

        let asm = AssembledArithWrapAir { m: air };
        let width = <AssembledArithWrapAir as p3_air::BaseAir<Val>>::width(&asm);
        let full_width = full_fused_w + 25 + N_GROUPS; // the AA3 (full-arith) wrap width, for comparison
        let lookups = Lookups::from_air::<Challenge, _>(&asm);
        let (_layout, log_nqc) = combined_constraint_layout(&asm, &lookups, 1);
        println!(
            "AA5.4 NARROW arith harvest: full fused_w {full_fused_w} (B {}×) → narrow {fused_w} (B {}×); wrap width \
             {width} = fused_w {fused_w} + {} (ro 2 + DeepFoldAir 18 + 4 markers + term_idx 1 + is_ch {N_GROUPS}), \
             was {full_width}; {} lookup(s), log_nqc {log_nqc} ≤ {LOG_BLOWUP}. Dropped z+px+inv+apow = {} felts \
             (7·n_terms: inv/apow externalized, z re-derived = ζ/ζ·g, px sourced from the ov/qc Merkle-leaf \
             carriers); only [pz] (the genuine OOD opening) kept — the arith tile is now the FULL-WIN minimum.",
            full_width / w_inner,
            width / w_inner,
            25 + N_GROUPS,
            lookups.len(),
            7 * n_terms
        );
        assert_eq!(width, fused_w + 25 + N_GROUPS, "the wrap adds only O(1) cols over the narrow fused_w");
        assert!(log_nqc <= LOG_BLOWUP, "the narrow arith-assembled wrap must compose within the degree budget");
        assert!(width < full_width, "narrow_arith must strictly shrink the wrap width (the AA5.2 win)");
        assert!(w_inner > 0);
    }

    /// **POST-SWAP SIZE MAP — which region now dominates `fused_w` (the B≤1 next-lever decision).** After the
    /// arith-tile narrow-tall swap (AA5.4: `9·n_terms` → `2·n_terms` columns), decompose the narrow join-split
    /// monolith's `fused_w` into its constituent regions, tag each with its SCALING LAW (inner-width, FRI-depth,
    /// or constant), and SELF-CHECK that the region widths sum to `fused_w()` exactly (the guard that the map is
    /// faithful, not hand-waved). Also isolates the `column_window` pis/cap window — the regime where the inner
    /// proof's `2^cap_height` caps become OUTER columns — so the caps-vs-canonicalization-vs-Tip5 fork is decided
    /// on measured widths, not the handoff's guess. Cheap (no prove): builds the air and reads offsets.
    #[cfg(feature = "recursion")]
    #[test]
    fn post_swap_region_breakdown() {
        use crate::joinsplit_air::{
            build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH,
        };
        use crate::recursion::monolith::tests::sim_full;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::{make_config, multicol_query_terms};
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (_bi, counts, binds, _chs, index_binds, index_felts) = sim_full(&config, &proof, &pvs);
        let (terms, _x, _a, _ro, _wt) = multicol_query_terms(&config, &JoinSplitAir, &proof, &pvs, 0);
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let mk = |narrow: bool, column_window: bool, narrow_caps: bool| MonolithAir {
            counts: counts.clone(),
            binds: binds.clone(),
            index_binds: index_binds.clone(),
            n_queries: index_felts.len(),
            n_terms: terms.len(),
            inner_counter: false,
            column_window,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints: constraints.clone(),
            w_inner_f: WIDTH,
            n_pub_f: N_PUBLIC,
            n_periodic_f: N_PERIODIC,
            is_zk: 0,
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
            narrow_arith: narrow, narrow_caps, narrow_openings: false, narrow_ov: false,
        };

        // Decompose fused_w (column_window=false: the arith-wrap regime the whole track measures B in). The regions
        // are laid out in offset order; each width is a difference of consecutive region bases. `S` tags scaling:
        // "inner" = grows with the inner's shape (w_inner / nqc / n_terms), "depth" = grows with the FRI depth `lg`,
        // "const" = fixed. n_terms ≈ 2·w_inner + 2·nqc, so the arith tile is the dominant inner-scaling term.
        let breakdown = |a: &MonolithAir| {
            let cw = a.cw(); // 0 at is_zk=0
            let _ = cw;
            vec![
                ("deep-hdr (DEEP idx region 9+lg + acc chain lg + alpha 2)", a.qt_terms(), "depth"),
                ("ARITH TILE (arith_stride · n_terms)", a.tile_w() - a.qt_terms(), "inner"),
                ("index-decomp SB (64 bits + sb_q + rem + carry)", a.ov() - a.sb_x(), "const"),
                ("trace-leaf carriers (input_leaf_felts)", a.input_leaf_felts() + a.random_carriers(), "inner"),
                ("quot-leaf carriers (2·nqc)", a.quot_leaf_felts(), "inner"),
                ("commit fold-group carriers (4·cm_rounds)", 4 * a.cm_rounds(), "depth"),
                ("cap-ENTRY carriers (selected entry, (2+cm_rounds)·4)", a.n_cap_c(), "depth"),
                ("Lagrange selectors", 6, "const"),
            ]
        };

        let full = mk(false, false, false);
        let narrow = mk(true, false, false);
        let (fw_full, fw) = (full.fused_w(), narrow.fused_w());
        let (n_terms, w_inner, lg, nqc, cap_h) =
            (narrow.n_terms, narrow.w_inner(), narrow.lg(), narrow.nqc(), narrow.cap_height);

        // SELF-CHECK: the region map must reconstruct fused_w exactly (else the map is wrong, not the code).
        let sum: usize = breakdown(&narrow).iter().map(|(_, wdt, _)| wdt).sum();
        assert_eq!(sum, fw, "narrow region breakdown ({sum}) must sum to fused_w ({fw})");
        let sum_full: usize = breakdown(&full).iter().map(|(_, wdt, _)| wdt).sum();
        assert_eq!(sum_full, fw_full, "full region breakdown ({sum_full}) must sum to fused_w ({fw_full})");

        let mut rows = breakdown(&narrow);
        rows.sort_by(|x, y| y.1.cmp(&x.1)); // largest first
        println!(
            "\n=== POST-SWAP fused_w REGION MAP (narrow join-split inner: w_inner={w_inner}, nqc={nqc}, \
             n_terms={n_terms}, lg={lg}, cap_height={cap_h}) ===\n  fused_w: FULL {fw_full} → NARROW {fw} \
             (arith 9→2/term saved {} cols)",
            fw_full - fw
        );
        for (name, wdt, scale) in &rows {
            println!("    {wdt:>4}  ({:>4.1}%)  [{scale:>5}]  {name}", 100.0 * *wdt as f64 / fw as f64);
        }

        // The column_window regime: the inner proof's pis (challenges/indices/final_poly/PUB/CAPS/periodic/qwt) are
        // mirrored into OUTER columns (+ the fold accumulators). This is where 2^cap_height enters fused_w — the
        // self-composition regime. Isolate its size and the cap portion within it.
        let narrow_cw = mk(true, true, false);
        let fw_cw = narrow_cw.fused_w();
        let cap_stride = narrow_cw.cap_stride(); // 2^cap_height · 4 (full cap)
        let cap_felts = 2 * cap_stride + narrow_cw.commit_caps_len(); // trace + quot + commit-round caps
        let fold_acc = 2 * narrow_cw.n_fold_acc();
        println!(
            "  --- column_window (self-composition) regime ---\n    fused_w with column_window: {fw_cw} \
             (= {fw} + pis-window {} + fold-acc {fold_acc})\n    of the pis window, CAPS = {cap_felts} felts \
             (cap_stride {cap_stride} = 2^{cap_h}·4; SCALES 2^cap_height with tree depth — small here, cap_height={cap_h})",
            fw_cw - fw - fold_acc
        );

        // === THE POST-CAPS cw=true REGIME (narrow_caps — the sound capstone `AssembledCapWrapCwAir`) ===
        // Now that the `2^cap_height` cap COLUMNS are dropped from the pis window + FS-anchored (the sponge-cap
        // bus, sound + proven), break down what REMAINS of the cw=true fused_w to find the NEW dominant region —
        // the next size lever toward the W5 fixed point B≤1. The base super-tile/transcript regions are unchanged
        // (`breakdown`), the pis window now carries NO caps (challenges / indices / final_poly / PUB / periodic+qwt).
        let nc = mk(true, true, true); // narrow_arith + column_window + narrow_caps
        let fw_nc = nc.fused_w();
        let n_binds = nc.binds.len();
        let mut nc_rows: Vec<(String, usize, &str)> =
            breakdown(&nc).into_iter().map(|(n, w, s)| (n.to_string(), w, s)).collect();
        let base_nc: usize = nc_rows.iter().map(|(_, w, _)| w).sum();
        let fold_acc_nc = 2 * nc.n_fold_acc();
        // The column_window pis-window is taken as the RESIDUAL `fw_nc − base − fold-acc` (the SAME way the full-cap
        // regime above measures it) — exact by construction. Carve it into named pis pieces + a residual for the
        // window's layout/padding (the fused_w window reserves ~24 cols beyond `pis_count` no accessor spans).
        let pis_win_nc = fw_nc - base_nc - fold_acc_nc;
        let periodic_qwt = nc.pis_count().saturating_sub(nc.periodic_base());
        let named_pis = 2 * n_binds + nc.n_queries + 2 + nc.n_pub() + periodic_qwt;
        nc_rows.push(("pis-win: challenges (2·n_binds)".to_string(), 2 * n_binds, "depth"));
        nc_rows.push(("pis-win: FRI query indices (n_queries)".to_string(), nc.n_queries, "inner"));
        nc_rows.push(("pis-win: final_poly".to_string(), 2, "const"));
        nc_rows.push(("pis-win: PUB (block tx-root / inner pis)".to_string(), nc.n_pub(), "const"));
        nc_rows.push(("pis-win: eo-periodic + quot-recompose wts".to_string(), periodic_qwt, "inner"));
        nc_rows.push(("pis-win: window layout/padding (residual)".to_string(), pis_win_nc.saturating_sub(named_pis), "const"));
        nc_rows.push(("fold-acc (constraint α-Horner chunks, 2·n_fold_acc)".to_string(), fold_acc_nc, "inner"));
        // SELF-CHECK: base regions + the caps-free pis window + fold-acc reconstruct the narrow cw=true fused_w.
        let nc_sum: usize = nc_rows.iter().map(|(_, w, _)| w).sum();
        assert_eq!(nc_sum, fw_nc, "post-caps cw=true region map ({nc_sum}) must sum to narrow_caps fused_w ({fw_nc})");
        nc_rows.sort_by(|x, y| y.1.cmp(&x.1)); // largest first
        println!(
            "\n=== POST-CAPS cw=true fused_w REGION MAP (narrow_caps — the sound capstone; caps DROPPED + FS-anchored) ===\
             \n  cw=true fused_w: FULL-CAP {fw_cw} → NARROW-CAP {fw_nc} ({} cap felts gone) — the NEW breakdown:",
            fw_cw - fw_nc
        );
        for (name, wdt, scale) in &nc_rows {
            println!("    {wdt:>4}  ({:>4.1}%)  [{scale:>5}]  {name}", 100.0 * *wdt as f64 / fw_nc as f64);
        }
        println!(
            "  ⇒ NEW dominant region post-caps: '{}' = {} ({:.1}% of {fw_nc})",
            nc_rows[0].0,
            nc_rows[0].1,
            100.0 * nc_rows[0].1 as f64 / fw_nc as f64
        );
        // THE HEADLINE: caps were the ONLY exponential (2^cap_height) depth-scaler; dropping them shrinks the
        // cw=true fused_w >5× AND leaves NO single dominator (top < 25% vs caps' 85%). What remains is a balance of
        // inner-scaling (arith tile) + constant (index-decomp SB) + LINEAR-depth carriers — so the next lever toward
        // B≤1 is CANONICALIZATION (fix w_inner/nqc/cap_height ⇒ the inner-scaling regions become constant), not
        // another narrow-tall swap (diminishing returns: every remaining region is < 20%).
        assert!(fw_nc * 5 < fw_cw, "dropping the caps must shrink cw=true fused_w >5× ({fw_cw} → {fw_nc})");
        assert!(
            nc_rows[0].1 * 4 < fw_nc,
            "post-caps: NO single dominator (top region {} < 25% of {fw_nc}) — the 2^cap_height exponential \
             bottleneck is gone (was caps 85%)",
            nc_rows[0].1
        );

        // Assertions that pin the findings so a regression is caught.
        assert_eq!(rows[0].0, "ARITH TILE (arith_stride · n_terms)", "arith tile is still the largest region post-swap");
        assert_eq!(narrow.tile_w() - narrow.qt_terms(), 2 * n_terms, "narrow arith tile = 2·n_terms");
        assert!(fw_cw > fw, "column_window mode widens fused_w by the pis window");
        assert!(w_inner > 0 && cap_h < lg);
    }

    /// **Step 4 (W4 — Tip5 for size): the lever is B-NEUTRAL — Tip5 shrinks the CONSTANT A, not the gate B**
    /// (`--features recursion`, cheap; NO prove). W4 (swap Poseidon2 → Tip5 in the Merkle/leaf hashing, ~4.6× fewer
    /// hash rows) is now an OPTIMIZATION, not a gate: Step 2/W5 already met marginal B = 0.00 < 1, so an attracting
    /// `W* = A/(1−B)` EXISTS without it. This sizes the lever + confirms it's B-safe at the fully-narrowed
    /// (arith+caps+openings+ov) cw=true geometry: the Merkle-HASH carriers (commit fold-group `4·cm_rounds` Merkle
    /// siblings + cap-ENTRY digests) are FRI-DEPTH-scaled — they do NOT depend on `w_inner`, so their marginal
    /// `d(fused_w)/d(w_inner) = 0` (measured) ⇒ Tip5 reduces the CONSTANT A, NOT the slope B ⇒ the W5 gate (B<1) is
    /// UNAFFECTED (the Tip5 gate criterion "B<1 on the hashing term" holds trivially — with marginal B = 0.00 EVERY
    /// term, including hashing, is B-neutral). Tip5's larger win is on hash ROWS (trace HEIGHT — the leaf/merge
    /// blocks), orthogonal to the width fixed point `W*`. ⇒ Tip5 is a safe, OPTIONAL size optimization; the full
    /// hash-gadget swap is deferred (multi-session, non-gate).
    #[cfg(feature = "recursion")]
    #[test]
    fn w4_tip5_lever_is_b_neutral() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use crate::recursion::monolith::tests::build_symbolic_inner_window;
        use crate::recursion::monolith::MonolithAir;
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (_tr, counts, binds, index_binds, n_terms, _pv0) =
            build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, false, false, false, false);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let cap_h = proof.commitments.trace.roots().len().trailing_zeros() as usize;
        // the fully-narrowed cw=true monolith (arith + caps + openings + ov all externalized — the converged geometry).
        let mk = |w_inner: usize, nt: usize| MonolithAir {
            counts: counts.clone(), binds: binds.clone(), index_binds: index_binds.clone(),
            n_queries: proof.opening_proof.query_proofs.len(), n_terms: nt,
            inner_counter: false, column_window: true, k_instances: 1, fold: false, fold_txstmt: false,
            constraints: constraints.clone(), w_inner_f: w_inner, n_pub_f: N_PUBLIC, n_periodic_f: N_PERIODIC, is_zk: 0,
            cap_height: cap_h, narrow_arith: true, narrow_caps: true, narrow_openings: true, narrow_ov: true };
        // the Merkle-HASH carriers Tip5 shrinks: commit fold-group (4·cm_rounds siblings) + cap-ENTRY (cap digests).
        let hash_w = |m: &MonolithAir| 4 * m.cm_rounds() + m.n_cap_c();
        let (w0, nt0, d) = (WIDTH, n_terms, 256usize);
        let (base, wide) = (mk(w0, nt0), mk(w0 + d, nt0 + 2 * d));
        let (fw, hw) = (base.fused_w(), hash_w(&base));
        // B-NEUTRALITY: the hash carriers are FRI-depth-scaled (cm_rounds/cap_height held) ⇒ identical at both inner
        // widths ⇒ marginal d(hash)/d(w_inner) = 0. (Subsumed by mb_ov = 0.00: EVERY region is B-neutral now.)
        let hash_marg = (hash_w(&wide) as f64 - hw as f64) / d as f64;
        println!(
            "W4 Tip5 lever (fully-narrowed cw=true, w_inner {w0}): Merkle-hash carriers (commit fold-group \
             4·cm_rounds + cap-ENTRY) = {hw} cols ({:.1}% of fused_w {fw}); marginal d(hash)/d(w_inner) = \
             {hash_marg:.2} = 0 ⇒ B-NEUTRAL. Tip5 shrinks the CONSTANT A (W* = A/(1−B)), NOT the slope B ⇒ the W5 \
             gate (B<1) is UNAFFECTED. Tip5's larger win is on hash ROWS (trace HEIGHT — leaf/merge blocks), \
             orthogonal to the width fixed point. ⇒ Tip5 is a safe, OPTIONAL size optimization (full swap deferred).",
            100.0 * hw as f64 / fw as f64
        );
        assert_eq!(hash_marg, 0.0, "the Merkle-hash carriers must be B-NEUTRAL (marginal d/d(w_inner) = 0) — Tip5 shrinks A, not B");
        assert!(hw > 0 && fw > 0);
    }

    /// **Arith-tile assembly increment AA2 — assemble the full arith-wrap trace.** Widen the reused monolith
    /// trace to `fused_w + 24`; for each query's arith head, seed a narrow-tall `DeepFoldAir` region from THAT
    /// head's committed openings (`α = qt_alpha`, `x = GEN·qt_acc[lg−1]`, per-term `(z, pz, px)` — the exact
    /// `deep_fold_matches_monolith_arith_tile` seed, now per query), place its `n_terms` rows in the trace SLACK
    /// (`df_sel = 1`, `df_first`/`df_end` at the ends), and fill `ro_col` at the head with the region's last-row
    /// `ro` (= the committed `QT_E`). The `ro` bus then binds each head's `ro_col` to its region's fold.
    /// Returns `(AssembledArithWrapAir, trace, pis)`.
    #[cfg(feature = "recursion")]
    fn assemble_arith_wrap(
        config: &crate::recursion::native_fri::MyConfig,
        proof: &p3_uni_stark::Proof<crate::recursion::native_fri::MyConfig>,
        pvs: &[Val],
    ) -> (AssembledArithWrapAir, RowMajorMatrix<Val>, Vec<Val>) {
        use crate::config::Challenge;
        use crate::wrap::deep_fold_trace_from;
        use p3_field::{BasedVectorSpace, Field, TwoAdicField};
        use p3_goldilocks::Goldilocks;

        let (air, mono_trace, pis) = wrap_build_reused(config, proof, pvs, true); // NARROW: inv/apow + z dropped
        let (fw, h) = (air.fused_w(), air.height());
        let (n_terms, n_q) = (air.n_terms, air.n_queries);
        let used = air.tr() + n_q * air.m_period();
        let width = fw + 25 + N_GROUPS;
        assert!(
            used + n_terms * n_q <= h,
            "DeepFold regions ({} rows) must fit the monolith slack ({})",
            n_terms * n_q,
            h - used
        );

        // Arith heads = the rows where the epilogue selector `tf` (= m_tf periodic) fires (one per query).
        let tf_col = BaseAir::<Val>::periodic_columns(&air)[air.m_tf()].clone();
        let heads: Vec<usize> = (0..h).filter(|&r| tf_col[r % tf_col.len()] == Val::ONE).collect();
        assert_eq!(heads.len(), n_q, "one arith head per query");

        let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
        let mut wide = vec![Val::ZERO; h * width];
        for r in 0..h {
            wide[r * width..r * width + fw].copy_from_slice(&mono_trace.values[r * fw..(r + 1) * fw]);
        }
        // Column bases — MUST match `AssembledArithWrapAir`'s accessors.
        let (ro_col, db) = (fw, fw + 2);
        let (df_sel, df_first, df_end, is_head) = (db + 18, db + 19, db + 20, db + 21);
        let (term_idx, is_ch0) = (db + 22, db + 23);

        for (q, &head) in heads.iter().enumerate() {
            // Seed query q's region from the head's committed columns (the per-query `deep_fold_matches` seed).
            let row = |col: usize| mono_trace.values[head * fw + col];
            let gv = |col: usize| Challenge::from_basis_coefficients_fn(|i| row(col + i));
            let alpha = gv(air.qt_alpha());
            let x = Challenge::from(<Goldilocks as Field>::GENERATOR * row(air.qt_acc() + air.lg() - 1));
            // NARROW: re-derive z (= ζ / ζ·g_trace) from the committed ζ = pis[2..4] (matching the wrap eval's
            // provide); FULL: read the stored z(k). pz/px are always the committed openings.
            let zeta = Challenge::from_basis_coefficients_fn(|i| pis[2 + i]);
            let g_trace = Challenge::from(Goldilocks::two_adic_generator(air.cm_rounds() - air.is_zk));
            let terms: Vec<(Challenge, Challenge, Challenge)> = (0..n_terms)
                .map(|k| {
                    let z = if air.narrow_arith {
                        if k >= air.trm_next_base() && k < air.trm_quot_base() {
                            zeta * g_trace
                        } else {
                            zeta
                        }
                    } else {
                        gv(air.z(k))
                    };
                    // NARROW: source px from the ov/qc carrier it's bound to; FULL: the stored px(k).
                    let px_col = if air.narrow_arith { air.px_source(k) } else { air.px(k) };
                    (z, gv(air.pz(k)), Challenge::from(row(px_col)))
                })
                .collect();
            let region = deep_fold_trace_from(alpha, x, &terms, 0);
            let dw = region.width; // 18

            // `ro_col` at the head = the region's last real term's `ro` (= the committed `QT_E`).
            let ro_last = Challenge::from_basis_coefficients_fn(|i| region.values[(n_terms - 1) * dw + 16 + i]);
            wide[head * width + ro_col..head * width + ro_col + 2].copy_from_slice(&cc(ro_last));
            wide[head * width + is_head] = Val::ONE;

            // Place the region's `n_terms` rows in the slack, with the boundary / end / sel markers.
            for k in 0..n_terms {
                let dst = used + q * n_terms + k;
                wide[dst * width + db..dst * width + db + 18].copy_from_slice(&region.values[k * dw..k * dw + 18]);
                wide[dst * width + df_sel] = Val::ONE;
                wide[dst * width + term_idx] = Val::from_u64(k as u64);
                wide[dst * width + is_ch0 + k % N_GROUPS] = Val::ONE; // route the read to the term's channel k%N_GROUPS
                if k == 0 {
                    wide[dst * width + df_first] = Val::ONE;
                }
                if k == n_terms - 1 {
                    wide[dst * width + df_end] = Val::ONE;
                }
            }
        }
        (AssembledArithWrapAir { m: air }, RowMajorMatrix::new(wide, width), pis)
    }

    /// **Arith-tile assembly increment AA2 — the assembled arith-wrap's `ro` bus balances** (native, cheap — NO
    /// prove). Assemble the trace and confirm the `ro` wiring bus balances as a signed multiset: each region's
    /// last row PROVIDES `[x, ro]` (−1) and each arith head READS `[x_head, ro_col]` (+1); addressed by the
    /// query point `x`, they cancel iff every head's `ro_col` == its region's fold `ro`. Localizes any address /
    /// placement / multiplicity bug before the heavy `prove_lookup` (as `wrap_assembled_bus_balances` did for
    /// the op-table).
    #[cfg(feature = "recursion")]
    #[test]
    fn arith_wrap_assembled_bus_balances() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_field::{Field, PrimeField64, TwoAdicField};
        use p3_goldilocks::Goldilocks;
        use p3_uni_stark::prove;
        use std::collections::HashMap;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, pis) = assemble_arith_wrap(&config, &proof, &pvs);

        let (fw, h) = (asm.m.fused_w(), asm.m.height());
        let width = fw + 25 + N_GROUPS;
        let db = fw + 2;
        let (ro_col, df_sel, df_end, is_head, term_idx) = (fw, db + 18, db + 20, db + 21, db + 22);
        let m = &asm.m;
        let ku = |v: Val| v.as_canonical_u64();

        // Key by (CHANNEL, tuple) — every channel (channel 0 = the ro bus; 1..=N_GROUPS = the input-binding
        // groups) must balance INDEPENDENTLY, so a mis-routed input read is caught, not just a value mismatch.
        let mut bus: HashMap<(usize, Vec<u64>), i128> = HashMap::new();
        for r in 0..h {
            let b = r * width;
            let g = |c: usize| trace.values[b + c];
            // Channel 0 — the ro bus. Region END provides `[x, ro]` (−1).
            if g(df_end) == Val::ONE {
                *bus.entry((0, vec![ku(g(db + 2)), ku(g(db + 3)), ku(g(db + 16)), ku(g(db + 17))])).or_default() -= 1;
            }
            if g(is_head) == Val::ONE {
                let x_head = <Goldilocks as Field>::GENERATOR * g(m.qt_acc() + m.lg() - 1);
                // Head READ `[x_head, ro_col]` (+1) on channel 0.
                *bus.entry((0, vec![ku(x_head), 0, ku(g(ro_col)), ku(g(ro_col + 1))])).or_default() += 1;
                // Head PROVIDES each committed term k (−1) on channel k%N_GROUPS+1: addr (x_head, k), value (z,pz,px).
                // NARROW: z re-derived (= ζ / ζ·g_trace from pis[2..4], matching the AIR + the region seed);
                // FULL: g(m.z(k)).
                let g_trace = Goldilocks::two_adic_generator(m.cm_rounds() - m.is_zk);
                for k in 0..m.n_terms {
                    let (z0, z1) = if m.narrow_arith {
                        if k >= m.trm_next_base() && k < m.trm_quot_base() {
                            (pis[2] * g_trace, pis[3] * g_trace)
                        } else {
                            (pis[2], pis[3])
                        }
                    } else {
                        (g(m.z(k)), g(m.z(k) + 1))
                    };
                    let px_col = if m.narrow_arith { m.px_source(k) } else { m.px(k) };
                    let tuple = vec![
                        ku(x_head), 0, k as u64,
                        ku(z0), ku(z1), ku(g(m.pz(k))), ku(g(m.pz(k) + 1)), ku(g(px_col)),
                    ];
                    *bus.entry((k % N_GROUPS + 1, tuple)).or_default() -= 1;
                }
            }
            // The region row READS its bundle (+1) on its one-hot is_ch channel: addr (x, term_idx), value (z,pz,px).
            if g(df_sel) == Val::ONE {
                let gch = (0..N_GROUPS).find(|&gc| g(db + 23 + gc) == Val::ONE).expect("a region row routes to one channel");
                let tuple = vec![
                    ku(g(db + 2)), ku(g(db + 3)), ku(g(term_idx)),
                    ku(g(db + 6)), ku(g(db + 7)), ku(g(db + 8)), ku(g(db + 9)), ku(g(db + 10)),
                ];
                *bus.entry((gch + 1, tuple)).or_default() += 1;
            }
        }
        let bad: Vec<_> = bus.iter().filter(|(_, &mm)| mm != 0).take(8).collect();
        assert!(
            bad.is_empty(),
            "every bus channel must balance; {} nonzero net entries, e.g. {bad:?}",
            bus.values().filter(|&&mm| mm != 0).count()
        );
        println!(
            "assembled arith-wrap bus (ro channel + {} input channels): {} distinct (channel, tuple) entries, all \
             net-zero — ro AND the (z, pz, px) inputs are bound to the committed columns, per channel",
            N_GROUPS,
            bus.len()
        );
    }

    /// **Arith-tile assembly increment AA4 — the assembled arith-wrap PROVES through `prove_lookup`.** The
    /// definitive soundness check (the `wrap_assembled_proves` analog for the arith tile): build the full trace
    /// (reused monolith regions + the narrow-tall `DeepFoldAir` slack region + the `ro` bus + the AA3 input
    /// binding) and prove + verify it end-to-end through the W1 lookup prover (outer is_zk=1). Confirms the
    /// sound-`ro` externalization holds under a REAL prove — the monolith A–J constraints, the narrow-tall fold,
    /// the `ro` bus binding `ro_col` to the region's fold, and the input bus binding `(z, pz, px)` to the
    /// committed columns all hold together as a SOUND STARK — at width `fused_w + 25 + N_GROUPS` (O(1)), the
    /// `9·n_terms` reduced-opening fold no longer inline. A corrupted region input is rejected. Heavy (2^16 →
    /// 2^17 hiding commit, ~2 proves); `--release --ignored`.
    #[cfg(feature = "recursion")]
    #[test]
    #[ignore = "heavy: proves the assembled arith-wrap (2^16 rows) through prove_lookup; run `--release --features lookup,recursion -- --ignored`"]
    fn arith_wrap_assembled_proves() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::lookup::prover::{prove_lookup, verify_lookup};
        use crate::recursion::native_fri::make_config;
        use p3_uni_stark::prove;

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (asm, trace, pis) = assemble_arith_wrap(&config, &proof, &pvs);
        let width = <AssembledArithWrapAir as BaseAir<Val>>::width(&asm);
        println!(
            "proving assembled arith-wrap (DeepFold region + ro bus + input binding): width {width}, {} rows",
            asm.m.height()
        );
        let lproof = prove_lookup(&asm, trace, &pis);
        assert!(
            verify_lookup(&asm, &lproof, &pis).is_ok(),
            "the assembled arith-wrap must prove + verify through prove_lookup"
        );

        // Corrupt a region input (the DeepFold `z` leaf on the first slack region row) ⇒ the input bus unbalances
        // (region z ≠ committed z) AND the region `inv·(z−x) = 1` fails ⇒ the corrupted trace must not verify.
        let (asm2, mut bad, pis2) = assemble_arith_wrap(&config, &proof, &pvs);
        let used = asm2.m.tr() + asm2.m.n_queries * asm2.m.m_period();
        let db = asm2.m.fused_w() + 2;
        bad.values[used * width + db + 6] += Val::ONE; // region z.0 at the first region row (q = 0, term 0)
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let p = prove_lookup(&asm2, bad, &pis2);
            verify_lookup(&asm2, &p, &pis2).is_err()
        }))
        .unwrap_or(true);
        std::panic::set_hook(hook);
        assert!(rejected, "a corrupted region input (z ≠ committed) must not produce a valid assembled arith-wrap proof");
    }

    /// **W2-measure (prove) — the assembled wrap is SOUND.** Build the reused-region trace (brick 1), fill the
    /// witnessed `c_k` columns (native mirror of the `Witnesser`) at each arith head, and PROVE + VERIFY the
    /// full `WrapAir` over a real join-split inner + reject a tampered inner pub. Confirms the witnessed
    /// epilogue (the assembled wrap, not just the symbolic degree) is correct. Heavy; `--release --ignored`.
    #[cfg(feature = "recursion")]
    #[test]
    #[ignore = "heavy: proves the assembled WrapAir (2^16 rows); run `--release --features lookup,recursion -- --ignored`"]
    fn wrap_air_proves() {
        use crate::config::Challenge;
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::{epilogue_openings, make_config};
        use p3_field::BasedVectorSpace;
        use p3_matrix::dense::RowMajorMatrix;
        use p3_uni_stark::{prove, verify};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (air, mono_trace, pis) = wrap_build_reused(&config, &proof, &pvs, false);
        // The native OOD openings the witnessed columns must equal (the same ζ-openings the epilogue reads).
        let (eo_local, eo_next, is_first, is_last, is_trans, _iv, _q, _a, _z, eo_periodic) =
            epilogue_openings(&config, &JoinSplitAir, &proof, &pvs);
        let eo_pubs: Vec<Challenge> = pvs.iter().map(|&p| Challenge::from(p)).collect();

        let (fw, h, n_q, tr, mp) = (air.fused_w(), air.height(), air.n_queries, air.tr(), air.m_period());
        let wrap = WrapAir::new(air);
        let width = fw + 2 * wrap.n_mul;
        let products = native_witnessed(
            &wrap.m.constraints, &eo_local, &eo_next, &eo_pubs, &eo_periodic, is_first, is_last, is_trans,
        );
        assert_eq!(products.len(), wrap.n_mul, "native witnessed products == n_mul columns");

        // Widen the monolith trace to the wrap width; fill the witnessed c_k columns at each arith head (M_TF).
        let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
        let mut wide = vec![Val::ZERO; h * width];
        for r in 0..h {
            wide[r * width..r * width + fw].copy_from_slice(&mono_trace.values[r * fw..(r + 1) * fw]);
        }
        for q in 0..n_q {
            let head = tr + q * mp;
            for (i, p) in products.iter().enumerate() {
                let c = cc(*p);
                wide[head * width + fw + 2 * i] = c[0];
                wide[head * width + fw + 2 * i + 1] = c[1];
            }
        }
        let wide_trace = RowMajorMatrix::new(wide, width);

        let prf = prove(&config, &wrap, wide_trace, &pis);
        assert!(verify(&config, &wrap, &prf, &pis).is_ok(), "the assembled wrap must verify over a real inner");
        let mut bad = pis.clone();
        bad[wrap.m.pub_pi()] += Val::ONE;
        assert!(verify(&config, &wrap, &prf, &bad).is_err(), "a tampered inner pub must be rejected");
    }

    /// **Arith-tile assembly brick 1 (plumbing) — `ArithWrapAir` PROVES with the reduced-opening fold
    /// EXTERNALIZED.** The monolith with `DeepFoldBci`: the `9·n_terms`-column inline fold replaced by a
    /// witnessed `ro` column bound to `QT_E` (the point stays inline + sound via `arith_point`). Filling `ro`
    /// with the correct reduced opening — the trace's own `QT_E`, which `deep_fold_matches_monolith_arith_tile`
    /// independently proves the narrow-tall `DeepFoldAir` reproduces — the wrap proves + verifies over a real
    /// join-split inner, and corrupting `ro` at an arith head is rejected. So the `emit_arith` override binds
    /// correctly end-to-end. (`ro`'s IN-CIRCUIT soundness — that it IS the fold of the committed openings — is
    /// the next brick: the narrow-tall `DeepFoldAir` region in slack + the opening seam. Width = fused_w + 2;
    /// the `9·n_terms` column removal — the actual width win — follows.) Heavy; `--release --ignored`.
    #[cfg(feature = "recursion")]
    #[test]
    #[ignore = "heavy: proves ArithWrapAir (2^16 rows); run `--release --features lookup,recursion -- --ignored`"]
    fn arith_wrap_witnessed_ro_proves() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::make_config;
        use p3_matrix::dense::RowMajorMatrix;
        use p3_uni_stark::{prove, verify};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (air, mono_trace, pis) = wrap_build_reused(&config, &proof, &pvs, false);

        let (fw, h, n_q, tr, mp) = (air.fused_w(), air.height(), air.n_queries, air.tr(), air.m_period());
        let width = fw + 2;
        let wrap = ArithWrapAir { m: air };

        // Widen the monolith trace by the `ro` column; fill `ro` (= the correct reduced opening, which the trace
        // already carries at QT_E = column 0) at each arith head (M_TF fires at tr + q·m_period).
        let mut wide = vec![Val::ZERO; h * width];
        for r in 0..h {
            wide[r * width..r * width + fw].copy_from_slice(&mono_trace.values[r * fw..(r + 1) * fw]);
        }
        for q in 0..n_q {
            let head = tr + q * mp;
            wide[head * width + fw] = mono_trace.values[head * fw]; // ro.0 = QT_E.0
            wide[head * width + fw + 1] = mono_trace.values[head * fw + 1]; // ro.1 = QT_E.1
        }
        let wide_trace = RowMajorMatrix::new(wide, width);

        let prf = prove(&config, &wrap, wide_trace.clone(), &pis);
        assert!(verify(&config, &wrap, &prf, &pis).is_ok(), "ArithWrapAir must verify with the fold externalized");

        // Corrupt `ro` at the first arith head ⇒ QT_E ≠ ro ⇒ reject (prove can't close the quotient, or verify).
        let mut bad = wide_trace;
        bad.values[tr * width + fw] += Val::ONE;
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let p = prove(&config, &wrap, bad, &pis);
            verify(&config, &wrap, &p, &pis).is_err()
        }))
        .unwrap_or(true);
        std::panic::set_hook(hook);
        assert!(rejected, "a corrupted `ro` (QT_E ≠ ro) must not produce a valid ArithWrapAir proof");
    }

    /// **The wrap FIXES the self-recursion explosion (R5) — the degree WIN, demonstrated.** Build the OUTER
    /// monolith verifying an INNER ConstAir monolith (the self-recursion case that motivates the wrap): the
    /// inline `MonolithAir` EXPLODES past the budget (`log_nqc > 4` — the inner's high-degree constraints
    /// folded inline), but the assembled `WrapAir` (witnessed epilogue) stays `≤ 4`. This is the payoff the
    /// whole wrap was built for, on a real high-degree inner (vs the join-split, maxdeg 8, where both are ≤4).
    /// Heavy (proves the inner monolith); `--release --features lookup,recursion -- --ignored`.
    #[cfg(feature = "recursion")]
    #[test]
    #[ignore = "heavy: proves an inner ConstAir monolith to demonstrate the wrap fixes self-recursion; --release --ignored"]
    fn wrap_fixes_self_recursion() {
        use crate::config::Challenge;
        use crate::recursion::monolith::tests::{build_symbolic_inner_window, sim_full};
        use crate::recursion::monolith::{monolith_build_trace, MonolithAir};
        use crate::recursion::native_fri::{
            gen_const_proof, make_config, query_commit_merkle_all, query_fold_data, query_input_merkle,
            query_quotient_merkle, query_terms,
        };
        use p3_air::BaseAir;
        use p3_field::{BasedVectorSpace, PrimeField64};
        use p3_uni_stark::{get_log_num_quotient_chunks, get_symbolic_constraints, prove, verify, AirLayout};

        // (1) INNER: a small ConstAir monolith, proven — the "inner proof" the OUTER must verify.
        let config = make_config(1, 4);
        let (proof, pvs) = gen_const_proof(&config, 42, 6);
        let (block_inputs, counts, binds, chs, index_binds, index_felts) = sim_full(&config, &proof, &pvs);
        let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
        let (mut per_query, mut quot_paths, mut commit_data, mut n_terms) =
            (Vec::new(), Vec::new(), Vec::new(), 0usize);
        let (mut final0, mut cap0, mut qcap0) = (Challenge::ZERO, [Val::ZERO; 4], [Val::ZERO; 4]);
        let mut ccap0 = vec![[Val::ZERO; 4]; proof.opening_proof.commit_phase_commits.len()];
        for q in 0..4 {
            let (terms, _x, alpha, ro) = query_terms(&config, &proof, &pvs, q);
            let (_r, rounds, _f, f0) = query_fold_data(&config, &proof, &pvs, q);
            let v = proof.opening_proof.query_proofs[q].input_proof[0].opened_values[0][0];
            let (_l, path, ce) = query_input_merkle(&config, &proof, &pvs, q);
            let (_ql, qpath, qce, _qw) = query_quotient_merkle(&config, &proof, &pvs, q);
            let cm = query_commit_merkle_all(&config, &proof, &pvs, q);
            if q == 0 {
                final0 = f0;
                cap0 = ce;
                qcap0 = qce;
                for (r, (_g, _l, _p, c)) in cm.iter().enumerate() {
                    ccap0[r] = *c;
                }
            }
            n_terms = terms.len();
            let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
            per_query.push(((index, terms, alpha, ro, rounds), v, path));
            quot_paths.push(qpath);
            commit_data.push(cm);
        }
        let inner = MonolithAir {
            counts: counts.clone(), binds, index_binds, n_queries: 4, n_terms, inner_counter: false,
            column_window: false, k_instances: 1, fold: false, fold_txstmt: false, constraints: vec![],
            w_inner_f: 1, n_pub_f: 1, n_periodic_f: 0, is_zk: 0, cap_height: 6, narrow_arith: false, narrow_caps: false, narrow_openings: false, narrow_ov: false };
        let mut pis = Vec::new();
        for ch in &chs {
            pis.push(ch[0]);
            pis.push(ch[1]);
        }
        for f in &index_felts {
            pis.push(*f);
        }
        let fp: [Val; 2] = final0.as_basis_coefficients_slice().try_into().unwrap();
        pis.push(fp[0]);
        pis.push(fp[1]);
        pis.extend_from_slice(&cap0);
        pis.extend_from_slice(&qcap0);
        pis.push(pvs[0]);
        for ce in &ccap0 {
            pis.extend_from_slice(ce);
        }
        let inner_trace = monolith_build_trace(
            &inner, &block_inputs, &per_query, chs[2], &index_felts, &quot_paths, &commit_data, &[], None,
        );
        let inner_prf = prove(&config, &inner, inner_trace, &pis);
        assert!(verify(&config, &inner, &inner_prf, &pis).is_ok(), "inner ConstAir monolith proves");
        let (w_in, np_in, nper_in) = (inner.fused_w(), pis.len(), BaseAir::<Val>::num_periodic_columns(&inner));
        let inner_cs = get_symbolic_constraints::<Val, MonolithAir>(&inner, AirLayout::from_air::<Val>(&inner));

        // (2) OUTER: the monolith verifying the INNER monolith. build_symbolic_inner_window builds + self-
        // validates the outer witness (self-recursion). Measure the outer as MonolithAir (inline) AND WrapAir.
        let (_otr, ocounts, obinds, oib, ont, _pv0) =
            build_symbolic_inner_window(&config, &inner, &inner_prf, &pis, w_in, np_in, nper_in, false, false, false, false);
        let cap_h = inner_prf.commitments.trace.roots().len().trailing_zeros() as usize;
        let outer = MonolithAir {
            counts: ocounts.clone(), binds: obinds.clone(), index_binds: oib.clone(), n_queries: 4, n_terms: ont,
            inner_counter: false, column_window: true, k_instances: 1, fold: false, fold_txstmt: false,
            constraints: inner_cs.clone(), w_inner_f: w_in, n_pub_f: np_in, n_periodic_f: nper_in, is_zk: 0,
            cap_height: cap_h, narrow_arith: false, narrow_caps: false, narrow_openings: false, narrow_ov: false };
        let olayout = AirLayout::from_air::<Val>(&outer);
        let inline_nqc = get_log_num_quotient_chunks::<Val, MonolithAir>(&outer, olayout, 0);
        let (inner_w, outer_w) = (inner.fused_w(), outer.fused_w());
        let (o_inst_h, o_used) = (outer.inst_h(), outer.tr() + outer.n_queries * outer.m_period());
        let wrap = WrapAir::new(outer);
        let wlayout = AirLayout::from_air::<Val>(&wrap);
        let wrap_nqc = get_log_num_quotient_chunks::<Val, WrapAir>(&wrap, wlayout, 0);
        println!(
            "R5 self-recursion (monolith-verifies-monolith, {} inner constraints): INLINE MonolithAir log_nqc = \
             {inline_nqc} (> {LOG_BLOWUP} = EXPLODES); WITNESSED WrapAir log_nqc = {wrap_nqc} (≤ {LOG_BLOWUP} = FIXED)",
            inner_cs.len()
        );
        // SIZE baseline (the W3–W5 target): the witnessed epilogue FIXES degree but ADDS width (2·n_mul c_k
        // columns) — the size cost the SIZE program removes (W3 narrow-tall C / canonicalize, W4 Tip5, W5 the
        // fixed point W_out ≤ W_in). Reported alongside the degree fix to ground the size program.
        let wrap_w = <WrapAir as BaseAir<Val>>::width(&wrap);
        println!(
            "R5 SIZE baseline: inner monolith W={inner_w}, outer inline W={outer_w}, outer WRAP W={wrap_w} \
             (+{} witnessed c_k cols for {} Muls). The witnessed degree fix TRADES for width ⇒ the SIZE \
             program (narrow-tall C / canonicalize / Tip5) must contract it to a fixed point.",
            wrap_w - outer_w,
            wrap.n_mul
        );
        // W3 op-table projection (MEASURED, not just targeted — bricks 1–4 built the op-table): build the
        // FLATTEN op-table for THIS R5 inner's constraint DAG and measure its geometry. The op-table lays the
        // c_k evaluation + the α-fold as ROWS at a CONSTANT width (13) that OVERLAY the outer's wide fused_w
        // columns on slack rows, so the 2·n_mul witnessed COLUMNS become slack ROWS and the wrap width
        // contracts to ≈ fused_w (the inline monolith) — only the folded value is an O(1) net-new binding at
        // the arith head. Height grows to fit the op rows (a proving-time cost, not a width cost).
        let (optab, _r, _f, _lb, _quot) =
            crate::wrap::op_table_f2_trace(&inner_cs, |_| Challenge::ONE, Some(Challenge::ONE), &[], None);
        let op_rows = optab.values.len() / 13;
        let slack = o_inst_h.saturating_sub(o_used);
        let fits = op_rows <= slack;
        let op_height = if fits { o_inst_h } else { (o_used + op_rows).next_power_of_two() };
        println!(
            "W3 op-table PROJECTION (R5 inner, {} constraints): FLATTEN op-table = {op_rows} ROWS × 13 cols \
             (overlaid on fused_w={outer_w}); outer slack = {slack} rows (used {o_used}/{o_inst_h}), \
             fits_in_slack={fits} ⇒ op height {op_height}. ⇒ projected WRAP width = fused_w + O(1) ≈ {outer_w} \
             (vs witnessed {wrap_w} = fused_w + 2·n_mul) — the {}-col c_k overhead becomes {op_rows} slack ROWS. \
             WIDTH CONTRACTS to ≈ the inline monolith; the residual is the brick-5 integration (bus composition \
             through the W1 lookup prover + region gating), NOT a width question.",
            inner_cs.len(),
            wrap_w - outer_w,
        );
        assert!(op_rows > 0 && 13 <= outer_w, "the op-table has rows and its width overlays fused_w (ample room)");

        // W3 op-table INTEGRATION — the ASSEMBLED wrap AIR at R5 scale (the brick-5 GATE, now PROVEN on
        // join-split). Build `AssembledWrapAir` over THIS R5 outer and measure: width `fused_w + 17` (O(1)) and
        // it composes within the degree budget. The join-split `AssembledWrapAir` PROVES through `prove_lookup`
        // at `fused_w + 17` (`wrap_assembled_proves`), so this is the SAME proven mechanism at R5 scale — the
        // `2·n_mul` c_k COLUMNS are gone, replaced by op-table slack ROWS.
        use crate::lookup::prover::combined_constraint_layout;
        use p3_lookup::Lookups;
        let asm = AssembledWrapAir {
            m: MonolithAir {
                counts: ocounts, binds: obinds, index_binds: oib, n_queries: 4, n_terms: ont, inner_counter: false,
                column_window: true, k_instances: 1, fold: false, fold_txstmt: false, constraints: inner_cs.clone(),
                w_inner_f: w_in, n_pub_f: np_in, n_periodic_f: nper_in, is_zk: 0, cap_height: cap_h, narrow_arith: false, narrow_caps: false, narrow_openings: false, narrow_ov: false },
            folded_addr: 0,
        };
        let asm_width = <AssembledWrapAir as BaseAir<Val>>::width(&asm);
        let asm_lookups = Lookups::from_air::<Challenge, _>(&asm);
        let (_al, asm_nqc) = combined_constraint_layout(&asm, &asm_lookups, 1);
        println!(
            "R5 ASSEMBLED (the op-table wrap, PROVEN on join-split): width {asm_width} = fused_w {outer_w} + {} \
             (op-table + folded + binding + is_ch routing), composes log_nqc {asm_nqc} ≤ {LOG_BLOWUP}. ⇒ the \
             WITNESSED WrapAir {wrap_w} CONTRACTS to the ASSEMBLED {asm_width} — back to ≈ the inline monolith \
             {outer_w}; the 2·n_mul c_k columns become {op_rows} slack ROWS. W3 SIZE FIX: PROVEN + MEASURED.",
            19 + N_GROUPS
        );
        assert_eq!(asm_width, outer_w + 19 + N_GROUPS, "the assembled wrap is fused_w + O(1), not fused_w + 2·n_mul");
        // The 2c binding's provides are split across N_GROUPS+1 lookup channels, so the assembled R5 wrap
        // composes within the degree budget (the naive single-lookup form was over budget).
        assert!(asm_nqc <= LOG_BLOWUP, "the assembled R5 wrap (split binding) must compose within the degree budget");
        assert!(inline_nqc > LOG_BLOWUP, "the inline monolith must EXPLODE on a monolith-as-inner (the R5 bug)");
        assert!(wrap_nqc <= LOG_BLOWUP, "the wrap must FIX it — witnessed epilogue stays within budget");
    }

    /// **Self-composition B at the NARROWED geometry** (`--release --ignored`, heavy — proves an inner monolith).
    /// Quantifies how far the deep-tree fixed point B≤1 is AFTER the arith-tile + caps + OPENINGS narrow-tall swaps.
    /// Builds the R5 self-recursion outer (a monolith verifying a W≈193 inner ConstAir monolith) and reads its
    /// `fused_w` at THREE geometry points — FULL, `narrow_arith`+`narrow_caps`, and +`narrow_openings` — plus the
    /// MARGINAL B = `d(fused_w)/d(w_inner)` (the asymptotic fixed-point ratio: the constant base cost amortizes as
    /// the inner grows, so the SLOPE decides convergence). `fused_w` is a pure width function ⇒ the variants need no
    /// re-prove. FINDING: absolute B 44×→8.7×→(openings) further; marginal **19 → 5 → ~1.00**. The openings
    /// externalization drops the arith-tile slope (`2·n_terms`) to 0, leaving ONLY the +1 `ov` opened-row/trace-leaf
    /// carrier (`input_leaf_felts = w_inner`) — so marginal B lands on the fixed-point BOUNDARY ≈ 1.00.
    /// CANONICALIZATION (freeze `w_inner`/`nqc`/`cap_height` ⇒ the inner-scaling regions become CONSTANT ⇒ slope → 0)
    /// — or externalizing the `ov` carrier narrow-tall — is the remaining lever to push B strictly < 1.
    #[cfg(feature = "recursion")]
    #[test]
    #[ignore = "heavy (proves an inner monolith): measures the self-composition B at the narrowed geometry (marginal 19→5→~1.00 across FULL/arith+caps/+openings); run `--release --features recursion -j1 -- --ignored`"]
    fn self_composition_b_narrowed() {
        use crate::config::Challenge;
        use crate::recursion::monolith::tests::{build_symbolic_inner_window, sim_full};
        use crate::recursion::monolith::{monolith_build_trace, MonolithAir};
        use crate::recursion::native_fri::{
            gen_const_proof, make_config, query_commit_merkle_all, query_fold_data, query_input_merkle,
            query_quotient_merkle, query_terms,
        };
        use p3_air::BaseAir;
        use p3_field::{BasedVectorSpace, PrimeField64};
        use p3_uni_stark::{get_symbolic_constraints, prove, verify, AirLayout};

        // INNER: a small ConstAir monolith, proven — the "inner proof" the OUTER must verify (the R5 setup, the
        // canonical monolith-verifies-monolith self-recursion). Identical to `wrap_fixes_self_recursion`'s inner.
        let config = make_config(1, 4);
        let (proof, pvs) = gen_const_proof(&config, 42, 6);
        let (block_inputs, counts, binds, chs, index_binds, index_felts) = sim_full(&config, &proof, &pvs);
        let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
        let (mut per_query, mut quot_paths, mut commit_data, mut n_terms) =
            (Vec::new(), Vec::new(), Vec::new(), 0usize);
        let (mut final0, mut cap0, mut qcap0) = (Challenge::ZERO, [Val::ZERO; 4], [Val::ZERO; 4]);
        let mut ccap0 = vec![[Val::ZERO; 4]; proof.opening_proof.commit_phase_commits.len()];
        for q in 0..4 {
            let (terms, _x, alpha, ro) = query_terms(&config, &proof, &pvs, q);
            let (_r, rounds, _f, f0) = query_fold_data(&config, &proof, &pvs, q);
            let v = proof.opening_proof.query_proofs[q].input_proof[0].opened_values[0][0];
            let (_l, path, ce) = query_input_merkle(&config, &proof, &pvs, q);
            let (_ql, qpath, qce, _qw) = query_quotient_merkle(&config, &proof, &pvs, q);
            let cm = query_commit_merkle_all(&config, &proof, &pvs, q);
            if q == 0 {
                final0 = f0;
                cap0 = ce;
                qcap0 = qce;
                for (r, (_g, _l, _p, c)) in cm.iter().enumerate() {
                    ccap0[r] = *c;
                }
            }
            n_terms = terms.len();
            let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
            per_query.push(((index, terms, alpha, ro, rounds), v, path));
            quot_paths.push(qpath);
            commit_data.push(cm);
        }
        let inner = MonolithAir {
            counts: counts.clone(), binds, index_binds, n_queries: 4, n_terms, inner_counter: false,
            column_window: false, k_instances: 1, fold: false, fold_txstmt: false, constraints: vec![],
            w_inner_f: 1, n_pub_f: 1, n_periodic_f: 0, is_zk: 0, cap_height: 6, narrow_arith: false, narrow_caps: false, narrow_openings: false, narrow_ov: false };
        let mut pis = Vec::new();
        for ch in &chs {
            pis.push(ch[0]);
            pis.push(ch[1]);
        }
        for f in &index_felts {
            pis.push(*f);
        }
        let fp: [Val; 2] = final0.as_basis_coefficients_slice().try_into().unwrap();
        pis.push(fp[0]);
        pis.push(fp[1]);
        pis.extend_from_slice(&cap0);
        pis.extend_from_slice(&qcap0);
        pis.push(pvs[0]);
        for ce in &ccap0 {
            pis.extend_from_slice(ce);
        }
        let inner_trace = monolith_build_trace(
            &inner, &block_inputs, &per_query, chs[2], &index_felts, &quot_paths, &commit_data, &[], None,
        );
        let inner_prf = prove(&config, &inner, inner_trace, &pis);
        assert!(verify(&config, &inner, &inner_prf, &pis).is_ok(), "inner ConstAir monolith proves");
        let (w_in, np_in, nper_in) = (inner.fused_w(), pis.len(), BaseAir::<Val>::num_periodic_columns(&inner));
        let inner_cs = get_symbolic_constraints::<Val, MonolithAir>(&inner, AirLayout::from_air::<Val>(&inner));

        // OUTER: the monolith verifying the inner (self-recursion). build_symbolic_inner_window builds + self-
        // validates the outer's witness; we only need its structural params (counts/binds/n_terms) for fused_w.
        let (_otr, ocounts, obinds, oib, ont, _pv0) =
            build_symbolic_inner_window(&config, &inner, &inner_prf, &pis, w_in, np_in, nper_in, false, false, false, false);
        let cap_h = inner_prf.commitments.trace.roots().len().trailing_zeros() as usize;

        // fused_w is a pure width function of the struct ⇒ read the outer width at FULL vs NARROWED geometry, and
        // the MARGINAL slope, with NO re-prove. Scale the w_inner-coupled inputs (w_inner + n_terms ≈ 2·w_inner) by
        // Δ; the FRI structure (nqc/cap_height/n_binds) is held (it scales only ~log with the inner size).
        let inner_w = w_in;
        // `narrow` toggles arith(9→2)+caps; `nopen` ADDS the openings externalization (arith_stride→0). The three
        // geometry points are FULL / arith+caps / +openings. (narrow_openings REQUIRES narrow_arith, so OR it in.)
        // `narrow` toggles arith(9→2)+caps; `nopen` ADDS the openings externalization (arith_stride→0); `nov` ADDS
        // the ov opened-row carrier externalization (brick 4b — the REAL 4th narrow flag, no longer a projection).
        let mk_outer = |w_inner: usize, nt: usize, narrow: bool, nopen: bool, nov: bool| MonolithAir {
            counts: ocounts.clone(), binds: obinds.clone(), index_binds: oib.clone(), n_queries: 4, n_terms: nt,
            inner_counter: false, column_window: true, k_instances: 1, fold: false, fold_txstmt: false,
            constraints: inner_cs.clone(), w_inner_f: w_inner, n_pub_f: np_in, n_periodic_f: nper_in, is_zk: 0,
            cap_height: cap_h, narrow_arith: narrow || nopen, narrow_caps: narrow, narrow_openings: nopen, narrow_ov: nov };
        let outer_w = mk_outer(w_in, ont, false, false, false).fused_w();
        let outer_narrow_w = mk_outer(w_in, ont, true, false, false).fused_w(); // arith 9→2 + caps
        let outer_open_w = mk_outer(w_in, ont, true, true, false).fused_w(); // + openings externalized (arith_stride→0)
        let outer_ov_w = mk_outer(w_in, ont, true, true, true).fused_w(); // + ov carrier externalized (brick 4b, REAL)
        let d = 256usize;
        let marg = |narrow: bool, nopen: bool, nov: bool| {
            (mk_outer(w_in + d, ont + 2 * d, narrow, nopen, nov).fused_w()
                - mk_outer(w_in, ont, narrow, nopen, nov).fused_w()) as f64
                / d as f64
        };
        let (mb_full, mb_narrow, mb_open) = (marg(false, false, false), marg(true, false, false), marg(true, true, false));
        println!(
            "SELF-COMPOSITION B (R5, inner monolith W={inner_w}): outer fused_w FULL {outer_w} (B {:.1}×) → NARROWED \
             (arith 9→2 + caps) {outer_narrow_w} (B {:.1}×) → +OPENINGS externalized {outer_open_w} (B {:.1}×) → +OV \
             externalized {outer_ov_w} (B {:.1}×). MARGINAL B = d(fused_w)/d(w_inner): FULL {mb_full:.2} → arith+caps \
             {mb_narrow:.2} → +openings {mb_open:.2} cols/col. The openings externalization drops the arith-tile slope \
             (2·n_terms) to 0, leaving ONLY the +1 `ov` opened-row/trace-leaf carrier (input_leaf_felts = w_inner) ⇒ \
             marginal B → ~1.00, the fixed-point BOUNDARY. Externalizing the `ov` carrier narrow-tall (brick 4b) \
             removes that last +1 slope — measured next.",
            outer_w as f64 / inner_w as f64,
            outer_narrow_w as f64 / inner_w as f64,
            outer_open_w as f64 / inner_w as f64,
            outer_ov_w as f64 / inner_w as f64,
        );
        assert!(outer_narrow_w < outer_w, "the arith+caps narrowing must shrink the R5 outer width ({outer_w} → {outer_narrow_w})");
        assert!(outer_open_w < outer_narrow_w, "externalizing the openings must shrink the outer further ({outer_narrow_w} → {outer_open_w}, drops 2·n_terms pz)");
        assert!(outer_ov_w < outer_open_w, "externalizing the ov carrier must shrink the outer further ({outer_open_w} → {outer_ov_w}, drops w_inner)");
        assert!(mb_narrow < mb_full, "arith+caps narrowing must reduce the marginal (asymptotic) B ({mb_full:.2} → {mb_narrow:.2})");
        assert!(mb_narrow > 1.0, "arith+caps ALONE leaves marginal B > 1 ({mb_narrow:.2}) — the openings externalization is the further lever");
        assert!(mb_open < mb_narrow, "the openings externalization must reduce the marginal B further ({mb_narrow:.2} → {mb_open:.2})");
        assert!(mb_open <= 1.5, "with openings externalized the marginal B drops to ~1.00 (only the `ov` trace-leaf carrier remains); externalizing it drives it < 1 (got {mb_open:.2})");

        // W5 GATE — the REAL +ov measurement (brick 4b made narrow_ov an actual geometry, not a projection). The `ov`
        // opened-row carrier (`input_leaf_felts` = w_inner) was the ONLY region still scaling with the inner width;
        // dropping it narrow-tall (columns → rows on the leaf-hash→px bus) removes its +1 slope. Measure the marginal
        // B of the REAL narrow_ov outer AND cross-check it equals the prior projection (`fused_w − input_leaf_felts`)
        // — validating brick 4b's byte-level narrowing at the R5 self-composition scale.
        let mb_ov = marg(true, true, true);
        // cross-check: the REAL narrow_ov fused_w == the projected (openings fused_w − the ov carrier) at both points.
        let proj_ov = |w_inner: usize, nt: usize| {
            let m = mk_outer(w_inner, nt, true, true, false);
            m.fused_w() - m.input_leaf_felts()
        };
        assert_eq!(outer_ov_w, proj_ov(w_in, ont), "the REAL narrow_ov fused_w must equal the openings width minus the ov carrier (brick 4b at R5)");
        assert_eq!(mk_outer(w_in + d, ont + 2 * d, true, true, true).fused_w(), proj_ov(w_in + d, ont + 2 * d), "…and at the +Δ point (the slope agrees)");
        println!(
            "W5 GATE [MEASURED, REAL narrow_ov]: marginal B = d(fused_w)/d(w_inner) = {mb_ov:.2} cols/col < 1 ⇒ a \
             STRICT CONTRACTION ⇒ the self-composition W_out = A + B·W_in CONVERGES to an attracting fixed point W* \
             (no explosion). The `ov` carrier was the LAST inner-scaling region; brick 4b externalized it (byte-level \
             matches-native), so the R5 outer width now grows SUB-linearly in the inner width. The heavy end-to-end \
             prove of the canonical wrap OOMs this 62 GB box, but the SIZE gate — the make-or-break W5 number — is met \
             by measurement: marginal B {mb_full:.2} (FULL) → {mb_narrow:.2} (arith+caps) → {mb_open:.2} (+openings) → \
             {mb_ov:.2} (+ov) < 1.",
        );
        assert!(mb_ov < 1.0, "W5 GATE: the REAL narrow_ov marginal B must be strictly < 1 (got {mb_ov:.2}) ⇒ an attracting fixed point exists");
        assert!(mb_ov < mb_open, "the ov externalization must reduce the marginal further ({mb_open:.2} → {mb_ov:.2})");
    }
}
