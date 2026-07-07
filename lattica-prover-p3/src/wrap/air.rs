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
    use crate::recursion::monolith::{InlineBci, MonolithAir, MonolithBci};
    use p3_air::{Air, AirBuilder, BaseAir};
    use p3_field::PrimeCharacteristicRing;
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
}

#[cfg(feature = "recursion")]
pub(crate) use wrap_air::{native_witnessed, WrapAir};

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
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
        };
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
        let (air, trace, pis) = wrap_build_reused(&config, &proof, &pvs);
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
            cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize,
        };
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
        let (air, mono_trace, pis) = wrap_build_reused(&config, &proof, &pvs);
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
            w_inner_f: 1, n_pub_f: 1, n_periodic_f: 0, is_zk: 0, cap_height: 6,
        };
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
            build_symbolic_inner_window(&config, &inner, &inner_prf, &pis, w_in, np_in, nper_in);
        let cap_h = inner_prf.commitments.trace.roots().len().trailing_zeros() as usize;
        let outer = MonolithAir {
            counts: ocounts, binds: obinds, index_binds: oib, n_queries: 4, n_terms: ont, inner_counter: false,
            column_window: true, k_instances: 1, fold: false, fold_txstmt: false, constraints: inner_cs.clone(),
            w_inner_f: w_in, n_pub_f: np_in, n_periodic_f: nper_in, is_zk: 0, cap_height: cap_h,
        };
        let olayout = AirLayout::from_air::<Val>(&outer);
        let inline_nqc = get_log_num_quotient_chunks::<Val, MonolithAir>(&outer, olayout, 0);
        let wrap = WrapAir::new(outer);
        let wlayout = AirLayout::from_air::<Val>(&wrap);
        let wrap_nqc = get_log_num_quotient_chunks::<Val, WrapAir>(&wrap, wlayout, 0);
        println!(
            "R5 self-recursion (monolith-verifies-monolith, {} inner constraints): INLINE MonolithAir log_nqc = \
             {inline_nqc} (> {LOG_BLOWUP} = EXPLODES); WITNESSED WrapAir log_nqc = {wrap_nqc} (≤ {LOG_BLOWUP} = FIXED)",
            inner_cs.len()
        );
        assert!(inline_nqc > LOG_BLOWUP, "the inline monolith must EXPLODE on a monolith-as-inner (the R5 bug)");
        assert!(wrap_nqc <= LOG_BLOWUP, "the wrap must FIX it — witnessed epilogue stays within budget");
    }
}
