//! W2 — the recursion **wrap** AIR (the deep-tree fixed point). RESEARCH; feature-gated behind `lookup`,
//! OFF by default, out of the audited staticlib. Built incrementally.
//!
//! The first brick isolates and MEASURES the **degree crux** — the load-bearing insight of
//! `docs/wrap-construction-plan.md`. The outer verifier's α_stark constraint-fold (the OOD epilogue B,
//! `recursion/monolith/air.rs:1310-1331`) is:
//! ```text
//!   for each inner constraint k:  c_k = eval_symbolic_circuit(constraint_k, opened_values)  // INLINE, deg ≤16
//!                                 folded = folded · α_stark + c_k                            // α-Horner
//!   check  folded · inv_vanishing == quotient(ζ)
//! ```
//! Because each `c_k` is evaluated **inline** (`gadgets.rs:919` `eval_symbolic_circuit` substitutes the
//! opened values into the degree-≤16 constraint expression), every fold step sits at degree ~16; chunking the
//! Horner (`FOLD_CHUNK = 7`, binding the running fold to a degree-1 witness column) caps the α-accumulation
//! but not the per-step `c_k` degree — so `base(16) + gating` exceeds the degree-16 / `log_nqc ≤ log_blowup`
//! cliff (p3-0.6.1 then silently produces unverifiable proofs; guarded in `native_verify.rs`). Measured:
//! `log_nqc = 7 > 4`.
//!
//! **The fix (B):** WITNESS each `c_k` in a degree-1 column (the outer AIR holds each inner-constraint value),
//! so the chunked Horner stays low-degree. This module measures that fix on a faithful model of the fold; the
//! *harder* companion — evaluating the `c_k` at low degree without the inline degree-16 expression (C, the
//! symbolic epilogue as a table / running-sum) — is the next W2 step.

use crate::config::Val;
use p3_air::symbolic::{AirLayout, SymbolicAirBuilder};
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::PrimeCharacteristicRing;
use p3_lookup::InteractionBuilder;
use p3_matrix::dense::RowMajorMatrix;
use p3_uni_stark::get_log_num_quotient_chunks;

pub mod air; // W2-assemble: the wrap AIR taking shape (the novel B/C/I regions fused, proven end-to-end)

/// A faithful model of the monolith's α_stark constraint-fold (B). Folds `n_constraints` inner-constraint
/// values `c_k` via the chunked α-Horner — `folded = folded·α + c_k`, binding the running fold to a degree-1
/// witness column (`fold_acc`) every `chunk` constraints — then checks `folded == target`.
///
/// Two knobs reproduce the degree behaviour and its fix:
/// - `c_cols_per_constraint` — how many trace columns each `c_k` multiplies. **1 models a WITNESSED `c_k`**
///   (degree 1 — the fix). **`d > 1` models the monolith's INLINE degree-`d` evaluation** (the explosion).
/// - `chunk` — the `FOLD_CHUNK` boundary. α_stark is a degree-1 witness column (column-window mode), so the
///   Horner accumulates α-degree; binding the partial fold every `chunk` steps caps *that* accumulation.
pub struct FoldAir {
    pub n_constraints: usize,
    pub chunk: usize,
    pub c_cols_per_constraint: usize,
}

impl FoldAir {
    /// Number of witnessed partial-fold columns = chunk boundaries = ⌈N / chunk⌉ − 1.
    fn n_fold_acc(&self) -> usize {
        self.n_constraints.div_ceil(self.chunk).saturating_sub(1)
    }
}

impl<F: p3_field::Field> BaseAir<F> for FoldAir {
    fn width(&self) -> usize {
        // [alpha, target, c_0..c_{N·cpc−1}, fold_acc_0..]
        2 + self.n_constraints * self.c_cols_per_constraint + self.n_fold_acc()
    }
}

impl<AB: AirBuilder<F = Val>> Air<AB> for FoldAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let alpha = local[0];
        let target = local[1];
        let c_base = 2;
        let cpc = self.c_cols_per_constraint;
        let acc_base = c_base + self.n_constraints * cpc;

        let mut folded: AB::Expr = AB::Expr::ZERO;
        let mut ai = 0;
        for k in 0..self.n_constraints {
            // c_k = ∏ of `cpc` columns (degree cpc); cpc = 1 ⇒ a single witnessed column (degree 1).
            let mut ck: AB::Expr = AB::Expr::ONE;
            for j in 0..cpc {
                ck = ck * local[c_base + k * cpc + j].into();
            }
            folded = folded * alpha.into() + ck;
            if (k + 1) % self.chunk == 0 && k + 1 < self.n_constraints {
                let acc = local[acc_base + ai];
                builder.assert_zero(acc.into() - folded.clone()); // bind the partial fold to a degree-1 column
                folded = acc.into();
                ai += 1;
            }
        }
        builder.assert_zero(folded - target.into());
    }
}

/// The `log_num_quotient_chunks` of a wrap AIR — the quantity that must stay ≤ `LOG_BLOWUP` (= 4). Above it,
/// p3-0.6.1 silently produces unverifiable proofs (the `native_verify.rs` degree guard). Computed symbolically
/// at the production `is_zk = 1`.
pub fn wrap_log_nqc<A>(air: &A) -> usize
where
    A: BaseAir<Val> + Air<SymbolicAirBuilder<Val>>,
{
    let layout = AirLayout::from_air::<Val>(air);
    get_log_num_quotient_chunks::<Val, A>(air, layout, 1)
}

/// `wrap_log_nqc` specialized to the α_stark fold model (kept for the W2-B tests).
pub fn fold_log_nqc(air: &FoldAir) -> usize {
    wrap_log_nqc(air)
}

/// **W2-C** — the combined constraint-evaluation-**and**-fold epilogue (C + B). For each of `n_constraints`
/// inner constraints, model its value `c_k` as a degree-`degree` product of opened columns, then α-fold the
/// `c_k` (chunked, à la [`FoldAir`]). The `witnessed` knob is the **C fix**:
/// - `witnessed = true` — evaluate each `c_k` through **degree-≤2 steps into witnessed intermediate columns**
///   (`t_0 = x_0·x_1`, `t_i = t_{i−1}·x_{i+1}`, …), so `c_k` is a *degree-1* column the fold consumes cheaply.
///   This is the low-degree analogue of `eval_symbolic_circuit` — "never re-evaluate the tree" as one
///   degree-`degree` expression. (A single degree-16 constraint is already `log_nqc = 4`; the explosion is the
///   fold stacking degree onto an inline degree-16 `c_k`, so witnessing the `c_k` is what lets B stay cheap.)
/// - `witnessed = false` — the monolith's INLINE evaluation: each `c_k` is one degree-`degree` expression fed
///   straight into the fold.
///
/// Soundness of the witnessed form: each intermediate is pinned by its own degree-2 constraint, so `c_k`
/// equals the product; a wrong intermediate fails its constraint. (Width cost — `2·degree − 1` columns per
/// constraint — is the SIZE lever addressed later by a shared op-table / lookup and Tip5, W3/W4; here we gate
/// only the DEGREE.)
pub struct DagFoldAir {
    pub n_constraints: usize,
    pub chunk: usize,
    pub degree: usize,
    pub witnessed: bool,
}

impl DagFoldAir {
    fn cols_per_constraint(&self) -> usize {
        if self.witnessed {
            2 * self.degree - 1 // `degree` inputs + `degree − 1` witnessed intermediates
        } else {
            self.degree // just the inputs; c_k is the inline product
        }
    }
    fn n_fold_acc(&self) -> usize {
        self.n_constraints.div_ceil(self.chunk).saturating_sub(1)
    }
}

impl<F: p3_field::Field> BaseAir<F> for DagFoldAir {
    fn width(&self) -> usize {
        2 + self.n_constraints * self.cols_per_constraint() + self.n_fold_acc()
    }
}

impl<AB: AirBuilder<F = Val>> Air<AB> for DagFoldAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let alpha = local[0];
        let target = local[1];
        let per = self.cols_per_constraint();
        let base = 2;
        let acc_base = base + self.n_constraints * per;

        let mut folded: AB::Expr = AB::Expr::ZERO;
        let mut ai = 0;
        for k in 0..self.n_constraints {
            let cb = base + k * per; // this constraint's column block
            let ck: AB::Expr = if self.witnessed {
                // C: evaluate the degree-`degree` product via degree-2 steps into witnessed intermediates.
                let t = cb + self.degree; // intermediate base
                builder.assert_zero(local[t].into() - local[cb].into() * local[cb + 1].into());
                for i in 1..self.degree - 1 {
                    builder.assert_zero(local[t + i].into() - local[t + i - 1].into() * local[cb + i + 1].into());
                }
                local[t + self.degree - 2].into() // c_k = final intermediate (degree-1 witnessed column)
            } else {
                // Inline (monolith): c_k is one degree-`degree` expression.
                let mut prod: AB::Expr = AB::Expr::ONE;
                for j in 0..self.degree {
                    prod = prod * local[cb + j].into();
                }
                prod
            };
            folded = folded * alpha.into() + ck;
            if (k + 1) % self.chunk == 0 && k + 1 < self.n_constraints {
                let acc = local[acc_base + ai];
                builder.assert_zero(acc.into() - folded.clone());
                folded = acc.into();
                ai += 1;
            }
        }
        builder.assert_zero(folded - target.into());
    }
}

/// **I (cap-mux)** — Merkle-cap membership as a LogUp lookup instead of the monolith's degree-`cap_height`
/// selector product over `2^cap_height` entries (`recursion/monolith/air.rs:1652-1664`). Columns
/// `[key, value, mult]` declare one 2-element `(key, value)` lookup carrying signed multiplicity `mult`: table
/// rows carry `−count[key]`, query rows `+1`, so the multiset balances iff every queried `(index, value)` is a
/// real `(j, cap[j])` pair — i.e. `value = cap[index]`. **Degree 3, width 3 (constant)** — killing both the
/// `cap_height`-degree product and the `2^cap_height` width. Proves + verifies through the W1 lookup prover.
///
/// (In the real wrap the cap table rows are bound to the transcript-committed cap; here they are trace rows,
/// so this validates the *mux mechanism* — that a query selects the right indexed entry — not that binding.)
pub struct CapMuxAir;

impl<F: p3_field::Field> BaseAir<F> for CapMuxAir {
    fn width(&self) -> usize {
        3
    }
}

impl<AB: AirBuilder<F = Val> + InteractionBuilder> Air<AB> for CapMuxAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let (key, value, mult) = (local[0], local[1], local[2]);
        // One 2-element (key, value) lookup tuple with signed multiplicity `mult` (LogUp "bus"): query rows
        // contribute +1, table rows −count[key]; balance ⇒ every queried (index, value) = a real (j, cap[j]).
        builder.push_local_interaction(vec![(vec![key.into(), value.into()], mult.into())]);
    }
}

/// Build a cap-mux trace: `cap.len()` table rows `(j, cap[j], −count[j])` plus one query row
/// `(index, cap[index], +1)` per query, padded (mult 0 ⇒ no contribution) to a power-of-two height.
pub fn cap_mux_trace(cap: &[Val], queries: &[usize]) -> RowMajorMatrix<Val> {
    let mut count = vec![0u64; cap.len()];
    for &q in queries {
        count[q] += 1;
    }
    let mut rows: Vec<[Val; 3]> = Vec::with_capacity(cap.len() + queries.len());
    for (j, &cj) in cap.iter().enumerate() {
        rows.push([Val::from_u64(j as u64), cj, -Val::from_u64(count[j])]); // table row: −count[j]
    }
    for &q in queries {
        rows.push([Val::from_u64(q as u64), cap[q], Val::ONE]); // query row: +1
    }
    rows.resize(rows.len().next_power_of_two(), [Val::ZERO, Val::ZERO, Val::ZERO]); // padding (mult 0)
    RowMajorMatrix::new(rows.into_iter().flatten().collect(), 3)
}

/// **W2-C (size)** — the size-efficient form of C: evaluate a product DOWN THE ROWS as a running product
/// (constant width) instead of across `2·degree − 1` columns (`DagFoldAir` witnessed). Boundary `prod = x` on
/// the first row; transition `prod' = prod · x'` (degree 2). Width 3 (`[x, prod, mult]`, constant regardless of
/// the product length — height carries the length), so a degree-`d` constraint costs `d` ROWS not `2d` columns
/// ("never re-evaluate the tree" as a running eval). Carries a trivially-balanced range-check lookup so it
/// proves + verifies through the W1 lookup prover — which also **exercises the prover's transition support**
/// (every earlier lookup AIR is local-only; the wrap's real inner has transition constraints).
pub struct ChainEvalAir;

impl<F: p3_field::Field> BaseAir<F> for ChainEvalAir {
    fn width(&self) -> usize {
        3
    }
}

impl<AB: AirBuilder<F = Val> + InteractionBuilder> Air<AB> for ChainEvalAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur = main.current_slice().to_vec();
        let nxt = main.next_slice().to_vec();
        let (x, prod, mult) = (cur[0], cur[1], cur[2]);
        builder.when_first_row().assert_zero(prod.into() - x.into()); // boundary: prod = x
        builder.when_transition().assert_zero(nxt[1].into() - prod.into() * nxt[0].into()); // prod' = prod·x'
        // A trivially-balanced (query x, provide x) range-check lookup to commit a terminal.
        builder.push_local_interaction(vec![
            (vec![x.into()], AB::Expr::ONE),
            (vec![x.into()], -(mult.into())),
        ]);
    }
}

/// A valid running-product trace: `x = 1` everywhere ⇒ `prod = 1`; `mult = 1` (the lookup self-cancels).
pub fn chain_eval_trace(height: usize) -> RowMajorMatrix<Val> {
    let mut flat = Vec::with_capacity(height * 3);
    for _ in 0..height {
        flat.push(Val::ONE); // x
        flat.push(Val::ONE); // prod (running product of 1s)
        flat.push(Val::ONE); // mult
    }
    RowMajorMatrix::new(flat, 3)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{Challenge, LOG_BLOWUP};
    use crate::joinsplit_air::JoinSplitAir;
    use crate::lookup::prover::{combined_constraint_layout, prove_lookup, verify_lookup, LookupVerifyError};
    use crate::poseidon2_air::Poseidon2RowsAir;
    use p3_air::symbolic::{get_symbolic_constraints, SymbolicExpr, SymbolicExpression};
    use p3_lookup::Lookups;
    use std::collections::HashSet;
    use std::sync::Arc;

    /// Count the **unique** Mul nodes reachable from a constraint DAG (memoized by `Arc` identity via `seen`),
    /// i.e. the witnessed intermediate columns the size-efficient C would need WITH sub-expression sharing
    /// ("never re-evaluate the tree"). Add/Sub/Neg don't raise degree, so only Mul nodes are witnessed.
    fn count_mul_nodes(expr: &SymbolicExpression<Val>, seen: &mut HashSet<usize>) -> usize {
        match expr {
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
            return 0; // already counted this shared sub-expression
        }
        count_mul_nodes(arc, seen)
    }

    /// The **B degree fix**: with WITNESSED inner-constraint values (degree-1 columns) and the chunked fold,
    /// the α_stark fold stays within the degree-16 / `log_blowup` cliff — even for a realistic 384-constraint
    /// inner (the join-split `MonolithAir` scale).
    #[test]
    fn witnessed_chunked_fold_stays_within_blowup() {
        let air = FoldAir { n_constraints: 384, chunk: 7, c_cols_per_constraint: 1 };
        let log_nqc = fold_log_nqc(&air);
        println!("WITNESSED chunked fold (N=384, chunk=7): log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        assert!(log_nqc <= LOG_BLOWUP, "witnessed + chunked fold must stay ≤ log_blowup (got {log_nqc})");
    }

    /// The explosion source the monolith actually hits: INLINE degree-16 constraint evaluation
    /// (`eval_symbolic_circuit`), even chunked, exceeds the cliff. Witnessing the `c_k` (above) is the fix.
    #[test]
    fn inline_high_degree_fold_exceeds_blowup() {
        let air = FoldAir { n_constraints: 384, chunk: 7, c_cols_per_constraint: 16 };
        let log_nqc = fold_log_nqc(&air);
        println!("INLINE deg-16 chunked fold (N=384, chunk=7): log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        assert!(log_nqc > LOG_BLOWUP, "inline degree-16 fold must exceed log_blowup (got {log_nqc})");
    }

    /// The second lever — chunking. Without it (chunk = N), the α-Horner accumulates α-degree across all N
    /// constraints and explodes even for WITNESSED (degree-1) `c_k`. Both witnessing and chunking are needed.
    #[test]
    fn unchunked_fold_exceeds_blowup() {
        let air = FoldAir { n_constraints: 384, chunk: 384, c_cols_per_constraint: 1 };
        let log_nqc = fold_log_nqc(&air);
        println!("UNCHUNKED witnessed fold (N=384): log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        assert!(log_nqc > LOG_BLOWUP, "an unchunked α-Horner fold explodes even for witnessed c_k (got {log_nqc})");
    }

    /// **W2-C** — the combined epilogue: evaluating each `c_k` via WITNESSED degree-2 steps (C) and folding the
    /// resulting degree-1 `c_k` (B) keeps the FULL fold within the degree-16 / log_blowup cliff, for a
    /// realistic 384-constraint × degree-16 inner.
    #[test]
    fn witnessed_dag_fold_stays_within_blowup() {
        let air = DagFoldAir { n_constraints: 384, chunk: 7, degree: 16, witnessed: true };
        let log_nqc = wrap_log_nqc(&air);
        println!("C+B WITNESSED (N=384, deg=16, chunk=7): log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        assert!(log_nqc <= LOG_BLOWUP, "witnessed c_k evaluation + fold must stay ≤ log_blowup (got {log_nqc})");
    }

    /// The monolith's inline path, for contrast: evaluating each `c_k` as one degree-16 expression and folding
    /// it inline exceeds the cliff. Witnessing the `c_k` (above) is the fix.
    #[test]
    fn inline_dag_fold_exceeds_blowup() {
        let air = DagFoldAir { n_constraints: 384, chunk: 7, degree: 16, witnessed: false };
        let log_nqc = wrap_log_nqc(&air);
        println!("C+B INLINE (N=384, deg=16, chunk=7): log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        assert!(log_nqc > LOG_BLOWUP, "inline degree-16 c_k evaluation + fold must exceed log_blowup (got {log_nqc})");
    }

    /// **W2-I** — the cap-mux, as a lookup, proves + verifies end to end through the W1 lookup prover: queries
    /// selecting the real `cap[index]` balance the multiset.
    #[test]
    fn cap_mux_round_trips() {
        let cap: Vec<Val> = (0..(1u64 << 6)).map(|j| Val::from_u64(0x1000 + j)).collect();
        let queries = vec![3usize, 3, 17, 40, 63, 0];
        let air = CapMuxAir;
        let proof = prove_lookup(&air, cap_mux_trace(&cap, &queries), &[]);
        assert!(verify_lookup(&air, &proof, &[]).is_ok(), "valid cap selections must verify");
    }

    /// A query selecting a WRONG value (≠ `cap[index]`) unbalances the multiset ⇒ non-zero terminal ⇒
    /// rejected — the mux soundness, at degree 3 (the product-mux would need a degree-`cap_height` selector).
    #[test]
    fn cap_mux_rejects_wrong_selection() {
        let cap: Vec<Val> = (0..(1u64 << 6)).map(|j| Val::from_u64(0x1000 + j)).collect();
        let queries = vec![3usize, 17, 40];
        let mut trace = cap_mux_trace(&cap, &queries);
        // The first query row follows the cap.len() table rows; corrupt its value column (col 1).
        let qrow = cap.len();
        trace.values[qrow * 3 + 1] = Val::from_u64(0xDEAD); // index 3 now selects a non-cap value
        let air = CapMuxAir;
        let proof = prove_lookup(&air, trace, &[]);
        assert!(
            matches!(verify_lookup(&air, &proof, &[]), Err(LookupVerifyError::NonZeroTerminal)),
            "a query selecting value ≠ cap[index] must be rejected"
        );
    }

    /// The degree + size win: the cap-mux lookup is **width 3 (constant)** and within the degree budget —
    /// versus the product-mux's `2^cap_height` width and `cap_height` degree.
    #[test]
    fn cap_mux_is_low_degree_and_narrow() {
        let air = CapMuxAir;
        assert_eq!(BaseAir::<Val>::width(&air), 3, "cap-mux width is constant (not 2^cap_height)");
        let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        println!("cap-mux lookup: width = 3, log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        assert!(log_nqc <= LOG_BLOWUP, "cap-mux lookup must be within the degree budget (got {log_nqc})");
    }

    /// **W2-C (size)** — the narrow-tall running eval proves + verifies through the W1 lookup prover, which
    /// also validates the prover's TRANSITION support end to end (every earlier lookup AIR is local-only).
    #[test]
    fn chain_eval_round_trips() {
        let air = ChainEvalAir;
        let proof = prove_lookup(&air, chain_eval_trace(1 << 5), &[]);
        assert!(verify_lookup(&air, &proof, &[]).is_ok(), "a valid running-product trace must verify");
    }

    /// Breaking the running product violates the `prod' = prod·x'` transition ⇒ OOD mismatch — confirming
    /// transition constraints are folded correctly in both the prover's quotient and the ζ-check.
    #[test]
    fn chain_eval_rejects_broken_product() {
        let air = ChainEvalAir;
        let mut trace = chain_eval_trace(1 << 5);
        trace.values[5 * 3 + 1] = Val::from_u64(2); // row 5's prod ≠ prod_4 · x_5
        let proof = prove_lookup(&air, trace, &[]);
        assert!(
            matches!(verify_lookup(&air, &proof, &[]), Err(LookupVerifyError::OodMismatch)),
            "a broken running product must fail the OOD identity"
        );
    }

    /// The size win: the running eval is WIDTH 3 (constant) and within the degree budget — a degree-`d`
    /// constraint costs `d` ROWS, not the wide layout's `2·d` columns.
    #[test]
    fn chain_eval_is_narrow_and_low_degree() {
        let air = ChainEvalAir;
        assert_eq!(BaseAir::<Val>::width(&air), 3, "running-eval width is constant (independent of length)");
        let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        println!("ChainEval: width = 3 (wide would be 2·degree), log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        assert!(log_nqc <= LOG_BLOWUP, "narrow-tall running eval must stay within the degree budget (got {log_nqc})");
    }

    /// **The synthetic result, grounded in the REAL inner.** Extract the actual `JoinSplitAir` constraints,
    /// report the real profile, and confirm the OOD epilogue — folding its `N` witnessed (degree-1) `c_k` via
    /// the chunked Horner (B) — stays within the degree-16 / log_blowup cliff, versus the monolith's inline
    /// evaluation at the real max degree.
    #[test]
    fn real_joinsplit_inner_epilogue_within_budget() {
        let layout = AirLayout::from_air::<Val>(&JoinSplitAir);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, layout);
        let n = constraints.len();
        let max_deg = constraints.iter().map(|c| c.degree_multiple()).max().unwrap_or(0);
        let mut seen = HashSet::new();
        let muls: usize = constraints.iter().map(|c| count_mul_nodes(c, &mut seen)).sum();
        println!(
            "REAL JoinSplitAir inner: {n} constraints, max degree {max_deg}, {muls} unique Mul nodes \
             (= witnessed C columns, shared)"
        );

        // The OOD epilogue folds the N witnessed degree-1 c_k via the chunked Horner (B).
        let witnessed = FoldAir { n_constraints: n, chunk: 7, c_cols_per_constraint: 1 };
        let log_nqc = wrap_log_nqc(&witnessed);
        println!("REAL epilogue (witnessed C + fold B): log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        assert!(log_nqc <= LOG_BLOWUP, "the real-inner witnessed epilogue must stay ≤ log_blowup (got {log_nqc})");

        // Contrast: the monolith's inline evaluation folds each c_k at the real max degree (reported, not
        // asserted — the explosion's magnitude depends on the inner's exact max degree).
        let inline = FoldAir { n_constraints: n, chunk: 7, c_cols_per_constraint: max_deg.max(1) };
        println!("REAL epilogue INLINE (monolith, deg {max_deg}): log_nqc = {}", wrap_log_nqc(&inline));
    }

    /// **W3 (size) — profile the epilogue DAG to choose the op-table canonicalization.** The witnessed epilogue
    /// (W2) pays `2·n_mul` COLUMNS (each F_p² `Mul` → a degree-1 column pair, filled only at the `n_queries`
    /// arith heads, wasted on every other row); W3 trades those for narrow-tall op-table ROWS at constant width
    /// (overlaid on slack rows). Two canonical forms are possible, and the REAL DAG shape decides between them:
    /// - **(A) FLATTEN** every op (Add/Sub/Neg/Mul) to its own row, wired by a permutation/LogUp bus — each row
    ///   reads exactly **2** operands by address and writes 1 output, so the width is a small CONSTANT and the
    ///   fan-in is trivially bounded; the cost is `n_ops` rows (all node types, not just `Mul`).
    /// - **(B) HYBRID** — keep the linear folding of Add/Sub/Neg and put one row per `Mul` (`n_mul` rows), but
    ///   then each `Mul` operand is a linear combination of terminals (opening leaves + child-`Mul` outputs)
    ///   needing **bounded bus fan-in** — viable only if the max operand fan-in is small.
    ///
    /// This measures the deciding data on the real inner: the node-type census over the shared DAG (Arc-dedup)
    /// and the per-`Mul` operand linear fan-in (distinct terminals reachable through Add/Sub/Neg without
    /// crossing another `Mul`). Reported, not asserted — it documents the op-table design input (like W2-real's
    /// "81 constraints, 214 Muls"), so the next brick builds the right canonical form.
    #[test]
    fn joinsplit_epilogue_dag_shape() {
        use p3_uni_stark::BaseLeaf;
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));

        // (1) Node-type census over the shared DAG (dedup at Arc boundaries, like `count_mul_nodes`; the 81
        // constraint ROOTS are owned, counted directly — sharing lives in their Arc children).
        #[derive(Default)]
        struct Census {
            leaf_var: usize,  // opening values (Main/Public/Periodic) — bus terminals
            leaf_sel: usize,  // is_first/is_last/is_trans selectors — witnessed at ζ, also terminals
            leaf_const: usize, // pure constants — affine constant term, not a bus read
            add: usize,
            sub: usize,
            neg: usize,
            mul: usize,
        }
        // Collect each unique Mul's operand arcs (for the fan-in pass) alongside the census.
        type Arcs = Vec<(Arc<SymbolicExpression<Val>>, Arc<SymbolicExpression<Val>>)>;
        fn census_node(e: &SymbolicExpression<Val>, seen: &mut HashSet<usize>, c: &mut Census, ops: &mut Arcs) {
            match e {
                SymbolicExpr::Leaf(l) => match l {
                    BaseLeaf::Constant(_) => c.leaf_const += 1,
                    BaseLeaf::Variable(_) => c.leaf_var += 1,
                    _ => c.leaf_sel += 1,
                },
                SymbolicExpr::Add { x, y, .. } => {
                    c.add += 1;
                    census_arc(x, seen, c, ops);
                    census_arc(y, seen, c, ops);
                }
                SymbolicExpr::Sub { x, y, .. } => {
                    c.sub += 1;
                    census_arc(x, seen, c, ops);
                    census_arc(y, seen, c, ops);
                }
                SymbolicExpr::Neg { x, .. } => {
                    c.neg += 1;
                    census_arc(x, seen, c, ops);
                }
                SymbolicExpr::Mul { x, y, .. } => {
                    c.mul += 1;
                    ops.push((x.clone(), y.clone()));
                    census_arc(x, seen, c, ops);
                    census_arc(y, seen, c, ops);
                }
            }
        }
        fn census_arc(arc: &Arc<SymbolicExpression<Val>>, seen: &mut HashSet<usize>, c: &mut Census, ops: &mut Arcs) {
            if seen.insert(Arc::as_ptr(arc) as usize) {
                census_node(arc.as_ref(), seen, c, ops);
            }
        }
        let (mut seen, mut cen, mut mul_ops) = (HashSet::new(), Census::default(), Arcs::new());
        for root in &constraints {
            census_node(root, &mut seen, &mut cen, &mut mul_ops);
        }
        let n_ops = cen.add + cen.sub + cen.neg + cen.mul;
        assert_eq!(cen.mul, mul_ops.len(), "one operand pair recorded per unique Mul node");

        // (2) Per-Mul operand linear fan-in: distinct terminals (non-constant leaf OR child-Mul cut point)
        // reachable through Add/Sub/Neg. This is the bus-read count a HYBRID (one-row-per-Mul) design needs
        // per operand — the number that decides whether B is viable vs. the always-2 FLATTEN form.
        fn terminals(arc: &Arc<SymbolicExpression<Val>>, set: &mut HashSet<usize>) {
            match arc.as_ref() {
                SymbolicExpr::Leaf(BaseLeaf::Constant(_)) => {} // constant term, not a bus read
                SymbolicExpr::Leaf(_) | SymbolicExpr::Mul { .. } => {
                    set.insert(Arc::as_ptr(arc) as usize); // opening terminal / Mul cut point
                }
                SymbolicExpr::Neg { x, .. } => terminals(x, set),
                SymbolicExpr::Add { x, y, .. } | SymbolicExpr::Sub { x, y, .. } => {
                    terminals(x, set);
                    terminals(y, set);
                }
            }
        }
        let mut fanins: Vec<usize> = Vec::with_capacity(2 * mul_ops.len());
        for (x, y) in &mul_ops {
            for operand in [x, y] {
                let mut set = HashSet::new();
                terminals(operand, &mut set);
                fanins.push(set.len());
            }
        }
        let max_fanin = fanins.iter().copied().max().unwrap_or(0);
        let sum_fanin: usize = fanins.iter().sum();
        let mean_fanin = sum_fanin as f64 / fanins.len().max(1) as f64;
        // Histogram over the fan-in buckets that matter for a fixed-width hybrid row.
        let buckets = [(1usize, 2usize), (3, 4), (5, 8), (9, 16), (17, usize::MAX)];
        let hist: Vec<(String, usize)> = buckets
            .iter()
            .map(|&(lo, hi)| {
                let label = if hi == usize::MAX { format!("{lo}+") } else { format!("{lo}-{hi}") };
                (label, fanins.iter().filter(|&&f| f >= lo && f <= hi).count())
            })
            .collect();

        println!(
            "W3 DAG shape (real JoinSplitAir epilogue): {} constraints ⇒ unique nodes: {} leaf-var (openings), \
             {} leaf-sel, {} const, {} add, {} sub, {} neg, {} MUL",
            constraints.len(), cen.leaf_var, cen.leaf_sel, cen.leaf_const, cen.add, cen.sub, cen.neg, cen.mul,
        );
        println!(
            "  op count n_ops = {n_ops} (add+sub+neg+mul); Mul operand fan-in: max {max_fanin}, mean {mean_fanin:.2}, \
             histogram {hist:?}",
        );
        // The size trade-off the number decides. Witnessed (W2) = 2·n_mul dedicated COLUMNS (all rows).
        // FLATTEN op-table = a small const width W_op over n_ops slack ROWS (fan-in exactly 2). HYBRID =
        // const width over n_mul ROWS but only if max_fanin is small enough to bound the per-row bus reads.
        println!(
            "  ⇒ witnessed W2 = {} COLUMNS; FLATTEN op-table = const-width × {n_ops} ROWS (fan-in 2); \
             HYBRID = const-width × {} ROWS (needs fan-in ≤ K, max here {max_fanin})",
            2 * cen.mul, cen.mul,
        );
    }

    /// **Wrap degree-budget rollup (W2-super).** `log_nqc` composes as the MAX over regions (it is monotonic
    /// in the max constraint degree), so the whole wrap's budget is the max of its regions' log_nqc. Roll up
    /// the real regions and confirm they compose within budget: the OOD epilogue (B, over the real inner's 81
    /// witnessed c_k), the real Poseidon2 hash rows (A), the cap-mux (I), and the narrow-tall C eval — plus,
    /// under `--features recursion`, the reused super-tile verifier tiles D (FRI β-fold), E (Merkle-opening +
    /// SUM-form not_term), F (transcript sponge). This turns the plan's "every other gadget is already ≤16"
    /// premise into a measurement. (G/H/J — DEEP α_fri / OOD selectors / tx-root fold — are `monolith/air.rs`
    /// regions, measured when the wrap AIR is assembled, W2-assemble.)
    #[test]
    fn wrap_degree_budget_rollup() {
        let n_inner =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir)).len();
        let l_epilogue = wrap_log_nqc(&FoldAir { n_constraints: n_inner, chunk: 7, c_cols_per_constraint: 1 });
        let l_hash = wrap_log_nqc(&Poseidon2RowsAir);
        let l_capmux =
            combined_constraint_layout(&CapMuxAir, &Lookups::from_air::<Challenge, _>(&CapMuxAir), 1).1;
        let l_chain =
            combined_constraint_layout(&ChainEvalAir, &Lookups::from_air::<Challenge, _>(&ChainEvalAir), 1).1;

        // Accessible without `--features recursion`: the OOD epilogue fold (B) over the real inner, the real
        // Poseidon2 hash rows (A), the cap-mux lookup (I), the narrow-tall C eval.
        let base = [
            ("epilogue(B)", l_epilogue),
            ("hash(Poseidon2,A)", l_hash),
            ("cap-mux(I)", l_capmux),
            ("chain-eval(C)", l_chain),
        ];

        // W2-super — the reused super-tile verifier tiles (standalone AIRs faithful to the monolith's fused
        // fold/Merkle/transcript regions). D (FRI β-fold) is F_p² arithmetic; E (Merkle-opening) and F
        // (transcript sponge) reuse the degree-7 Poseidon2 S-box. Each must land within the budget.
        #[cfg(feature = "recursion")]
        let extra: Vec<(&str, usize)> = {
            use crate::recursion::fri_fold::FriFoldAir;
            use crate::recursion::fri_merkle::FriMerkleAir;
            use crate::recursion::transcript::SpongeAir;
            vec![
                ("fri-fold(D)", wrap_log_nqc(&FriFoldAir)),
                ("fri-merkle(E)", wrap_log_nqc(&FriMerkleAir)),
                ("transcript(F)", wrap_log_nqc(&SpongeAir { blocks: 2 })),
            ]
        };
        #[cfg(not(feature = "recursion"))]
        let extra: Vec<(&str, usize)> = Vec::new();

        let regions: Vec<(&str, usize)> = base.iter().copied().chain(extra).collect();
        let composed = regions.iter().map(|&(_, l)| l).max().unwrap();
        let detail = regions.iter().map(|(n, l)| format!("{n}={l}")).collect::<Vec<_>>().join(", ");
        println!("WRAP budget rollup: {detail} ⇒ composed log_nqc = {composed} (budget {LOG_BLOWUP})");

        for (name, l) in &regions {
            assert!(*l <= LOG_BLOWUP, "wrap region {name} exceeds the degree budget: log_nqc {l} > {LOG_BLOWUP}");
        }
        assert!(composed <= LOG_BLOWUP, "the wrap regions must compose within the degree budget");

        #[cfg(not(feature = "recursion"))]
        println!(
            "  (super-tile FRI β-fold (D) / Merkle-path (E) / transcript (F) live behind --features \
             recursion — run `--features lookup,recursion` to fold them in)"
        );
        #[cfg(feature = "recursion")]
        println!(
            "  remaining: DEEP α_fri (G) / OOD selectors (H) / tx-root fold (J) — monolith/air.rs regions, \
             measured when the wrap AIR is assembled (W2-assemble)"
        );
    }

    /// **W2-assemble prerequisite — the full wrap feature-combination in ONE AIR.** The composed wrap AIR
    /// exercises transitions, periodic selectors, public values, AND multiple lookups simultaneously; each was
    /// validated in isolation (`ChainEvalAir` transitions here; `PeriodicAir`/`PinnedAir`/`TwoLookupAir` in
    /// the lookup prover) but never COMBINED. `CompositeAir` combines all four so the W1 lookup prover's
    /// combined layout + quotient sizing is proven ready for the composed wrap before the coupled W2-assemble
    /// build (a cheap gate on a genuine prover-integration risk).
    ///
    /// Cols `[x, prod, y, table, m1, m2]`: `x` is the running-product input, range-checked by two lookups;
    /// `prod` is the running product (transition `prod' = prod·x'`, boundary `prod = x`) — kept OUTSIDE the
    /// lookups so a broken product is isolable; `y` is pinned to `public[0]` (first row) and periodic-gated
    /// (`sel·(y−1) = 0` on even rows) — also outside the lookups; `table` provides both range-checks.
    struct CompositeAir;

    impl<F: p3_field::Field> BaseAir<F> for CompositeAir {
        fn width(&self) -> usize {
            6
        }
        fn num_public_values(&self) -> usize {
            1
        }
        fn num_periodic_columns(&self) -> usize {
            1
        }
        fn periodic_columns(&self) -> Vec<Vec<F>> {
            vec![vec![F::ONE, F::ZERO]] // period-2 selector: 1 on even rows
        }
    }

    impl<AB: AirBuilder<F = Val> + InteractionBuilder> Air<AB> for CompositeAir {
        fn eval(&self, builder: &mut AB) {
            let main = builder.main();
            let cur = main.current_slice().to_vec();
            let nxt = main.next_slice().to_vec();
            let (x, prod, y, table, m1, m2) = (cur[0], cur[1], cur[2], cur[3], cur[4], cur[5]);
            let sel: AB::Expr = builder.periodic_values()[0].into();
            let pin: AB::Expr = builder.public_values()[0].into();

            // base constraints over columns NOT carried in any lookup, so each is independently tamperable.
            builder.when_first_row().assert_zero(prod.into() - x.into()); // boundary: prod = x
            builder.when_transition().assert_zero(nxt[1].into() - prod.into() * nxt[0].into()); // prod' = prod·x'
            builder.when_first_row().assert_eq(y, pin); // y(row 0) == public[0]
            builder.assert_zero(sel * (y.into() - AB::Expr::ONE)); // even rows (sel = 1): y == 1

            // two LogUp range-checks of x against the shared table (multi-lookup ⇒ aux width 3).
            builder
                .push_local_interaction(vec![(vec![x.into()], AB::Expr::ONE), (vec![table.into()], -(m1.into()))]);
            builder
                .push_local_interaction(vec![(vec![x.into()], AB::Expr::ONE), (vec![table.into()], -(m2.into()))]);
        }
    }

    /// A valid trace: everything `1` (both range-checks self-cancel; running product of ones; even-row
    /// `y == 1`; first-row `y == public[0] = 1`).
    fn composite_trace(height: usize) -> RowMajorMatrix<Val> {
        let mut flat = Vec::with_capacity(height * 6);
        for _ in 0..height {
            flat.extend_from_slice(&[Val::ONE; 6]);
        }
        RowMajorMatrix::new(flat, 6)
    }

    /// The combination proves + verifies end to end (aux width 3 = 1 accumulator + 2 fractions) — the W1
    /// lookup prover threads transitions + periodic + public values + multi-lookup together, the composed
    /// wrap AIR's prover requirements, validated before the coupled assembly.
    #[test]
    fn composite_air_round_trips() {
        let air = CompositeAir;
        let proof = prove_lookup(&air, composite_trace(1 << 5), &[Val::ONE]);
        assert_eq!(proof.aux_width, 3, "two lookups ⇒ aux width = 1 accumulator + 2 fractions");
        assert!(verify_lookup(&air, &proof, &[Val::ONE]).is_ok(), "the combined-feature AIR must verify end to end");
    }

    /// Breaking the running product (a column outside the lookups) violates the transition ⇒ OOD mismatch —
    /// transitions fold correctly amid the periodic + multi-lookup constraints.
    #[test]
    fn composite_air_rejects_broken_product() {
        let air = CompositeAir;
        let mut trace = composite_trace(1 << 5);
        trace.values[5 * 6 + 1] = Val::from_u64(2); // row 5's prod ≠ prod_4 · x_5
        let proof = prove_lookup(&air, trace, &[Val::ONE]);
        assert!(
            matches!(verify_lookup(&air, &proof, &[Val::ONE]), Err(LookupVerifyError::OodMismatch)),
            "a broken running product must fail the OOD identity"
        );
    }

    /// Violating an even row's periodic-gated bind (`y ≠ 1`, kept lookup-balanced since `y` is outside the
    /// lookups) ⇒ OOD mismatch — periodic columns fold consistently alongside the lookups.
    #[test]
    fn composite_air_rejects_violated_periodic() {
        let air = CompositeAir;
        let mut trace = composite_trace(1 << 5);
        trace.values[2 * 6 + 2] = Val::from_u64(5); // row 2 (even, sel = 1): y = 5 ≠ 1
        let proof = prove_lookup(&air, trace, &[Val::ONE]);
        assert!(
            matches!(verify_lookup(&air, &proof, &[Val::ONE]), Err(LookupVerifyError::OodMismatch)),
            "a violated even-row periodic constraint must fail the OOD identity"
        );
    }

    /// Unbalancing one lookup (bump a multiplicity) leaves the base constraints satisfied but breaks that
    /// lookup's LogUp terminal ⇒ rejected — the two lookups are checked independently in the combined layout.
    #[test]
    fn composite_air_rejects_unbalanced_lookup() {
        let air = CompositeAir;
        let mut trace = composite_trace(1 << 5);
        trace.values[7 * 6 + 4] = Val::from_u64(2); // row 7's m1 = 2 ⇒ lookup 1 no longer cancels
        let proof = prove_lookup(&air, trace, &[Val::ONE]);
        assert!(
            matches!(verify_lookup(&air, &proof, &[Val::ONE]), Err(LookupVerifyError::NonZeroTerminal)),
            "an unbalanced lookup must be rejected by the terminal check"
        );
    }
}
