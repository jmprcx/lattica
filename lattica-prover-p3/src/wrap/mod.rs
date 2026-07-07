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
    use crate::lookup::prover::{combined_constraint_layout, prove_lookup, verify_lookup, LookupVerifyError};
    use p3_lookup::{LookupProtocol, Lookups};

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
}
