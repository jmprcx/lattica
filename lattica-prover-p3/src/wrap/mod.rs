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
use p3_air::symbolic::AirLayout;
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::PrimeCharacteristicRing;
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

/// The `log_num_quotient_chunks` of the fold AIR — the quantity that must stay ≤ `LOG_BLOWUP` (= 4). Above it,
/// p3-0.6.1 silently produces unverifiable proofs (the `native_verify.rs` degree guard). Computed symbolically
/// at the production `is_zk = 1`.
pub fn fold_log_nqc(air: &FoldAir) -> usize {
    let layout = AirLayout::from_air::<Val>(air);
    get_log_num_quotient_chunks::<Val, FoldAir>(air, layout, 1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::LOG_BLOWUP;

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
}
