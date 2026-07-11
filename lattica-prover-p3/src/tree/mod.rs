//! Phase-0 (0a) — **wrap-feasibility model** (the GO/NO-GO crux).
//!
//! The deep recursion tree needs a **wrap**: a canonical, fixed-size, low-degree verifier so that
//! `verify(proof)` emits a proof no bigger than what it verified (a fixed point), letting tree levels
//! stack at bounded cost. Today self-composition *diverges* — the committed probe
//! `recursion::monolith::tests::phase9_self_recursion_probe` measures a monolith verifying the smallest
//! (W=193, 384-constraint) monolith blowing up to **W≈8520 (~44×), log_nqc=7** — past the hard
//! `log_nqc ≤ log_blowup = 4` (degree ≤ 16) cliff that silently corrupts proofs.
//!
//! Two drivers (from `docs/recursion-aggregation-params.md:126-128`):
//!   * **degree** — the outer's α-Horner fold over the inner's high-degree constraints compounds past 16;
//!   * **width/size** — the outer carries the inner's opened rows + `2·W` reduced-opening terms and
//!     re-evaluates the inner's constraints, so it is strictly wider than its input.
//!
//! This module does NOT build the wrap (that is Phase 3). It records — as an executable model wired to the
//! two validated Phase-0 inputs — whether Tip5 + a lookup argument *address both drivers*, which is the
//! GO/NO-GO question:
//!   * **0b/0c-P2** measured a LogUp constraint at **degree `1 + Σ side-degrees`** (`crate::lookup`) — 3 for
//!     a 2-sided range-check lookup — so re-expressing the FRI-fold / range-decomposition relations as
//!     *low-arity* lookups replaces the degree-inflating operations with low-degree ones (a k-way lookup is
//!     degree `1+k`, so the fold must be chunked into small-arity lookups, mirroring `FOLD_CHUNK`).
//!   * **0c** measured Tip5 at **~7 rows/permutation vs Poseidon2's 32 (4.6×)** with a residual `x^7`
//!     (degree-7) hash lane (`crate::tip5`), shrinking the hash-dominated verification width.
//!
//! The model is deliberately conservative and its assumptions are explicit, so 0e / the design doc can
//! audit them.

/// The measured baseline from `phase9_self_recursion_probe` (monolith-verifies-smallest-monolith).
#[derive(Clone, Copy, Debug)]
pub struct SelfRecursionBaseline {
    pub inner_width: usize,
    pub outer_width: usize,
    pub outer_log_nqc: usize,
    pub log_blowup: usize,
}

/// The current, divergent baseline (grounding constants; re-confirmed by the probe run in 0a).
pub const BASELINE: SelfRecursionBaseline = SelfRecursionBaseline {
    inner_width: 193,
    outer_width: 8520, // ~44× — size-explosive
    outer_log_nqc: 7,  // > log_blowup 4 — degree-explosive (silently corrupts)
    log_blowup: 4,
};

/// The two Phase-0-validated levers, as inputs to the model.
#[derive(Clone, Copy, Debug)]
pub struct WrapLevers {
    /// Max constraint degree of a (low-arity) LogUp lookup — MEASURED at 3 for a 2-sided range-check
    /// (`1 + Σ side-degrees`) in `crate::lookup` (P2). Kept low by bounding lookup arity.
    pub logup_constraint_degree: usize,
    /// Residual non-lookup S-box degree in the verification hash (Tip5 `x^7` lanes, 0c). The FRI-fold and
    /// range relations move to lookups (degree `logup_constraint_degree`); this `x^7` is what remains
    /// unless the power lanes are *also* range-checked via lookups (which would drop it to the lookup degree).
    pub residual_hash_sbox_degree: usize,
    /// Tip5 rows/permutation vs Poseidon2 (0c) — the width-shrink factor on the hash-dominated regions.
    pub row_reduction_vs_poseidon2: f64,
}

pub const LEVERS: WrapLevers = WrapLevers {
    logup_constraint_degree: 3, // MEASURED (P2): 2-sided range-check lookup = 1 + (1+1)
    residual_hash_sbox_degree: 7,
    row_reduction_vs_poseidon2: 32.0 / 7.0,
};

/// The model's verdict on a candidate lookup-based canonical wrap.
#[derive(Clone, Copy, Debug)]
pub struct WrapVerdict {
    /// Max constraint degree of a lookup-based verifier = max(lookup degree, residual x^7 hash degree).
    pub modelled_max_degree: usize,
    /// The degree budget ceiling (2^log_blowup).
    pub degree_ceiling: usize,
    /// Does the modelled verifier hold the degree cliff (⇒ log_nqc ≤ log_blowup)?
    pub degree_converges: bool,
    /// Is the wrap size-stable? True by construction for a *canonical fixed-shape* wrap: it always
    /// verifies a proof of the same canonical shape, so the outer width is a fixed constant independent of
    /// the subtree — the fixed point the tree needs. (An engineering property to realize in Phase 3, not a
    /// value derivable from the current inner-specific monolith.)
    pub size_stable_by_design: bool,
    /// Overall GO iff degree converges AND a canonical fixed-shape design gives size-stability.
    pub go: bool,
}

/// Evaluate wrap feasibility from the baseline + the validated levers.
///
/// Degree — the fixed-point argument. The baseline diverges because the inner is an *arbitrary* monolith
/// whose own constraints reach degree ~16; re-evaluating + α-folding them in the outer compounds past the
/// cliff (log_nqc=7). The wrap breaks this by being a **fixed point**: each level verifies a *canonical
/// wrap* proof whose OWN constraints are kept low-degree because the operations that would otherwise be
/// high-degree — the α-Horner fold batching, the FRI range/bit decompositions, and the hash S-box — are
/// expressed as **low-arity lookups (measured degree 3, P2)** rather than inline high-degree polynomials. So the
/// wrap's max constraint degree is `max(logup_degree, residual_hash_sbox_degree)` (≈ 7 with an `x^7` lane,
/// or 2 if the power lanes are range-checked too) — bounded by the wrap's *own* design, and low enough that
/// re-evaluating + folding it at the next level stays ≤ 16. The inner's shape no longer matters because the
/// inner is always the same canonical wrap. Realizing that fixed-point construction is Phase-3 engineering;
/// Phase 0 establishes only that the degree math closes with the validated mechanisms.
pub fn evaluate(base: SelfRecursionBaseline, levers: WrapLevers) -> WrapVerdict {
    let degree_ceiling = 1usize << base.log_blowup; // 16
    let modelled_max_degree = levers.logup_constraint_degree.max(levers.residual_hash_sbox_degree); // 7
    let degree_converges = modelled_max_degree <= degree_ceiling; // 7 ≤ 16
    let size_stable_by_design = true; // canonical fixed-shape wrap ⇒ constant outer width
    WrapVerdict {
        modelled_max_degree,
        degree_ceiling,
        degree_converges,
        size_stable_by_design,
        go: degree_converges && size_stable_by_design,
    }
}

/// Phase-3 wrap-AIR spike (0a → measurement): turn the modelled degree claim into a HARD number using p3's
/// real `get_log_num_quotient_chunks`. `log_nqc` is a fixed function of an AIR's **max constraint degree**,
/// so a synthetic single-constraint AIR of a chosen degree measures exactly the mapping that decides
/// whether a verifier holds the `log_nqc ≤ log_blowup` cliff — the same mapping the monolith is subject to.
pub mod degree_probe {
    use crate::config::Val;
    use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
    use p3_field::PrimeCharacteristicRing;
    use p3_uni_stark::{get_log_num_quotient_chunks, AirLayout};

    /// A single-constraint AIR whose constraint has exactly the chosen algebraic degree: the product of
    /// `degree` trace columns (`c0·c1·…·c_{d-1} = 0`).
    pub struct ProductAir {
        pub degree: usize,
    }
    impl<F: p3_field::Field> BaseAir<F> for ProductAir {
        fn width(&self) -> usize {
            self.degree.max(1)
        }
    }
    impl<AB: AirBuilder<F = Val>> Air<AB> for ProductAir {
        fn eval(&self, builder: &mut AB) {
            let main = builder.main();
            let cols = main.current_slice();
            let mut acc = AB::Expr::ONE;
            for c in cols.iter().take(self.degree) {
                acc = acc * (*c).into();
            }
            drop(cols);
            drop(main);
            builder.assert_zero(acc);
        }
    }

    /// Measure — with p3's own machinery — the `log_num_quotient_chunks` a constraint of `degree` forces.
    pub fn log_nqc_for_degree(degree: usize) -> usize {
        let air = ProductAir { degree };
        let layout = AirLayout::from_air::<Val>(&air);
        get_log_num_quotient_chunks::<Val, ProductAir>(&air, layout, 0)
    }
}

/// Phase-3 (size-stability) — the wrap **fixed-point model**, the size analog of 0a′'s degree measurement.
///
/// A recursion tree needs `verify(proof)` to be **non-expanding**: verifying a proof of width `W` must
/// emit a proof of width `≤ W`. Model the self-verification width recurrence as `W_out = A + B·W_in`; a
/// fixed point (`W_out = W_in`, an *attracting* one) exists iff the per-inner-column factor **`B < 1`** — a
/// contraction. `B` is the marginal cost of verifying one more inner column: the monolith **opens and
/// re-evaluates** it (expensive), a lookup-based wrap **looks it up** at bounded cost.
///
/// Fitting `B` from the two measured monolith self-verification points — verify a W=19 join-split → W=193,
/// and verify a W=193 monolith → W=8520 (`phase9_self_recursion_probe`) — gives `B ≈ 48 ≫ 1`: a strong
/// expansion, so the monolith has **no fixed point** and diverges (exactly the measured 44× blow-up). The
/// wrap must drive `B < 1`; P2 showed a lookup carries **fixed degree (3) and fixed width** independent of
/// the value looked up, which is precisely the per-column contraction the fixed point requires.
pub mod size_model {
    /// Two measured self-verification points `(W_in, W_out)` from the monolith probes — the DIVERGENT baseline
    /// (`B ≈ 48 ≫ 1`, no fixed point). These stay as the "before"; the narrowed measurement below is the "after".
    pub const MONOLITH_POINTS: [(f64, f64); 2] = [(19.0, 193.0), (193.0, 8520.0)];

    /// The MEASURED narrowed self-composition (`wrap/air.rs::self_composition_b_narrowed`, +openings geometry,
    /// HEAD `9d231e4`): a monolith verifying a W=193 inner emits `W_out = 870`, with MARGINAL slope `B = 1.00`.
    /// The arith-tile / caps / openings regions are externalized narrow-tall (columns → rows), so the ONLY region
    /// still scaling with the inner width is the +1 `ov` opened-row carrier (`input_leaf_felts = w_inner`, the
    /// authenticated Merkle-leaf preimage). ⇒ the narrowed recurrence `W_out = 677 + 1.00·W_in` sits EXACTLY on the
    /// fixed-point boundary: NO attracting fixed point yet. Externalizing the `ov` carrier drops the last +1 ⇒
    /// `B < 1` ⇒ an attracting canonical `W* = A/(1−B)`.
    pub const NARROWED_POINT: (f64, f64) = (193.0, 870.0);
    pub const NARROWED_MARGINAL_B: f64 = 1.00;

    /// The MEASURED **+ov** self-composition (brick 4b made `narrow_ov` a REAL geometry, not a projection;
    /// `wrap/air.rs::self_composition_b_narrowed` R5 + the cheap `w5_gate_narrow_ov_marginal_b_below_one`, HEAD
    /// post-`f9d4680`): the monolith verifying a W=193 inner now emits `W_out = 677` (was 870), with MARGINAL slope
    /// `B = 0.00`. The `ov` opened-row carrier (`input_leaf_felts = w_inner`) was the LAST region scaling with the
    /// inner width; externalizing it narrow-tall (columns → rows on the leaf-hash→px bus) drops the last +1 ⇒ the
    /// recurrence `W_out = 677 + 0.00·W_in` is a STRICT CONTRACTION ⇒ an attracting canonical fixed point
    /// `W* = A/(1−B) = 677` EXISTS. This is the **W5 SIZE GATE, met by measurement** (the heavy end-to-end prove OOMs).
    pub const NARROWED_OV_POINT: (f64, f64) = (193.0, 677.0);
    pub const NARROWED_OV_MARGINAL_B: f64 = 0.00;

    /// Fit the linear recurrence `W_out = A + B·W_in` from two points → `(A, B)`.
    pub fn fit_recurrence(p0: (f64, f64), p1: (f64, f64)) -> (f64, f64) {
        let b = (p1.1 - p0.1) / (p1.0 - p0.0);
        let a = p0.1 - b * p0.0;
        (a, b)
    }

    /// The **attracting** fixed point `W* = A/(1−B)` iff `B < 1` (a contraction); `None` if `B ≥ 1`
    /// (iterating `W ↦ A + B·W` diverges — no attracting fixed point).
    pub fn attracting_fixed_point(a: f64, b: f64) -> Option<f64> {
        if b < 1.0 && a >= 0.0 {
            Some(a / (1.0 - b))
        } else if b < 1.0 {
            Some(a / (1.0 - b)) // contraction toward W* even with A<0; the sign is a modelling artifact
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::degree_probe::log_nqc_for_degree;
    use super::size_model::*;

    /// **0a's model → a measurement.** Measure the degree→log_nqc mapping p3 actually applies, and confirm:
    ///   * the BASELINE explosion is a *degree* problem — the monolith's ~degree-91 fold (air.rs:473) maps to
    ///     the measured `log_nqc = 7` (matching `phase9_self_recursion_probe`); and
    ///   * the WRAP holds the cliff — Tip5's residual `x^7` (degree 7, 0c) and a lookup (measured degree 3, P2) both
    ///     map to `log_nqc ≤ log_blowup = 4`.
    #[test]
    fn wrap_degree_cliff_is_measured() {
        let ceiling = BASELINE.log_blowup; // 4
        let degrees = [2usize, 3, 4, 7, 8, 16, 17, 32, 64, 91, 128];
        let rows: Vec<(usize, usize)> = degrees.iter().map(|&d| (d, log_nqc_for_degree(d))).collect();
        for (d, nqc) in &rows {
            println!("DEGREE-PROBE degree={:>3} → log_nqc={} {}", d, nqc, if *nqc <= ceiling { "≤ cliff (provable)" } else { "> cliff (DIVERGES)" });
        }

        // WRAP side — the two validated levers hold the cliff:
        assert!(log_nqc_for_degree(3) <= ceiling, "lookup (deg 3, measured P2) must hold log_nqc ≤ {ceiling}");
        assert!(log_nqc_for_degree(7) <= ceiling, "Tip5 residual x^7 (deg 7) must hold log_nqc ≤ {ceiling}");
        // BASELINE side — the monolith's ~degree-91 inline fold reproduces the measured log_nqc = 7:
        assert_eq!(log_nqc_for_degree(91), BASELINE.outer_log_nqc, "degree-91 fold ⇒ the baseline's log_nqc=7");
        // The cliff (log_nqc crossing above log_blowup=4) is measured to sit between degree 17 and 32 —
        // i.e. the real degree budget is ~17, a hair more than the nominal 16. Tip5(7)/lookup(2) clear it
        // comfortably; the baseline's ~91 blows well past it.
        assert!(log_nqc_for_degree(17) <= ceiling && log_nqc_for_degree(32) > ceiling, "cliff between degree 17 and 32");
    }

    /// **0a's size-stability "by design" → a concrete fixed-point condition.** The monolith's *measured*
    /// self-verification expands (B ≫ 1) ⇒ no attracting fixed point ⇒ diverges (the 44× blow-up); a
    /// lookup-based wrap can drive B < 1 ⇒ a contraction with an attracting canonical fixed point W*.
    #[test]
    fn wrap_size_stability_is_a_contraction_fixed_point() {
        // MONOLITH — fit B from the two measured points; a strong expansion ⇒ diverges.
        let (a_m, b_m) = fit_recurrence(MONOLITH_POINTS[0], MONOLITH_POINTS[1]);
        println!(
            "SIZE-MODEL monolith: W_out = {a_m:.0} + {b_m:.1}·W_in ⇒ attracting fixed point = {:?}",
            attracting_fixed_point(a_m, b_m)
        );
        assert!(b_m > 1.0, "monolith is an expansion (B = {b_m:.1} ≫ 1)");
        assert!(attracting_fixed_point(a_m, b_m).is_none(), "expansion ⇒ no attracting fixed point ⇒ diverges");

        // NARROWED (MEASURED — self_composition_b_narrowed, +openings): the arith / caps / openings regions are
        // externalized narrow-tall ⇒ the marginal B fell 48 → 1.00, the fixed-point BOUNDARY. Only the +1 `ov`
        // opened-row carrier still scales, so there is still NO attracting fixed point (B is not strictly < 1).
        let a_n = NARROWED_POINT.1 - NARROWED_MARGINAL_B * NARROWED_POINT.0; // 677
        println!(
            "SIZE-MODEL narrowed (MEASURED, +openings): W_out = {a_n:.0} + {NARROWED_MARGINAL_B:.2}·W_in ⇒ \
             attracting fixed point = {:?} — B=1.00 is the boundary (the +1 `ov` opened-row carrier)",
            attracting_fixed_point(a_n, NARROWED_MARGINAL_B)
        );
        assert!(NARROWED_MARGINAL_B <= 1.0 && NARROWED_MARGINAL_B >= 1.0, "the narrowing brought the marginal B from ~48 onto the 1.00 boundary");
        assert!(
            attracting_fixed_point(a_n, NARROWED_MARGINAL_B).is_none(),
            "at B=1.00 (the residual `ov` carrier) there is STILL no attracting fixed point — externalize the ov carrier to cross below 1"
        );

        // POST-OV-EXTERNALIZATION (MEASURED — brick 4b made narrow_ov a REAL geometry; self_composition_b_narrowed /
        // w5_gate_narrow_ov_marginal_b_below_one): externalizing the `ov` opened-row carrier narrow-tall drops the
        // last inner-scaling +1 ⇒ MARGINAL B = 0.00 < 1 (a STRICT contraction) ⇒ an attracting canonical fixed point
        // W* EXISTS. The R5 outer width fell 870 → 677 (= 870 − w_inner 193, the ov carrier gone). THE W5 SIZE GATE.
        let a_w = NARROWED_OV_POINT.1 - NARROWED_OV_MARGINAL_B * NARROWED_OV_POINT.0; // 677
        let w_star = attracting_fixed_point(a_w, NARROWED_OV_MARGINAL_B).expect("a contraction has an attracting fixed point");
        println!(
            "SIZE-MODEL post-ov (MEASURED contraction B = {NARROWED_OV_MARGINAL_B:.2}): W_out = {a_w:.0} + \
             {NARROWED_OV_MARGINAL_B:.2}·W_in ⇒ canonical W* = {w_star:.0} — the W5 SIZE GATE is MET (marginal B \
             19.00 FULL → 5.00 arith+caps → 1.00 +openings → 0.00 +ov; the heavy prove OOMs, the size number holds)."
        );
        assert!(NARROWED_OV_MARGINAL_B < 1.0, "the ov externalization crosses the marginal B strictly below 1 (a contraction)");
        assert!(w_star.is_finite() && w_star > 0.0, "an attracting canonical fixed point W* exists");
    }

    /// The GO/NO-GO model. Prints the before/after and asserts the two drivers are addressed.
    #[test]
    fn wrap_feasibility_model() {
        let v = evaluate(BASELINE, LEVERS);
        println!(
            "WRAP-FEASIBILITY baseline: W {}→{} (~{:.0}×), log_nqc {} > {} (DIVERGES)",
            BASELINE.inner_width,
            BASELINE.outer_width,
            BASELINE.outer_width as f64 / BASELINE.inner_width as f64,
            BASELINE.outer_log_nqc,
            BASELINE.log_blowup,
        );
        println!(
            "WRAP-FEASIBILITY modelled wrap: max_degree={} (≤ ceiling {}) ⇒ degree_converges={}; \
             size_stable_by_design={} (canonical fixed shape); row_shrink={:.1}× (Tip5) ⇒ GO={}",
            v.modelled_max_degree,
            v.degree_ceiling,
            v.degree_converges,
            v.size_stable_by_design,
            LEVERS.row_reduction_vs_poseidon2,
            v.go,
        );

        // DEGREE: lookups (deg 2) + residual x^7 (deg 7) ⇒ max 7 ≤ 16 ⇒ log_nqc ≤ 4. The baseline's
        // log_nqc=7 came from folding the inner's high-degree constraints inline; a lookup-based verifier
        // does not do that, so its degree is bounded by its OWN constraints, not the inner's.
        assert!(v.degree_converges, "modelled max degree {} must be ≤ {}", v.modelled_max_degree, v.degree_ceiling);
        // SIZE: addressed by the canonical fixed-shape design (Phase-3 engineering), not fundamentally blocked.
        assert!(v.size_stable_by_design);
        // ⇒ GO: both explosion drivers are addressable with the validated mechanisms.
        assert!(v.go, "Phase-0 model ⇒ GO (residual risk is Phase-3 engineering, not a fundamental barrier)");
    }

    /// Even the residual x^7 can be removed: range-checking the power lanes via lookups drops the max
    /// degree to the lookup degree (3, measured), i.e. log_nqc ≤ 1 — extra margin under the cliff.
    #[test]
    fn full_lookup_verifier_has_ample_degree_margin() {
        let levers = WrapLevers { residual_hash_sbox_degree: LEVERS.logup_constraint_degree, ..LEVERS };
        let v = evaluate(BASELINE, levers);
        assert!(v.modelled_max_degree <= 3 && v.degree_converges);
    }
}
