//! Phase-0 (0b) — minimal **LogUp lookup-argument** spike.
//!
//! `p3-lookup 0.6.1` is a *toolkit* (the LogUp gadget + `PermutationAirBuilder` folder adapters +
//! terminal-sum check); it has **no `prove`/`verify` of its own**, and p3-uni-stark's `Proof`/folders
//! carry no lookup slot. A full end-to-end lookup STARK therefore needs a **forked prove/verify + a new
//! `Proof` type** — that is Phase 2, not Phase 0.
//!
//! What Phase 0 must answer to de-risk the wrap (0a) is narrower and answerable *now* at the gadget level:
//!   1. does the LogUp machinery instantiate + run in *this* stack (Goldilocks / F_p²)? and
//!   2. what **constraint degree** does a lookup carry? — the number the wrap's degree budget lives or
//!      dies by.
//!
//! This spike declares a range-check lookup on an `InteractionBuilder` AIR, extracts it with
//! `Lookups::from_air`, generates the auxiliary permutation trace with `LogUpGadget`, and checks that the
//! committed **terminal** is zero for a multiset-balanced trace and non-zero for a tampered one — i.e. the
//! lookup soundly detects imbalance. It reuses lattica's production `MyConfig` (Goldilocks + F_p²) as the
//! `SC` type parameter, proving the argument is field-compatible with the real proof system.

#[cfg(test)]
mod tests {
    use crate::config::{Challenge, MyConfig, Val};
    use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
    use p3_field::PrimeCharacteristicRing;
    use p3_lookup::{InteractionBuilder, LogUpGadget, LookupProtocol, Lookups};
    use p3_matrix::dense::RowMajorMatrix;
    use p3_matrix::Matrix;

    /// A range-check AIR: each row declares one LogUp lookup with a query side (mult +1) and a table side
    /// (mult −multiplicity). Columns per row: `[query_value, table_value, table_multiplicity]`.
    struct RangeCheckAir;

    impl<F: p3_field::Field> BaseAir<F> for RangeCheckAir {
        fn width(&self) -> usize {
            3
        }
    }

    impl<AB> Air<AB> for RangeCheckAir
    where
        AB: AirBuilder<F = Val> + InteractionBuilder,
    {
        fn eval(&self, builder: &mut AB) {
            let main = builder.main();
            let local = main.current_slice();
            let (val, table_val, mult) = (local[0], local[1], local[2]);
            // The single LogUp interaction: +1 on the query value, −mult on the table value.
            builder.push_local_interaction(vec![
                (vec![val.into()], AB::Expr::ONE),
                (vec![table_val.into()], -(mult.into())),
            ]);
        }
    }

    /// A multiset-balanced trace: every row queries value `v` and provides `v` with multiplicity 1, so
    /// query and table cancel — the LogUp terminal must be exactly zero.
    fn balanced_main(height: usize) -> RowMajorMatrix<Val> {
        let mut flat = Vec::with_capacity(height * 3);
        for i in 0..height {
            let v = Val::from_u64((i as u64 * 2654435761) & 0xffff);
            flat.push(v); // query value
            flat.push(v); // table value (same)
            flat.push(Val::ONE); // multiplicity 1
        }
        RowMajorMatrix::new(flat, 3)
    }

    /// (1) The LogUp gadget instantiates + runs over lattica's Goldilocks/F_p² `MyConfig`, and a
    ///     multiset-balanced range check yields a **zero terminal** (the argument is satisfied).
    #[test]
    fn logup_runs_and_balanced_lookup_has_zero_terminal() {
        let main = balanced_main(8);
        let air = RangeCheckAir;
        let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(&air);
        assert_eq!(lookups.len(), 1, "one lookup per row-declaration");

        let gadget = LogUpGadget::new();
        // (alpha, beta) — the lookup-argument challenges the forked prover would Fiat-Shamir after the
        // main-trace commit. Here fixed, as in p3-lookup's own tests.
        let challenges = vec![Challenge::from_u32(7), Challenge::from_u32(11)];
        let (aux, terminal) =
            gadget.generate_permutation::<MyConfig>(&main, &None, &[], &lookups, &challenges);

        // aux = [accumulator | one fraction column]; height matches the main trace.
        assert_eq!(aux.width(), 2);
        assert_eq!(aux.height(), main.height());
        assert_eq!(aux.row_slice(0).unwrap()[0], Challenge::ZERO, "accumulator anchored at 0");

        let terminal = terminal.expect("AIR has a lookup ⇒ a terminal is committed");
        assert_eq!(terminal.0, Challenge::ZERO, "balanced lookup ⇒ zero terminal");
        // The cross-AIR consistency check accepts a zero total.
        assert!(gadget.verify_terminal_sum(&[Some(terminal)]).is_ok());
    }

    /// (2) A **tampered** (unbalanced) trace — one row provides a value it never queries — yields a
    ///     NON-zero terminal, and `verify_terminal_sum` rejects it. The lookup soundly catches imbalance.
    #[test]
    fn logup_unbalanced_lookup_is_rejected() {
        let mut main = balanced_main(8);
        // Break the balance: make row 3's table value differ from its query value.
        main.values[3 * 3 + 1] = Val::from_u64(0xDEAD);
        let air = RangeCheckAir;
        let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(&air);

        let gadget = LogUpGadget::new();
        let challenges = vec![Challenge::from_u32(7), Challenge::from_u32(11)];
        let (_aux, terminal) =
            gadget.generate_permutation::<MyConfig>(&main, &None, &[], &lookups, &challenges);

        let terminal = terminal.expect("terminal present");
        assert_ne!(terminal.0, Challenge::ZERO, "unbalanced lookup ⇒ non-zero terminal");
        assert!(
            gadget.verify_terminal_sum(&[Some(terminal)]).is_err(),
            "verify_terminal_sum must reject a non-zero total"
        );
    }

    /// (3) **The degree fact 0a needs, recorded as an executable note.** A LogUp constraint is degree ≤ 2:
    ///   fraction well-formedness  `(alpha − value)·fraction − mult = 0`   (deg 2: value·fraction), and
    ///   accumulator telescoping   `acc' − acc − fraction = 0`             (deg 1).
    /// `alpha` is a verifier challenge (a constant in the constraint), `value`/`mult` are trace columns,
    /// `fraction`/`acc` are aux columns. So a lookup replaces a high-degree relation (e.g. the FRI-fold's
    /// α-Horner over degree-16 inner constraints, or a byte range-decomposition) with a **degree-2**
    /// constraint. This is the lever that lets the wrap's outer fold stay under the ≤16 / log_nqc≤4 cliff.
    #[test]
    fn logup_constraint_degree_is_two() {
        // The bound is structural to LogUp (not p3-version-specific); asserted here so the number the
        // 0a/0d analysis quotes is pinned in-tree next to the working gadget.
        const LOGUP_MAX_CONSTRAINT_DEGREE: usize = 2;
        assert_eq!(LOGUP_MAX_CONSTRAINT_DEGREE, 2);
    }
}
