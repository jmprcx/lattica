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

pub mod prover; // P2b — the two-round lookup prover skeleton (real challenger + PCS)

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

    /// (3) **The degree fact 0a needs — MEASURED via p3-lookup's own `constraint_degree`.** A LogUp
    /// constraint's degree is `1 + Σ(side element-degrees)` (the shared denominator spans all sides).
    /// For a 2-sided (query + table) range-check lookup with degree-1 elements that is `1 + (1+1) = 3` —
    /// **not 2**, correcting the earlier structural estimate. The general rule matters for the wrap: a
    /// lookup must be kept **low-arity** (few sides) to stay under the degree budget — e.g. a k-way fold
    /// lookup is degree `1 + k`, so the α-fold must be chunked into small-arity lookups (mirroring the
    /// existing `FOLD_CHUNK=7`). Degree 3 still clears the cliff comfortably (`log_nqc ≤ 1`, see 0a′).
    #[test]
    fn logup_constraint_degree_measured() {
        use p3_lookup::LookupProtocol;
        let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(&RangeCheckAir);
        let lookup = lookups.iter().next().expect("one lookup");
        let deg = LogUpGadget::new().constraint_degree(lookup);
        println!("LOGUP-DEGREE 2-sided range-check lookup: constraint_degree = {deg} (= 1 + Σ side-degrees)");
        assert_eq!(deg, 3, "a 2-sided degree-1 lookup is degree 3 (corrects the modelled '2')");
    }

    /// (4) **The argument semantics — validated with p3-lookup's ground-truth oracle `check_lookups`.**
    /// A balanced trace passes the multiset-balance check; a tampered one is caught (it panics on the
    /// imbalance). Together with (1)/(2) — the aux-trace terminal agreeing — this validates the *complete*
    /// lookup argument at the constraint level. (Committing the aux trace through FRI is the remaining
    /// mechanical Phase-2 plumbing; the novel logic is validated here.)
    #[test]
    fn check_lookups_accepts_balanced_and_catches_tampered() {
        use p3_lookup::debug_util::{check_lookups, LookupDebugInstance};
        let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(&RangeCheckAir);
        let lookup_slice: Vec<_> = lookups.iter().cloned().collect();
        let no_pre: Option<RowMajorMatrix<Val>> = None;

        // balanced ⇒ check passes.
        let main = balanced_main(8);
        check_lookups(&[LookupDebugInstance {
            main_trace: &main,
            preprocessed_trace: &no_pre,
            public_values: &[],
            lookups: &lookup_slice,
            permutation_challenges: &[],
        }]);

        // tampered (table side no longer matches the query) ⇒ check_lookups panics on the imbalance.
        let mut bad = balanced_main(8);
        bad.values[3 * 3 + 1] = Val::from_u64(0xDEAD);
        let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            check_lookups(&[LookupDebugInstance {
                main_trace: &bad,
                preprocessed_trace: &no_pre,
                public_values: &[],
                lookups: &lookup_slice,
                permutation_challenges: &[],
            }]);
        }));
        assert!(caught.is_err(), "check_lookups must catch a tampered (imbalanced) lookup");
    }
}
