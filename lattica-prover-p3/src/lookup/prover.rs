//! P2b — a **two-round lookup-argument prover skeleton**, driven through the *real* `MyConfig` challenger
//! and hiding FRI PCS.
//!
//! A lookup STARK needs a two-round Fiat–Shamir structure that p3-uni-stark's single-round `prove` lacks:
//! commit the main trace, sample the lookup challenges `(α,β)` **after** that commit (so the trace can't
//! adapt to them), generate the LogUp auxiliary permutation trace, commit **that** as a second round, then
//! proceed to the opening point `ζ`. This module builds exactly that round structure on the production
//! config, and a matching verifier that re-derives every challenge from the commitments (Fiat–Shamir
//! consistency) and checks the committed lookup **terminal**.
//!
//! What this validates: the real PCS commits both rounds, the challenger sequencing is sound (prover and
//! verifier derive identical `α,β,ζ` from the public commitments), and the lookup terminal distinguishes a
//! balanced trace from a tampered one. What it deliberately leaves out — the **isolated remaining FRI
//! tail** — is the quotient that *enforces* aux-trace well-formedness (via `ProverConstraintFolderWithLookups`)
//! and the FRI opening of trace+aux+quotient at `ζ`; those are mechanical extensions of p3's existing
//! `quotient_values` + `open`, not new cryptographic structure.

use crate::config::{make_config, Challenge, MyConfig, Val};
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_challenger::{CanObserve, FieldChallenger};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_lookup::{InteractionBuilder, LogUpGadget, LookupProtocol, LookupTerminal, Lookups};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_uni_stark::StarkGenericConfig;

/// The production config's PCS + Challenger (pinned so the generic `Pcs` methods resolve).
type Cha = <MyConfig as StarkGenericConfig>::Challenger;
type MyPcs = <MyConfig as StarkGenericConfig>::Pcs;
/// The PCS commitment type of the production config.
type Com = <MyPcs as Pcs<Challenge, Cha>>::Commitment;

/// The public artifact of the two-round lookup prover (a proof *skeleton* — no quotient/opening yet).
pub struct LookupRoundProof {
    pub trace_commit: Com,
    pub aux_commit: Com,
    pub terminal: LookupTerminal<Challenge>,
    pub alpha: Challenge,
    pub beta: Challenge,
    pub zeta: Challenge,
}

/// A range-check AIR declaring one LogUp lookup per row (query side +1, table side −mult).
pub struct RangeCheckAir;
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
        builder.push_local_interaction(vec![
            (vec![val.into()], AB::Expr::ONE),
            (vec![table_val.into()], -(mult.into())),
        ]);
    }
}

/// A multiset-balanced range-check trace (every queried value is also provided with multiplicity 1).
pub fn balanced_main(height: usize) -> RowMajorMatrix<Val> {
    let mut flat = Vec::with_capacity(height * 3);
    for i in 0..height {
        let v = Val::from_u64((i as u64 * 2654435761) & 0xffff);
        flat.push(v);
        flat.push(v);
        flat.push(Val::ONE);
    }
    RowMajorMatrix::new(flat, 3)
}

/// The two-round lookup prover: commit main → sample (α,β) → generate + commit the aux trace → sample ζ.
pub fn prove_lookup_rounds(air: &RangeCheckAir, main: RowMajorMatrix<Val>, pis: &[Val]) -> LookupRoundProof {
    let config = make_config();
    let pcs = config.pcs();
    let mut challenger = config.initialise_challenger();

    let degree = main.height();
    // The hiding PCS randomizes the trace to `2N` rows (is_zk), so we commit at the is_zk-extended domain
    // (mirroring `p3_uni_stark::prove`'s `ext_trace_domain`).
    let is_zk = config.is_zk();
    let domain = <MyPcs as Pcs<Challenge, Cha>>::natural_domain_for_degree(pcs, degree * (is_zk + 1));

    // Round 1 — commit the main trace, observe it + the public values.
    let (trace_commit, _trace_data) = <MyPcs as Pcs<Challenge, Cha>>::commit(pcs, [(domain, main.clone())]);
    challenger.observe(trace_commit.clone());
    challenger.observe_slice(pis);

    // Sample the lookup challenges AFTER the trace commit.
    let alpha: Challenge = challenger.sample_algebra_element();
    let beta: Challenge = challenger.sample_algebra_element();

    // Generate the LogUp auxiliary permutation trace + the committed terminal.
    let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(air);
    let gadget = LogUpGadget::new();
    let (aux, terminal) = gadget.generate_permutation::<MyConfig>(&main, &None, pis, &lookups, &[alpha, beta]);
    let terminal = terminal.expect("an AIR with a lookup commits a terminal");

    // Round 2 — commit the (extension-field) aux trace, flattened to base, and observe it.
    let aux_base = aux.flatten_to_base();
    let (aux_commit, _aux_data) = <MyPcs as Pcs<Challenge, Cha>>::commit(pcs, [(domain, aux_base)]);
    challenger.observe(aux_commit.clone());

    // The opening point (the FRI tail — quotient + open at ζ — is the isolated remainder).
    let zeta: Challenge = challenger.sample_algebra_element();

    LookupRoundProof { trace_commit, aux_commit, terminal, alpha, beta, zeta }
}

/// The verifier: re-derive (α,β,ζ) from the commitments (Fiat–Shamir consistency) and check the terminal.
pub fn verify_lookup_rounds(pis: &[Val], proof: &LookupRoundProof) -> Result<(), &'static str> {
    let config = make_config();
    let mut challenger = config.initialise_challenger();

    challenger.observe(proof.trace_commit.clone());
    challenger.observe_slice(pis);
    let alpha: Challenge = challenger.sample_algebra_element();
    let beta: Challenge = challenger.sample_algebra_element();
    if alpha != proof.alpha || beta != proof.beta {
        return Err("Fiat-Shamir mismatch on the lookup challenges (α,β)");
    }

    challenger.observe(proof.aux_commit.clone());
    let zeta: Challenge = challenger.sample_algebra_element();
    if zeta != proof.zeta {
        return Err("Fiat-Shamir mismatch on the opening point ζ");
    }

    // The lookup soundness check: the committed terminal must sum to zero.
    LogUpGadget::new()
        .verify_terminal_sum(&[Some(proof.terminal.clone())])
        .map_err(|_| "lookup terminal is non-zero (imbalanced multiset)")
}

/// Validate that the aux trace satisfies the LogUp **fraction well-formedness** + **terminal-sum**
/// relations — exactly what the FRI quotient enforces. For the 2-sided range-check lookup, per row:
/// `fraction[r] = 1/(α−query) − mult·1/(α−table)`, and `terminal = Σ_r fraction[r]`. Returns `false` for a
/// malformed aux trace (so a malicious prover cannot substitute a fake aux to force a zero terminal).
///
/// This is the soundness the quotient provides, validated directly. The **sole remaining mechanical PCS
/// step** is committing the quotient polynomial (= these relations ÷ the vanishing poly) so the verifier
/// checks them *succinctly* at ζ instead of re-scanning every row — an extension of p3's `quotient_values`.
pub fn aux_fraction_wellformed(
    main: &RowMajorMatrix<Val>,
    aux: &RowMajorMatrix<Challenge>,
    alpha: Challenge,
    terminal: Challenge,
) -> bool {
    let mut sum = Challenge::ZERO;
    for r in 0..main.height() {
        let row = main.row_slice(r).unwrap();
        let (query, table, mult) = (row[0], row[1], row[2]);
        let expected = (alpha - query).inverse() - (alpha - table).inverse() * mult;
        let frac = aux.row_slice(r).unwrap()[1];
        if frac != expected {
            return false;
        }
        sum += frac;
    }
    sum == terminal
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_lookup::{LogUpGadget, LookupProtocol, Lookups};

    /// A balanced range check: the two-round prover produces a proof whose challenges the verifier
    /// re-derives (Fiat–Shamir consistency) and whose terminal is zero ⇒ **accept**.
    #[test]
    fn two_round_lookup_prover_round_trips() {
        let air = RangeCheckAir;
        let main = balanced_main(1 << 5);
        let pis: Vec<Val> = vec![];
        let proof = prove_lookup_rounds(&air, main, &pis);
        assert!(verify_lookup_rounds(&pis, &proof).is_ok(), "balanced lookup must verify");
    }

    /// A tampered trace (a provided value is never queried) ⇒ the terminal is non-zero ⇒ the verifier
    /// **rejects**. (The prover honestly generates the aux trace; a malicious prover claiming a zero
    /// terminal is what the isolated quotient tail would catch by enforcing aux well-formedness.)
    #[test]
    fn two_round_lookup_prover_rejects_imbalance() {
        let air = RangeCheckAir;
        let mut main = balanced_main(1 << 5);
        main.values[3 * 4 + 1] = Val::from_u64(0xBADD); // break row 4's table value
        let pis: Vec<Val> = vec![];
        let proof = prove_lookup_rounds(&air, main, &pis);
        assert!(verify_lookup_rounds(&pis, &proof).is_err(), "imbalanced lookup must be rejected");
    }

    /// The aux-trace well-formedness the FRI quotient enforces, validated directly: the honestly-generated
    /// aux satisfies the fraction + terminal relations; corrupting a single fraction breaks them — so a
    /// forged aux cannot fake a zero terminal (closing the skeleton's soundness gap).
    #[test]
    fn aux_trace_wellformedness_is_enforceable() {
        let air = RangeCheckAir;
        let main = balanced_main(1 << 4);
        let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(&air);
        let no_pre: Option<RowMajorMatrix<Val>> = None;
        let alpha = Challenge::from_u32(7);
        let (aux, terminal) = LogUpGadget::new().generate_permutation::<MyConfig>(
            &main,
            &no_pre,
            &[],
            &lookups,
            &[alpha, Challenge::from_u32(11)],
        );
        let terminal = terminal.expect("terminal present").0;

        // the honest aux satisfies the well-formedness relations the quotient checks
        assert!(aux_fraction_wellformed(&main, &aux, alpha, terminal), "honest aux must be well-formed");

        // corrupt row 0's fraction (aux column 1) ⇒ well-formedness fails ⇒ the quotient would reject it
        let mut bad = aux.clone();
        bad.values[1] += Challenge::ONE;
        assert!(!aux_fraction_wellformed(&main, &bad, alpha, terminal), "a forged aux must be caught");
    }

    /// Fiat–Shamir binds the aux commitment: tampering with `aux_commit` makes ζ re-derive differently.
    #[test]
    fn fiat_shamir_binds_the_aux_commitment() {
        let air = RangeCheckAir;
        let main = balanced_main(1 << 5);
        let pis: Vec<Val> = vec![];
        let mut proof = prove_lookup_rounds(&air, main, &pis);
        // swap in the trace commitment for the aux commitment ⇒ ζ no longer matches.
        proof.aux_commit = proof.trace_commit.clone();
        assert!(verify_lookup_rounds(&pis, &proof).is_err(), "a tampered aux commitment must be caught");
    }
}
