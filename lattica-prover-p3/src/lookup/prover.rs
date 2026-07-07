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
//! balanced trace from a tampered one.
//!
//! **W1.2** extends the skeleton with the constraint **quotient**: `prove_lookup_with_quotient` folds the
//! batched (base AIR + LogUp) constraints across the quotient domain, divides by `Z_H`, and commits the
//! quotient (`lookup_quotient_values` + `commit_quotient`). **W1.3** adds the **ζ-opening** of trace + aux +
//! quotient (one batched FRI proof) and the matching verifier (`prove_lookup` / `verify_lookup`) — the OOD
//! identity `folded(ζ)·Z_H(ζ)^{-1} = Q(ζ)` plus the terminal check — completing the **W1 milestone**: a
//! lookup AIR that proves and verifies end to end, rejecting a tampered opening, an imbalance, or a forged
//! aux. (ZK note: hiding is retained via the salted-Merkle + random-column PCS; the extra opt-randomization
//! FRI-batch poly is omitted — ZK-only, not soundness — the sole deferred hardening.)

use crate::config::{make_config, Challenge, MyConfig, Val};
use p3_air::symbolic::{AirLayout, ConstraintLayout};
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_challenger::{CanObserve, FieldChallenger};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{BasedVectorSpace, ExtensionField, Field, PrimeCharacteristicRing};
use p3_lookup::{
    InteractionBuilder, InteractionSymbolicBuilder, LogUpGadget, LookupProtocol, LookupTerminal, Lookups,
};
use p3_air::RowWindow;
use p3_lookup::folder::VerifierConstraintFolderWithLookups;
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_matrix::stack::VerticalPair;
use p3_matrix::Matrix;
use p3_uni_stark::{recompose_quotient_from_chunks, StarkGenericConfig, VerifierConstraintFolder};

/// The production config's PCS + Challenger (pinned so the generic `Pcs` methods resolve).
type Cha = <MyConfig as StarkGenericConfig>::Challenger;
type MyPcs = <MyConfig as StarkGenericConfig>::Pcs;
/// The PCS commitment type of the production config.
type Com = <MyPcs as Pcs<Challenge, Cha>>::Commitment;
/// The PCS polynomial domain of the production config (a two-adic multiplicative coset).
type Dom = <MyPcs as Pcs<Challenge, Cha>>::Domain;
/// The batched FRI opening proof type of the production PCS.
type PcsProof = <MyPcs as Pcs<Challenge, Cha>>::Proof;

/// The AIR capabilities the lookup prover needs: a base AIR (width), symbolic evaluation (for the combined
/// constraint layout + lookup extraction), and folding through the lookup-aware verifier folder (shared by
/// the quotient and the ζ-check). Any interaction AIR generic over its builder satisfies this via the blanket
/// impl below. (Not yet threaded: public values + periodic columns — see `batched_constraints_at_point`.)
pub trait LookupAir:
    BaseAir<Val>
    + Air<InteractionSymbolicBuilder<Val, Challenge>>
    + for<'a> Air<VerifierConstraintFolderWithLookups<'a, MyConfig>>
{
}
impl<A> LookupAir for A where
    A: BaseAir<Val>
        + Air<InteractionSymbolicBuilder<Val, Challenge>>
        + for<'a> Air<VerifierConstraintFolderWithLookups<'a, MyConfig>>
{
}

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

/// W1.1 — the **combined** (AIR-base + LogUp-lookup) constraint layout + `log_num_quotient_chunks`, sized
/// over the FULL constraint set (base `assert_zero`s **plus** the lookup fraction/accumulator constraints).
/// p3's `get_log_num_quotient_chunks` runs only `air.eval` and so misses the lookup constraints — using it
/// would make the alpha-power layout and the quotient domain too small. The forked quotient (W1.2) must use
/// THIS layout + degree. Emission order is `air.eval` then `gadget.eval_all` (matched by prover + verifier).
pub fn combined_constraint_layout<A: LookupAir>(
    air: &A,
    lookups: &Lookups<Val>,
    is_zk: usize,
) -> (ConstraintLayout, usize) {
    let layout = AirLayout {
        preprocessed_width: 0,
        main_width: BaseAir::<Val>::width(air),
        num_public_values: 0,
        permutation_width: lookups.len() + 1, // accumulator + one fraction column per lookup
        num_permutation_challenges: 2,        // LogUp (α_L, β)
        num_permutation_values: 1,            // the committed terminal
        num_periodic_columns: 0,
    };
    let mut isb = InteractionSymbolicBuilder::<Val, Challenge>::new(layout);
    air.eval(&mut isb);
    LogUpGadget::new().eval_all(&mut isb, lookups);

    let clayout = isb.constraint_layout();
    let max_deg = isb
        .base_constraints()
        .iter()
        .map(|c| c.degree_multiple())
        .chain(isb.extension_constraints().iter().map(|c| c.degree_multiple()))
        .max()
        .unwrap_or(0);
    let constraint_degree = (max_deg + is_zk).max(2);
    let log_nqc = (constraint_degree - 1).next_power_of_two().ilog2() as usize;
    (clayout, log_nqc)
}

/// W1.2 core — evaluate the batched (base AIR + LogUp lookup) constraints at a single point via the **real**
/// `VerifierConstraintFolderWithLookups` (Horner batching by `alpha`). The forked quotient (per
/// quotient-domain point, `÷ Z_H`) and the verifier's ζ-check both call this, so prover/verifier consistency
/// is automatic — no `decompose_alpha` / packed-aux reconstruction, and no risk of the two sides folding
/// constraints differently (the classic FRI-fork bug). Values are in the extension field.
#[allow(clippy::too_many_arguments)]
pub fn batched_constraints_at_point<A: LookupAir>(
    air: &A,
    lookups: &Lookups<Val>,
    trace_local: &[Challenge],
    trace_next: &[Challenge],
    aux_local: &[Challenge],
    aux_next: &[Challenge],
    is_first_row: Challenge,
    is_last_row: Challenge,
    is_transition: Challenge,
    alpha: Challenge,
    lookup_challenges: &[Challenge], // [α_L, β]
    permutation_values: &[Challenge], // [terminal]
) -> Challenge {
    let empty: &[Challenge] = &[];
    let main = VerticalPair::new(
        RowMajorMatrixView::new_row(trace_local),
        RowMajorMatrixView::new_row(trace_next),
    );
    let preprocessed = VerticalPair::new(RowMajorMatrixView::new(empty, 0), RowMajorMatrixView::new(empty, 0));
    let preprocessed_window = RowWindow::from_two_rows(empty, empty);
    let inner = VerifierConstraintFolder::<MyConfig> {
        main,
        preprocessed,
        preprocessed_window,
        periodic_values: empty,
        public_values: &[],
        is_first_row,
        is_last_row,
        is_transition,
        alpha,
        accumulator: Challenge::ZERO,
    };
    let permutation = VerticalPair::new(
        RowMajorMatrixView::new_row(aux_local),
        RowMajorMatrixView::new_row(aux_next),
    );
    let mut folder = VerifierConstraintFolderWithLookups {
        inner,
        permutation,
        permutation_challenges: lookup_challenges,
        permutation_values,
    };
    air.eval(&mut folder); // base AIR constraints + drains the interaction into the lookup folder
    LogUpGadget::new().eval_all(&mut folder, lookups); // the LogUp fraction/accumulator constraints
    folder.inner.accumulator
}

/// The public artifact of the **W1.2 lookup prover** — the two-round skeleton **plus** a committed
/// constraint quotient. Compared with `LookupRoundProof` this adds `quotient_commit` and the constraint-fold
/// challenge `alpha` (sampled after the aux commit). `quotient_values` is the raw quotient evaluation vector,
/// exposed so the `÷ Z_H` / low-degree gate can be checked directly; a real succinct proof carries only the
/// commitment plus the ζ-openings (the remaining FRI tail), not these values.
pub struct LookupQuotientProof {
    pub trace_commit: Com,
    pub aux_commit: Com,
    pub quotient_commit: Com,
    pub terminal: LookupTerminal<Challenge>,
    pub lookup_alpha: Challenge,
    pub lookup_beta: Challenge,
    pub alpha: Challenge,
    pub zeta: Challenge,
    pub log_num_quotient_chunks: usize,
    pub quotient_values: Vec<Challenge>,
}

/// W1.2-rest — the lookup **quotient**: fold the batched (base AIR + LogUp) constraints across the whole
/// quotient domain, divide by the trace domain's vanishing polynomial `Z_H`, and return the quotient
/// evaluations ready for `commit_quotient`. This is the lookup analogue of `p3_uni_stark::quotient_values`
/// (mirrored by `quotient_gpu::cpu_quotient_values`): the selector / `inv_vanishing` / `next_step` setup is
/// identical, but the per-point fold runs through `batched_constraints_at_point` — the *exact* same
/// `VerifierConstraintFolderWithLookups` the verifier's ζ-check calls (W1.2-core), so prover and verifier
/// fold constraints identically. The extension-field aux trace is reconstructed from its `flatten_to_base`
/// layout: Challenge column `c` ← base columns `c*D .. c*D+D`.
#[allow(clippy::too_many_arguments)]
pub fn lookup_quotient_values<A: LookupAir, Mt, Ma>(
    air: &A,
    lookups: &Lookups<Val>,
    trace_domain: Dom,
    quotient_domain: Dom,
    trace_on_quotient_domain: &Mt,
    aux_on_quotient_domain: &Ma,
    aux_width: usize,
    alpha: Challenge,
    lookup_challenges: &[Challenge],
    permutation_values: &[Challenge],
) -> Vec<Challenge>
where
    Mt: Matrix<Val>,
    Ma: Matrix<Val>,
{
    let quotient_size = quotient_domain.size();
    let sels = trace_domain.selectors_on_coset(quotient_domain);
    let next_step = quotient_size / trace_domain.size();
    let d = <Challenge as BasedVectorSpace<Val>>::DIMENSION;

    // Lift a base trace row to the extension field.
    let trace_row = |i: usize| -> Vec<Challenge> {
        trace_on_quotient_domain.row(i).unwrap().into_iter().map(Challenge::from).collect()
    };
    // Reconstruct a Challenge aux row from the `flatten_to_base` layout (col `c*D + dd`).
    let aux_row = |i: usize| -> Vec<Challenge> {
        let base: Vec<Val> = aux_on_quotient_domain.row(i).unwrap().into_iter().collect();
        (0..aux_width)
            .map(|c| Challenge::from_basis_coefficients_fn(|dd| base[c * d + dd]))
            .collect()
    };

    (0..quotient_size)
        .map(|i| {
            let inext = (i + next_step) % quotient_size;
            let folded = batched_constraints_at_point(
                air,
                lookups,
                &trace_row(i),
                &trace_row(inext),
                &aux_row(i),
                &aux_row(inext),
                Challenge::from(sels.is_first_row[i]),
                Challenge::from(sels.is_last_row[i]),
                Challenge::from(sels.is_transition[i]),
                alpha,
                lookup_challenges,
                permutation_values,
            );
            // quotient(x) = C(x) / Z_H(x) = folded · inv_vanishing(x).
            folded * Challenge::from(sels.inv_vanishing[i])
        })
        .collect()
}

/// W1.2-rest — the **three-round** lookup prover: commit the main trace → sample `(α_L, β)` → generate +
/// commit the LogUp aux trace → sample the constraint-fold `α` → **fold the batched constraints over the
/// quotient domain, ÷ `Z_H`, and `commit_quotient`** → sample the opening point `ζ`. This extends
/// `prove_lookup_rounds` (the two-round skeleton) with the quotient commit — the half of the FRI tail that
/// binds the trace + aux to the constraints. What remains is only the ζ-opening (trace + aux + quotient FRI
/// openings and the OOD identity), a mechanical extension of p3's `open`.
pub fn prove_lookup_with_quotient<A: LookupAir>(
    air: &A,
    main: RowMajorMatrix<Val>,
    pis: &[Val],
) -> LookupQuotientProof {
    let config = make_config();
    let pcs = config.pcs();
    let mut challenger = config.initialise_challenger();

    let degree = main.height();
    let log_degree = degree.trailing_zeros() as usize;
    let is_zk = config.is_zk();
    let log_ext_degree = log_degree + is_zk;

    // W1.1 — size the quotient over the FULL (base + lookup) constraint set; p3's own helper runs only
    // `air.eval` and would miss the lookup constraints, making the quotient domain too small.
    let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(air);
    let (_layout, log_num_quotient_chunks) = combined_constraint_layout(air, &lookups, is_zk);
    let num_quotient_chunks = 1 << (log_num_quotient_chunks + is_zk);

    let trace_domain = <MyPcs as Pcs<Challenge, Cha>>::natural_domain_for_degree(pcs, degree);
    let ext_trace_domain =
        <MyPcs as Pcs<Challenge, Cha>>::natural_domain_for_degree(pcs, degree * (is_zk + 1));

    // Round 1 — commit the main trace, observe it + the public values, then sample the lookup challenges.
    let (trace_commit, trace_data) =
        <MyPcs as Pcs<Challenge, Cha>>::commit(pcs, [(ext_trace_domain, main.clone())]);
    challenger.observe(trace_commit.clone());
    challenger.observe_slice(pis);
    let lookup_alpha: Challenge = challenger.sample_algebra_element();
    let lookup_beta: Challenge = challenger.sample_algebra_element();

    // Round 2 — generate + commit the LogUp aux (permutation) trace.
    let gadget = LogUpGadget::new();
    let (aux, terminal) =
        gadget.generate_permutation::<MyConfig>(&main, &None, pis, &lookups, &[lookup_alpha, lookup_beta]);
    let terminal = terminal.expect("an AIR with a lookup commits a terminal");
    let aux_width = aux.width();
    let aux_base = aux.flatten_to_base();
    let (aux_commit, aux_data) =
        <MyPcs as Pcs<Challenge, Cha>>::commit(pcs, [(ext_trace_domain, aux_base)]);
    challenger.observe(aux_commit.clone());

    // The constraint-fold challenge α — sampled AFTER the aux commit so the quotient may bind the aux trace.
    let alpha: Challenge = challenger.sample_algebra_element();

    // Round 3 — the quotient: batched constraints over the quotient domain ÷ Z_H, then commit.
    let quotient_domain =
        ext_trace_domain.create_disjoint_domain(1 << (log_ext_degree + log_num_quotient_chunks));
    let trace_on_qd =
        <MyPcs as Pcs<Challenge, Cha>>::get_evaluations_on_domain(pcs, &trace_data, 0, quotient_domain);
    let aux_on_qd =
        <MyPcs as Pcs<Challenge, Cha>>::get_evaluations_on_domain(pcs, &aux_data, 0, quotient_domain);
    let quotient_values = lookup_quotient_values(
        air,
        &lookups,
        trace_domain,
        quotient_domain,
        &trace_on_qd,
        &aux_on_qd,
        aux_width,
        alpha,
        &[lookup_alpha, lookup_beta],
        &[terminal.0],
    );
    let quotient_flat = RowMajorMatrix::new_col(quotient_values.clone()).flatten_to_base();
    let (quotient_commit, _quotient_data) = <MyPcs as Pcs<Challenge, Cha>>::commit_quotient(
        pcs,
        quotient_domain,
        quotient_flat,
        num_quotient_chunks,
    );
    challenger.observe(quotient_commit.clone());

    // The opening point ζ (the remaining FRI tail — openings of trace + aux + quotient at ζ — is deferred).
    let zeta: Challenge = challenger.sample_algebra_element();

    LookupQuotientProof {
        trace_commit,
        aux_commit,
        quotient_commit,
        terminal,
        lookup_alpha,
        lookup_beta,
        alpha,
        zeta,
        log_num_quotient_chunks,
        quotient_values,
    }
}

/// The values of the committed polynomials opened at the out-of-domain point ζ (and ζ·g for the local/next
/// rows). `trace_*` are the base-valued trace columns at the point; `aux_*` are the LogUp aux columns in
/// `flatten_to_base` layout (each Challenge column = `D` consecutive extension-basis coefficients);
/// `quotient_chunks` are the `num_quotient_chunks` chunk openings (each `D` extension-basis coefficients).
pub struct LookupOpenedValues {
    pub trace_local: Vec<Challenge>,
    pub trace_next: Vec<Challenge>,
    pub aux_local: Vec<Challenge>,
    pub aux_next: Vec<Challenge>,
    pub quotient_chunks: Vec<Vec<Challenge>>,
}

/// W1.3 — a complete lookup STARK proof: the three commitments, the committed LogUp terminal, the ζ-openings
/// of trace + aux + quotient, and the single batched FRI opening proof. (ZK note: per-commit salted-Merkle +
/// random-column hiding is retained via the production hiding PCS; the extra opt-randomization FRI-batch poly
/// `p3_uni_stark` adds is omitted — it is ZK-only, not soundness, and is the sole deferred ZK-hardening.)
pub struct LookupProof {
    pub trace_commit: Com,
    pub aux_commit: Com,
    pub quotient_commit: Com,
    pub terminal: LookupTerminal<Challenge>,
    pub opened: LookupOpenedValues,
    pub opening_proof: PcsProof,
    pub degree_bits: usize,
    pub aux_width: usize,
}

/// Why a lookup proof was rejected.
#[derive(Debug)]
pub enum LookupVerifyError {
    /// An opened-values vector had the wrong length.
    Shape(&'static str),
    /// The batched FRI / Merkle opening argument failed (a tampered opening is caught here).
    Pcs(String),
    /// ζ landed on the trace domain (a completeness event; honest Fiat–Shamir reaches it negligibly).
    OodPointInDomain,
    /// The constraint identity `folded(ζ)·Z_H(ζ)^{-1} = Q(ζ)` failed — the trace/aux violate the AIR + lookup
    /// constraints (aux not well-formed, or a forged quotient).
    OodMismatch,
    /// The committed LogUp terminal is non-zero — the looked-up multiset is imbalanced.
    NonZeroTerminal,
}

/// W1.3 — the complete lookup prover: `prove_lookup_with_quotient`'s three rounds followed by the **ζ-opening**
/// of trace + aux + quotient (one batched FRI proof). Completes the W1 milestone (`prove` → `verify` end to
/// end); see `verify_lookup` for the matching verifier.
pub fn prove_lookup<A: LookupAir>(air: &A, main: RowMajorMatrix<Val>, pis: &[Val]) -> LookupProof {
    prove_lookup_inner(air, main, pis, false)
}

/// The prover core. `forge_aux` (test-only) corrupts one committed aux fraction so the batched constraints no
/// longer vanish on `H`, driving the verifier's OOD rejection path.
fn prove_lookup_inner<A: LookupAir>(
    air: &A,
    main: RowMajorMatrix<Val>,
    pis: &[Val],
    forge_aux: bool,
) -> LookupProof {
    let config = make_config();
    let pcs = config.pcs();
    let mut challenger = config.initialise_challenger();

    let degree = main.height();
    let log_degree = degree.trailing_zeros() as usize;
    let is_zk = config.is_zk();
    let log_ext_degree = log_degree + is_zk;

    let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(air);
    let (_layout, log_num_quotient_chunks) = combined_constraint_layout(air, &lookups, is_zk);
    let num_quotient_chunks = 1 << (log_num_quotient_chunks + is_zk);

    let trace_domain = <MyPcs as Pcs<Challenge, Cha>>::natural_domain_for_degree(pcs, degree);
    let ext_trace_domain =
        <MyPcs as Pcs<Challenge, Cha>>::natural_domain_for_degree(pcs, degree * (is_zk + 1));

    // Round 1 — main trace.
    let (trace_commit, trace_data) =
        <MyPcs as Pcs<Challenge, Cha>>::commit(pcs, [(ext_trace_domain, main.clone())]);
    challenger.observe(trace_commit.clone());
    challenger.observe_slice(pis);
    let lookup_alpha: Challenge = challenger.sample_algebra_element();
    let lookup_beta: Challenge = challenger.sample_algebra_element();

    // Round 2 — LogUp aux trace.
    let gadget = LogUpGadget::new();
    let (mut aux, terminal) =
        gadget.generate_permutation::<MyConfig>(&main, &None, pis, &lookups, &[lookup_alpha, lookup_beta]);
    let terminal = terminal.expect("an AIR with a lookup commits a terminal");
    if forge_aux {
        aux.values[1] += Challenge::ONE; // break one fraction ⇒ constraints no longer vanish on H
    }
    let aux_width = aux.width();
    let aux_base = aux.flatten_to_base();
    let (aux_commit, aux_data) =
        <MyPcs as Pcs<Challenge, Cha>>::commit(pcs, [(ext_trace_domain, aux_base)]);
    challenger.observe(aux_commit.clone());
    let alpha: Challenge = challenger.sample_algebra_element();

    // Round 3 — quotient (÷ Z_H) commit.
    let quotient_domain =
        ext_trace_domain.create_disjoint_domain(1 << (log_ext_degree + log_num_quotient_chunks));
    let trace_on_qd =
        <MyPcs as Pcs<Challenge, Cha>>::get_evaluations_on_domain(pcs, &trace_data, 0, quotient_domain);
    let aux_on_qd =
        <MyPcs as Pcs<Challenge, Cha>>::get_evaluations_on_domain(pcs, &aux_data, 0, quotient_domain);
    let quotient_values = lookup_quotient_values(
        air, &lookups, trace_domain, quotient_domain, &trace_on_qd, &aux_on_qd, aux_width, alpha,
        &[lookup_alpha, lookup_beta], &[terminal.0],
    );
    let quotient_flat = RowMajorMatrix::new_col(quotient_values).flatten_to_base();
    let (quotient_commit, quotient_data) = <MyPcs as Pcs<Challenge, Cha>>::commit_quotient(
        pcs,
        quotient_domain,
        quotient_flat,
        num_quotient_chunks,
    );
    challenger.observe(quotient_commit.clone());

    // Round 4 (W1.3) — the ζ-opening. Sample ζ, then open trace + aux at {ζ, ζ·g} and every quotient chunk
    // at ζ, in one batched FRI proof. Round order [trace, aux, quotient] is mirrored by `verify_lookup`.
    let zeta: Challenge = challenger.sample_algebra_element();
    let zeta_next = trace_domain.next_point(zeta).expect("two-adic domain has a next point");
    let rounds = vec![
        (&trace_data, vec![vec![zeta, zeta_next]]),
        (&aux_data, vec![vec![zeta, zeta_next]]),
        (&quotient_data, vec![vec![zeta]; num_quotient_chunks]),
    ];
    let (opened_values, opening_proof) = <MyPcs as Pcs<Challenge, Cha>>::open(pcs, rounds, &mut challenger);

    let opened = LookupOpenedValues {
        trace_local: opened_values[0][0][0].clone(),
        trace_next: opened_values[0][0][1].clone(),
        aux_local: opened_values[1][0][0].clone(),
        aux_next: opened_values[1][0][1].clone(),
        quotient_chunks: opened_values[2].iter().map(|v| v[0].clone()).collect(),
    };

    LookupProof {
        trace_commit,
        aux_commit,
        quotient_commit,
        terminal,
        opened,
        opening_proof,
        degree_bits: log_ext_degree,
        aux_width,
    }
}

/// W1.3 — the matching verifier: re-derive `(α_L, β, α, ζ)` from the commitments (Fiat–Shamir), verify the
/// batched FRI opening of trace + aux + quotient at ζ, then check the two soundness relations — the OOD
/// constraint identity `folded(ζ)·Z_H(ζ)^{-1} = Q(ζ)` (base AIR + LogUp constraints via the *same*
/// `batched_constraints_at_point` the prover's quotient used) and the LogUp terminal sum.
pub fn verify_lookup<A: LookupAir>(
    air: &A,
    proof: &LookupProof,
    pis: &[Val],
) -> Result<(), LookupVerifyError> {
    let config = make_config();
    let pcs = config.pcs();
    let is_zk = config.is_zk();
    let degree_bits = proof.degree_bits;
    let degree = 1usize << degree_bits;
    let d = <Challenge as BasedVectorSpace<Val>>::DIMENSION;

    let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(air);
    let (_layout, log_num_quotient_chunks) = combined_constraint_layout(air, &lookups, is_zk);
    let num_quotient_chunks = 1 << (log_num_quotient_chunks + is_zk);

    // Domains: ext (2N) for the committed trace/aux; init (N) for selectors + vanishing; quotient (disjoint).
    let ext_trace_domain = <MyPcs as Pcs<Challenge, Cha>>::natural_domain_for_degree(pcs, degree);
    let init_trace_domain =
        <MyPcs as Pcs<Challenge, Cha>>::natural_domain_for_degree(pcs, degree >> is_zk);
    let quotient_domain =
        ext_trace_domain.create_disjoint_domain(1 << (degree_bits + log_num_quotient_chunks));
    let quotient_chunks_domains = quotient_domain.split_domains(num_quotient_chunks);
    // The hiding `commit_quotient` randomizes each chunk to a doubled domain; verify on those.
    let randomized_quotient_chunks_domains: Vec<Dom> = quotient_chunks_domains
        .iter()
        .map(|d| <MyPcs as Pcs<Challenge, Cha>>::natural_domain_for_degree(pcs, d.size() << is_zk))
        .collect();

    // Shape checks.
    let air_width = BaseAir::<Val>::width(air);
    if proof.opened.trace_local.len() != air_width || proof.opened.trace_next.len() != air_width {
        return Err(LookupVerifyError::Shape("trace opening width"));
    }
    if proof.opened.aux_local.len() != proof.aux_width * d
        || proof.opened.aux_next.len() != proof.aux_width * d
    {
        return Err(LookupVerifyError::Shape("aux opening width"));
    }
    if proof.opened.quotient_chunks.len() != num_quotient_chunks
        || proof.opened.quotient_chunks.iter().any(|c| c.len() != d)
    {
        return Err(LookupVerifyError::Shape("quotient chunk shape"));
    }

    // Fiat–Shamir — mirror the prover exactly.
    let mut challenger = config.initialise_challenger();
    challenger.observe(proof.trace_commit.clone());
    challenger.observe_slice(pis);
    let lookup_alpha: Challenge = challenger.sample_algebra_element();
    let lookup_beta: Challenge = challenger.sample_algebra_element();
    challenger.observe(proof.aux_commit.clone());
    let alpha: Challenge = challenger.sample_algebra_element();
    challenger.observe(proof.quotient_commit.clone());
    let zeta: Challenge = challenger.sample_algebra_element();

    if init_trace_domain.vanishing_poly_at_point(zeta).is_zero() {
        return Err(LookupVerifyError::OodPointInDomain);
    }
    let zeta_next = init_trace_domain.next_point(zeta).expect("two-adic domain has a next point");

    // Verify the batched FRI opening (same round order the prover used).
    let coms = vec![
        (
            proof.trace_commit.clone(),
            vec![(
                ext_trace_domain,
                vec![
                    (zeta, proof.opened.trace_local.clone()),
                    (zeta_next, proof.opened.trace_next.clone()),
                ],
            )],
        ),
        (
            proof.aux_commit.clone(),
            vec![(
                ext_trace_domain,
                vec![
                    (zeta, proof.opened.aux_local.clone()),
                    (zeta_next, proof.opened.aux_next.clone()),
                ],
            )],
        ),
        (
            proof.quotient_commit.clone(),
            randomized_quotient_chunks_domains
                .iter()
                .zip(&proof.opened.quotient_chunks)
                .map(|(dom, vals)| (*dom, vec![(zeta, vals.clone())]))
                .collect(),
        ),
    ];
    <MyPcs as Pcs<Challenge, Cha>>::verify(pcs, coms, &proof.opening_proof, &mut challenger)
        .map_err(|e| LookupVerifyError::Pcs(format!("{e:?}")))?;

    // Reconstruct Q(ζ) from the chunk openings, and the aux rows from their extension-basis coefficients.
    let quotient_at_zeta = recompose_quotient_from_chunks::<MyConfig>(
        &quotient_chunks_domains,
        &proof.opened.quotient_chunks,
        zeta,
    );
    let aux_local: Vec<Challenge> = (0..proof.aux_width)
        .map(|c| <Challenge as ExtensionField<Val>>::from_ext_basis_coefficients(&proof.opened.aux_local[c * d..(c + 1) * d]).unwrap())
        .collect();
    let aux_next: Vec<Challenge> = (0..proof.aux_width)
        .map(|c| <Challenge as ExtensionField<Val>>::from_ext_basis_coefficients(&proof.opened.aux_next[c * d..(c + 1) * d]).unwrap())
        .collect();

    // The OOD constraint identity — folded (base + lookup) via the SAME folder the prover's quotient used.
    let sels = init_trace_domain.selectors_at_point(zeta);
    let folded = batched_constraints_at_point(
        air,
        &lookups,
        &proof.opened.trace_local,
        &proof.opened.trace_next,
        &aux_local,
        &aux_next,
        sels.is_first_row,
        sels.is_last_row,
        sels.is_transition,
        alpha,
        &[lookup_alpha, lookup_beta],
        &[proof.terminal.0],
    );
    if folded * sels.inv_vanishing != quotient_at_zeta {
        return Err(LookupVerifyError::OodMismatch);
    }

    // The LogUp terminal: the looked-up multiset must balance (Σ fractions == 0).
    LogUpGadget::new()
        .verify_terminal_sum(&[Some(proof.terminal.clone())])
        .map_err(|_| LookupVerifyError::NonZeroTerminal)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::Dft;
    use p3_dft::TwoAdicSubgroupDft;
    use p3_lookup::{LogUpGadget, LookupProtocol, Lookups};

    /// Lift a base-field trace row into the extension field (the folder evaluates over F_p²).
    fn lift(row: &[Val]) -> Vec<Challenge> {
        row.iter().map(|&v| Challenge::from(v)).collect()
    }

    /// Evaluate the batched constraints at trace-domain row `r` (selectors from the row position; the
    /// last-row `next` wraps to row 0, masked by `is_transition=0`).
    #[allow(clippy::too_many_arguments)]
    fn batched_at_row(
        air: &RangeCheckAir,
        lookups: &Lookups<Val>,
        main: &RowMajorMatrix<Val>,
        aux: &RowMajorMatrix<Challenge>,
        r: usize,
        n: usize,
        alpha: Challenge,
        lc: &[Challenge],
        pv: &[Challenge],
    ) -> Challenge {
        let nr = (r + 1) % n;
        let (tl, tn) = (lift(&main.row_slice(r).unwrap()), lift(&main.row_slice(nr).unwrap()));
        let (al, an) = (aux.row_slice(r).unwrap().to_vec(), aux.row_slice(nr).unwrap().to_vec());
        let one = Challenge::ONE;
        let zero = Challenge::ZERO;
        let is_first = if r == 0 { one } else { zero };
        let is_last = if r == n - 1 { one } else { zero };
        let is_trans = if r == n - 1 { zero } else { one };
        batched_constraints_at_point(air, lookups, &tl, &tn, &al, &an, is_first, is_last, is_trans, alpha, lc, pv)
    }

    /// W1.2 core — the batched (base + lookup) constraints **vanish on every trace-domain row** for a valid
    /// trace (the constraints hold ⇒ the quotient is well-defined), and a forged aux violates them. This is
    /// the exact folder the verifier's ζ-check uses, so a valid quotient is now computable per-point.
    #[test]
    fn batched_constraints_vanish_on_trace_domain() {
        let air = RangeCheckAir;
        let main = balanced_main(1 << 4);
        let n = main.height();
        let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(&air);
        let (alpha_l, beta) = (Challenge::from_u32(7), Challenge::from_u32(11));
        let (aux, terminal) =
            LogUpGadget::new().generate_permutation::<MyConfig>(&main, &None, &[], &lookups, &[alpha_l, beta]);
        let terminal = terminal.expect("terminal").0;
        let alpha = Challenge::from_u32(13); // the constraint-fold challenge (distinct from α_L)

        // valid: constraints vanish on every row
        for r in 0..n {
            let acc = batched_at_row(&air, &lookups, &main, &aux, r, n, alpha, &[alpha_l, beta], &[terminal]);
            assert_eq!(acc, Challenge::ZERO, "constraints must vanish at row {r} for a valid trace");
        }

        // forged aux: some row's constraints do not vanish
        let mut bad = aux.clone();
        bad.values[1] += Challenge::ONE;
        let any_nonzero = (0..n)
            .any(|r| batched_at_row(&air, &lookups, &main, &bad, r, n, alpha, &[alpha_l, beta], &[terminal]) != Challenge::ZERO);
        assert!(any_nonzero, "a forged aux must violate the batched constraints");
    }

    /// W1.1 — the combined layout counts the base + lookup constraints, and their degree gives a small
    /// `log_nqc` (the number the forked quotient domain + alpha-powers must be sized against).
    #[test]
    fn combined_layout_counts_base_plus_lookup_constraints() {
        let air = RangeCheckAir;
        let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(&air);
        let (layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        println!(
            "W1.1 combined layout: {} constraints (base {} + ext {}), log_nqc={}",
            layout.total_constraints(),
            layout.base_indices.len(),
            layout.ext_indices.len(),
            log_nqc
        );
        assert!(layout.total_constraints() >= 1, "the lookup fraction/accumulator constraints must be counted");
        assert!(log_nqc <= 2, "a degree-3 lookup ⇒ log_nqc ≤ 2");
    }

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

    /// Rebuild the quotient domain for a `degree`-row trace at `log_nqc` (as `prove_lookup_with_quotient`).
    fn quotient_domain_for(degree: usize, log_nqc: usize) -> Dom {
        let config = make_config();
        let is_zk = config.is_zk();
        let log_ext_degree = degree.trailing_zeros() as usize + is_zk;
        let ext =
            <MyPcs as Pcs<Challenge, Cha>>::natural_domain_for_degree(config.pcs(), degree * (is_zk + 1));
        ext.create_disjoint_domain(1 << (log_ext_degree + log_nqc))
    }

    /// Interpolate the quotient evaluations (coset iDFT over the quotient coset) into coefficient rows.
    fn quotient_coeff_rows(quotient_values: &[Challenge], quotient_domain: Dom) -> RowMajorMatrix<Val> {
        let flat = RowMajorMatrix::new_col(quotient_values.to_vec()).flatten_to_base();
        Dft::default().coset_idft_batch(flat, quotient_domain.first_point())
    }

    /// Are all coefficients in the top `n` degrees zero (across every base column)?
    fn top_coeffs_all_zero(coeffs: &RowMajorMatrix<Val>, n: usize) -> bool {
        let h = coeffs.height();
        (h - n..h).all(|r| coeffs.row_slice(r).unwrap().iter().all(|&v| v == Val::ZERO))
    }

    /// W1.2-rest — the committed quotient is a genuine polynomial of degree `< quotient_size − |H|` (the
    /// `÷ Z_H` is exact, i.e. the batched base+lookup constraints vanish on `H`): its top `|H|` interpolated
    /// coefficients are zero. Tampering a single quotient value makes it a non-polynomial and breaks that —
    /// exactly the low-degree property the deferred FRI opening enforces succinctly at `ζ`.
    #[test]
    fn lookup_quotient_is_low_degree_and_commits() {
        let air = RangeCheckAir;
        let degree = 1 << 5;
        let proof = prove_lookup_with_quotient(&air, balanced_main(degree), &[]);

        let qd = quotient_domain_for(degree, proof.log_num_quotient_chunks);
        assert_eq!(proof.quotient_values.len(), qd.size(), "one quotient value per quotient-domain point");

        let coeffs = quotient_coeff_rows(&proof.quotient_values, qd);
        assert!(
            top_coeffs_all_zero(&coeffs, degree),
            "an honest quotient C/Z_H has degree < quotient_size − |H| ⇒ its top |H| coefficients vanish"
        );

        let mut tampered = proof.quotient_values.clone();
        tampered[3] += Challenge::ONE;
        assert!(
            !top_coeffs_all_zero(&quotient_coeff_rows(&tampered, qd), degree),
            "a tampered quotient value must break the low-degree property"
        );
    }

    /// The two soundness mechanisms are distinct: the **quotient** enforces aux-trace well-formedness (it is
    /// low-degree for any honestly-generated aux, balanced or not), while the committed **terminal** enforces
    /// multiset balance. An imbalanced trace therefore keeps a well-formed quotient but a non-zero terminal.
    #[test]
    fn quotient_wellformed_while_terminal_catches_imbalance() {
        let air = RangeCheckAir;
        let degree = 1 << 5;

        let bal = prove_lookup_with_quotient(&air, balanced_main(degree), &[]);
        let qd = quotient_domain_for(degree, bal.log_num_quotient_chunks);
        assert_eq!(bal.terminal.0, Challenge::ZERO, "balanced ⇒ zero terminal");
        assert!(top_coeffs_all_zero(&quotient_coeff_rows(&bal.quotient_values, qd), degree));

        let mut m = balanced_main(degree);
        m.values[3 * 4 + 1] = Val::from_u64(0xBADD); // break row 4's table value ⇒ multiset imbalance
        let imb = prove_lookup_with_quotient(&air, m, &[]);
        assert_ne!(imb.terminal.0, Challenge::ZERO, "imbalanced ⇒ non-zero terminal");
        assert!(
            top_coeffs_all_zero(&quotient_coeff_rows(&imb.quotient_values, qd), degree),
            "the honestly-generated aux stays well-formed, so the quotient remains a valid polynomial"
        );
    }

    /// W1.3 — the W1 milestone: a balanced range-check lookup AIR **proves and verifies end to end** through
    /// the ζ-opening of trace + aux + quotient (batched FRI) + the OOD identity + the terminal check.
    #[test]
    fn lookup_prove_verify_round_trips() {
        let air = RangeCheckAir;
        let proof = prove_lookup(&air, balanced_main(1 << 5), &[]);
        assert!(verify_lookup(&air, &proof, &[]).is_ok(), "a balanced lookup must verify end to end");
    }

    /// An imbalanced trace opens + folds correctly (the honest aux is well-formed ⇒ the OOD identity holds),
    /// but the committed terminal is non-zero ⇒ the verifier rejects at the terminal check.
    #[test]
    fn lookup_verify_rejects_imbalance() {
        let air = RangeCheckAir;
        let mut main = balanced_main(1 << 5);
        main.values[3 * 4 + 1] = Val::from_u64(0xBADD); // row 4's table value ≠ its query value
        let proof = prove_lookup(&air, main, &[]);
        assert!(
            matches!(verify_lookup(&air, &proof, &[]), Err(LookupVerifyError::NonZeroTerminal)),
            "an imbalanced multiset must be rejected at the terminal check"
        );
    }

    /// Tampering an opened value breaks its Merkle opening ⇒ the batched FRI/PCS verification rejects it
    /// (the opening is bound to the commitment).
    #[test]
    fn lookup_verify_rejects_tampered_opening() {
        let air = RangeCheckAir;
        let mut proof = prove_lookup(&air, balanced_main(1 << 5), &[]);
        proof.opened.trace_local[0] += Challenge::ONE;
        assert!(
            matches!(verify_lookup(&air, &proof, &[]), Err(LookupVerifyError::Pcs(_))),
            "a tampered opening must be caught by the PCS opening argument"
        );
    }

    /// A forged aux (committed but not well-formed) still opens + FRI-verifies (its columns are low-degree),
    /// but the recomposed quotient no longer matches the folded constraints at the out-of-domain ζ ⇒ the
    /// verifier rejects with an OOD mismatch. This is the soundness the ζ-opening buys over the raw commit.
    #[test]
    fn lookup_verify_rejects_forged_aux() {
        let air = RangeCheckAir;
        let proof = prove_lookup_inner(&air, balanced_main(1 << 5), &[], true);
        assert!(
            matches!(verify_lookup(&air, &proof, &[]), Err(LookupVerifyError::OodMismatch)),
            "a forged aux must fail the OOD constraint identity"
        );
    }

    /// A second interaction AIR (distinct from `RangeCheckAir`) exercising the generalized prover: a boolean
    /// column `b` (base constraint `b·(b−1)=0`, degree 2 — which `RangeCheckAir` has none of) plus one LogUp
    /// range-check of `b` against a table. Columns: `[b, table, mult]`.
    struct BooleanAir;
    impl<F: p3_field::Field> BaseAir<F> for BooleanAir {
        fn width(&self) -> usize {
            3
        }
    }
    impl<AB> Air<AB> for BooleanAir
    where
        AB: AirBuilder<F = Val> + InteractionBuilder,
    {
        fn eval(&self, builder: &mut AB) {
            let main = builder.main();
            let local = main.current_slice();
            let (b, table, mult) = (local[0], local[1], local[2]);
            builder.assert_zero(b.into() * (b.into() - AB::Expr::ONE)); // b ∈ {0,1}
            builder.push_local_interaction(vec![
                (vec![b.into()], AB::Expr::ONE),
                (vec![table.into()], -(mult.into())),
            ]);
        }
    }

    /// A balanced boolean trace: `b = i mod 2`, provided in the table with multiplicity 1 (the lookup balances
    /// and every `b` is boolean).
    fn boolean_main(height: usize) -> RowMajorMatrix<Val> {
        let mut flat = Vec::with_capacity(height * 3);
        for i in 0..height {
            let b = Val::from_u64((i as u64) & 1);
            flat.push(b);
            flat.push(b);
            flat.push(Val::ONE);
        }
        RowMajorMatrix::new(flat, 3)
    }

    /// W2 groundwork — the generalized prover proves + verifies a DIFFERENT interaction AIR (boolean + lookup,
    /// with a real base constraint) end to end, not just `RangeCheckAir`.
    #[test]
    fn boolean_air_prove_verify_round_trips() {
        let air = BooleanAir;
        let proof = prove_lookup(&air, boolean_main(1 << 5), &[]);
        assert!(verify_lookup(&air, &proof, &[]).is_ok(), "the boolean+lookup AIR must verify end to end");
    }

    /// A non-boolean `b` (base constraint violated), kept lookup-balanced so the terminal stays zero, is caught
    /// by the OOD constraint identity — proving base constraints are folded on the generalized path (the
    /// terminal alone would not catch it).
    #[test]
    fn boolean_air_verify_rejects_broken_base_constraint() {
        let air = BooleanAir;
        let mut main = boolean_main(1 << 5);
        main.values[3 * 4] = Val::from_u64(2); // row 4: b = 2 (not boolean)
        main.values[3 * 4 + 1] = Val::from_u64(2); // table = 2 keeps the lookup balanced (terminal stays 0)
        let proof = prove_lookup(&air, main, &[]);
        assert!(
            matches!(verify_lookup(&air, &proof, &[]), Err(LookupVerifyError::OodMismatch)),
            "a non-boolean b must fail the OOD constraint identity (base constraint)"
        );
    }
}
