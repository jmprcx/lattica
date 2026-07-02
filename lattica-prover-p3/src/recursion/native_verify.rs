//! B3-wire — a native re-verifier that re-implements `p3_uni_stark::verify`'s orchestration explicitly,
//! validated to agree with the real `verify` (accept valid, reject tampered). This is the porting
//! blueprint for the in-circuit verifier: it spells out the transcript replay (observe → sample α →
//! observe → sample ζ), the opening-rounds construction, and the quotient/constraint check, with the FRI
//! low-degree test delegated to `pcs.verify` (whose internals are covered by the separately-validated
//! primitives `fri_merkle`/`transcript`/`fri_fold`).
//!
//! Built against a minimal `ConstAir` (one column, constant) to keep the AIR-specific quotient logic
//! small, under the **production hiding (ZK) FRI config** — so the orchestration is validated against the
//! real ZK path (random commitment + the hiding opening structure + the `is_zk`-adjusted quotient-chunk
//! count). Transcript, openings, quotient, constraints are all exercised end-to-end.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_challenger::{CanObserve, CanSampleBits, DuplexChallenger, FieldChallenger, GrindingChallenger};
use p3_commit::{BatchOpening, ExtensionMmcs, Mmcs, Pcs, PolynomialSpace};
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing, TwoAdicField};
use p3_fri::{FriParameters, HidingFriPcs, TwoAdicFriFolding};
use p3_goldilocks::{Goldilocks, Poseidon2Goldilocks};
use p3_matrix::Dimensions;
use p3_merkle_tree::MerkleTreeHidingMmcs;
use rand_chacha::ChaCha20Rng;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use super::native_fri::{eval_final_poly, final_query_point, reverse_bits_len, verify_query, CommitStep};
use p3_uni_stark::{
    get_log_num_quotient_chunks, recompose_quotient_from_chunks, validate_degree_bits, verify_constraints,
    AirLayout, Proof, StarkConfig, StarkGenericConfig,
};

type Val = Goldilocks;
type Challenge = BinomialExtensionField<Val, 2>;

/// Minimal AIR: a single column constrained to a public constant on every row.
pub struct ConstAir;

impl BaseAir<Goldilocks> for ConstAir {
    fn width(&self) -> usize {
        1
    }
    fn num_public_values(&self) -> usize {
        1
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for ConstAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        builder.when_first_row().assert_zero(cur[0].clone() - pis[0].clone());
        builder.when_transition().assert_zero(nxt[0].clone() - cur[0].clone());
    }
}

/// Minimal NON-DEGENERATE AIR (Phase 6): a single column counting up — `cur = pub` on the first row,
/// `next = cur + 1` on every transition. Unlike `ConstAir`, its trace is NON-constant, so the committed
/// Merkle leaves (hence the cap entries) differ per query and the quotient at ζ is non-zero — this is what
/// exercises the cap-mux and the OOD epilogue that `ConstAir`'s degeneracy masks.
pub struct CounterAir;

impl BaseAir<Goldilocks> for CounterAir {
    fn width(&self) -> usize {
        1
    }
    fn num_public_values(&self) -> usize {
        1
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for CounterAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        builder.when_first_row().assert_zero(cur[0].clone() - pis[0].clone());
        builder.when_transition().assert_zero(nxt[0].clone() - cur[0].clone() - AB::Expr::ONE);
    }
}

/// A MULTI-COLUMN inner (Phase 7): the classic Fibonacci recurrence over 2 columns `[a, b]`. First row seeds
/// `a=pub[0]`, `b=pub[1]`; transition `a'=b`, `b'=a+b`; last row `b=pub[2]`. Unlike the 1-column ConstAir/
/// CounterAir, it exercises the GENERAL OOD epilogue: multi-column openings, CROSS-column constraints, and
/// all three Lagrange selectors (first, transition, last) in the α-fold — the first bounded step toward the
/// arbitrary-inner-AIR epilogue (the blocker for B5 recursion depth + folding real join-split statements).
/// Constraint EMISSION ORDER (the α-fold is Horner, first-emitted gets the highest power): C0 first-row a,
/// C1 first-row b, C2 transition a', C3 transition b', C4 last-row b.
pub struct FibonacciAir;

impl BaseAir<Goldilocks> for FibonacciAir {
    fn width(&self) -> usize {
        2
    }
    fn num_public_values(&self) -> usize {
        3
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for FibonacciAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        builder.when_first_row().assert_zero(cur[0].clone() - pis[0].clone()); // C0
        builder.when_first_row().assert_zero(cur[1].clone() - pis[1].clone()); // C1
        builder.when_transition().assert_zero(nxt[0].clone() - cur[1].clone()); // C2: a' = b
        builder.when_transition().assert_zero(nxt[1].clone() - cur[0].clone() - cur[1].clone()); // C3: b' = a + b
        builder.when_last_row().assert_zero(cur[1].clone() - pis[2].clone()); // C4
    }
}

/// A DEGREE-2 multi-column inner (Phase 7.5): 3 columns `[a, b, c]` with two counters (a'=a+1, b'=b+1) and a
/// NON-AFFINE product constraint `c = a·b` (every row). Unlike Fibonacci (whose constraints are all affine —
/// Add/Sub + a selector multiply), this has a Mul of two TRACE VARIABLES, so it exercises the symbolic
/// evaluator's variable·variable path — the constraint shape real high-degree AIRs (Poseidon, range checks)
/// use. Emission order: C0 first-row a, C1 first-row b, C2 product c−a·b (unconditional), C3 a'−a−1, C4 b'−b−1.
pub struct MulAir;

impl BaseAir<Goldilocks> for MulAir {
    fn width(&self) -> usize {
        3
    }
    fn num_public_values(&self) -> usize {
        2 // seed a, seed b
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for MulAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        builder.when_first_row().assert_zero(cur[0].clone() - pis[0].clone()); // C0
        builder.when_first_row().assert_zero(cur[1].clone() - pis[1].clone()); // C1
        builder.assert_zero(cur[2].clone() - cur[0].clone() * cur[1].clone()); // C2: c = a·b (degree 2, every row)
        builder.when_transition().assert_zero(nxt[0].clone() - cur[0].clone() - AB::Expr::ONE); // C3: a' = a + 1
        builder.when_transition().assert_zero(nxt[1].clone() - cur[1].clone() - AB::Expr::ONE); // C4: b' = b + 1
    }
}

/// An inner with a PERIODIC column (Phase 7.7): 1 trace column `a` accumulating a repeating pattern
/// `p = [3, 7]` (a periodic column, e.g. round constants in real AIRs): first row `a = pub[0]`, transition
/// `a' = a + p`. The transition constraint references the periodic value `p` (BaseEntry::Periodic in the
/// symbolic tree) — the last leaf kind the evaluator needs for real high-degree AIRs. Emission order: C0
/// first-row seed, C1 transition accumulate.
pub struct PeriodicAir;

/// The periodic pattern `[3, 7]` (period 2), shared by the AIR and the proof/oracle.
pub const PERIODIC_PATTERN: [u64; 2] = [3, 7];

impl BaseAir<Goldilocks> for PeriodicAir {
    fn width(&self) -> usize {
        1
    }
    fn num_public_values(&self) -> usize {
        1 // seed
    }
    fn num_periodic_columns(&self) -> usize {
        1 // (the default is 0; must be overridden alongside periodic_columns)
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        vec![PERIODIC_PATTERN.iter().map(|&v| Goldilocks::from_u64(v)).collect()]
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for PeriodicAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        builder.when_first_row().assert_zero(cur[0].clone() - pis[0].clone()); // C0
        builder.when_transition().assert_zero(nxt[0].clone() - cur[0].clone() - p[0].clone()); // C1: a' = a + p
    }
}

/// A WIDE inner (Phase 7 "wire it"): `WIDE_W`=8 independent counter columns (`col_i' = col_i + 1`, first row
/// `col_i = pub_i`). W=8 > RATE=4, so the trace-commitment leaf at a query row spans `ceil(8/4)=2` Poseidon
/// blocks — the smallest inner that exercises the MONOLITH'S MULTI-BLOCK input-leaf hashing (the real
/// join-split needs W=19 ⇒ 5 blocks). Still degree-1 (nqc=1), so ONLY the leaf-block dimension is new (the
/// quotient stays single-block). Emission order: C0..C7 first-row seeds, then C8..C15 transitions.
pub struct WideAir;

/// Trace width of `WideAir` (chosen > RATE=4 to force a 2-block Merkle leaf).
pub const WIDE_W: usize = 8;

impl BaseAir<Goldilocks> for WideAir {
    fn width(&self) -> usize {
        WIDE_W
    }
    fn num_public_values(&self) -> usize {
        WIDE_W // one seed per column
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for WideAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        for i in 0..WIDE_W {
            builder.when_first_row().assert_zero(cur[i].clone() - pis[i].clone()); // C_i: seed col_i = pub_i
        }
        for i in 0..WIDE_W {
            builder.when_transition().assert_zero(nxt[i].clone() - cur[i].clone() - AB::Expr::ONE); // C_{W+i}: col_i' = col_i + 1
        }
    }
}

/// A DEGREE-3 inner (Phase 7 "wire it", quotient half): 2 columns `[a, c]` with a counter `a'=a+1` and a
/// CUBIC constraint `c = a³` (every row). Max constraint degree 3 ⇒ p3 splits the quotient into
/// nqc = next_pow2(3−1) = 2 chunks, so the monolith must open 2·nqc = 4 quotient reduced-opening terms and
/// RECOMPOSE quotient(ζ) = Σ_i zps_i·chunk_i over the 2 chunks (vs the nqc=1 `c0+c1·X`). Still a single-block
/// quotient leaf (2·nqc=4 ≤ RATE), so it isolates the multi-CHUNK recompose from the multi-BLOCK quotient
/// leaf (the degree-4 CubeAir's bigger sibling). Emission: C0 first-row a-seed, C1 cubic c−a³, C2 a'−a−1.
pub struct CubeAir;

impl BaseAir<Goldilocks> for CubeAir {
    fn width(&self) -> usize {
        2
    }
    fn num_public_values(&self) -> usize {
        1 // seed a
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for CubeAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        builder.when_first_row().assert_zero(cur[0].clone() - pis[0].clone()); // C0: a = pub
        let a = cur[0].clone();
        builder.assert_zero(cur[1].clone() - a.clone() * a.clone() * a); // C1: c = a³ (degree 3, every row)
        builder.when_transition().assert_zero(nxt[0].clone() - cur[0].clone() - AB::Expr::ONE); // C2: a' = a + 1
    }
}

/// A DEGREE-4 inner (Phase 7 "wire it", quotient half B2): 2 columns `[a, c]` with a counter `a'=a+1` and a
/// QUARTIC constraint `c = a⁴` (every row). Max constraint degree 4 ⇒ nqc = next_pow2(4−1) = 4 chunks, so
/// 2·nqc = 8 > RATE = 4: the quotient-Merkle leaf spans ceil(8/4) = 2 Poseidon blocks — the smallest inner
/// that exercises the monolith's MULTI-BLOCK QUOTIENT leaf (on top of the multi-chunk recompose). Emission:
/// C0 first-row a-seed, C1 quartic c−a⁴, C2 a'−a−1.
pub struct QuartAir;

impl BaseAir<Goldilocks> for QuartAir {
    fn width(&self) -> usize {
        2
    }
    fn num_public_values(&self) -> usize {
        1 // seed a
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for QuartAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        builder.when_first_row().assert_zero(cur[0].clone() - pis[0].clone()); // C0: a = pub
        let a2 = cur[0].clone() * cur[0].clone();
        builder.assert_zero(cur[1].clone() - a2.clone() * a2); // C1: c = a⁴ (degree 4, every row)
        builder.when_transition().assert_zero(nxt[0].clone() - cur[0].clone() - AB::Expr::ONE); // C2: a' = a + 1
    }
}

// --- hiding (ZK) FRI config — the PRODUCTION config family lattica uses (so the re-verifier is
//     validated against the real ZK path: random commitment + hiding opening structure).
type Perm = Poseidon2Goldilocks<8>;
type MyHash = PaddingFreeSponge<Perm, 8, 4, 4>;
type MyCompress = TruncatedPermutation<Perm, 2, 4, 8>;
type ValMmcs =
    MerkleTreeHidingMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, ChaCha20Rng, 2, 4, 4>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Challenger = DuplexChallenger<Val, Perm, 8, 4>;
type Dft = Radix2DitParallel<Val>;
type MyPcs = HidingFriPcs<Val, Dft, ValMmcs, ChallengeMmcs, ChaCha20Rng>;
type MyConfig = StarkConfig<MyPcs, Challenge, Challenger>;

/// Native re-verifier: re-implements `verify`'s orchestration step-by-step (production hiding/ZK config;
/// the `is_zk=1` path — random commitment observed, `init_trace_domain = degree >> is_zk`, quotient-chunk
/// count `1 << (log + is_zk)`), delegating only the FRI low-degree test to `pcs.verify`.
pub fn reverify(config: &MyConfig, proof: &Proof<MyConfig>, public_values: &[Val]) -> Result<(), String> {
    let air = ConstAir;
    let Proof { commitments, opened_values, opening_proof, degree_bits } = proof;
    let degree_bits = *degree_bits;
    let pcs = config.pcs();
    let is_zk = config.is_zk();

    let (base_degree_bits, degree) =
        validate_degree_bits(None, degree_bits, is_zk, <MyPcs as Pcs<Challenge, Challenger>>::log_max_lde_height(pcs)).map_err(|e| format!("degree bits: {e:?}"))?;
    let trace_domain = <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, degree);
    let preprocessed_width = 0usize; // ConstAir has no preprocessed trace

    let layout = AirLayout::from_air::<Val>(&air);
    let log_num_quotient_chunks = get_log_num_quotient_chunks::<Val, ConstAir>(&air, layout, is_zk);
    let num_quotient_chunks = 1usize << (log_num_quotient_chunks + is_zk); // checked_log_size_sum(log, is_zk)

    let mut challenger = config.initialise_challenger();
    let init_trace_domain = <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, degree >> is_zk);

    let quotient_domain_size = 1usize << (degree_bits + log_num_quotient_chunks);
    let quotient_domain = trace_domain.create_disjoint_domain(quotient_domain_size);
    let quotient_chunks_domains = quotient_domain.split_domains(num_quotient_chunks);
    let randomized_quotient_chunks_domains: Vec<_> = quotient_chunks_domains
        .iter()
        .map(|d| <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, d.size() << is_zk))
        .collect();

    // ---- observe the instance ----
    challenger.observe(Val::from_usize(degree_bits));
    challenger.observe(Val::from_usize(base_degree_bits));
    challenger.observe(Val::from_usize(preprocessed_width));
    challenger.observe(commitments.trace.clone());
    challenger.observe_slice(public_values);

    // ---- α (constraint combination) ----
    let alpha: Challenge = challenger.sample_algebra_element();
    challenger.observe(commitments.quotient_chunks.clone());
    if let Some(r) = commitments.random.clone() {
        challenger.observe(r);
    }

    // ---- ζ (out-of-domain point) ----
    let zeta: Challenge = challenger.sample_algebra_element();
    if init_trace_domain.vanishing_poly_at_point(zeta).is_zero() {
        return Err("zeta in trace domain".into());
    }

    let periodic_columns = air.periodic_columns();
    let periodic_values: Vec<Challenge> = periodic_columns
        .iter()
        .map(|c| init_trace_domain.evaluate_periodic_column_at(c, zeta))
        .collect();
    let zeta_next = init_trace_domain.next_point(zeta).ok_or("no next point")?;

    // ---- opening rounds (random, trace, quotient) ----
    let main_next = !air.main_next_row_columns().is_empty();
    let mut coms_to_verify = if let Some(random_commit) = &commitments.random {
        let random_values = opened_values.random.as_ref().ok_or("missing random opened values")?;
        vec![(random_commit.clone(), vec![(trace_domain, vec![(zeta, random_values.clone())])])]
    } else {
        vec![]
    };
    let trace_round = {
        let mut pts = vec![(zeta, opened_values.trace_local.clone())];
        if main_next {
            pts.push((zeta_next, opened_values.trace_next.clone().ok_or("missing trace_next")?));
        }
        (commitments.trace.clone(), vec![(trace_domain, pts)])
    };
    coms_to_verify.push(trace_round);
    coms_to_verify.push((
        commitments.quotient_chunks.clone(),
        randomized_quotient_chunks_domains
            .iter()
            .zip(&opened_values.quotient_chunks)
            .map(|(d, v)| (*d, vec![(zeta, v.clone())]))
            .collect(),
    ));

    // ---- FRI low-degree test (delegated; internals = the validated primitives) ----
    <MyPcs as Pcs<Challenge, Challenger>>::verify(pcs, coms_to_verify, opening_proof, &mut challenger).map_err(|e| format!("pcs.verify: {e:?}"))?;

    // ---- recompose the quotient + check the constraint relation at ζ ----
    let quotient = recompose_quotient_from_chunks::<MyConfig>(&quotient_chunks_domains, &opened_values.quotient_chunks, zeta);
    let zeros;
    let trace_next_slice: &[Challenge] = match &opened_values.trace_next {
        Some(v) => v.as_slice(),
        None => {
            zeros = Challenge::zero_vec(air.width());
            &zeros
        }
    };
    verify_constraints::<MyConfig, ConstAir, <MyPcs as Pcs<Challenge, Challenger>>::Error>(
        &air,
        &opened_values.trace_local,
        trace_next_slice,
        None,
        None,
        &periodic_values,
        public_values,
        init_trace_domain,
        zeta,
        alpha,
        quotient,
    )
    .map_err(|e| format!("constraints: {e:?}"))?;

    Ok(())
}

// =================================================================================================
// NATIVE HIDING (is_zk=1) ORACLE — the HidingFriPcs analog of native_fri's non-hiding oracle
// (full_transcript_challenges / multicol_query_terms). Extracts, from a hiding proof, exactly the values the
// in-circuit hiding monolith will reproduce: the challenges (with the RANDOM-commitment absorb) and the
// per-query reduced-opening terms (the extra RANDOM opening round + the trace + the 2·is_zk-doubled quotient
// chunks over randomized domains). Salt (in the MMCS opening_proof, not opened_values) is a leaf-hash concern
// deferred to the in-circuit increment — it does not affect the challenges or the reduced opening. Validated
// natively: the reduced opening folds to final_poly via the FRI (§ tests::hiding_oracle_folds_to_final_poly).
// =================================================================================================

/// The Fiat–Shamir challenges of a HIDING proof (α_stark, ζ, α_fri, β_r, query index felts). Same sequence as
/// the non-hiding `full_transcript_challenges` PLUS the two `is_zk=1` insertions: `observe(random_commitment)`
/// after the quotient commitment (before ζ), and `observe(random_opened_values)` FIRST in the pre-α_fri
/// opened-value absorb (the random round is coms_to_verify[0] in `reverify`).
#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(crate) fn hiding_transcript_challenges(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    public_values: &[Val],
) -> (Challenge, Challenge, Challenge, Vec<Challenge>, Vec<Val>) {
    use p3_challenger::{CanSample, FieldChallenger, GrindingChallenger};
    let pcs = config.pcs();
    let is_zk = config.is_zk();
    let degree_bits = proof.degree_bits;
    let (base_degree_bits, _) =
        validate_degree_bits(None, degree_bits, is_zk, <MyPcs as Pcs<Challenge, Challenger>>::log_max_lde_height(pcs)).expect("degree bits");
    let mut ch = config.initialise_challenger();
    // preamble → α_stark
    ch.observe(Val::from_usize(degree_bits));
    ch.observe(Val::from_usize(base_degree_bits));
    ch.observe(Val::from_usize(0)); // preprocessed width (ConstAir)
    ch.observe(proof.commitments.trace.clone());
    ch.observe_slice(public_values);
    let alpha_stark: Challenge = ch.sample_algebra_element();
    // quotient + RANDOM commitments → ζ
    ch.observe(proof.commitments.quotient_chunks.clone());
    if let Some(r) = proof.commitments.random.clone() {
        ch.observe(r);
    }
    let zeta: Challenge = ch.sample_algebra_element();
    // pre-α_fri opened-value absorb. HidingFriPcs::verify MERGES each round's public openings with the hidden
    // random codewords (opening_proof.0, indexed [round][matrix][point]) BEFORE the inner TwoAdicFriPcs::verify
    // observes them — so the transcript absorbs `public ‖ codewords`. Round order = coms_to_verify:
    // [random?, trace{ζ, ζ_next}, quotient{chunks}].
    let rand_cws = &proof.opening_proof.0;
    let mut round = 0usize;
    let observe_merged = |ch: &mut Challenger, public: &[Challenge], cw: &[Challenge]| {
        let mut m = public.to_vec();
        m.extend_from_slice(cw);
        ch.observe_algebra_slice(&m);
    };
    if let Some(rv) = &proof.opened_values.random {
        observe_merged(&mut ch, rv, &rand_cws[round][0][0]);
        round += 1;
    }
    observe_merged(&mut ch, &proof.opened_values.trace_local, &rand_cws[round][0][0]);
    if let Some(tn) = &proof.opened_values.trace_next {
        observe_merged(&mut ch, tn, &rand_cws[round][0][1]);
    }
    round += 1;
    for (i, c) in proof.opened_values.quotient_chunks.iter().enumerate() {
        observe_merged(&mut ch, c, &rand_cws[round][i][0]);
    }
    let alpha_fri: Challenge = ch.sample_algebra_element();
    // per commit round → β_r (hiding opening_proof = (random-poly openings, FriProof); the FriProof is .1)
    let fri = &proof.opening_proof.1;
    let mut betas = Vec::new();
    for (comm, w) in fri.commit_phase_commits.iter().zip(&fri.commit_pow_witnesses) {
        ch.observe(comm.clone());
        assert!(ch.check_witness(0, *w), "commit pow (0 bits)");
        betas.push(ch.sample_algebra_element::<Challenge>());
    }
    // final_poly + arities + query-PoW → the query index felts
    ch.observe_algebra_slice(&fri.final_poly);
    let log_arities: Vec<usize> = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).collect();
    for &la in &log_arities {
        ch.observe(Val::from_usize(la));
    }
    assert!(ch.check_witness(16, fri.query_pow_witness), "query pow");
    let index_felts: Vec<Val> = (0..fri.query_proofs.len()).map(|_| ch.sample()).collect();
    (alpha_stark, zeta, alpha_fri, betas, index_felts)
}

/// Native hiding reduced-opening oracle — the `HidingFriPcs` analog of native_fri's `open_input`. For one
/// query it computes the DEEP reduced opening `ro = Σ_matrices Σ_points Σ_cols α^k (p_z − p_x)/(z − x)` per
/// height, from the query rows `p_x` (input_proof) and the MERGED opened values `p_z` (public ‖ hidden random
/// codewords — see `hiding_transcript_challenges`). The arithmetic is identical to the non-hiding open_input;
/// the hiding structure is entirely in the caller-supplied `merged_coms` (the extra random round + the 2×
/// quotient chunks over randomized domains, with codewords appended). The salted-leaf INPUT Merkle
/// authentication is a SEPARATE oracle piece (reverify covers it); this focuses on the reduced opening.
///
/// `merged_coms[batch] = mats`, each mat `(log_domain_size, points[(z, values_with_codewords)])`, in the same
/// round order as `input_proof`: `[random?, trace{ζ, ζ_next}, quotient{chunks}]`.
#[cfg_attr(not(test), allow(dead_code))]
fn hiding_query_terms(
    log_blowup: usize,
    log_global_max_height: usize,
    index: usize,
    input_proof: &[BatchOpening<Val, ValMmcs>],
    alpha: Challenge,
    merged_coms: &[Vec<(usize, Vec<(Challenge, Vec<Challenge>)>)>],
) -> Result<Vec<(usize, Challenge)>, String> {
    use std::collections::BTreeMap;
    let mut reduced: BTreeMap<usize, (Challenge, Challenge)> = BTreeMap::new();
    if input_proof.len() != merged_coms.len() {
        return Err(format!("batch count {} != {}", input_proof.len(), merged_coms.len()));
    }
    for (batch_opening, mats) in input_proof.iter().zip(merged_coms.iter()) {
        if batch_opening.opened_values.len() != mats.len() {
            return Err("batch matrix count mismatch".into());
        }
        for (mat_opening, (log_dom, mat_pts)) in batch_opening.opened_values.iter().zip(mats.iter()) {
            let log_height = log_dom + log_blowup;
            let bits_reduced = log_global_max_height - log_height;
            let rev = reverse_bits_len(index >> bits_reduced, log_height);
            let x = Val::GENERATOR * Val::two_adic_generator(log_height).exp_u64(rev as u64);
            let (alpha_pow, ro) = reduced.entry(log_height).or_insert((Challenge::ONE, Challenge::ZERO));
            for (z, ps_at_z) in mat_pts.iter() {
                if mat_opening.len() != ps_at_z.len() {
                    return Err(format!("col count {} != {} (merge shape)", mat_opening.len(), ps_at_z.len()));
                }
                let quotient = (*z - x).try_inverse().ok_or("opening point matches query point")?;
                for (&p_at_x, &p_at_z) in mat_opening.iter().zip(ps_at_z.iter()) {
                    *ro += *alpha_pow * (p_at_z - p_at_x) * quotient;
                    *alpha_pow *= alpha;
                }
            }
        }
    }
    Ok(reduced.into_iter().rev().map(|(lh, (_, ro))| (lh, ro)).collect())
}

/// The HIDING analog of monolith's `multicol_query_terms`: the per-query DEEP reduced-opening TERMS in the
/// monolith's format — `(terms=[(z, p_z, p_x)], x, α_fri, ro)`. `p_z` is the MERGED opened value (public ‖
/// codewords, Challenge), `p_x` the committed row felt (Val). Round order [random?, trace{ζ,ζ_next}, quotient
/// chunks over randomized domains]; for a hiding ConstAir all input matrices share one height (log_global), so
/// there is a single `x`. This is the arith-tile witness the in-circuit hiding monolith's reduced opening
/// consumes; the count is much larger than the is_zk=0 case (random round + merged widths + 2× quotient).
#[cfg(test)]
fn hiding_multicol_query_terms(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    public_values: &[Val],
    q: usize,
) -> (Vec<(Challenge, Challenge, Val)>, Val, Challenge, Challenge) {
    use p3_field::PrimeField64;
    let pcs = config.pcs();
    let is_zk = config.is_zk();
    let degree_bits = proof.degree_bits;
    let (_a_stark, zeta, alpha_fri, _betas, index_felts) = hiding_transcript_challenges(config, proof, public_values);

    // domains (mirror reverify): trace_domain (committed), init_trace_domain (constraint), randomized quotient.
    let (_, degree) = validate_degree_bits(None, degree_bits, is_zk, <MyPcs as Pcs<Challenge, Challenger>>::log_max_lde_height(pcs)).expect("degree bits");
    let trace_domain = <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, degree);
    let init_trace_domain = <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, degree >> is_zk);
    let layout = AirLayout::from_air::<Val>(&ConstAir);
    let log_nqc = get_log_num_quotient_chunks::<Val, ConstAir>(&ConstAir, layout, is_zk);
    let nqc = 1usize << (log_nqc + is_zk);
    let qd = trace_domain.create_disjoint_domain(1 << (degree_bits + log_nqc));
    let rqcd: Vec<_> = qd
        .split_domains(nqc)
        .iter()
        .map(|d| <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, d.size() << is_zk))
        .collect();
    let zeta_next = init_trace_domain.next_point(zeta).expect("next");

    // merged coms (public ‖ codewords), round order [random?, trace{ζ,ζ_next}, quotient chunks].
    let rand_cws = &proof.opening_proof.0;
    let fri = &proof.opening_proof.1;
    let ld_trace = degree_bits;
    let mut rounds_um: Vec<Vec<(usize, Vec<(Challenge, Vec<Challenge>)>)>> = Vec::new();
    if let Some(rv) = &proof.opened_values.random {
        rounds_um.push(vec![(ld_trace, vec![(zeta, rv.clone())])]);
    }
    {
        let mut pts = vec![(zeta, proof.opened_values.trace_local.clone())];
        if let Some(tn) = &proof.opened_values.trace_next {
            pts.push((zeta_next, tn.clone()));
        }
        rounds_um.push(vec![(ld_trace, pts)]);
    }
    rounds_um.push(
        rqcd.iter()
            .zip(&proof.opened_values.quotient_chunks)
            .map(|(d, v)| (d.size().trailing_zeros() as usize, vec![(zeta, v.clone())]))
            .collect(),
    );
    let mut merged: Vec<Vec<(usize, Vec<(Challenge, Vec<Challenge>)>)>> = Vec::new();
    for (r, rmats) in rounds_um.iter().enumerate() {
        let mut mr = Vec::new();
        for (m, (ld, pts)) in rmats.iter().enumerate() {
            let mut mp = Vec::new();
            for (p, (z, vals)) in pts.iter().enumerate() {
                let mut mv = vals.clone();
                mv.extend_from_slice(&rand_cws[r][m][p]);
                mp.push((*z, mv));
            }
            mr.push((*ld, mp));
        }
        merged.push(mr);
    }

    let log_global: usize = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).sum::<usize>() + 4;
    let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);

    // open_input's reduced-opening loop, capturing the terms (z, p_z_merged, p_x).
    let input_proof = &fri.query_proofs[q].input_proof;
    let mut terms = Vec::new();
    let mut alpha_pow = Challenge::ONE;
    let mut ro = Challenge::ZERO;
    let mut x_out = Val::ZERO;
    for (bo, mats) in input_proof.iter().zip(merged.iter()) {
        for (mat_opening, (log_dom, mat_pts)) in bo.opened_values.iter().zip(mats.iter()) {
            let log_height = log_dom + 4;
            let bits_reduced = log_global - log_height;
            let rev = reverse_bits_len(index >> bits_reduced, log_height);
            let x = Val::GENERATOR * Val::two_adic_generator(log_height).exp_u64(rev as u64);
            x_out = x;
            for (z, ps_at_z) in mat_pts.iter() {
                let inv = (*z - x).inverse();
                for (&p_x, &p_z) in mat_opening.iter().zip(ps_at_z.iter()) {
                    terms.push((*z, p_z, p_x));
                    ro += alpha_pow * (p_z - p_x) * inv;
                    alpha_pow *= alpha_fri;
                }
            }
        }
    }
    (terms, x_out, alpha_fri, ro)
}

/// The HIDING analog of query_fold_data (ARITY-2): the commit-phase fold-chain witness `(sibling, β, bit, s)`
/// per round, folding `ro` (from hiding_multicol_query_terms) down to the final value `e`. For
/// log_final_poly_len=0 the accept is `e == final_poly[0]`. This is the fold-chain witness the monolith's
/// arith-tile fold consumes; the commit-phase fold is is_zk-agnostic (the hiding deltas are all in the INPUT,
/// not the fold) but the proof MUST be arity-2 (the monolith's fold chain folds one bit per round).
#[cfg(test)]
fn hiding_query_fold_data(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    public_values: &[Val],
    q: usize,
) -> (Challenge, Vec<(Challenge, Challenge, bool, Val)>, Challenge, Challenge) {
    use p3_field::PrimeField64;
    let (_, _, _, betas, index_felts) = hiding_transcript_challenges(config, proof, public_values);
    let (_terms, _x, _alpha, ro) = hiding_multicol_query_terms(config, proof, public_values, q);
    let fri = &proof.opening_proof.1;
    let log_global: usize = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).sum::<usize>() + 4;
    let mut start = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
    let mut e = ro;
    let mut log_current = log_global;
    let mut rounds = Vec::new();
    for (r, step) in fri.query_proofs[q].commit_phase_openings.iter().enumerate() {
        let la = step.log_arity as usize;
        let arity = 1usize << la;
        let bit = start % arity;
        let sibling = step.sibling_values[0];
        let log_folded = log_current - la;
        start >>= la;
        let s = Val::two_adic_generator(log_folded + la).exp_u64(reverse_bits_len(start, log_folded) as u64);
        let (e0, e1) = if bit == 0 { (e, sibling) } else { (sibling, e) };
        e = crate::recursion::fri_fold::native_fold(e0, e1, betas[r], s);
        rounds.push((sibling, betas[r], bit == 1, s));
        log_current = log_folded;
    }
    (ro, rounds, e, fri.final_poly[0])
}

/// The HIDING analog of query_input_merkle: the trace-round inline-Merkle witness — the SALTED leaf
/// `MyHash(committed_row ‖ salt)` (salt from opening_proof.0), the sibling path, and the cap entry
/// `cap[index >> depth]`. Trace is input round 1 when the random round is present (is_zk=1). This is the
/// leaf+path witness the monolith's inline input-Merkle region consumes (its leaf sponge now absorbs W+8 felts).
#[cfg(test)]
fn hiding_query_input_merkle(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    public_values: &[Val],
    q: usize,
) -> ([Val; 4], Vec<([Val; 4], bool)>, [Val; 4]) {
    use p3_field::PrimeField64;
    use p3_goldilocks::default_goldilocks_poseidon2_8;
    use p3_symmetric::CryptographicHasher;
    let (_, _, _, _, index_felts) = hiding_transcript_challenges(config, proof, public_values);
    let fri = &proof.opening_proof.1;
    let log_global: usize = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).sum::<usize>() + 4;
    let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
    let trace_batch = if proof.commitments.random.is_some() { 1 } else { 0 };
    let batch = &fri.query_proofs[q].input_proof[trace_batch];
    let row = &batch.opened_values[0];
    let salt = &batch.opening_proof.0[0]; // hiding MMCS Proof = (salts, siblings); salt per matrix
    let hasher = MyHash::new(default_goldilocks_poseidon2_8());
    let preimage: Vec<Val> = row.iter().chain(salt.iter()).copied().collect();
    let leaf: [Val; 4] = hasher.hash_iter(preimage.iter().copied());
    let siblings = &batch.opening_proof.1;
    let path: Vec<([Val; 4], bool)> = siblings.iter().enumerate().map(|(lvl, &s)| (s, (index >> lvl) & 1 == 1)).collect();
    let depth = siblings.len();
    let cap_entry = proof.commitments.trace.roots()[index >> depth];
    (leaf, path, cap_entry)
}

/// The HIDING analog of query_quotient_merkle: the quotient-round inline-Merkle witness. Unlike the trace
/// (single matrix), the hiding quotient is nqc SEPARATE same-height matrices in ONE tree, so the leaf is a
/// MULTI-MATRIX salted hash: `MyHash((row_0 ‖ salt_0) ‖ (row_1 ‖ salt_1) ‖ …)` over the nqc chunks in matrix
/// order (matching MerkleTreeHidingMmcs's per-matrix `row ‖ salt` feeding the inner tree). All chunks sit at
/// log_global (randomized domain 2^degree_bits), so reduction is 0.
#[cfg(test)]
fn hiding_query_quotient_merkle(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    public_values: &[Val],
    q: usize,
) -> ([Val; 4], Vec<([Val; 4], bool)>, [Val; 4], usize) {
    use p3_field::PrimeField64;
    use p3_goldilocks::default_goldilocks_poseidon2_8;
    use p3_symmetric::CryptographicHasher;
    let (_, _, _, _, index_felts) = hiding_transcript_challenges(config, proof, public_values);
    let fri = &proof.opening_proof.1;
    let log_global: usize = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).sum::<usize>() + 4;
    let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
    let quot_batch = if proof.commitments.random.is_some() { 2 } else { 1 };
    let batch = &fri.query_proofs[q].input_proof[quot_batch];
    // multi-matrix salted leaf: per chunk, row_m ‖ salt_m, concatenated in matrix order.
    let mut preimage: Vec<Val> = Vec::new();
    for (m, row) in batch.opened_values.iter().enumerate() {
        preimage.extend_from_slice(row);
        preimage.extend_from_slice(&batch.opening_proof.0[m]);
    }
    let hasher = MyHash::new(default_goldilocks_poseidon2_8());
    let leaf: [Val; 4] = hasher.hash_iter(preimage.iter().copied());
    let siblings = &batch.opening_proof.1;
    let depth = siblings.len();
    let reduction = (log_global - 6) - depth; // cap_height=6; 0 when the quotient is at log_global
    let reduced = index >> reduction;
    let path: Vec<([Val; 4], bool)> = siblings.iter().enumerate().map(|(lvl, &s)| (s, (reduced >> lvl) & 1 == 1)).collect();
    let cap_entry = proof.commitments.quotient_chunks.roots()[reduced >> depth];
    (leaf, path, cap_entry, preimage.len())
}

/// The HIDING analog of query_commit_merkle_all (ARITY-2): the per-round commit-phase Merkle witness. The
/// commit phase ALSO uses the salted MMCS (HidingFriPcs's inner TwoAdicFriPcs is built on the hiding
/// ChallengeMmcs), so each round's leaf is `MyHash(group ‖ salt)` where group = the arity-2 fold pair
/// [g0, g1] (4 felts) and salt (4 felts) comes from the step's opening_proof (a (salts, siblings) tuple for
/// the hiding MMCS, vs a bare siblings Vec in the non-hiding case). Returns per round (group, leaf, path, cap).
#[cfg(test)]
fn hiding_query_commit_merkle_all(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    public_values: &[Val],
    q: usize,
) -> Vec<([Val; 4], [Val; 4], Vec<([Val; 4], bool)>, [Val; 4])> {
    use p3_field::{BasedVectorSpace, PrimeField64};
    use p3_goldilocks::default_goldilocks_poseidon2_8;
    use p3_symmetric::CryptographicHasher;
    let (_, _, _, _, index_felts) = hiding_transcript_challenges(config, proof, public_values);
    let (ro, rounds, _e, _f0) = hiding_query_fold_data(config, proof, public_values, q);
    let fri = &proof.opening_proof.1;
    let log_global: usize = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).sum::<usize>() + 4;
    let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
    let hasher = MyHash::new(default_goldilocks_poseidon2_8());
    let mut e = ro;
    let mut start = index;
    let mut out = Vec::new();
    for (r, step) in fri.query_proofs[q].commit_phase_openings.iter().enumerate() {
        let la = step.log_arity as usize;
        let (sibling, beta, bit, s) = rounds[r];
        let (g0, g1) = if !bit { (e, sibling) } else { (sibling, e) };
        let flat: Vec<Val> = [g0, g1].iter().flat_map(|x| x.as_basis_coefficients_slice().to_vec()).collect();
        let group: [Val; 4] = flat.clone().try_into().unwrap();
        // hiding: the committed leaf is `group ‖ salt` (salt from the hiding-MMCS (salts, siblings) proof).
        let salt = &step.opening_proof.0[0];
        let mut preimage = flat;
        preimage.extend_from_slice(salt);
        let leaf: [Val; 4] = hasher.hash_iter(preimage.iter().copied());
        start >>= la;
        let path_siblings = &step.opening_proof.1;
        let path: Vec<([Val; 4], bool)> = path_siblings.iter().enumerate().map(|(lvl, &sb)| (sb, (start >> lvl) & 1 == 1)).collect();
        let depth = path_siblings.len();
        let cap_entry = fri.commit_phase_commits[r].roots()[start >> depth];
        out.push((group, leaf, path, cap_entry));
        e = crate::recursion::fri_fold::native_fold(g0, g1, beta, s);
    }
    out
}

/// The HIDING analog of epilogue_openings (for ConstAir): the OOD-constraint witness — trace openings,
/// selectors, recomposed quotient(ζ), α_stark, ζ, periodic values. The is_zk=1 deltas: the selectors and
/// periodic columns are evaluated on the HALVED constraint domain init_trace_domain = degree>>is_zk (z_h uses
/// degree_bits−is_zk), and the quotient is recomposed over the is_zk-aware split domains (nqc = 1<<(log+is_zk)).
/// This is the epilogue witness the monolith's OOD region consumes; validated via p3's verify_constraints.
#[cfg(test)]
#[allow(clippy::type_complexity)]
fn hiding_epilogue_openings(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    public_values: &[Val],
) -> (Vec<Challenge>, Vec<Challenge>, Challenge, Challenge, Challenge, Challenge, Challenge, Challenge, Challenge, Vec<Challenge>) {
    let air = ConstAir;
    let (alpha_stark, zeta, _, _, _) = hiding_transcript_challenges(config, proof, public_values);
    let pcs = config.pcs();
    let is_zk = config.is_zk();
    let (_, degree) = validate_degree_bits(None, proof.degree_bits, is_zk, <MyPcs as Pcs<Challenge, Challenger>>::log_max_lde_height(pcs)).unwrap();
    let trace_domain = <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, degree);
    let init_trace_domain = <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, degree >> is_zk);
    let layout = AirLayout::from_air::<Val>(&air);
    let log_nqc = get_log_num_quotient_chunks::<Val, ConstAir>(&air, layout, is_zk);
    let nqc = 1usize << (log_nqc + is_zk);
    let qd = trace_domain.create_disjoint_domain(1 << (proof.degree_bits + log_nqc));
    let qcd = qd.split_domains(nqc);
    let quotient = recompose_quotient_from_chunks::<MyConfig>(&qcd, &proof.opened_values.quotient_chunks, zeta);
    let local = proof.opened_values.trace_local.clone();
    let next = proof.opened_values.trace_next.clone().unwrap_or_default();
    let sel = init_trace_domain.selectors_at_point(zeta);
    let periodic: Vec<Challenge> = air.periodic_columns().iter().map(|c| init_trace_domain.evaluate_periodic_column_at(c, zeta)).collect();
    (local, next, sel.is_first_row, sel.is_last_row, sel.is_transition, sel.inv_vanishing, quotient, alpha_stark, zeta, periodic)
}

/// Native hiding FRI low-degree verifier — the explicit `HidingFriPcs::verify` analog (what the in-circuit
/// hiding monolith's query region will reproduce). Replays the hiding transcript (random-commitment absorb +
/// codeword-merged opened values, as in `hiding_transcript_challenges`), then per query computes the reduced
/// opening via `hiding_query_terms` and folds it down the commit phase to `final_poly` (reusing the generic
/// `verify_query`, which re-checks each round's salted commit-phase Merkle). Accepts iff the reduced-opening
/// oracle is correct — the fold only reaches `final_poly` when `ro` is the true DEEP-combined opening, so a
/// wrong `hiding_query_terms` (missing the random round / codeword merge / randomized quotient domains) fails.
#[cfg_attr(not(test), allow(dead_code))]
fn hiding_verify_fri_native(
    config: &MyConfig,
    fri_params: &FriParameters<ChallengeMmcs>,
    input_mmcs: &ValMmcs,
    proof: &Proof<MyConfig>,
    public_values: &[Val],
) -> Result<(), String> {
    let air = ConstAir;
    let Proof { commitments, opened_values, opening_proof, degree_bits } = proof;
    let degree_bits = *degree_bits;
    let pcs = config.pcs();
    let is_zk = config.is_zk();

    let (base_degree_bits, degree) =
        validate_degree_bits(None, degree_bits, is_zk, <MyPcs as Pcs<Challenge, Challenger>>::log_max_lde_height(pcs))
            .map_err(|e| format!("degree bits: {e:?}"))?;
    let trace_domain = <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, degree);
    let init_trace_domain = <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, degree >> is_zk);
    let layout = AirLayout::from_air::<Val>(&air);
    let log_num_quotient_chunks = get_log_num_quotient_chunks::<Val, ConstAir>(&air, layout, is_zk);
    let num_quotient_chunks = 1usize << (log_num_quotient_chunks + is_zk);
    let quotient_domain_size = 1usize << (degree_bits + log_num_quotient_chunks);
    let quotient_domain = trace_domain.create_disjoint_domain(quotient_domain_size);
    let quotient_chunks_domains = quotient_domain.split_domains(num_quotient_chunks);
    let randomized_quotient_chunks_domains: Vec<_> = quotient_chunks_domains
        .iter()
        .map(|d| <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, d.size() << is_zk))
        .collect();

    // ---- transcript preamble → ζ (mirrors reverify) ----
    let mut ch = config.initialise_challenger();
    ch.observe(Val::from_usize(degree_bits));
    ch.observe(Val::from_usize(base_degree_bits));
    ch.observe(Val::from_usize(0)); // preprocessed_width (ConstAir: none)
    ch.observe(commitments.trace.clone());
    ch.observe_slice(public_values);
    let _alpha_stark: Challenge = ch.sample_algebra_element();
    ch.observe(commitments.quotient_chunks.clone());
    if let Some(r) = commitments.random.clone() {
        ch.observe(r);
    }
    let zeta: Challenge = ch.sample_algebra_element();
    let main_next = !air.main_next_row_columns().is_empty();
    let zeta_next = init_trace_domain.next_point(zeta).ok_or("no next point")?;

    // ---- build the un-merged rounds (round order = coms_to_verify) ----
    let ld_trace = degree_bits;
    let mut rounds_um: Vec<Vec<(usize, Vec<(Challenge, Vec<Challenge>)>)>> = Vec::new();
    if let Some(rv) = &opened_values.random {
        rounds_um.push(vec![(ld_trace, vec![(zeta, rv.clone())])]);
    }
    {
        let mut pts = vec![(zeta, opened_values.trace_local.clone())];
        if main_next {
            pts.push((zeta_next, opened_values.trace_next.clone().ok_or("missing trace_next")?));
        }
        rounds_um.push(vec![(ld_trace, pts)]);
    }
    rounds_um.push(
        randomized_quotient_chunks_domains
            .iter()
            .zip(&opened_values.quotient_chunks)
            .map(|(d, v)| (d.size().trailing_zeros() as usize, vec![(zeta, v.clone())]))
            .collect(),
    );

    // ---- merge codewords into each opened value + observe (α_fri absorb) ----
    let rand_cws = &opening_proof.0;
    let fri = &opening_proof.1;
    let mut merged: Vec<Vec<(usize, Vec<(Challenge, Vec<Challenge>)>)>> = Vec::new();
    for (r, round_mats) in rounds_um.iter().enumerate() {
        let mut mround = Vec::new();
        for (m, (ld, pts)) in round_mats.iter().enumerate() {
            let mut mpts = Vec::new();
            for (p, (z, vals)) in pts.iter().enumerate() {
                let mut mv = vals.clone();
                mv.extend_from_slice(&rand_cws[r][m][p]);
                ch.observe_algebra_slice(&mv);
                mpts.push((*z, mv));
            }
            mround.push((*ld, mpts));
        }
        merged.push(mround);
    }
    let alpha_fri: Challenge = ch.sample_algebra_element();

    // ---- β_r (per commit-phase round) ----
    let mut betas: Vec<Challenge> = Vec::new();
    for (comm, w) in fri.commit_phase_commits.iter().zip(&fri.commit_pow_witnesses) {
        ch.observe(comm.clone());
        if !ch.check_witness(fri_params.commit_proof_of_work_bits, *w) {
            return Err("invalid commit pow".into());
        }
        betas.push(ch.sample_algebra_element());
    }
    if fri.final_poly.len() != fri_params.final_poly_len() {
        return Err("final poly length mismatch".into());
    }
    ch.observe_algebra_slice(&fri.final_poly);
    let log_arities: Vec<usize> =
        fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).collect();
    for &la in &log_arities {
        ch.observe(Val::from_usize(la));
    }
    if !ch.check_witness(fri_params.query_proof_of_work_bits, fri.query_pow_witness) {
        return Err("invalid query pow".into());
    }

    // ---- per-query: reduced opening (hiding_query_terms) → fold → final_poly ----
    let total: usize = log_arities.iter().sum();
    let log_global_max_height = total + fri_params.log_blowup + fri_params.log_final_poly_len;
    let log_final_height = fri_params.log_blowup + fri_params.log_final_poly_len;
    let folding: TwoAdicFriFolding<(), <ChallengeMmcs as Mmcs<Challenge>>::Error> =
        TwoAdicFriFolding(core::marker::PhantomData);
    // input commitments in round order (matches `merged`/`rounds_um`): [random?, trace, quotient].
    let mut input_commits: Vec<&<ValMmcs as Mmcs<Val>>::Commitment> = Vec::new();
    if let Some(r) = commitments.random.as_ref() {
        input_commits.push(r);
    }
    input_commits.push(&commitments.trace);
    input_commits.push(&commitments.quotient_chunks);
    for qp in fri.query_proofs.iter() {
        let index = ch.sample_bits(log_global_max_height);
        // salted-leaf INPUT Merkle auth (the hiding-MMCS delta): the outer verify_batch reconstructs each
        // leaf as `row ‖ 4 salt` (salt from the opening_proof) and widens dims by SALT_ELEMS=4 internally, so
        // we pass the UN-salted row width. This is the exact preimage the in-circuit salted-leaf gadget hashes.
        for (b, mats) in merged.iter().enumerate() {
            let bo = &qp.input_proof[b];
            let heights: Vec<usize> = mats.iter().map(|(ld, _)| 1usize << (ld + fri_params.log_blowup)).collect();
            let dims: Vec<Dimensions> = mats
                .iter()
                .zip(&heights)
                .map(|((_, pts), &h)| Dimensions { width: pts[0].1.len(), height: h })
                .collect();
            let max_h = *heights.iter().max().ok_or("empty batch")?;
            let reduced_index = index >> (log_global_max_height - max_h.trailing_zeros() as usize);
            input_mmcs
                .verify_batch(input_commits[b], &dims, reduced_index, bo.into())
                .map_err(|_| format!("input batch {b} salted MMCS verify failed"))?;
        }
        let ro = hiding_query_terms(fri_params.log_blowup, log_global_max_height, index, &qp.input_proof, alpha_fri, &merged)?;
        let mut domain_index = index;
        let fold_data: Vec<CommitStep<'_, ChallengeMmcs>> = betas
            .iter()
            .zip(fri.commit_phase_commits.iter())
            .zip(qp.commit_phase_openings.iter())
            .map(|((&beta, commit), opening)| CommitStep { beta, commit, opening })
            .collect();
        let folded = verify_query(fri_params, &folding, &mut domain_index, &fold_data, ro, log_global_max_height, log_final_height)?;
        let x = final_query_point(domain_index, log_global_max_height);
        if eval_final_poly(&fri.final_poly, x) != folded {
            return Err("final poly mismatch".into());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_fri::FriParameters;
    use p3_goldilocks::default_goldilocks_poseidon2_8;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_uni_stark::{prove, verify};
    use rand::SeedableRng;

    /// Hiding config parameterized by FRI arity + query count. `max_log_arity=1` ⇒ ARITY-2 (what the in-circuit
    /// monolith's fold chain needs; all monolith end-to-end tests are arity-2). `=4` ⇒ the production arity-4.
    fn make_config_ar(max_log_arity: usize, num_queries: usize) -> MyConfig {
        let perm = default_goldilocks_poseidon2_8();
        let val_mmcs = ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), 6, ChaCha20Rng::from_rng(&mut rand::rng()));
        let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
        let fri = FriParameters {
            log_blowup: 4,
            log_final_poly_len: 0,
            max_log_arity,
            num_queries,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: 16,
            mmcs: challenge_mmcs,
        };
        let pcs = MyPcs::new(Dft::default(), val_mmcs, fri, 4, ChaCha20Rng::from_rng(&mut rand::rng()));
        MyConfig::new(pcs, Challenger::new(perm))
    }

    fn make_config() -> MyConfig {
        make_config_ar(4, 96)
    }

    fn gen_proof(config: &MyConfig, value: u64, log_height: usize) -> (Proof<MyConfig>, Vec<Val>) {
        let v = Val::from_u64(value);
        let trace = RowMajorMatrix::new(vec![v; 1 << log_height], 1);
        let pvs = vec![v];
        (prove(config, &ConstAir, trace, &pvs), pvs)
    }

    /// Ground-truth geometry of a HIDING (is_zk=1) ConstAir proof — the exact shape the in-circuit hiding
    /// monolith must lay out. Prints, per input round, the opened-row widths, codeword widths, and salt
    /// widths (⇒ the salted-leaf preimage width = committed_row ‖ salt), plus the commit-phase arities.
    #[test]
    #[ignore = "diagnostic: dump hiding ConstAir proof geometry"]
    fn hiding_proof_geometry() {
        let config = make_config();
        let (proof, _pvs) = gen_proof(&config, 42, 6);
        let fri = &proof.opening_proof.1;
        let rand_cws = &proof.opening_proof.0;
        println!("degree_bits={}", proof.degree_bits);
        println!("commitments.random present: {}", proof.commitments.random.is_some());
        println!("opened_values: trace_local={} trace_next={:?} quotient_chunks={} (each {:?}) random={:?}",
            proof.opened_values.trace_local.len(),
            proof.opened_values.trace_next.as_ref().map(|v| v.len()),
            proof.opened_values.quotient_chunks.len(),
            proof.opened_values.quotient_chunks.first().map(|c| c.len()),
            proof.opened_values.random.as_ref().map(|v| v.len()));
        println!("rand_cws rounds={}", rand_cws.len());
        for (r, round) in rand_cws.iter().enumerate() {
            let per_mat: Vec<usize> = round.iter().map(|m| m.iter().map(|p| p.len()).sum()).collect();
            println!("  round {r}: {} matrices, codeword felts/mat(sum over pts)={:?}", round.len(), per_mat);
        }
        println!("commit_phase rounds={}, arities={:?}", fri.commit_phase_commits.len(),
            fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity).collect::<Vec<_>>());
        let ip = &fri.query_proofs[0].input_proof;
        println!("input_proof batches={}", ip.len());
        for (b, bo) in ip.iter().enumerate() {
            let row_widths: Vec<usize> = bo.opened_values.iter().map(|r| r.len()).collect();
            let salt_widths: Vec<usize> = bo.opening_proof.0.iter().map(|s| s.len()).collect();
            println!("  batch {b}: {} matrices, row_widths={:?}, salt_widths={:?}  ⇒ leaf preimage(s) = row‖salt = {:?}",
                bo.opened_values.len(), row_widths, salt_widths,
                row_widths.iter().zip(&salt_widths).map(|(r, s)| r + s).collect::<Vec<_>>());
        }
    }

    #[test]
    #[ignore = "slow: native re-verifier vs p3::verify"]
    fn reverify_agrees_with_p3() {
        let config = make_config();
        let (proof, pvs) = gen_proof(&config, 42, 6);

        // sanity: p3 accepts the proof.
        assert!(verify(&config, &ConstAir, &proof, &pvs).is_ok(), "p3::verify should accept");
        // the native re-verifier accepts the same valid proof.
        if let Err(e) = reverify(&config, &proof, &pvs) {
            panic!("reverify rejected a valid proof: {e}");
        }

        // tampered public value ⇒ both reject (the constraint check fails the OOD relation).
        let bad_pvs = vec![Val::from_u64(43)];
        assert!(verify(&config, &ConstAir, &proof, &bad_pvs).is_err());
        assert!(reverify(&config, &proof, &bad_pvs).is_err(), "reverify should reject wrong public value");
    }

    /// Native hiding oracle (step 1): `hiding_transcript_challenges` extracts α_stark/ζ from a HIDING proof
    /// (the transcript with the RANDOM-commitment absorb — the defining is_zk=1 delta before ζ). Validated
    /// NON-CIRCULARLY: the proof's opened values are at the PROVER's ζ, so the OOD constraint relation
    /// (recompose quotient(ζ) + verify_constraints on the is_zk-halved init_trace_domain) holds iff the
    /// extracted ζ/α_stark equal the prover's — i.e., the hiding transcript (incl. the random absorb) is right.
    #[test]
    #[ignore = "slow: native hiding transcript oracle (α_stark/ζ + random absorb) vs the OOD constraint check"]
    fn hiding_transcript_matches_ood() {
        let config = make_config();
        let (proof, pvs) = gen_proof(&config, 42, 6);
        assert!(reverify(&config, &proof, &pvs).is_ok(), "sanity: reverify accepts the hiding proof");

        let (alpha_stark, zeta, _alpha_fri, _betas, index_felts) = hiding_transcript_challenges(&config, &proof, &pvs);
        assert_eq!(index_felts.len(), 96, "one index felt per FRI query");

        // OOD check with the ORACLE's α_stark/ζ — replicates reverify's constraint step (is_zk-aware domains).
        let air = ConstAir;
        let pcs = config.pcs();
        let is_zk = config.is_zk();
        let (_, degree) = validate_degree_bits(None, proof.degree_bits, is_zk, <MyPcs as Pcs<Challenge, Challenger>>::log_max_lde_height(pcs)).unwrap();
        let trace_domain = <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, degree);
        let init_trace_domain = <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, degree >> is_zk);
        let layout = AirLayout::from_air::<Val>(&air);
        let log_nqc = get_log_num_quotient_chunks::<Val, ConstAir>(&air, layout, is_zk);
        let nqc = 1usize << (log_nqc + is_zk);
        let qd = trace_domain.create_disjoint_domain(1 << (proof.degree_bits + log_nqc));
        let qcd = qd.split_domains(nqc);
        let quotient = recompose_quotient_from_chunks::<MyConfig>(&qcd, &proof.opened_values.quotient_chunks, zeta);
        let zeros = Challenge::zero_vec(air.width());
        let trace_next: &[Challenge] = proof.opened_values.trace_next.as_deref().unwrap_or(&zeros);
        let periodic: Vec<Challenge> = air.periodic_columns().iter().map(|c| init_trace_domain.evaluate_periodic_column_at(c, zeta)).collect();
        verify_constraints::<MyConfig, ConstAir, <MyPcs as Pcs<Challenge, Challenger>>::Error>(
            &air, &proof.opened_values.trace_local, trace_next, None, None, &periodic, &pvs, init_trace_domain, zeta, alpha_stark, quotient,
        )
        .expect("OOD check with the oracle's α_stark/ζ must hold ⇒ the hiding transcript (incl. random absorb) is correct");

        // wrong ζ ⇒ the OOD relation fails (guards against a vacuous check).
        let bad_quotient = recompose_quotient_from_chunks::<MyConfig>(&qcd, &proof.opened_values.quotient_chunks, zeta + Challenge::ONE);
        assert!(
            verify_constraints::<MyConfig, ConstAir, <MyPcs as Pcs<Challenge, Challenger>>::Error>(
                &air, &proof.opened_values.trace_local, trace_next, None, None, &periodic, &pvs, init_trace_domain, zeta + Challenge::ONE, alpha_stark, bad_quotient,
            )
            .is_err(),
            "a wrong ζ must fail the OOD relation"
        );
        println!("native hiding oracle: transcript α_stark/ζ (with the random-commitment absorb) validated via the OOD constraint check");
    }

    /// Native hiding oracle (step 2): `hiding_query_terms` (the reduced-opening extraction) + the native
    /// hiding FRI verify (`hiding_verify_fri_native`). Validated NON-CIRCULARLY against `p3::verify`: the
    /// native verifier reconstructs the reduced opening from the merged (public ‖ codeword) openings + the
    /// randomized quotient domains + the extra random round, then folds it to `final_poly`. The fold reaches
    /// `final_poly` iff `ro` is the TRUE DEEP-combined opening — so accepting the same proof p3 accepts
    /// validates the whole reduced-opening oracle. A tamper (wrong opened value) must break the fold.
    #[test]
    #[ignore = "slow: native hiding FRI verify (reduced opening + fold) vs p3::verify"]
    fn hiding_query_terms_folds_to_final_poly() {
        let config = make_config();
        let (mut proof, pvs) = gen_proof(&config, 42, 6);
        assert!(verify(&config, &ConstAir, &proof, &pvs).is_ok(), "sanity: p3::verify accepts");

        // Rebuild the hiding FRI parameters the driver/verify_query need (deterministic — Poseidon2 + the
        // literals are fixed; the ChaCha rng only salts on the PROVE side, so any seed verifies identically).
        let perm = default_goldilocks_poseidon2_8();
        let val_mmcs = ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), 6, ChaCha20Rng::seed_from_u64(0));
        let fri_params = FriParameters {
            log_blowup: 4,
            log_final_poly_len: 0,
            max_log_arity: 4,
            num_queries: 96,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: 16,
            mmcs: ChallengeMmcs::new(val_mmcs.clone()),
        };

        // the native hiding FRI verifier accepts the valid proof: salted-leaf INPUT Merkle auth (row ‖ 4 salt)
        // + reduced opening (hiding_query_terms) folds to final_poly ⇒ the whole reduced-opening oracle is true.
        if let Err(e) = hiding_verify_fri_native(&config, &fri_params, &val_mmcs, &proof, &pvs) {
            panic!("native hiding FRI verify rejected a valid proof: {e}");
        }

        // tamper: corrupt an opened trace value ⇒ the reduced opening is wrong ⇒ the fold misses final_poly.
        proof.opened_values.trace_local[0] += Challenge::ONE;
        assert!(
            hiding_verify_fri_native(&config, &fri_params, &val_mmcs, &proof, &pvs).is_err(),
            "a tampered opened value must break the fold to final_poly"
        );
        println!("native hiding oracle: salted-leaf INPUT Merkle (row ‖ 4 salt) + reduced opening + fold validated vs p3::verify");
    }

    // ---------------- in-circuit hiding monolith harness (#86) — transcript witness ----------------
    // A copy of the monolith's transcript simulator `Sim`, driving the HIDING transcript so the in-circuit
    // transcript region's block schedule can be derived from a hiding proof. Poseidon2 sponge (W=8, RATE=4,
    // overwrite-mode duplex) — identical to monolith::tests::Sim.
    use crate::poseidon2_air::{native_permute, W as SPONGE_W};
    const RATE: usize = 4;
    const CAP_LANE: usize = RATE;

    struct Sim {
        state: [Val; SPONGE_W],
        input: Vec<Val>,
        output: Vec<Val>,
        block_inputs: Vec<[Val; SPONGE_W]>,
        counts: Vec<u8>,
    }
    impl Sim {
        fn new() -> Self {
            Self { state: [Val::ZERO; SPONGE_W], input: vec![], output: vec![], block_inputs: vec![], counts: vec![] }
        }
        fn duplex(&mut self) {
            let num = self.input.len();
            for (i, v) in self.input.drain(..).enumerate() {
                self.state[i] = v;
            }
            if num > 0 {
                for i in num..RATE {
                    self.state[i] = Val::ZERO;
                }
                self.state[CAP_LANE] += Val::from_u64(num as u64);
            }
            self.block_inputs.push(self.state);
            self.counts.push(num as u8);
            self.state = native_permute(self.state);
            self.output = self.state[..RATE].to_vec();
        }
        fn observe(&mut self, v: Val) {
            self.output.clear();
            self.input.push(v);
            if self.input.len() == RATE {
                self.duplex();
            }
        }
        fn observe_ext(&mut self, x: Challenge) {
            use p3_field::BasedVectorSpace;
            for &c in x.as_basis_coefficients_slice() {
                self.observe(c);
            }
        }
        fn sample_base(&mut self) -> Val {
            if !self.input.is_empty() || self.output.is_empty() {
                self.duplex();
            }
            self.output.pop().unwrap()
        }
        fn sample_ext(&mut self) -> [Val; 2] {
            let c0 = self.sample_base();
            let c1 = self.sample_base();
            [c0, c1]
        }
        // block/lane-recording variants (for deriving the monolith's challenge/index binds from the schedule).
        fn sample_base_bl(&mut self) -> (Val, usize, usize) {
            if !self.input.is_empty() || self.output.is_empty() {
                self.duplex();
            }
            let blk = self.block_inputs.len() - 1;
            let lane = self.output.len() - 1; // pop from the back
            (self.output.pop().unwrap(), blk, lane)
        }
        fn sample_ext_bl(&mut self) -> ([Val; 2], usize) {
            let (c0, blk, _) = self.sample_base_bl();
            let (c1, _, _) = self.sample_base_bl();
            ([c0, c1], blk)
        }
    }

    fn cap_felts_h(commit: &<ValMmcs as p3_commit::Mmcs<Val>>::Commitment) -> Vec<Val> {
        commit.roots().iter().flatten().copied().collect()
    }

    /// The HIDING analog of monolith::tests::sim_full: replay the is_zk=1 transcript in the block-based Sim
    /// (the random-commitment absorb after the quotient commitment, and the codeword-MERGED opened-value
    /// absorb before α_fri), returning the Poseidon2 block schedule + the challenges [α_stark, ζ, α_fri, β_r].
    fn sim_full_hiding(config: &MyConfig, proof: &Proof<MyConfig>, pvs: &[Val]) -> (Vec<[Val; SPONGE_W]>, Vec<u8>, Vec<[Val; 2]>) {
        let pcs = config.pcs();
        let is_zk = config.is_zk();
        let degree_bits = proof.degree_bits;
        let (base_degree_bits, _) =
            validate_degree_bits(None, degree_bits, is_zk, <MyPcs as Pcs<Challenge, Challenger>>::log_max_lde_height(pcs)).expect("degree bits");
        let mut s = Sim::new();
        // preamble → α_stark
        s.observe(Val::from_usize(degree_bits));
        s.observe(Val::from_usize(base_degree_bits));
        s.observe(Val::from_usize(0));
        for f in cap_felts_h(&proof.commitments.trace) {
            s.observe(f);
        }
        for &p in pvs {
            s.observe(p);
        }
        let a_stark = s.sample_ext();
        // quotient + RANDOM commitments → ζ
        for f in cap_felts_h(&proof.commitments.quotient_chunks) {
            s.observe(f);
        }
        if let Some(r) = &proof.commitments.random {
            for f in cap_felts_h(r) {
                s.observe(f);
            }
        }
        let zeta = s.sample_ext();
        // codeword-merged opened-value absorb (round order [random?, trace{ζ,ζ_next}, quotient chunks])
        let rand_cws = &proof.opening_proof.0;
        let mut round = 0usize;
        let observe_merged = |s: &mut Sim, public: &[Challenge], cw: &[Challenge]| {
            for &x in public {
                s.observe_ext(x);
            }
            for &x in cw {
                s.observe_ext(x);
            }
        };
        if let Some(rv) = &proof.opened_values.random {
            observe_merged(&mut s, rv, &rand_cws[round][0][0]);
            round += 1;
        }
        observe_merged(&mut s, &proof.opened_values.trace_local, &rand_cws[round][0][0]);
        if let Some(tn) = &proof.opened_values.trace_next {
            observe_merged(&mut s, tn, &rand_cws[round][0][1]);
        }
        round += 1;
        for (i, c) in proof.opened_values.quotient_chunks.iter().enumerate() {
            observe_merged(&mut s, c, &rand_cws[round][i][0]);
        }
        let a_fri = s.sample_ext();
        // β_r (commit-pow is 0 bits ⇒ check_witness is a no-op, matching sim_full)
        let fri = &proof.opening_proof.1;
        let mut chs = vec![a_stark, zeta, a_fri];
        for comm in &fri.commit_phase_commits {
            for f in cap_felts_h(comm) {
                s.observe(f);
            }
            chs.push(s.sample_ext());
        }
        (s.block_inputs, s.counts, chs)
    }

    /// Native hiding monolith harness (#86, step 1): the block-based transcript Sim reproduces the HIDING
    /// challenges (α_stark, ζ, α_fri, β_r) that the real challenger produces (hiding_transcript_challenges).
    /// This validates the Poseidon2 block schedule the in-circuit transcript region will replay — including
    /// the two is_zk=1 deltas (random-commitment absorb + codeword-merged opened-value absorb).
    #[test]
    #[ignore = "slow: hiding transcript Sim (block schedule) vs the real challenger"]
    fn hiding_transcript_sim_matches() {
        use p3_field::BasedVectorSpace;
        let config = make_config();
        let (proof, pvs) = gen_proof(&config, 42, 6);
        let (blocks, counts, chs) = sim_full_hiding(&config, &proof, &pvs);
        assert_eq!(blocks.len(), counts.len());
        let (a_stark, zeta, a_fri, betas, _idx) = hiding_transcript_challenges(&config, &proof, &pvs);
        let c = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
        assert_eq!(chs[0], c(a_stark), "Sim α_stark != challenger");
        assert_eq!(chs[1], c(zeta), "Sim ζ != challenger");
        assert_eq!(chs[2], c(a_fri), "Sim α_fri != challenger (random absorb + codeword merge)");
        assert_eq!(chs.len(), 3 + betas.len(), "β count");
        for (i, b) in betas.iter().enumerate() {
            assert_eq!(chs[3 + i], c(*b), "Sim β_{i} != challenger");
        }
        println!("hiding transcript Sim: {} blocks reproduce α_stark/ζ/α_fri/{} β_r vs the real challenger", blocks.len(), betas.len());
    }

    /// Native hiding monolith harness (#86, step 2): `hiding_multicol_query_terms` produces the per-query
    /// reduced-opening TERMS (z, p_z, p_x) in the monolith's arith-tile format. Validated by folding their `ro`
    /// to `final_poly` (reusing verify_query) for several queries — the fold reaches final_poly ONLY when the
    /// terms are the true DEEP reduced opening (so this validates the terms extraction: random round + merged
    /// codewords + 2× quotient over randomized domains). Reports the term count (≫ the is_zk=0 case).
    #[test]
    #[ignore = "slow: hiding per-query reduced-opening terms fold to final_poly"]
    fn hiding_multicol_terms_fold_to_final() {
        use p3_field::PrimeField64;
        let config = make_config();
        let (proof, pvs) = gen_proof(&config, 42, 6);
        let perm = default_goldilocks_poseidon2_8();
        let val_mmcs = ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), 6, ChaCha20Rng::seed_from_u64(0));
        let fri_params = FriParameters {
            log_blowup: 4,
            log_final_poly_len: 0,
            max_log_arity: 4,
            num_queries: 96,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: 16,
            mmcs: ChallengeMmcs::new(val_mmcs),
        };
        let (_, _, alpha_fri, betas, index_felts) = hiding_transcript_challenges(&config, &proof, &pvs);
        let fri = &proof.opening_proof.1;
        let log_global: usize = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).sum::<usize>() + 4;
        let folding: TwoAdicFriFolding<(), <ChallengeMmcs as Mmcs<Challenge>>::Error> = TwoAdicFriFolding(core::marker::PhantomData);
        let mut n_terms = 0;
        for q in [0usize, 1, fri.query_proofs.len() - 1] {
            let (terms, _x, alpha, ro) = hiding_multicol_query_terms(&config, &proof, &pvs, q);
            assert_eq!(alpha, alpha_fri, "q{q}: terms use α_fri");
            n_terms = terms.len();
            // all hiding-ConstAir input matrices share one height (log_global) ⇒ ro seeds the fold at log_global.
            let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
            let mut di = index;
            let qp = &fri.query_proofs[q];
            let fold_data: Vec<CommitStep<'_, ChallengeMmcs>> = betas
                .iter()
                .zip(fri.commit_phase_commits.iter())
                .zip(qp.commit_phase_openings.iter())
                .map(|((&b, c), o)| CommitStep { beta: b, commit: c, opening: o })
                .collect();
            let folded = verify_query(&fri_params, &folding, &mut di, &fold_data, vec![(log_global, ro)], log_global, 4).expect("fold");
            let x = final_query_point(di, log_global);
            assert_eq!(eval_final_poly(&fri.final_poly, x), folded, "q{q}: terms' ro must fold to final_poly");
        }
        println!("hiding per-query terms: {n_terms} reduced-opening terms fold to final_poly (random round + merged codewords + 2× quotient) — the true reduced opening");
    }

    /// Native hiding monolith harness (#86, step 3): the ARITY-2 fold-chain witness. On an ARITY-2 hiding proof
    /// (what the in-circuit monolith consumes), hiding_query_fold_data folds ro through the commit phase to `e`,
    /// and `e == final_poly[0]` (log_final_poly_len=0) — the monolith's fold-chain accept. Confirms the hiding
    /// proof folds identically to the non-hiding case once arity-2 (the hiding deltas are all in the input).
    #[test]
    #[ignore = "slow: arity-2 hiding fold-chain witness reaches final_poly[0]"]
    fn hiding_fold_rounds_reach_final() {
        let config = make_config_ar(1, 96); // ARITY-2 hiding (the monolith's fold arity)
        let (proof, pvs) = gen_proof(&config, 42, 6);
        assert!(reverify(&config, &proof, &pvs).is_ok(), "sanity: arity-2 hiding proof is valid");
        let fri = &proof.opening_proof.1;
        assert!(
            fri.query_proofs[0].commit_phase_openings.iter().all(|o| o.log_arity == 1),
            "config must be arity-2 (log_arity==1) for the monolith fold chain"
        );
        let mut n_rounds = 0;
        for q in [0usize, 1, fri.query_proofs.len() - 1] {
            let (_ro, rounds, e, final0) = hiding_query_fold_data(&config, &proof, &pvs, q);
            assert_eq!(e, final0, "q{q}: hiding fold chain must reach final_poly[0]");
            n_rounds = rounds.len();
        }
        println!("hiding fold chain (arity-2): {n_rounds} rounds fold ro → final_poly[0] (monolith-compatible fold witness)");
    }

    /// Native hiding monolith harness (#86, step 4): the SALTED inline-Merkle witness. hiding_query_input_merkle
    /// gives the trace leaf `MyHash(row ‖ salt)` + path + cap entry; folding the leaf up the path (MyCompress,
    /// index-bit direction) must reach the cap entry — i.e., the salted leaf authenticates against the trace
    /// commitment. This is the leaf+path the monolith's inline Merkle region binds (validated leaf sponge W+8).
    #[test]
    #[ignore = "slow: hiding salted input-Merkle leaf+path folds to the trace cap"]
    fn hiding_input_merkle_folds_to_cap() {
        use p3_symmetric::PseudoCompressionFunction;
        let config = make_config();
        let (proof, pvs) = gen_proof(&config, 42, 6);
        let compressor = MyCompress::new(default_goldilocks_poseidon2_8());
        let fri = &proof.opening_proof.1;
        let mut depth = 0;
        for q in [0usize, 1, fri.query_proofs.len() - 1] {
            let (leaf, path, cap_entry) = hiding_query_input_merkle(&config, &proof, &pvs, q);
            let mut node = leaf;
            for (sib, dir) in &path {
                node = if *dir { compressor.compress([*sib, node]) } else { compressor.compress([node, *sib]) };
            }
            assert_eq!(node, cap_entry, "q{q}: salted leaf (row ‖ salt) + path must fold to the trace cap entry");
            depth = path.len();
        }
        println!("hiding input Merkle: salted leaf (row ‖ salt) + {depth}-level path folds to the trace cap entry");
    }

    /// Native hiding monolith harness (#86, step 5): the MULTI-MATRIX salted quotient-Merkle witness.
    /// hiding_query_quotient_merkle builds the leaf from all nqc chunks (per-chunk row ‖ salt, concatenated);
    /// folding it up the path must reach the quotient cap entry — validating both the multi-matrix leaf
    /// concatenation order and the salted quotient authentication against the quotient commitment.
    #[test]
    #[ignore = "slow: hiding multi-matrix salted quotient-Merkle leaf+path folds to the quotient cap"]
    fn hiding_quotient_merkle_folds_to_cap() {
        use p3_symmetric::PseudoCompressionFunction;
        let config = make_config();
        let (proof, pvs) = gen_proof(&config, 42, 6);
        let compressor = MyCompress::new(default_goldilocks_poseidon2_8());
        let fri = &proof.opening_proof.1;
        let nqc = proof.opened_values.quotient_chunks.len();
        let mut leaf_felts = 0;
        for q in [0usize, 1, fri.query_proofs.len() - 1] {
            let (leaf, path, cap_entry, n) = hiding_query_quotient_merkle(&config, &proof, &pvs, q);
            leaf_felts = n;
            let mut node = leaf;
            for (sib, dir) in &path {
                node = if *dir { compressor.compress([*sib, node]) } else { compressor.compress([node, *sib]) };
            }
            assert_eq!(node, cap_entry, "q{q}: multi-matrix salted quotient leaf + path must fold to the quotient cap entry");
        }
        println!("hiding quotient Merkle: {nqc}-chunk multi-matrix salted leaf ({leaf_felts} felts) + path folds to the quotient cap entry");
    }

    /// Native hiding monolith harness (#86, step 6): the per-round commit-phase salted-Merkle witness (ARITY-2).
    /// hiding_query_commit_merkle_all gives, per commit round, the fold group + salted leaf MyHash(group ‖ salt)
    /// + path + round cap; folding each leaf up its path must reach that round's commitment cap — validating the
    /// salted commit-phase Merkle (the FRI fold's authentication) in the monolith's per-round format.
    #[test]
    #[ignore = "slow: arity-2 hiding commit-phase salted Merkle folds to each round's cap"]
    fn hiding_commit_merkle_folds_to_cap() {
        use p3_symmetric::PseudoCompressionFunction;
        let config = make_config_ar(1, 96); // ARITY-2 (commit-phase fold group is a pair)
        let (proof, pvs) = gen_proof(&config, 42, 6);
        let compressor = MyCompress::new(default_goldilocks_poseidon2_8());
        let fri = &proof.opening_proof.1;
        let mut n_rounds = 0;
        for q in [0usize, 1, fri.query_proofs.len() - 1] {
            let rounds = hiding_query_commit_merkle_all(&config, &proof, &pvs, q);
            n_rounds = rounds.len();
            for (r, (_group, leaf, path, cap_entry)) in rounds.iter().enumerate() {
                let mut node = *leaf;
                for (sib, dir) in path {
                    node = if *dir { compressor.compress([*sib, node]) } else { compressor.compress([node, *sib]) };
                }
                assert_eq!(node, *cap_entry, "q{q} round {r}: salted commit-phase leaf + path must fold to the round cap");
            }
        }
        println!("hiding commit-phase Merkle: {n_rounds} rounds of salted MyHash(group ‖ salt) + path fold to each round's cap");
    }

    /// Native hiding monolith harness (#86, step 7 — the last witness piece): the OOD-constraint epilogue.
    /// hiding_epilogue_openings packages the trace openings + HALVED-domain selectors + recomposed quotient(ζ)
    /// + α_stark/ζ; p3's verify_constraints on init_trace_domain (degree>>is_zk) must accept — i.e., the OOD
    /// relation holds at the extracted challenges. A tampered quotient(ζ) must fail (guards a vacuous check).
    #[test]
    #[ignore = "slow: hiding epilogue openings pass verify_constraints on the halved domain"]
    fn hiding_epilogue_openings_pass_verify_constraints() {
        let config = make_config();
        let (proof, pvs) = gen_proof(&config, 42, 6);
        assert!(reverify(&config, &proof, &pvs).is_ok(), "sanity: hiding proof valid");
        let (local, next, is_first, is_last, is_trans, inv_van, quotient, alpha, zeta, periodic) =
            hiding_epilogue_openings(&config, &proof, &pvs);
        let air = ConstAir;
        let pcs = config.pcs();
        let is_zk = config.is_zk();
        let (_, degree) = validate_degree_bits(None, proof.degree_bits, is_zk, <MyPcs as Pcs<Challenge, Challenger>>::log_max_lde_height(pcs)).unwrap();
        let init_trace_domain = <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, degree >> is_zk);
        // sanity: the packaged selectors are exactly the halved-domain selectors at ζ.
        let sel = init_trace_domain.selectors_at_point(zeta);
        assert_eq!((is_first, is_last, is_trans, inv_van), (sel.is_first_row, sel.is_last_row, sel.is_transition, sel.inv_vanishing));
        verify_constraints::<MyConfig, ConstAir, <MyPcs as Pcs<Challenge, Challenger>>::Error>(
            &air, &local, &next, None, None, &periodic, &pvs, init_trace_domain, zeta, alpha, quotient,
        )
        .expect("hiding epilogue openings must satisfy the OOD constraint relation");
        // tamper: wrong quotient(ζ) ⇒ reject.
        assert!(
            verify_constraints::<MyConfig, ConstAir, <MyPcs as Pcs<Challenge, Challenger>>::Error>(
                &air, &local, &next, None, None, &periodic, &pvs, init_trace_domain, zeta, alpha, quotient + Challenge::ONE,
            )
            .is_err(),
            "a tampered quotient(ζ) must fail the OOD relation"
        );
        println!("hiding epilogue: OOD openings (halved domain, is_zk-recomposed quotient) satisfy verify_constraints");
    }

    // ================================ #86 AIR mode — END-TO-END hiding monolith ================================

    fn peak_rss_bytes() -> u64 {
        // VmHWM = peak resident set size of this process (Linux).
        std::fs::read_to_string("/proc/self/status")
            .ok()
            .and_then(|s| {
                s.lines().find_map(|l| l.strip_prefix("VmHWM:").and_then(|r| r.split_whitespace().next()?.parse::<u64>().ok()))
            })
            .map(|kb| kb * 1024)
            .unwrap_or(0)
    }

    /// The is_zk-aware analog of quotient_recompose_weights: the in-circuit epilogue's quotient(ζ) = Σ_i zps_i·
    /// chunk_i(ζ), with zps_i the verifier-computed weights over the HIDING split domains (nqc = 1<<(log+is_zk)).
    /// Matches p3's recompose_quotient_from_chunks (asserted against it in the harness before feeding the pis).
    fn hiding_quotient_recompose_weights(config: &MyConfig, proof: &Proof<MyConfig>, pvs: &[Val]) -> Vec<Challenge> {
        use p3_commit::PolynomialSpace;
        let (_, zeta, _, _, _) = hiding_transcript_challenges(config, proof, pvs);
        let pcs = config.pcs();
        let is_zk = config.is_zk();
        let (_, degree) = validate_degree_bits(None, proof.degree_bits, is_zk, <MyPcs as Pcs<Challenge, Challenger>>::log_max_lde_height(pcs)).unwrap();
        let trace_domain = <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, degree);
        let layout = AirLayout::from_air::<Val>(&ConstAir);
        let log_nqc = get_log_num_quotient_chunks::<Val, ConstAir>(&ConstAir, layout, is_zk);
        let nqc = 1usize << (log_nqc + is_zk);
        let qd = trace_domain.create_disjoint_domain(1 << (proof.degree_bits + log_nqc));
        let qcd = qd.split_domains(nqc);
        (0..nqc)
            .map(|i| {
                let mut zp = Challenge::ONE;
                for j in 0..nqc {
                    if j != i {
                        zp *= qcd[j].vanishing_poly_at_point(zeta) * qcd[j].vanishing_poly_at_point(qcd[i].first_point()).inverse();
                    }
                }
                zp
            })
            .collect()
    }

    /// The HIDING analog of monolith::tests::sim_full: sim_full_hiding + recording the challenge binds (block per
    /// challenge) and the index binds/felts (block, lane per query) — the full transcript schedule the monolith needs.
    #[allow(clippy::type_complexity)]
    fn sim_full_hiding_all(
        config: &MyConfig,
        proof: &Proof<MyConfig>,
        pvs: &[Val],
    ) -> (Vec<[Val; SPONGE_W]>, Vec<u8>, Vec<usize>, Vec<[Val; 2]>, Vec<(usize, usize)>, Vec<Val>) {
        let pcs = config.pcs();
        let is_zk = config.is_zk();
        let degree_bits = proof.degree_bits;
        let (base_degree_bits, _) =
            validate_degree_bits(None, degree_bits, is_zk, <MyPcs as Pcs<Challenge, Challenger>>::log_max_lde_height(pcs)).expect("degree bits");
        let mut s = Sim::new();
        s.observe(Val::from_usize(degree_bits));
        s.observe(Val::from_usize(base_degree_bits));
        s.observe(Val::from_usize(0));
        for f in cap_felts_h(&proof.commitments.trace) {
            s.observe(f);
        }
        for &p in pvs {
            s.observe(p);
        }
        let (a_stark, b0) = s.sample_ext_bl();
        for f in cap_felts_h(&proof.commitments.quotient_chunks) {
            s.observe(f);
        }
        if let Some(r) = &proof.commitments.random {
            for f in cap_felts_h(r) {
                s.observe(f);
            }
        }
        let (zeta, b1) = s.sample_ext_bl();
        let rand_cws = &proof.opening_proof.0;
        let mut round = 0usize;
        let observe_merged = |s: &mut Sim, public: &[Challenge], cw: &[Challenge]| {
            for &x in public {
                s.observe_ext(x);
            }
            for &x in cw {
                s.observe_ext(x);
            }
        };
        if let Some(rv) = &proof.opened_values.random {
            observe_merged(&mut s, rv, &rand_cws[round][0][0]);
            round += 1;
        }
        observe_merged(&mut s, &proof.opened_values.trace_local, &rand_cws[round][0][0]);
        if let Some(tn) = &proof.opened_values.trace_next {
            observe_merged(&mut s, tn, &rand_cws[round][0][1]);
        }
        round += 1;
        for (i, c) in proof.opened_values.quotient_chunks.iter().enumerate() {
            observe_merged(&mut s, c, &rand_cws[round][i][0]);
        }
        let (a_fri, b2) = s.sample_ext_bl();
        let mut binds = vec![b0, b1, b2];
        let mut chs = vec![a_stark, zeta, a_fri];
        let fri = &proof.opening_proof.1;
        for comm in &fri.commit_phase_commits {
            for f in cap_felts_h(comm) {
                s.observe(f);
            }
            let (beta, bb) = s.sample_ext_bl();
            binds.push(bb);
            chs.push(beta);
        }
        for &x in &fri.final_poly {
            s.observe_ext(x);
        }
        let log_arities: Vec<usize> = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).collect();
        for &la in &log_arities {
            s.observe(Val::from_usize(la));
        }
        s.observe(fri.query_pow_witness);
        let _ = s.sample_base_bl();
        let mut index_binds = Vec::new();
        let mut index_felts = Vec::new();
        for _ in 0..fri.query_proofs.len() {
            let (f, blk, lane) = s.sample_base_bl();
            index_binds.push((blk, lane));
            index_felts.push(f);
        }
        (s.block_inputs, s.counts, binds, chs, index_binds, index_felts)
    }

    /// #86 AIR mode — the END-TO-END hiding monolith: builds MonolithAir{is_zk:1} over a real arity-2 HIDING
    /// ConstAir proof (HidingFriPcs), proves it with p3_uni_stark::prove, and asserts p3_uni_stark::verify
    /// accepts — the single in-circuit AIR accepts iff p3::verify(hiding_inner) accepts. Returns (log2 height,
    /// peak RSS bytes). Reduced queries keep it inside the 8 GB budget (arity-2, is_zk=1).
    fn run_hiding_monolith(n_queries: usize, check_only: bool) -> (u32, u64) {
        run_hiding_monolith_lh(n_queries, 6, check_only)
    }

    fn run_hiding_monolith_lh(n_queries: usize, log_height: usize, check_only: bool) -> (u32, u64) {
        use crate::recursion::monolith::{monolith_build_trace, HidingWitness, MonolithAir};
        use p3_field::{BasedVectorSpace, PrimeField64};
        let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
        let config = make_config_ar(1, n_queries); // arity-2 hiding
        let (proof, pvs) = gen_proof(&config, 42, log_height);
        assert!(verify(&config, &ConstAir, &proof, &pvs).is_ok(), "sanity: p3::verify accepts the hiding ConstAir proof");
        let (block_inputs, counts, binds, chs, index_binds, index_felts) = sim_full_hiding_all(&config, &proof, &pvs);
        let fri = &proof.opening_proof.1;
        let log_global: usize = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).sum::<usize>() + 4;
        let random_present = proof.commitments.random.is_some();
        let trace_batch = if random_present { 1 } else { 0 };
        let quot_batch = trace_batch + 1;
        let nqc = proof.opened_values.quotient_chunks.len();

        let mut per_query = Vec::new();
        let mut quot_paths = Vec::new();
        let mut commit_data = Vec::new();
        let mut hiding = Vec::new();
        let mut n_terms = 0;
        let mut final0 = Challenge::ZERO;
        for q in 0..n_queries {
            let (terms, _x, alpha, ro) = hiding_multicol_query_terms(&config, &proof, &pvs, q);
            let (_ro2, rounds, _e, f0) = hiding_query_fold_data(&config, &proof, &pvs, q);
            let (_leaf, path, _cap) = hiding_query_input_merkle(&config, &proof, &pvs, q);
            let (_ql, qpath, _qce, _qw) = hiding_query_quotient_merkle(&config, &proof, &pvs, q);
            let cm = hiding_query_commit_merkle_all(&config, &proof, &pvs, q);
            if q == 0 {
                final0 = f0;
            }
            n_terms = terms.len();
            let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
            // salts extracted directly from the proof (mirroring the salted-leaf witness fns).
            let qp = &fri.query_proofs[q];
            let trace_salt: [Val; 4] = qp.input_proof[trace_batch].opening_proof.0[0].clone().try_into().unwrap();
            let rbatch = &qp.input_proof[0]; // random-round batch
            let random_salt: [Val; 4] = rbatch.opening_proof.0[0].clone().try_into().unwrap();
            let random_path: Vec<([Val; 4], bool)> =
                rbatch.opening_proof.1.iter().enumerate().map(|(lvl, &s)| (s, (index >> lvl) & 1 == 1)).collect();
            let quot_salts: Vec<[Val; 4]> =
                (0..nqc).map(|m| qp.input_proof[quot_batch].opening_proof.0[m].clone().try_into().unwrap()).collect();
            let commit_salts: Vec<[Val; 4]> =
                qp.commit_phase_openings.iter().map(|o| o.opening_proof.0[0].clone().try_into().unwrap()).collect();
            per_query.push(((index, terms, alpha, ro, rounds), pvs[0], path));
            quot_paths.push(qpath);
            commit_data.push(cm);
            hiding.push(HidingWitness { trace_salt, random_salt, random_path, quot_salts, commit_salts });
        }

        let air = MonolithAir {
            counts,
            binds,
            index_binds,
            n_queries,
            n_terms,
            inner_counter: false,
            column_window: false,
            k_instances: 1,
            fold: false,
            constraints: vec![],
            w_inner_f: 1,
            n_pub_f: 1,
            n_periodic_f: 0,
            is_zk: 1,
        };

        // pis in the geometry's order: challenges, index felts, final_poly[0], full trace cap, full quotient cap,
        // inner pub, per-round commit caps, (periodic — none for ConstAir), qwt weights (nqc>1), full random cap.
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
        for e in proof.commitments.trace.roots().iter() {
            pis.extend_from_slice(e);
        }
        for e in proof.commitments.quotient_chunks.roots().iter() {
            pis.extend_from_slice(e);
        }
        pis.push(pvs[0]);
        for comm in fri.commit_phase_commits.iter() {
            for e in comm.roots().iter() {
                pis.extend_from_slice(e);
            }
        }
        if nqc > 1 {
            // qwt weights; pre-check Σ zps_i·chunk_i == p3's recompose (guards the in-circuit recompose).
            let zps = hiding_quotient_recompose_weights(&config, &proof, &pvs);
            let (_, _, _, _, _, _, eo_quot, _, _, _) = hiding_epilogue_openings(&config, &proof, &pvs);
            let x = Challenge::from_basis_coefficients_fn(|k| if k == 1 { Val::ONE } else { Val::ZERO });
            let mut rq = Challenge::ZERO;
            for (i, ch) in proof.opened_values.quotient_chunks.iter().enumerate() {
                rq += zps[i] * (ch[0] + ch[1] * x);
            }
            assert_eq!(rq, eo_quot, "hiding qwt: Σ zps_i·chunk_i must equal p3 recompose_quotient_from_chunks");
            for z in &zps {
                let c = cc(*z);
                pis.push(c[0]);
                pis.push(c[1]);
            }
        }
        for e in proof.commitments.random.as_ref().unwrap().roots().iter() {
            pis.extend_from_slice(e);
        }
        assert_eq!(pis.len(), air.pis_count(), "assembled pis length must match the geometry's pis_count");

        let trace = monolith_build_trace(&air, &block_inputs, &per_query, chs[2], &index_felts, &quot_paths, &commit_data, &[], Some(&hiding));
        let hh = air.height();
        println!("hiding monolith @ {n_queries} queries: 2^{} rows (width {}, is_zk=1, arity-2)", hh.trailing_zeros(), air.fused_w());
        // per-query masked indices — for correlating an index-dependent failure with the triggering query.
        let idxs: Vec<usize> = index_felts.iter().map(|f| (f.as_canonical_u64() as usize) & ((1 << log_global) - 1)).collect();
        println!("  query indices (lg={log_global}): {idxs:?}");
        if check_only {
            // localize a constraint/build mismatch fast (row + constraint index) without the slow FRI, then
            // prove+verify the SAME instance — one run settles whether a failure is a constraint violation
            // (check panics with row+constraint) or something else (check passes, verify rejects).
            p3_air::check_constraints(&air, &trace, &pis);
            println!("check_constraints PASSED @ {n_queries} queries (2^{} rows) — proving the SAME instance...", hh.trailing_zeros());
            let prf = prove(&config, &air, trace, &pis);
            if let Err(e) = verify(&config, &air, &prf, &pis) {
                panic!("IMPOSSIBLE-CLASS bug: check_constraints passed but verify rejected the SAME instance: {e:?}");
            }
            println!("prove+verify ALSO PASSED on the same instance @ {n_queries} queries");
            return (hh.trailing_zeros(), peak_rss_bytes());
        }
        let prf = prove(&config, &air, trace, &pis);
        if let Err(e) = verify(&config, &air, &prf, &pis) {
            panic!("hiding monolith rejected a valid proof: {e:?}");
        }
        // tamper: wrong inner public value ⇒ OOD epilogue fails ⇒ reject.
        let mut bad = pis.clone();
        bad[air.pub_pi()] += Val::ONE;
        assert!(verify(&config, &air, &prf, &bad).is_err(), "tampered inner pub ⇒ epilogue rejects");
        // tamper: the FULL trace cap entry query 0 selects (index0 >> input_depth) ⇒ cap-mux ≠ terminal ⇒ reject.
        let idx0 = (index_felts[0].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        let input_depth = log_global - 6;
        let mut bad_cap = pis.clone();
        bad_cap[air.cap_base() + (idx0 >> input_depth) * 4] += Val::ONE;
        assert!(verify(&config, &air, &prf, &bad_cap).is_err(), "tampered selected trace cap ⇒ cap-mux rejects");
        // tamper: the selected RANDOM cap entry ⇒ the random round's cap-mux ⇒ reject (validates the hiding auth).
        let mut bad_rcap = pis.clone();
        bad_rcap[air.random_cap_base() + (idx0 >> input_depth) * 4] += Val::ONE;
        assert!(verify(&config, &air, &prf, &bad_rcap).is_err(), "tampered selected random cap ⇒ cap-mux rejects");
        let rss = peak_rss_bytes();
        println!(" -> peak RSS {} MiB", rss / (1 << 20));
        (hh.trailing_zeros(), rss)
    }

    #[test]
    #[ignore = "slow: end-to-end hiding (is_zk=1) monolith proves + p3::verify accepts (#86)"]
    fn hiding_monolith_end_to_end() {
        // The LARGEST hiding config inside the 8 GB budget: log_height=4 (degree_bits=5, log_global=9,
        // cm_rounds=5) at 8 queries ⇒ 2^15 rows. Exercises the FULL hiding path: random round, salted
        // 3-block trace / 10-block multi-matrix quotient / 2-block commit leaves (depth-2 AND depth-0
        // rounds), halved z_h, nqc=4 recompose, random cap-mux. The plan's log_height=6 config is
        // functionally green too (see hiding_monolith_plan_config) but its transcript forces 2^16 rows
        // (>512 sponge blocks of cap absorbs) ⇒ ~16 GB — outside the budget at any query count.
        let (log_h, rss) = run_hiding_monolith_lh(8, 4, false);
        assert!(rss < 8u64 << 30, "hiding monolith must fit in 8 GB (got {} MiB)", rss / (1 << 20));
        println!("HIDING monolith end-to-end: 2^{log_h} rows, {} MiB — accept-iff-p3::verify(hiding ConstAir)", rss / (1 << 20));
    }

    /// The PLAN's full config (log_height=6 ⇒ degree_bits=7/log_global=11/cm_rounds=7): accept-iff-p3::verify
    /// + tamper rejects VALIDATED (2^16 rows / width 619 / ~16.2 GB peak) — functionally green, but the
    /// transcript's cap absorbs exceed 512 sponge blocks ⇒ tr=2^15 ⇒ 2^16 total rows, so it can never fit the
    /// 8 GB budget (production verifies hiding proofs via the aggregation tree, not one giant monolith).
    #[test]
    #[ignore = "slow + ~16 GB RSS: the plan's log_height=6 hiding config end-to-end (no 8 GB assert)"]
    fn hiding_monolith_plan_config() {
        let (log_h, rss) = run_hiding_monolith_lh(8, 6, false);
        println!("HIDING monolith (plan config, db=7): 2^{log_h} rows, {} MiB — accept-iff-p3::verify + tampers", rss / (1 << 20));
    }

    #[test]
    #[ignore = "debug: localize a failing hiding constraint via check_constraints (run in DEBUG, 1 query)"]
    fn hiding_monolith_check() {
        run_hiding_monolith(1, true);
    }

    #[test]
    #[ignore = "debug: fast constraint localization — small inner (log_height=4, first failing db)"]
    fn hiding_monolith_check_small() {
        // 1-query PASSED check_constraints at db=4 but the 4-query e2e FAILED ⇒ query-index-specific. 8 queries
        // (same 2^15 height) maximizes trigger odds; check_only now ALSO proves the same instance, so one run
        // either panics at the exact (row, constraint) or settles that the instance is genuinely fine.
        run_hiding_monolith_lh(8, 4, true);
    }

    /// Degree-overflow discriminator: the OUTER MonolithAir's symbolic max constraint degree + log_nqc at
    /// db=3 (passes) vs db=4 (fails). The merge-link `not_term` = Π(1−one_hot) gains a factor per commit
    /// round (+3 hiding factors), so its degree GROWS with db — if log_nqc crosses between db=3 and db=4,
    /// the quotient/LDE capacity is the failure mechanism (invisible to row-wise check_constraints).
    #[test]
    #[ignore = "debug: outer-AIR symbolic max degree + log_nqc at db=3 vs db=4"]
    fn hiding_monolith_degree_probe() {
        use crate::recursion::monolith::MonolithAir;
        use p3_air::symbolic::get_symbolic_constraints;
        for lh in [3usize, 4] {
            let config = make_config_ar(1, 8);
            let (proof, pvs) = gen_proof(&config, 42, lh);
            let (_bi, counts, binds, _chs, index_binds, index_felts) = sim_full_hiding_all(&config, &proof, &pvs);
            let (terms, _x, _a, _ro) = hiding_multicol_query_terms(&config, &proof, &pvs, 0);
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
                constraints: vec![],
                w_inner_f: 1,
                n_pub_f: 1,
                n_periodic_f: 0,
                is_zk: 1,
            };
            let layout = AirLayout::from_air::<Val>(&air);
            let cs = get_symbolic_constraints::<Val, MonolithAir>(&air, layout);
            let maxd = cs.iter().map(|c| c.degree_multiple()).max().unwrap();
            let log_nqc = get_log_num_quotient_chunks::<Val, MonolithAir>(&air, layout, 1);
            println!(
                "inner log_height={lh} (degree_bits={}): outer max_constraint_degree={maxd}, outer log_nqc={log_nqc} ({} constraints)",
                lh + 1,
                cs.len()
            );
        }
    }

    #[test]
    #[ignore = "debug: hypothesis-B probe — db=3 with 8 queries (is the failure index-dependent at ALL db?)"]
    fn hiding_monolith_e2e_small() {
        // db=3/4q e2e PASSED, db=4/4q FAILED. If db=3 with MORE index samples also fails, the bug is
        // index-dependent at all db (not tied to db=4's extra index bit).
        run_hiding_monolith_lh(8, 3, false);
        println!("=== db=3 @ 8 queries PASSED ===");
    }
}
