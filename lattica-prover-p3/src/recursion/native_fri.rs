//! B3b WIRING — native FRI verify (re-implementing `p3-fri::verify_fri`), the blueprint to port to the
//! in-circuit AIR.  ✅ COMPLETE + VALIDATED (native): `verify_proof` runs the full FRI-STARK verify with
//! NO `pcs.verify` delegation and agrees with `p3::verify` (test `native_fri_verify_agrees_with_p3`:
//! accept a real proof; reject a tampered public value, a tampered commit-phase sibling, and a tampered
//! `final_poly`). The remaining work is the AIR PORT — turning this validated native algorithm into
//! constraints, using the in-circuit gadget each step already maps to.
//!
//! The in-circuit verifier's last and largest part is the FRI query loop. It can only be validated as a
//! whole, so it was built as ONE native re-implementation first (the algorithm), then ported to
//! constraints (every operation it performs already has a validated in-circuit gadget).
//!
//! ## The algorithm (`p3-fri::verify_fri`), mapped to the validated building blocks
//! 1. **Transcript** — sample α; per FRI round observe `commit_phase_commits[r]` + PoW, sample β_r;
//!    observe `final_poly`; sample each query index via `sample_bits(log_global_max_height)`.
//!    → in-circuit: `TranscriptAir`/`FriTranscriptAir` (α, β_r) + `SampleBitsAir` (the index).
//! 2. **`open_input`** (per query) — for each committed batch, MMCS-verify the opened rows and reduce
//!    them to `ro[log_height] = Σ α^k·(p_k − y_k)/(x − z)`, where `x = GENERATOR·g^reverse_bits(index)`.
//!    → in-circuit: `LeafHashAir` + `fri_merkle` (the MMCS opening) + `ReducedOpeningAir` (the DEEP term).
//!    SUBTLETIES to preserve: the `GENERATOR` coset shift; `reverse_bits_len(index >> bits_reduced,
//!    log_height)`; α-power accumulation keyed by descending `log_height`; matrix widths pinned to the
//!    claimed eval counts (not the proof).
//! 3. **`verify_query`** (per query) — fold the running eval down the commit phase: reconstruct each
//!    round's arity group from the running eval + `sibling_values`, MMCS-verify the group against
//!    `commit_phase_commits[r]`, fold at β_r, roll in reduced openings at matching heights.
//!    → in-circuit: `fri_merkle` (the per-round opening) + `fri_fold` (the fold) — IMPLEMENTED below
//!    natively (`verify_query`).
//! 4. **Final check** — `eval(final_poly, x) == folded_eval`, `x = g^reverse_bits(domain_index)`.
//!    → in-circuit: a Horner evaluation (cheap F_p² arithmetic).
//!
//! ## Status — native wiring COMPLETE + validated
//! - `open_input` (step 2), `verify_query` (step 3), the `verify_fri_native` driver (steps 1+4), and the
//!   `verify_proof` STARK wrapper are all implemented natively, mirroring p3. NO `pcs.verify` is used —
//!   the FRI low-degree test runs from scratch. End-to-end validated by `native_fri_verify_agrees_with_p3`.
//! - Remaining: the AIR PORT (replace this native code with the in-circuit gadgets + the constraint
//!   folder as constraints), then B4/B5 aggregation. This native verify is the exact algorithm to port.

use alloc::collections::BTreeMap;

use p3_air::BaseAir;
use p3_challenger::{CanObserve, DuplexChallenger, FieldChallenger};
use p3_commit::{BatchOpening, ExtensionMmcs, Mmcs, Pcs, PolynomialSpace};
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing, TwoAdicField};
use p3_fri::{CommitPhaseProofStep, FriParameters, TwoAdicFriFolding, TwoAdicFriPcs};
use p3_goldilocks::{default_goldilocks_poseidon2_8, Goldilocks, Poseidon2Goldilocks};
use p3_matrix::Dimensions;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{
    get_log_num_quotient_chunks, recompose_quotient_from_chunks, validate_degree_bits, verify_constraints,
    AirLayout, Proof, StarkGenericConfig,
};

use super::native_verify::ConstAir;

extern crate alloc;

pub(crate) type Val = Goldilocks;
pub(crate) type Challenge = BinomialExtensionField<Val, 2>;

/// log2 of a power of two (replaces `p3_util::log2_strict`, which isn't a direct dependency).
fn log2_strict(n: usize) -> usize {
    debug_assert!(n.is_power_of_two());
    n.trailing_zeros() as usize
}

/// One commit-phase round's data for a query: (β_r, commitment, opening step).
pub struct CommitStep<'a, M: Mmcs<Challenge>> {
    pub beta: Challenge,
    pub commit: &'a M::Commitment,
    pub opening: &'a CommitPhaseProofStep<Challenge, M>,
}

/// The commit-phase fold loop for one query — a faithful native port of `p3-fri::verify_query`.
/// Folds `reduced_openings` down the commit phase, MMCS-checking each round's sibling group and folding
/// at β_r (the fold matches `fri_fold::native_fold`, our validated in-circuit gadget). Returns the final
/// folded evaluation (to be compared against `final_poly(x)` by the caller).
///
/// `reduced_openings` is `(log_height, value)` pairs sorted by DESCENDING height (the input openings,
/// per `open_input`). `start_index` is the query index; it is shifted down by each round's `log_arity`.
pub fn verify_query<M: Mmcs<Challenge>>(
    params: &FriParameters<M>,
    folding: &TwoAdicFriFolding<(), M::Error>,
    start_index: &mut usize,
    fold_data: &[CommitStep<'_, M>],
    reduced_openings: Vec<(usize, Challenge)>,
    log_global_max_height: usize,
    log_final_height: usize,
) -> Result<Challenge, String>
where
    M::Error: core::fmt::Debug + Sync,
{
    use p3_fri::FriFoldingStrategy;

    let mut ro_iter = reduced_openings.into_iter().peekable();
    let Some(&(first_log_height, _)) = ro_iter.peek() else {
        return Err("missing initial reduced opening".into());
    };
    if first_log_height != log_global_max_height {
        return Err(format!("initial reduced-opening height {first_log_height} != {log_global_max_height}"));
    }
    let mut folded_eval = ro_iter.next().unwrap().1;
    let mut log_current_height = log_global_max_height;

    for (round, step) in fold_data.iter().enumerate() {
        let max_log_arity = core::cmp::min(params.max_log_arity, log_current_height);
        let log_arity = step.opening.log_arity as usize; // checked_log_arity is private; replicate it
        if !(1..=max_log_arity).contains(&log_arity) {
            return Err(format!("round {round}: invalid log_arity {log_arity} (max {max_log_arity})"));
        }
        let arity = 1 << log_arity;
        if step.opening.sibling_values.len() != arity - 1 {
            return Err(format!("round {round}: sibling_values len != arity-1"));
        }

        // Reconstruct the arity group from the running eval + the siblings, at the index's group slot.
        let index_in_group = *start_index % arity;
        let mut evals = Challenge::zero_vec(arity);
        evals[index_in_group] = folded_eval;
        let mut sib = 0;
        for (j, e) in evals.iter_mut().enumerate() {
            if j != index_in_group {
                *e = step.opening.sibling_values[sib];
                sib += 1;
            }
        }

        let log_folded_height = log_current_height - log_arity;
        let dims = [Dimensions { width: arity, height: 1 << log_folded_height }];
        *start_index >>= log_arity;

        // MMCS-verify the sibling group against the round commitment (in-circuit: fri_merkle).
        params
            .mmcs
            .verify_batch(step.commit, &dims, *start_index, p3_commit::BatchOpeningRef::new(&[evals.clone()], &step.opening.opening_proof))
            .map_err(|_| format!("round {round}: commit-phase MMCS verify failed"))?;

        // Fold the group at β_r (in-circuit: fri_fold; this fold_row == fri_fold::native_fold).
        folded_eval = <TwoAdicFriFolding<(), M::Error> as FriFoldingStrategy<Val, Challenge>>::fold_row(
            folding,
            *start_index,
            log_folded_height,
            log_arity,
            step.beta,
            evals.into_iter(),
        );
        log_current_height = log_folded_height;

        // Roll in any reduced opening newly available at this height, scaled by β^arity.
        if let Some((_, ro)) = ro_iter.next_if(|(lh, _)| *lh == log_folded_height) {
            folded_eval += step.beta.exp_power_of_2(log_arity) * ro;
        }
    }

    if log_current_height != log_final_height {
        return Err(format!("final fold height {log_current_height} != {log_final_height}"));
    }
    if ro_iter.next().is_some() {
        return Err("unconsumed reduced openings".into());
    }
    Ok(folded_eval)
}

/// Evaluate the final polynomial at `x` (Horner) — the per-query final check `eval == folded_eval`.
/// (In-circuit: a short F_p² Horner chain.) `x = g^reverse_bits_len(domain_index, log_global_max_height)`.
pub fn eval_final_poly(final_poly: &[Challenge], x: Challenge) -> Challenge {
    let mut eval = Challenge::ZERO;
    for &coeff in final_poly.iter().rev() {
        eval = eval * x + coeff;
    }
    eval
}

/// The final-domain point for a query: `g^reverse_bits_len(domain_index, log_global_max_height)`.
pub fn final_query_point(domain_index: usize, log_global_max_height: usize) -> Challenge {
    let rev = reverse_bits_len(domain_index, log_global_max_height);
    Challenge::from(Val::two_adic_generator(log_global_max_height).exp_u64(rev as u64))
}

/// Reorder a length-2^k slice into bit-reversed index order (replaces `p3_util::reverse_slice_index_bits`).
#[cfg(test)]
pub(crate) fn reverse_slice_index_bits<T>(xs: &mut [T]) {
    let n = xs.len();
    if n <= 1 {
        return;
    }
    let log_n = log2_strict(n);
    for i in 0..n {
        let j = reverse_bits_len(i, log_n);
        if i < j {
            xs.swap(i, j);
        }
    }
}

pub(crate) fn reverse_bits_len(mut x: usize, bits: usize) -> usize {
    let mut r = 0;
    for _ in 0..bits {
        r = (r << 1) | (x & 1);
        x >>= 1;
    }
    r
}

// --- non-ZK config (standard TwoAdicFriPcs — `verify_fri` applies exactly, no hiding randomization) ---
pub(crate) type Perm = Poseidon2Goldilocks<8>;
pub(crate) type MyHash = PaddingFreeSponge<Perm, 8, 4, 4>;
type MyCompress = TruncatedPermutation<Perm, 2, 4, 8>;
pub(crate) type InputMmcs = MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, 2, 4>;
pub(crate) type ChallengeMmcs = ExtensionMmcs<Val, Challenge, InputMmcs>;
pub(crate) type Chal = DuplexChallenger<Val, Perm, 8, 4>;
pub(crate) type Dft = Radix2DitParallel<Val>;
pub(crate) type MyPcs = TwoAdicFriPcs<Val, Dft, InputMmcs, ChallengeMmcs>;
pub type MyConfig = p3_uni_stark::StarkConfig<MyPcs, Challenge, Chal>;
pub(crate) type Domain = <MyPcs as Pcs<Challenge, Chal>>::Domain;
pub(crate) type InputCommit = <InputMmcs as Mmcs<Val>>::Commitment;
pub(crate) type ComOpenings = Vec<(InputCommit, Vec<(Domain, Vec<(Challenge, Vec<Challenge>)>)>)>;

/// `open_input` — per-query reduced openings (faithful port of `p3-fri::open_input`): MMCS-verify each
/// committed batch's opened rows, then reduce to `ro[log_height] = Σ α^k·(p_z − p_x)/(z − x)` with
/// `x = GENERATOR·g^reverse_bits(index >> bits_reduced, log_height)`, accumulating the α-power per height.
#[allow(clippy::type_complexity)]
pub(crate) fn open_input(
    params: &FriParameters<ChallengeMmcs>,
    log_global_max_height: usize,
    index: usize,
    input_proof: &[BatchOpening<Val, InputMmcs>],
    alpha: Challenge,
    input_mmcs: &InputMmcs,
    coms: &[(InputCommit, Vec<(Domain, Vec<(Challenge, Vec<Challenge>)>)>)],
) -> Result<Vec<(usize, Challenge)>, String> {
    let mut reduced: BTreeMap<usize, (Challenge, Challenge)> = BTreeMap::new();
    if input_proof.len() != coms.len() {
        return Err("input proof batch count mismatch".into());
    }
    for (batch_opening, (batch_commit, mats)) in input_proof.iter().zip(coms.iter()) {
        if batch_opening.opened_values.len() != mats.len() {
            return Err("batch opened-values count mismatch".into());
        }
        let batch_heights: Vec<usize> = mats.iter().map(|(d, _)| d.size() << params.log_blowup).collect();
        let batch_dims: Vec<Dimensions> = mats
            .iter()
            .zip(&batch_heights)
            .map(|((_, pts), &height)| {
                let (_, values) = pts.first().ok_or("matrix without opening points")?;
                Ok(Dimensions { width: values.len(), height })
            })
            .collect::<Result<Vec<_>, String>>()?;
        let reduced_index = batch_heights
            .iter()
            .max()
            .map(|&h| index >> (log_global_max_height - log2_strict(h)))
            .unwrap_or(0);
        input_mmcs
            .verify_batch(batch_commit, &batch_dims, reduced_index, batch_opening.into())
            .map_err(|_| "input MMCS verify failed".to_string())?;

        for (mat_opening, (mat_domain, mat_pts)) in batch_opening.opened_values.iter().zip(mats.iter()) {
            let log_height = log2_strict(mat_domain.size()) + params.log_blowup;
            let bits_reduced = log_global_max_height - log_height;
            let rev = reverse_bits_len(index >> bits_reduced, log_height);
            let x = Val::GENERATOR * Val::two_adic_generator(log_height).exp_u64(rev as u64);
            let (alpha_pow, ro) = reduced.entry(log_height).or_insert((Challenge::ONE, Challenge::ZERO));
            for (z, ps_at_z) in mat_pts.iter() {
                if mat_opening.len() != ps_at_z.len() {
                    return Err("point evaluation count mismatch".into());
                }
                let quotient = (*z - x).try_inverse().ok_or("opening point matches query point")?;
                for (&p_at_x, &p_at_z) in mat_opening.iter().zip(ps_at_z.iter()) {
                    *ro += *alpha_pow * (p_at_z - p_at_x) * quotient;
                    *alpha_pow *= alpha;
                }
            }
        }
    }
    if let Some((_, ro)) = reduced.get(&params.log_blowup) {
        if !ro.is_zero() {
            return Err("nonzero blowup-height reduced opening".into());
        }
    }
    Ok(reduced.into_iter().rev().map(|(lh, (_, ro))| (lh, ro)).collect())
}

/// The FRI verify driver (faithful port of `p3-fri::verify_fri`): sample α, derive βs per round, then per
/// query open the input (`open_input`) + fold the commit phase (`verify_query`) + check `final_poly`.
fn verify_fri_native(
    params: &FriParameters<ChallengeMmcs>,
    fri_proof: &p3_fri::FriProof<Challenge, ChallengeMmcs, Val, Vec<BatchOpening<Val, InputMmcs>>>,
    challenger: &mut Chal,
    coms: &ComOpenings,
    input_mmcs: &InputMmcs,
) -> Result<(), String> {
    use p3_challenger::{CanSampleBits, GrindingChallenger};
    if params.num_queries == 0 {
        return Err("zero queries".into());
    }
    let alpha: Challenge = challenger.sample_algebra_element();

    let expected_rounds = fri_proof.commit_phase_commits.len();
    for qp in &fri_proof.query_proofs {
        if qp.commit_phase_openings.len() != expected_rounds {
            return Err("query commit-phase opening count mismatch".into());
        }
    }
    let log_arities: Vec<usize> = fri_proof
        .query_proofs
        .first()
        .map(|qp| qp.commit_phase_openings.iter().map(|o| o.log_arity as usize).collect())
        .unwrap_or_default();
    let total: usize = log_arities.iter().sum();
    let log_global_max_height = total + params.log_blowup + params.log_final_poly_len;
    let expected = coms
        .iter()
        .flat_map(|(_, mats)| mats.iter().map(|(d, _)| log2_strict(d.size()) + params.log_blowup))
        .max();
    if let Some(e) = expected {
        if log_global_max_height != e {
            return Err(format!("global max height {log_global_max_height} != {e}"));
        }
    }

    let betas: Vec<Challenge> = fri_proof
        .commit_phase_commits
        .iter()
        .zip(&fri_proof.commit_pow_witnesses)
        .map(|(comm, witness)| {
            challenger.observe(comm.clone());
            if !challenger.check_witness(params.commit_proof_of_work_bits, *witness) {
                return Err("invalid commit pow".to_string());
            }
            Ok(challenger.sample_algebra_element())
        })
        .collect::<Result<_, _>>()?;

    if fri_proof.final_poly.len() != params.final_poly_len() {
        return Err("final poly length mismatch".into());
    }
    challenger.observe_algebra_slice(&fri_proof.final_poly);
    if fri_proof.query_proofs.len() != params.num_queries {
        return Err("query proof count mismatch".into());
    }
    for &la in &log_arities {
        challenger.observe(Val::from_usize(la));
    }
    if !challenger.check_witness(params.query_proof_of_work_bits, fri_proof.query_pow_witness) {
        return Err("invalid query pow".into());
    }
    let log_final_height = params.log_blowup + params.log_final_poly_len;
    // The fold only needs FriFoldingStrategy::fold_row (independent of the InputProof type param); a
    // `<()>` folding suffices, and ChallengeMmcs::Error == InputMmcs::Error so the trait bound holds.
    let folding: TwoAdicFriFolding<(), <ChallengeMmcs as Mmcs<Challenge>>::Error> = TwoAdicFriFolding(core::marker::PhantomData);

    for qp in fri_proof.query_proofs.iter() {
        let index = challenger.sample_bits(log_global_max_height);
        let ro = open_input(params, log_global_max_height, index, &qp.input_proof, alpha, input_mmcs, coms)?;
        let mut domain_index = index;
        let fold_data: Vec<CommitStep<'_, ChallengeMmcs>> = betas
            .iter()
            .zip(fri_proof.commit_phase_commits.iter())
            .zip(qp.commit_phase_openings.iter())
            .map(|((&beta, commit), opening)| CommitStep { beta, commit, opening })
            .collect();
        let folded = verify_query(params, &folding, &mut domain_index, &fold_data, ro, log_global_max_height, log_final_height)?;
        let x = final_query_point(domain_index, log_global_max_height);
        if eval_final_poly(&fri_proof.final_poly, x) != folded {
            return Err("final poly mismatch".into());
        }
    }
    Ok(())
}

/// Rebuild the input MMCS + FRI parameters deterministically (identical to the config's, since Poseidon2
/// + the literals are fixed) — `TwoAdicFriPcs` doesn't expose them, and my FRI verify needs both.
/// `max_log_arity` selects the FRI folding arity (1 ⇒ arity-2 FRI, the monolith's first-milestone config);
/// `num_queries` selects the FRI query count (the production config is 96; the monolith milestone uses a
/// reduced count to fit the 8 GB budget — the construction is query-count-agnostic, production restores 96).
pub(crate) fn build_mmcs_and_params(max_log_arity: usize, num_queries: usize) -> (Perm, InputMmcs, FriParameters<ChallengeMmcs>) {
    let perm = default_goldilocks_poseidon2_8();
    let input_mmcs = InputMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), 6);
    let params = FriParameters {
        log_blowup: 4,
        log_final_poly_len: 0,
        max_log_arity,
        num_queries,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 16,
        mmcs: ChallengeMmcs::new(input_mmcs.clone()),
    };
    (perm, input_mmcs, params)
}

/// Build a StarkConfig for the given FRI folding `max_log_arity` (1 = arity-2 FRI) + `num_queries`.
/// (Test/oracle helper: the aggregator receives inner proofs; only tests build configs + generate them.)
#[cfg(test)]
pub(crate) fn make_config(max_log_arity: usize, num_queries: usize) -> MyConfig {
    let (perm, input_mmcs, params) = build_mmcs_and_params(max_log_arity, num_queries);
    let pcs = MyPcs::new(Dft::default(), input_mmcs, params);
    MyConfig::new(pcs, Chal::new(perm))
}

/// Generate a real inner proof for the minimal `ConstAir` (one column = a public constant), at the given
/// trace `log_height`. The inner proof the monolith verifier AIR consumes (test/oracle helper).
#[cfg(test)]
pub(crate) fn gen_const_proof(config: &MyConfig, value: u64, log_height: usize) -> (Proof<MyConfig>, Vec<Val>) {
    use p3_matrix::dense::RowMajorMatrix;
    let v = Val::from_u64(value);
    let trace = RowMajorMatrix::new(vec![v; 1 << log_height], 1);
    let pvs = vec![v];
    (p3_uni_stark::prove(config, &ConstAir, trace, &pvs), pvs)
}

/// A `MerkleCap` commitment flattened to its felt sequence (roots in order) — EXACTLY the felts the
/// challenger observes via `observe(cap)`. The monolith transcript region must absorb this same sequence.
#[cfg(test)]
pub(crate) fn cap_felts(commit: &InputCommit) -> Vec<Val> {
    commit.roots().iter().flatten().copied().collect()
}

/// Oracle for the monolith's transcript PREAMBLE (Phase 1): replays the real challenger exactly as
/// `verify_proof` does up to ζ, returning the absorbed felt sequences + the ground-truth (α, ζ). The
/// in-circuit preamble must absorb `(instance ‖ commitment)` and reproduce this (α, ζ).
/// Returns `(instance_felts, commitment_felts, α, ζ)` with α/ζ as `[Val; 2]` coefficient pairs.
#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(crate) fn preamble_challenges(config: &MyConfig, proof: &Proof<MyConfig>, pvs: &[Val]) -> (Vec<Val>, Vec<Val>, [Val; 2], [Val; 2]) {
    use p3_field::BasedVectorSpace;
    let pcs = config.pcs();
    let degree_bits = proof.degree_bits;
    let (base_degree_bits, _degree) =
        validate_degree_bits(None, degree_bits, 0, <MyPcs as Pcs<Challenge, Chal>>::log_max_lde_height(pcs)).expect("degree bits");
    let preprocessed_width = 0usize;
    let pair = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };

    // Ground truth: the REAL challenger, observing exactly verify_proof's preamble sequence.
    let mut ch = config.initialise_challenger();
    ch.observe(Val::from_usize(degree_bits));
    ch.observe(Val::from_usize(base_degree_bits));
    ch.observe(Val::from_usize(preprocessed_width));
    ch.observe(proof.commitments.trace.clone());
    ch.observe_slice(pvs);
    let alpha: Challenge = ch.sample_algebra_element();
    ch.observe(proof.commitments.quotient_chunks.clone());
    let zeta: Challenge = ch.sample_algebra_element();

    // The same felts the in-circuit sponge absorbs (instance → α, commitment → ζ).
    let mut instance = vec![Val::from_usize(degree_bits), Val::from_usize(base_degree_bits), Val::from_usize(preprocessed_width)];
    instance.extend(cap_felts(&proof.commitments.trace));
    instance.extend_from_slice(pvs);
    let commitment = cap_felts(&proof.commitments.quotient_chunks);
    (instance, commitment, pair(alpha), pair(zeta))
}

/// Oracle for the FULL monolith transcript (Phase 2): replays the real challenger through the entire
/// FRI-STARK verify, returning the ground-truth challenges the in-circuit transcript must reproduce —
/// (α_stark, ζ, α_fri, β_0..β_{R-1}, query indices). Mirrors verify_proof + verify_fri_native's challenger
/// calls exactly (incl. the +num_absorbed duplex counts, the opened-value partial absorb, commit-PoW
/// early-return at 0 bits, the query-PoW witness observe, and the squeeze-only index tail).
#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(crate) fn full_transcript_challenges(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
) -> ([Val; 2], [Val; 2], [Val; 2], Vec<[Val; 2]>, Vec<Val>) {
    use p3_challenger::{CanSample, GrindingChallenger};
    use p3_field::BasedVectorSpace;
    let pcs = config.pcs();
    let degree_bits = proof.degree_bits;
    let (base_degree_bits, _) =
        validate_degree_bits(None, degree_bits, 0, <MyPcs as Pcs<Challenge, Chal>>::log_max_lde_height(pcs)).expect("degree bits");
    let pair = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
    let mut ch = config.initialise_challenger();

    // preamble → α_stark, ζ
    ch.observe(Val::from_usize(degree_bits));
    ch.observe(Val::from_usize(base_degree_bits));
    ch.observe(Val::from_usize(0));
    ch.observe(proof.commitments.trace.clone());
    ch.observe_slice(pvs);
    let alpha_stark: Challenge = ch.sample_algebra_element();
    ch.observe(proof.commitments.quotient_chunks.clone());
    let zeta: Challenge = ch.sample_algebra_element();

    // opened values → α_fri
    ch.observe_algebra_slice(&proof.opened_values.trace_local);
    if let Some(tn) = &proof.opened_values.trace_next {
        ch.observe_algebra_slice(tn);
    }
    for c in &proof.opened_values.quotient_chunks {
        ch.observe_algebra_slice(c);
    }
    let alpha_fri: Challenge = ch.sample_algebra_element();

    // per commit round → β_r (commit PoW is 0 bits ⇒ check_witness returns early, no observe)
    let fri = &proof.opening_proof;
    let mut betas = Vec::new();
    for (comm, w) in fri.commit_phase_commits.iter().zip(&fri.commit_pow_witnesses) {
        ch.observe(comm.clone());
        assert!(ch.check_witness(0, *w), "commit pow (0 bits)"); // build_mmcs_and_params: commit_proof_of_work_bits = 0
        betas.push(ch.sample_algebra_element::<Challenge>());
    }

    // final_poly + arities + query-PoW, then the query indices
    ch.observe_algebra_slice(&fri.final_poly);
    let log_arities: Vec<usize> = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).collect();
    for &la in &log_arities {
        ch.observe(Val::from_usize(la));
    }
    assert!(ch.check_witness(16, fri.query_pow_witness), "query pow");
    // sample_bits(b) = sample::<Val>() & ((1<<b)-1) (DuplexChallenger); capture the index FELTS (the
    // in-circuit transcript reproduces these; the low-`bits` masking is the validated SampleBitsAir).
    let index_felts: Vec<Val> = (0..fri.query_proofs.len())
        .map(|_| {
            let f: Val = ch.sample();
            f
        })
        .collect();

    (pair(alpha_stark), pair(zeta), pair(alpha_fri), betas.iter().map(|b| pair(*b)).collect(), index_felts)
}

/// Per-query oracle (Phase 3): builds the opening rounds like `verify_proof`, then mirrors `open_input`'s
/// reduced-opening loop for query `q`, returning the DEEP terms `[(z, p_z, p_x)]` (z = opening point ext,
/// p_z = claimed eval ext, p_x = opened row value base), the DEEP point x (base, shared across the
/// milestone's single log_height), α_fri, and the native reduced opening `ro = Σ α^k (p_z − p_x)/(z − x)`.
#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(crate) fn query_terms(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
    q: usize,
) -> (Vec<(Challenge, Challenge, Val)>, Val, Challenge, Challenge) {
    use p3_field::BasedVectorSpace;
    let to_ext = |p: [Val; 2]| Challenge::from_basis_coefficients_fn(|i| p[i]);
    let (_, zeta_p, alpha_p, _, index_felts) = full_transcript_challenges(config, proof, pvs);
    let zeta = to_ext(zeta_p);
    let alpha = to_ext(alpha_p);

    // opening rounds (mirror verify_proof): trace at {ζ, ζ_next} + quotient chunks at ζ.
    let air = ConstAir;
    let pcs = config.pcs();
    let degree_bits = proof.degree_bits;
    let (_, degree) = validate_degree_bits(None, degree_bits, 0, <MyPcs as Pcs<Challenge, Chal>>::log_max_lde_height(pcs)).unwrap();
    let trace_domain = <MyPcs as Pcs<Challenge, Chal>>::natural_domain_for_degree(pcs, degree);
    let layout = AirLayout::from_air::<Val>(&air);
    let log_nqc = get_log_num_quotient_chunks::<Val, ConstAir>(&air, layout, 0);
    let nqc = 1usize << log_nqc;
    let qd = trace_domain.create_disjoint_domain(1 << (degree_bits + log_nqc));
    let qcd = qd.split_domains(nqc);
    let zeta_next = trace_domain.next_point(zeta).unwrap();
    let trace_pts = vec![(zeta, proof.opened_values.trace_local.clone()), (zeta_next, proof.opened_values.trace_next.clone().unwrap())];
    let coms: ComOpenings = vec![
        (proof.commitments.trace.clone(), vec![(trace_domain, trace_pts)]),
        (proof.commitments.quotient_chunks.clone(), qcd.iter().zip(&proof.opened_values.quotient_chunks).map(|(d, v)| (*d, vec![(zeta, v.clone())])).collect()),
    ];

    // log_global + the query index.
    let fri = &proof.opening_proof;
    let log_global: usize = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).sum::<usize>() + 4;
    use p3_field::PrimeField64;
    let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);

    // open_input's reduced-opening loop, capturing the terms.
    let input_proof = &fri.query_proofs[q].input_proof;
    let mut terms = Vec::new();
    let mut alpha_pow = Challenge::ONE;
    let mut ro = Challenge::ZERO;
    let mut x_out = Val::ZERO;
    for (batch_opening, (_, mats)) in input_proof.iter().zip(coms.iter()) {
        for (mat_opening, (mat_domain, mat_pts)) in batch_opening.opened_values.iter().zip(mats.iter()) {
            let log_height = log2_strict(mat_domain.size()) + 4;
            let bits_reduced = log_global - log_height;
            let rev = reverse_bits_len(index >> bits_reduced, log_height);
            let x = Val::GENERATOR * Val::two_adic_generator(log_height).exp_u64(rev as u64);
            x_out = x;
            for (z, ps_at_z) in mat_pts.iter() {
                let inv = (*z - x).inverse();
                for (&p_x, &p_z) in mat_opening.iter().zip(ps_at_z.iter()) {
                    terms.push((*z, p_z, p_x));
                    ro += alpha_pow * (p_z - p_x) * inv;
                    alpha_pow *= alpha;
                }
            }
        }
    }
    (terms, x_out, alpha, ro)
}

/// Epilogue probe/oracle: the OOD constraint-check inputs + the recomposed quotient(ζ), plus p3's OWN
/// Lagrange selectors at ζ on the real trace domain (the non-circular anchor for the in-circuit selector
/// chain). Internally asserts the in-circuit recompose kernel `Σ_i zps_i·(c_{i,0}+c_{i,1}·X)` matches p3's
/// `recompose_quotient_from_chunks` on SYNTHETIC non-trivial chunks (the constant proof's quotient is 0).
/// Returns (degree_bits, nqc, chunk_lens, quotient(ζ), local, next, [chunks at ζ], α_stark, ζ,
///          native_is_first, native_is_trans, native_inv_van).
#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(crate) fn epilogue_oracle(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
) -> (usize, usize, Vec<usize>, Challenge, Challenge, Challenge, Vec<Challenge>, Challenge, Challenge, Challenge, Challenge, Challenge) {
    use p3_field::BasedVectorSpace;
    let to_ext = |p: [Val; 2]| Challenge::from_basis_coefficients_fn(|i| p[i]);
    // the ext generator element X (= 0 + 1·X); for the binomial ext with X²=W: c0 + c1·X in coords.
    let x_gen = Challenge::from_basis_coefficients_fn(|i| if i == 1 { Val::ONE } else { Val::ZERO });
    let (_, zeta_p, alpha_p, _, _) = full_transcript_challenges(config, proof, pvs);
    let zeta = to_ext(zeta_p);
    let alpha_stark = to_ext(alpha_p);
    let air = ConstAir;
    let pcs = config.pcs();
    let degree_bits = proof.degree_bits;
    let (_, degree) = validate_degree_bits(None, degree_bits, 0, <MyPcs as Pcs<Challenge, Chal>>::log_max_lde_height(pcs)).unwrap();
    let trace_domain = <MyPcs as Pcs<Challenge, Chal>>::natural_domain_for_degree(pcs, degree);
    let layout = AirLayout::from_air::<Val>(&air);
    let log_nqc = get_log_num_quotient_chunks::<Val, ConstAir>(&air, layout, 0);
    let nqc = 1usize << log_nqc;
    let qd = trace_domain.create_disjoint_domain(1 << (degree_bits + log_nqc));
    let qcd = qd.split_domains(nqc);
    let quotient = recompose_quotient_from_chunks::<MyConfig>(&qcd, &proof.opened_values.quotient_chunks, zeta);
    // --- self-check the in-circuit recompose kernel against p3 on synthetic NON-TRIVIAL chunks ---
    // zps_i = Π_{j≠i} (S_db − c_j)/(c_i − c_j), c_j = ζ^(2^db) − vanishing_j(ζ); chunk_i value = ch_{i,0}+ch_{i,1}·X.
    let s_db = zeta.exp_power_of_2(degree_bits);
    let c_ext: Vec<Challenge> = qcd.iter().map(|d| s_db - d.vanishing_poly_at_point(zeta)).collect();
    {
        let synth: Vec<Vec<Challenge>> = (0..nqc)
            .map(|i| vec![Challenge::from_u64((7 * i + 3) as u64), Challenge::from_u64((11 * i + 5) as u64)])
            .collect();
        let native_r = recompose_quotient_from_chunks::<MyConfig>(&qcd, &synth, zeta);
        let mut mine = Challenge::ZERO;
        for i in 0..nqc {
            let chunk_val = synth[i][0] + synth[i][1] * x_gen;
            let mut zp = Challenge::ONE;
            for j in 0..nqc {
                if j != i {
                    zp *= (s_db - c_ext[j]) * (c_ext[i] - c_ext[j]).inverse();
                }
            }
            mine += zp * chunk_val;
        }
        assert_eq!(mine, native_r, "in-circuit recompose kernel matches p3 recompose_quotient_from_chunks");
    }
    let chunk_lens: Vec<usize> = proof.opened_values.quotient_chunks.iter().map(|v| v.len()).collect();
    let local = proof.opened_values.trace_local[0];
    let next = proof.opened_values.trace_next.as_ref().unwrap()[0];
    let chunks: Vec<Challenge> = proof.opened_values.quotient_chunks.iter().flatten().copied().collect();
    // p3's own selectors at ζ on the real trace domain — the anchor for the in-circuit selector chain.
    let sel = trace_domain.selectors_at_point(zeta);
    (
        degree_bits, nqc, chunk_lens, quotient, local, next, chunks, alpha_stark, zeta,
        sel.is_first_row, sel.is_transition, sel.inv_vanishing,
    )
}

/// Per-query commit-phase oracle (Phase 3): mirrors `verify_query` for query `q`, returning the reduced
/// opening e0 = ro, the per-round fold data `(sibling, β_r, bit, point s_r)` (bit = the arity-2 group slot
/// of the running eval; s_r = g_{log+1}^reverse_bits(parent_index, log)), the resulting `folded_eval`, and
/// `final_poly[0]` (= eval_final_poly for log_final_poly_len = 0). The per-query accept is
/// `folded_eval == final_poly[0]`.
#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(crate) fn query_fold_data(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
    q: usize,
) -> (Challenge, Vec<(Challenge, Challenge, bool, Val)>, Challenge, Challenge) {
    use p3_field::{BasedVectorSpace, PrimeField64};
    let to_ext = |p: [Val; 2]| Challenge::from_basis_coefficients_fn(|i| p[i]);
    let (_, _, _, betas_p, index_felts) = full_transcript_challenges(config, proof, pvs);
    let betas: Vec<Challenge> = betas_p.iter().map(|&p| to_ext(p)).collect();
    let (_, _, _, ro) = query_terms(config, proof, pvs, q);

    let fri = &proof.opening_proof;
    let log_global: usize = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).sum::<usize>() + 4;
    let mut start = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
    let mut e = ro;
    let mut log_current = log_global;
    let mut rounds = Vec::new();
    for (r, step) in fri.query_proofs[q].commit_phase_openings.iter().enumerate() {
        let la = step.log_arity as usize; // arity-2 ⇒ 1
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
    let final0 = fri.final_poly[0];
    (ro, rounds, e, final0)
}

/// Per-query input-Merkle oracle (Phase 4): for query `q`, the trace batch's opening — the leaf
/// `MyHash(opened row)`, the authentication path `(sibling, bit)` (bit = index bit per level, binary tree),
/// and the committed cap entry `commit.roots()[index >> depth]` the path must reach. Mirrors the MMCS
/// `verify_batch` (leaf-hash → binary-compress up to the cap_height=6 cap → cap membership).
#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(crate) fn query_input_merkle(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
    q: usize,
) -> ([Val; 4], Vec<([Val; 4], bool)>, [Val; 4]) {
    use p3_field::PrimeField64;
    use p3_symmetric::CryptographicHasher;
    let (_, _, _, _, index_felts) = full_transcript_challenges(config, proof, pvs);
    let fri = &proof.opening_proof;
    let log_global: usize = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).sum::<usize>() + 4;
    let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);

    // trace batch (batch 0), matrix 0 — the trace is committed at height 2^log_global (= max), so the
    // reduced index is `index` and the binary path has (log_global − cap_height) levels to the cap.
    let batch = &fri.query_proofs[q].input_proof[0];
    let row = &batch.opened_values[0];
    let hasher = MyHash::new(default_goldilocks_poseidon2_8());
    let leaf: [Val; 4] = hasher.hash_iter(row.iter().copied());
    let siblings = &batch.opening_proof; // Vec<[Val; 4]>, one per level
    let path: Vec<([Val; 4], bool)> = siblings.iter().enumerate().map(|(lvl, &s)| (s, (index >> lvl) & 1 == 1)).collect();
    let depth = siblings.len();
    let cap = proof.commitments.trace.roots();
    let cap_entry = cap[index >> depth];
    (leaf, path, cap_entry)
}

/// Per-query QUOTIENT-batch Merkle oracle: the quotient row (input_proof[1]) hashes to a leaf and
/// authenticates to the quotient commitment cap. Mirrors the trace opening; the quotient may be committed at
/// a height ≤ 2^log_global, so the path uses the reduced index `index >> (4 − depth)` (4 = log_global − cap).
/// Returns (leaf, path, cap entry, row width).
#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(crate) fn query_quotient_merkle(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
    q: usize,
) -> ([Val; 4], Vec<([Val; 4], bool)>, [Val; 4], usize) {
    use p3_field::PrimeField64;
    use p3_symmetric::CryptographicHasher;
    let (_, _, _, _, index_felts) = full_transcript_challenges(config, proof, pvs);
    let fri = &proof.opening_proof;
    let log_global: usize = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).sum::<usize>() + 4;
    let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
    let batch = &fri.query_proofs[q].input_proof[1]; // quotient batch
    let row = &batch.opened_values[0];
    let hasher = MyHash::new(default_goldilocks_poseidon2_8());
    let leaf: [Val; 4] = hasher.hash_iter(row.iter().copied());
    let siblings = &batch.opening_proof;
    let depth = siblings.len();
    let reduction = (log_global - 6) - depth; // cap_height = 6 ⇒ total drop to the cap is log_global − 6
    let reduced = index >> reduction;
    let path: Vec<([Val; 4], bool)> = siblings.iter().enumerate().map(|(lvl, &s)| (s, (reduced >> lvl) & 1 == 1)).collect();
    let cap = proof.commitments.quotient_chunks.roots();
    let cap_entry = cap[reduced >> depth];
    (leaf, path, cap_entry, row.len())
}

/// Per-query commit-phase Merkle oracle (Phase 4), round 1: the reconstructed arity-2 group
/// {e_1, sibling} (e_1 = running eval after round 0's fold; ordered by the index bit) hashes to a leaf,
/// then authenticates up to the round-1 commitment's cap entry. Mirrors `verify_query`'s per-round
/// `mmcs.verify_batch`. (Round 1's folded height 2^8 gives a depth-2 path = 64 rows = a power of two, the
/// FriMerkleAir trace shape; round 0's depth-3 path would need a padded variant.)
#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(crate) fn query_commit_merkle(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
    q: usize,
) -> ([Val; 4], [Val; 4], Vec<([Val; 4], bool)>, [Val; 4]) {
    use p3_field::{BasedVectorSpace, PrimeField64};
    use p3_symmetric::CryptographicHasher;
    let (_, _, _, _, index_felts) = full_transcript_challenges(config, proof, pvs);
    let (ro, rounds, _, _) = query_fold_data(config, proof, pvs, q);
    let fri = &proof.opening_proof;
    let log_global: usize = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).sum::<usize>() + 4;
    let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);

    // running eval after round 0's fold: e_1 = fold({ro, sib_0} by bit_0, β_0, s_0).
    let (sib0, beta0, bit0, s0) = rounds[0];
    let (a, b) = if bit0 { (sib0, ro) } else { (ro, sib0) };
    let e1 = crate::recursion::fri_fold::native_fold(a, b, beta0, s0);

    // round 1: group = {e_1, sibling_1} ordered by the round-1 index bit.
    let step1 = &fri.query_proofs[q].commit_phase_openings[1];
    let bit1 = (index >> 1) & 1;
    let sibling = step1.sibling_values[0];
    let (g0, g1) = if bit1 == 0 { (e1, sibling) } else { (sibling, e1) };
    let flat: Vec<Val> = [g0, g1].iter().flat_map(|x| x.as_basis_coefficients_slice().to_vec()).collect();
    let group: [Val; 4] = flat.clone().try_into().unwrap(); // the leaf preimage (the arity-2 group)
    let leaf: [Val; 4] = MyHash::new(default_goldilocks_poseidon2_8()).hash_iter(flat);

    // path: parent index = index >> 2 (after rounds 0,1), at the round-1 folded height 2^8.
    let parent = index >> 2;
    let path_siblings = &step1.opening_proof;
    let path: Vec<([Val; 4], bool)> = path_siblings.iter().enumerate().map(|(lvl, &s)| (s, (parent >> lvl) & 1 == 1)).collect();
    let depth = path_siblings.len();
    let cap_entry = fri.commit_phase_commits[1].roots()[parent >> depth];
    (leaf, group, path, cap_entry)
}

/// Per-query commit-phase Merkle oracle for ALL rounds (the generalization of `query_commit_merkle` used by
/// the monolith inline). For each fold round r returns `(group, leaf, path, cap_entry)`: `group` = the
/// bit-ordered arity-2 pair {e_r, sib_r} (e_r = the running eval before round r's fold — reconstructed
/// exactly as `query_fold_data`), `leaf = MyHash(group)`, `path` = the round's authentication path (parent
/// index = index >> (r+1)), and `cap_entry = commit_phase_commits[r].roots()[parent >> depth]`. Depths for the
/// milestone (log_global=10, cap_height=6) are [3,2,1,0,0,0]. This binds every fold sibling to the committed
/// FRI codeword — the last opening the monolith must authenticate.
#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(crate) fn query_commit_merkle_all(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
    q: usize,
) -> Vec<([Val; 4], [Val; 4], Vec<([Val; 4], bool)>, [Val; 4])> {
    use p3_field::{BasedVectorSpace, PrimeField64};
    use p3_symmetric::CryptographicHasher;
    let (_, _, _, _, index_felts) = full_transcript_challenges(config, proof, pvs);
    let (ro, rounds, _e_final, _f0) = query_fold_data(config, proof, pvs, q);
    let fri = &proof.opening_proof;
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
        let leaf: [Val; 4] = hasher.hash_iter(flat);
        start >>= la; // parent index at the folded height
        let path_siblings = &step.opening_proof;
        let path: Vec<([Val; 4], bool)> = path_siblings.iter().enumerate().map(|(lvl, &sb)| (sb, (start >> lvl) & 1 == 1)).collect();
        let depth = path_siblings.len();
        let cap_entry = fri.commit_phase_commits[r].roots()[start >> depth];
        out.push((group, leaf, path, cap_entry));
        e = crate::recursion::fri_fold::native_fold(g0, g1, beta, s);
    }
    out
}

/// GENERAL-ARITY commit-phase fold oracle (Phase 5). For query `q`, mirrors `verify_query`'s per-round fold
/// but for ARBITRARY arity 2^la (the milestone uses la=1; `make_config(2,·)` gives la=2 arity-4). Per round
/// returns `(evals, beta, xs, folded)`: `evals` = the reconstructed arity-2^la group (running eval slotted at
/// `index % arity`, siblings elsewhere), `beta` = the round challenge, `xs` = the fold-point coset (EXACTLY
/// p3 `fold_row`'s points: `reverse_bits( subgroup_start · g_la^i )`, `subgroup_start = g_{lf+la}^rev(idx,lf)`),
/// and `folded` = p3's own `fold_row` result (the reference the in-circuit gadget must reproduce).
#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(crate) fn general_fold_oracle(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
    q: usize,
) -> Vec<(Vec<Challenge>, Challenge, Vec<Val>, Challenge)> {
    use p3_field::{BasedVectorSpace, PrimeField64};
    use p3_fri::FriFoldingStrategy;
    let to_ext = |p: [Val; 2]| Challenge::from_basis_coefficients_fn(|i| p[i]);
    let (_, _, _, betas_p, index_felts) = full_transcript_challenges(config, proof, pvs);
    let betas: Vec<Challenge> = betas_p.iter().map(|&p| to_ext(p)).collect();
    let (_, _, _, ro) = query_terms(config, proof, pvs, q);
    let fri = &proof.opening_proof;
    let log_global: usize = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).sum::<usize>() + 4;
    let mut index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
    let mut e = ro;
    let mut log_current = log_global;
    let folding: TwoAdicFriFolding<(), <ChallengeMmcs as Mmcs<Challenge>>::Error> = TwoAdicFriFolding(core::marker::PhantomData);
    let mut out = Vec::new();
    for (r, step) in fri.query_proofs[q].commit_phase_openings.iter().enumerate() {
        let la = step.log_arity as usize;
        let arity = 1usize << la;
        let index_in_group = index % arity;
        let mut evals = Challenge::zero_vec(arity);
        evals[index_in_group] = e;
        let mut sib = 0;
        for (j, ev) in evals.iter_mut().enumerate() {
            if j != index_in_group {
                *ev = step.sibling_values[sib];
                sib += 1;
            }
        }
        let log_folded = log_current - la;
        index >>= la;
        // xs = p3 fold_row's coset points (base field): reverse_bits( subgroup_start · g_la^i ).
        let subgroup_start = Val::two_adic_generator(log_folded + la).exp_u64(reverse_bits_len(index, log_folded) as u64);
        let g_la = Val::two_adic_generator(la);
        let mut xs: Vec<Val> = (0..arity).map(|i| subgroup_start * g_la.exp_u64(i as u64)).collect();
        reverse_slice_index_bits(&mut xs);
        let folded = <TwoAdicFriFolding<(), <ChallengeMmcs as Mmcs<Challenge>>::Error> as FriFoldingStrategy<Val, Challenge>>::fold_row(
            &folding, index, log_folded, la, betas[r], evals.iter().copied(),
        );
        out.push((evals.clone(), betas[r], xs, folded));
        e = folded;
        log_current = log_folded;
    }
    out
}

/// THE COMPLETE NATIVE WIRING — a full STARK verify that uses my native FRI verify (`verify_fri_native`)
/// in place of `pcs.verify`. Mirrors `p3_uni_stark::verify`'s orchestration for the non-ZK path (is_zk=0):
/// transcript replay (observe → α → observe → ζ) → opening rounds → observe opened evals → MY FRI verify
/// → recompose quotient → constraint/OOD check. Validated to agree with `p3::verify`.
pub fn verify_proof(config: &MyConfig, proof: &Proof<MyConfig>, public_values: &[Val]) -> Result<(), String> {
    let air = ConstAir;
    let Proof { commitments, opened_values, opening_proof, degree_bits } = proof;
    let degree_bits = *degree_bits;
    let pcs = config.pcs();
    let is_zk = 0usize;

    let (base_degree_bits, degree) =
        validate_degree_bits(None, degree_bits, is_zk, <MyPcs as Pcs<Challenge, Chal>>::log_max_lde_height(pcs)).map_err(|e| format!("degree bits: {e:?}"))?;
    let trace_domain = <MyPcs as Pcs<Challenge, Chal>>::natural_domain_for_degree(pcs, degree);
    let preprocessed_width = 0usize;
    let layout = AirLayout::from_air::<Val>(&air);
    let log_num_quotient_chunks = get_log_num_quotient_chunks::<Val, ConstAir>(&air, layout, is_zk);
    let num_quotient_chunks = 1usize << log_num_quotient_chunks; // is_zk=0

    let mut challenger = config.initialise_challenger();
    let init_trace_domain = <MyPcs as Pcs<Challenge, Chal>>::natural_domain_for_degree(pcs, degree);
    let quotient_domain_size = 1usize << (degree_bits + log_num_quotient_chunks);
    let quotient_domain = trace_domain.create_disjoint_domain(quotient_domain_size);
    let quotient_chunks_domains = quotient_domain.split_domains(num_quotient_chunks);
    let randomized_quotient_chunks_domains = quotient_chunks_domains.clone(); // << is_zk = 0

    challenger.observe(Val::from_usize(degree_bits));
    challenger.observe(Val::from_usize(base_degree_bits));
    challenger.observe(Val::from_usize(preprocessed_width));
    challenger.observe(commitments.trace.clone());
    challenger.observe_slice(public_values);
    let alpha: Challenge = challenger.sample_algebra_element();
    challenger.observe(commitments.quotient_chunks.clone());
    // no random commitment (non-ZK)
    let zeta: Challenge = challenger.sample_algebra_element();
    if init_trace_domain.vanishing_poly_at_point(zeta).is_zero() {
        return Err("zeta in trace domain".into());
    }
    let periodic_columns = air.periodic_columns();
    let periodic_values: Vec<Challenge> =
        periodic_columns.iter().map(|c| init_trace_domain.evaluate_periodic_column_at(c, zeta)).collect();
    let zeta_next = init_trace_domain.next_point(zeta).ok_or("no next point")?;
    let main_next = !air.main_next_row_columns().is_empty();

    let trace_round = {
        let mut pts = vec![(zeta, opened_values.trace_local.clone())];
        if main_next {
            pts.push((zeta_next, opened_values.trace_next.clone().ok_or("missing trace_next")?));
        }
        (commitments.trace.clone(), vec![(trace_domain, pts)])
    };
    let coms_to_verify: ComOpenings = vec![
        trace_round,
        (
            commitments.quotient_chunks.clone(),
            randomized_quotient_chunks_domains.iter().zip(&opened_values.quotient_chunks).map(|(d, v)| (*d, vec![(zeta, v.clone())])).collect(),
        ),
    ];

    // observe all opened evaluations — `TwoAdicFriPcs::verify` does this before `verify_fri`.
    for (_, round) in &coms_to_verify {
        for (_, mat) in round {
            for (_, point) in mat {
                challenger.observe_algebra_slice(point);
            }
        }
    }

    // ---- MY native FRI verify (the wiring), in place of pcs.verify ----
    // max_log_arity=4 is an upper bound in verify_query, so this validates arity-2 milestone proofs too.
    let (_perm, input_mmcs, params) = build_mmcs_and_params(4, 96);
    verify_fri_native(&params, opening_proof, &mut challenger, &coms_to_verify, &input_mmcs)?;

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
    verify_constraints::<MyConfig, ConstAir, <MyPcs as Pcs<Challenge, Chal>>::Error>(
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

#[cfg(test)]
mod tests {
    use super::*;
    use p3_uni_stark::verify;

    #[test]
    #[ignore = "slow: COMPLETE native FRI verify (the wiring) vs p3::verify"]
    fn native_fri_verify_agrees_with_p3() {
        let config = make_config(4, 96);
        let (mut proof, pvs) = gen_const_proof(&config, 42, 6);

        // p3 accepts the proof.
        assert!(verify(&config, &ConstAir, &proof, &pvs).is_ok(), "p3::verify should accept");
        // my COMPLETE native FRI verify (open_input + verify_query + final-poly, no pcs.verify) accepts it.
        if let Err(e) = verify_proof(&config, &proof, &pvs) {
            panic!("native FRI verify rejected a valid proof: {e}");
        }
        // tampered public value ⇒ reject.
        let bad = vec![Val::from_u64(43)];
        assert!(verify(&config, &ConstAir, &proof, &bad).is_err());
        assert!(verify_proof(&config, &proof, &bad).is_err(), "should reject wrong public value");

        // corrupt a query's commit-phase sibling ⇒ reject (proves verify_query's MMCS/fold actually checks).
        // (Non-ZK proving is deterministic, so this is the same proof generated fresh.)
        let (mut p2, _) = gen_const_proof(&config, 42, 6);
        p2.opening_proof.query_proofs[0].commit_phase_openings[0].sibling_values[0] += Challenge::ONE;
        assert!(verify_proof(&config, &p2, &pvs).is_err(), "should reject tampered commit-phase sibling");

        // corrupt a final_poly coefficient ⇒ reject (proves the final low-degree check is doing work).
        proof.opening_proof.final_poly[0] += Challenge::ONE;
        assert!(verify_proof(&config, &proof, &pvs).is_err(), "should reject tampered final_poly");
    }
}
