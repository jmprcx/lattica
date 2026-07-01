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

/// Generate a real inner proof for the NON-DEGENERATE `CounterAir` (one column counting up from `value`) —
/// a non-constant trace, so per-query cap entries DIFFER and the quotient at ζ is non-zero. The inner proof
/// used to exercise the cap-mux + OOD epilogue + FS absorb-binding (test/oracle helper).
#[cfg(test)]
pub(crate) fn gen_counter_proof(config: &MyConfig, value: u64, log_height: usize) -> (Proof<MyConfig>, Vec<Val>) {
    use super::native_verify::CounterAir;
    use p3_matrix::dense::RowMajorMatrix;
    let n = 1usize << log_height;
    let trace = RowMajorMatrix::new((0..n).map(|i| Val::from_u64(value + i as u64)).collect(), 1);
    let pvs = vec![Val::from_u64(value)];
    (p3_uni_stark::prove(config, &CounterAir, trace, &pvs), pvs)
}

/// Generate a real inner proof for the MULTI-COLUMN `FibonacciAir` (2 cols `[a,b]`, seeds `a0=seed_a`,
/// `b0=seed_b`). pvs = `[seed_a, seed_b, b_{n-1}]` (the last-row result). The inner proof used to exercise the
/// GENERAL OOD epilogue (multi-column openings, cross-column constraints, all three selectors).
#[cfg(test)]
pub(crate) fn gen_fib_proof(config: &MyConfig, seed_a: u64, seed_b: u64, log_height: usize) -> (Proof<MyConfig>, Vec<Val>) {
    use super::native_verify::FibonacciAir;
    use p3_matrix::dense::RowMajorMatrix;
    let n = 1usize << log_height;
    let (mut a, mut b) = (Val::from_u64(seed_a), Val::from_u64(seed_b));
    let mut vals = Vec::with_capacity(n * 2);
    for _ in 0..n {
        vals.push(a);
        vals.push(b);
        let (na, nb) = (b, a + b); // a' = b, b' = a + b
        a = na;
        b = nb;
    }
    let last_b = vals[(n - 1) * 2 + 1]; // b at the last row
    let pvs = vec![Val::from_u64(seed_a), Val::from_u64(seed_b), last_b];
    (p3_uni_stark::prove(config, &FibonacciAir, RowMajorMatrix::new(vals, 2), &pvs), pvs)
}

/// Generate a real inner proof for the DEGREE-2 `MulAir` (3 cols `[a, b, c]`, a'=a+1, b'=b+1, c=a·b) — a
/// non-affine (variable·variable) constraint, so per-query caps differ AND the constraint tree exercises the
/// symbolic evaluator's Mul path. pvs = `[seed_a, seed_b]`.
#[cfg(test)]
pub(crate) fn gen_mul_proof(config: &MyConfig, seed_a: u64, seed_b: u64, log_height: usize) -> (Proof<MyConfig>, Vec<Val>) {
    use super::native_verify::MulAir;
    use p3_matrix::dense::RowMajorMatrix;
    let n = 1usize << log_height;
    let mut vals = Vec::with_capacity(n * 3);
    for i in 0..n {
        let a = Val::from_u64(seed_a + i as u64);
        let b = Val::from_u64(seed_b + i as u64);
        vals.push(a);
        vals.push(b);
        vals.push(a * b);
    }
    let pvs = vec![Val::from_u64(seed_a), Val::from_u64(seed_b)];
    (p3_uni_stark::prove(config, &MulAir, RowMajorMatrix::new(vals, 3), &pvs), pvs)
}

/// Generate a real inner proof for `PeriodicAir` (1 col accumulating the periodic pattern `[3,7]`: a'=a+p) —
/// exercises a PERIODIC-column reference in a (non-degenerate) transition constraint. pvs = `[seed]`.
#[cfg(test)]
pub(crate) fn gen_periodic_proof(config: &MyConfig, seed: u64, log_height: usize) -> (Proof<MyConfig>, Vec<Val>) {
    use super::native_verify::{PeriodicAir, PERIODIC_PATTERN};
    use p3_matrix::dense::RowMajorMatrix;
    let n = 1usize << log_height;
    let mut a = Val::from_u64(seed);
    let mut vals = Vec::with_capacity(n);
    for i in 0..n {
        vals.push(a);
        a += Val::from_u64(PERIODIC_PATTERN[i % PERIODIC_PATTERN.len()]); // a' = a + p_i
    }
    let pvs = vec![Val::from_u64(seed)];
    (p3_uni_stark::prove(config, &PeriodicAir, RowMajorMatrix::new(vals, 1), &pvs), pvs)
}

/// Generate a real inner proof for the WIDE `WideAir` (WIDE_W=8 independent counters, `col_i(r)=seed0+i+r`) —
/// W=8 > RATE, so each committed trace row hashes to a 2-block Merkle leaf, exercising the monolith's
/// MULTI-BLOCK input-leaf hashing. pvs = the WIDE_W column seeds.
#[cfg(test)]
pub(crate) fn gen_wide_proof(config: &MyConfig, seed0: u64, log_height: usize) -> (Proof<MyConfig>, Vec<Val>) {
    use super::native_verify::{WideAir, WIDE_W};
    use p3_matrix::dense::RowMajorMatrix;
    let n = 1usize << log_height;
    let mut vals = Vec::with_capacity(n * WIDE_W);
    for r in 0..n {
        for i in 0..WIDE_W {
            vals.push(Val::from_u64(seed0 + i as u64 + r as u64)); // col_i(r) = seed0 + i + r
        }
    }
    let pvs: Vec<Val> = (0..WIDE_W).map(|i| Val::from_u64(seed0 + i as u64)).collect();
    (p3_uni_stark::prove(config, &WideAir, RowMajorMatrix::new(vals, WIDE_W), &pvs), pvs)
}

/// Generate a real inner proof for the DEGREE-3 `CubeAir` (2 cols `[a, c]`, a'=a+1, c=a³) — max constraint
/// degree 3 ⇒ nqc=2 quotient chunks, exercising the monolith's multi-CHUNK quotient recompose (2·nqc=4
/// reduced-opening terms). pvs = `[seed]`.
#[cfg(test)]
pub(crate) fn gen_cube_proof(config: &MyConfig, seed: u64, log_height: usize) -> (Proof<MyConfig>, Vec<Val>) {
    use super::native_verify::CubeAir;
    use p3_matrix::dense::RowMajorMatrix;
    let n = 1usize << log_height;
    let mut vals = Vec::with_capacity(n * 2);
    for i in 0..n {
        let a = Val::from_u64(seed + i as u64);
        vals.push(a);
        vals.push(a * a * a); // c = a³
    }
    let pvs = vec![Val::from_u64(seed)];
    (p3_uni_stark::prove(config, &CubeAir, RowMajorMatrix::new(vals, 2), &pvs), pvs)
}

/// Generate a real inner proof for the DEGREE-4 `QuartAir` (2 cols `[a, c]`, a'=a+1, c=a⁴) — max constraint
/// degree 4 ⇒ nqc=4 quotient chunks ⇒ 2·nqc=8 > RATE, exercising the monolith's MULTI-BLOCK quotient leaf.
/// pvs = `[seed]`.
#[cfg(test)]
pub(crate) fn gen_quart_proof(config: &MyConfig, seed: u64, log_height: usize) -> (Proof<MyConfig>, Vec<Val>) {
    use super::native_verify::QuartAir;
    use p3_matrix::dense::RowMajorMatrix;
    let n = 1usize << log_height;
    let mut vals = Vec::with_capacity(n * 2);
    for i in 0..n {
        let a = Val::from_u64(seed + i as u64);
        vals.push(a);
        vals.push(a * a * a * a); // c = a⁴
    }
    let pvs = vec![Val::from_u64(seed)];
    (p3_uni_stark::prove(config, &QuartAir, RowMajorMatrix::new(vals, 2), &pvs), pvs)
}

/// The nqc quotient-recompose weights — EXACTLY p3's `recompose_quotient_from_chunks`:
/// `zps_i = Π_{j≠i} vanishing_j(ζ) · vanishing_j(domain_i.first_point())⁻¹`. These verifier-computed public
/// F_p² scalars are what the monolith's epilogue consumes to recompose quotient(ζ) = Σ_i zps_i·chunk_i.
/// Deterministic in ζ + the public quotient sub-domains (so, like the periodic column values, sound to supply
/// as public inputs in pis-mode).
#[cfg(test)]
pub(crate) fn quotient_recompose_weights<A>(config: &MyConfig, air: &A, proof: &Proof<MyConfig>, pvs: &[Val]) -> Vec<Challenge>
where
    A: p3_air::Air<p3_uni_stark::SymbolicAirBuilder<Val>>,
{
    use p3_commit::PolynomialSpace;
    use p3_field::BasedVectorSpace;
    let to_ext = |p: [Val; 2]| Challenge::from_basis_coefficients_fn(|i| p[i]);
    let (_, zeta_p, _, _, _) = full_transcript_challenges(config, proof, pvs);
    let zeta = to_ext(zeta_p);
    let pcs = config.pcs();
    let degree_bits = proof.degree_bits;
    let (_, degree) = validate_degree_bits(None, degree_bits, 0, <MyPcs as Pcs<Challenge, Chal>>::log_max_lde_height(pcs)).unwrap();
    let trace_domain = <MyPcs as Pcs<Challenge, Chal>>::natural_domain_for_degree(pcs, degree);
    let layout = AirLayout::from_air::<Val>(air);
    let log_nqc = get_log_num_quotient_chunks::<Val, A>(air, layout, 0);
    let nqc = 1usize << log_nqc;
    let qd = trace_domain.create_disjoint_domain(1 << (degree_bits + log_nqc));
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

    // opening rounds (mirror verify_proof): trace at {ζ, ζ_next} + quotient chunks at ζ. nqc is derived from
    // the PROOF (quotient_chunks.len()), NOT a fixed AIR — so the reduced opening `ro` (which seeds the FRI fold
    // chain in query_fold_data) covers all 2·nqc quotient terms for any inner degree (ConstAir/fib nqc=1, cube
    // nqc=2, join-split nqc=8). A ConstAir assumption here silently dropped chunks ≥1 for higher-degree inners.
    let pcs = config.pcs();
    let degree_bits = proof.degree_bits;
    let (_, degree) = validate_degree_bits(None, degree_bits, 0, <MyPcs as Pcs<Challenge, Chal>>::log_max_lde_height(pcs)).unwrap();
    let trace_domain = <MyPcs as Pcs<Challenge, Chal>>::natural_domain_for_degree(pcs, degree);
    let nqc = proof.opened_values.quotient_chunks.len();
    let log_nqc = log2_strict(nqc);
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

/// Phase 7.3/7.6 (multi-column reduced opening — native reference, AIR-GENERIC): the DEEP reduced-opening
/// terms + `ro` for a MULTI-COLUMN inner AIR query, mirroring `open_input` like `query_terms`. Returns
/// `(terms=[(z, p_z, p_x)], x, α_fri, ro, w)` where `w` = trace width. The trace batch contributes `2·w`
/// terms — `w` columns × {ζ, ζ_next} — and the opened row value `p_x` is SHARED between a column's ζ and
/// ζ_next terms (`terms[c].px == terms[w+c].px` = the authenticated row value), the multi-column soundness
/// point. Internally asserts that px-sharing structure. Reference for the in-circuit reduced opening.
#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(crate) fn multicol_query_terms<A>(
    config: &MyConfig,
    air: &A,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
    q: usize,
) -> (Vec<(Challenge, Challenge, Val)>, Val, Challenge, Challenge, usize)
where
    A: p3_air::Air<p3_uni_stark::SymbolicAirBuilder<Val>>,
{
    use p3_field::{BasedVectorSpace, PrimeField64};
    let to_ext = |p: [Val; 2]| Challenge::from_basis_coefficients_fn(|i| p[i]);
    let (_, zeta_p, alpha_p, _, index_felts) = full_transcript_challenges(config, proof, pvs);
    let zeta = to_ext(zeta_p);
    let alpha = to_ext(alpha_p);
    let width = air.width();
    let pcs = config.pcs();
    let degree_bits = proof.degree_bits;
    let (_, degree) = validate_degree_bits(None, degree_bits, 0, <MyPcs as Pcs<Challenge, Chal>>::log_max_lde_height(pcs)).unwrap();
    let trace_domain = <MyPcs as Pcs<Challenge, Chal>>::natural_domain_for_degree(pcs, degree);
    let layout = AirLayout::from_air::<Val>(air);
    let log_nqc = get_log_num_quotient_chunks::<Val, A>(air, layout, 0);
    let nqc = 1usize << log_nqc;
    let qd = trace_domain.create_disjoint_domain(1 << (degree_bits + log_nqc));
    let qcd = qd.split_domains(nqc);
    let zeta_next = trace_domain.next_point(zeta).unwrap();
    let trace_pts = vec![(zeta, proof.opened_values.trace_local.clone()), (zeta_next, proof.opened_values.trace_next.clone().unwrap())];
    let coms: ComOpenings = vec![
        (proof.commitments.trace.clone(), vec![(trace_domain, trace_pts)]),
        (proof.commitments.quotient_chunks.clone(), qcd.iter().zip(&proof.opened_values.quotient_chunks).map(|(d, v)| (*d, vec![(zeta, v.clone())])).collect()),
    ];
    let fri = &proof.opening_proof;
    let log_global: usize = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).sum::<usize>() + 4;
    let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
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
    // px-sharing: the first 2·w terms are the trace's {ζ:cols, ζ_next:cols}; column c's two openings share the
    // one authenticated row value terms[c].px == terms[w+c].px.
    for c in 0..width {
        assert_eq!(terms[c].2, terms[width + c].2, "trace column {c}: ζ and ζ_next openings share the authenticated p_x");
    }
    (terms, x_out, alpha, ro, width)
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
    // α_stark (the constraint-combination challenge, sampled after the trace commit + pvs) is the FIRST
    // returned challenge; the OOD fold uses it, NOT α_fri (the 3rd). (ConstAir's zero folded masked this.)
    let (alpha_p, zeta_p, _, _, _) = full_transcript_challenges(config, proof, pvs);
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

/// Phase 7 (arbitrary-inner epilogue — native reference): the GENERAL OOD constraint fold on a real
/// MULTI-COLUMN `FibonacciAir` proof. Returns the fold inputs the in-circuit general epilogue consumes
/// (openings `local[0..2]`/`next[0..2]` at ζ/ζ·g; the three Lagrange selectors is_first/is_trans/is_last +
/// inv_van at ζ; quotient(ζ); α_stark; ζ) and INTERNALLY asserts the hand-written Horner α-fold
/// `folded = Σ_i α^(4−i)·C_i` (C_i = selector_i·expr_i in FibonacciAir's emission order) satisfies
/// `folded·inv_van == quotient(ζ)` — i.e. reproduces p3's `verify_constraints`. Non-circular reference for
/// generalizing the monolith epilogue beyond the 1-column ConstAir/CounterAir (the B5 / real-join-split blocker).
/// Returns (local, next, is_first, is_trans, is_last, inv_van, quotient, α_stark, ζ).
#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(crate) fn fib_epilogue_oracle(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
) -> ([Challenge; 2], [Challenge; 2], Challenge, Challenge, Challenge, Challenge, Challenge, Challenge, Challenge) {
    use super::native_verify::FibonacciAir;
    use p3_field::BasedVectorSpace;
    let to_ext = |p: [Val; 2]| Challenge::from_basis_coefficients_fn(|i| p[i]);
    let (alpha_p, zeta_p, _, _, _) = full_transcript_challenges(config, proof, pvs);
    let alpha = to_ext(alpha_p);
    let zeta = to_ext(zeta_p);
    let air = FibonacciAir;
    let pcs = config.pcs();
    let degree_bits = proof.degree_bits;
    let (_, degree) = validate_degree_bits(None, degree_bits, 0, <MyPcs as Pcs<Challenge, Chal>>::log_max_lde_height(pcs)).unwrap();
    let trace_domain = <MyPcs as Pcs<Challenge, Chal>>::natural_domain_for_degree(pcs, degree);
    let layout = AirLayout::from_air::<Val>(&air);
    let log_nqc = get_log_num_quotient_chunks::<Val, FibonacciAir>(&air, layout, 0);
    let nqc = 1usize << log_nqc;
    let qd = trace_domain.create_disjoint_domain(1 << (degree_bits + log_nqc));
    let qcd = qd.split_domains(nqc);
    let quotient = recompose_quotient_from_chunks::<MyConfig>(&qcd, &proof.opened_values.quotient_chunks, zeta);
    let local: [Challenge; 2] = proof.opened_values.trace_local[..2].try_into().unwrap();
    let next: [Challenge; 2] = proof.opened_values.trace_next.as_ref().unwrap()[..2].try_into().unwrap();
    let sel = trace_domain.selectors_at_point(zeta);
    let (is_first, is_trans, is_last, inv_van) = (sel.is_first_row, sel.is_transition, sel.is_last_row, sel.inv_vanishing);
    // Confirm the exact selector-derivation formulas the IN-CIRCUIT epilogue reconstructs from ζ (n = 2^db,
    // g = two_adic_generator(db)): z_h = ζ^n − 1; is_trans = ζ − g^{-1}; is_first·(ζ−1) = z_h;
    // is_last·(ζ−g^{-1}) = z_h; inv_van·z_h = 1. (Non-circular: sel.* come from p3's selectors_at_point.)
    {
        use p3_field::{Field, TwoAdicField};
        let g_inv = Challenge::from(Val::two_adic_generator(degree_bits)).inverse();
        let z_h = zeta.exp_power_of_2(degree_bits) - Challenge::ONE;
        assert_eq!(is_trans, zeta - g_inv, "is_transition = ζ − g^{{-1}}");
        assert_eq!(is_first * (zeta - Challenge::ONE), z_h, "is_first·(ζ−1) = z_h");
        assert_eq!(is_last * (zeta - g_inv), z_h, "is_last·(ζ−g^{{-1}}) = z_h");
        assert_eq!(inv_van * z_h, Challenge::ONE, "inv_van·z_h = 1");
    }
    // hand-written GENERAL α-fold (Horner, first-emitted highest power), matching FibonacciAir's eval order.
    let pub0 = to_ext([pvs[0], Val::ZERO]);
    let pub1 = to_ext([pvs[1], Val::ZERO]);
    let pub2 = to_ext([pvs[2], Val::ZERO]);
    let cs = [
        is_first * (local[0] - pub0),               // C0: first-row a
        is_first * (local[1] - pub1),               // C1: first-row b
        is_trans * (next[0] - local[1]),            // C2: a' − b
        is_trans * (next[1] - local[0] - local[1]), // C3: b' − a − b
        is_last * (local[1] - pub2),                // C4: last-row b
    ];
    let mut folded = Challenge::ZERO;
    for c in cs {
        folded = folded * alpha + c;
    }
    assert_eq!(folded * inv_van, quotient, "general α-fold: folded·inv_van == quotient(ζ) (matches p3 verify_constraints)");
    (local, next, is_first, is_trans, is_last, inv_van, quotient, alpha, zeta)
}

/// Phase 7.5 (arbitrary-inner epilogue — GENERIC symbolic evaluator): recursively evaluate a p3
/// `SymbolicExpression` (an AIR constraint tree extracted via `get_symbolic_constraints`, with the Lagrange
/// selectors baked in as leaves) at the OOD openings. Main{offset 0/1} → local/next[index]; Public → pub;
/// the selector leaves → their values at ζ; Add/Sub/Neg/Mul recurse. This is the AIR-INDEPENDENT constraint
/// evaluator — the same tree the in-circuit epilogue walks — so the monolith can verify ANY inner AIR from
/// its symbolic constraints rather than a hardcoded per-AIR fold.
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn eval_symbolic_native(
    e: &p3_uni_stark::SymbolicExpression<Val>,
    local: &[Challenge],
    next: &[Challenge],
    pubs: &[Challenge],
    periodic: &[Challenge],
    is_first: Challenge,
    is_last: Challenge,
    is_trans: Challenge,
) -> Challenge {
    use p3_uni_stark::{BaseEntry, BaseLeaf, SymbolicExpr};
    match e {
        SymbolicExpr::Leaf(leaf) => match leaf {
            BaseLeaf::Variable(v) => match v.entry {
                BaseEntry::Main { offset } => {
                    if offset == 0 {
                        local[v.index]
                    } else {
                        next[v.index]
                    }
                }
                BaseEntry::Public => pubs[v.index],
                BaseEntry::Periodic => periodic[v.index], // periodic column value at ζ
                BaseEntry::Preprocessed { .. } => panic!("preprocessed columns unsupported"),
            },
            BaseLeaf::IsFirstRow => is_first,
            BaseLeaf::IsLastRow => is_last,
            BaseLeaf::IsTransition => is_trans,
            BaseLeaf::Constant(c) => Challenge::from(*c),
        },
        SymbolicExpr::Add { x, y, .. } => {
            eval_symbolic_native(x, local, next, pubs, periodic, is_first, is_last, is_trans) + eval_symbolic_native(y, local, next, pubs, periodic, is_first, is_last, is_trans)
        }
        SymbolicExpr::Sub { x, y, .. } => {
            eval_symbolic_native(x, local, next, pubs, periodic, is_first, is_last, is_trans) - eval_symbolic_native(y, local, next, pubs, periodic, is_first, is_last, is_trans)
        }
        SymbolicExpr::Neg { x, .. } => -eval_symbolic_native(x, local, next, pubs, periodic, is_first, is_last, is_trans),
        SymbolicExpr::Mul { x, y, .. } => {
            eval_symbolic_native(x, local, next, pubs, periodic, is_first, is_last, is_trans) * eval_symbolic_native(y, local, next, pubs, periodic, is_first, is_last, is_trans)
        }
    }
}

/// Phase 7.5 (generic): the OOD epilogue INPUTS for an ARBITRARY inner AIR — the trace openings at ζ/ζ_next,
/// the three Lagrange selectors + inv_van at ζ, quotient(ζ), α_stark, ζ. AIR-generic (the only AIR-specific
/// step is the quotient-chunk count via `get_log_num_quotient_chunks`); the symbolic evaluator does the fold.
/// Returns (local, next, is_first, is_last, is_trans, inv_van, quotient, α_stark, ζ).
#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(crate) fn epilogue_openings<A>(
    config: &MyConfig,
    air: &A,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
) -> (Vec<Challenge>, Vec<Challenge>, Challenge, Challenge, Challenge, Challenge, Challenge, Challenge, Challenge, Vec<Challenge>)
where
    A: p3_air::Air<p3_uni_stark::SymbolicAirBuilder<Val>>,
{
    use p3_field::BasedVectorSpace;
    let to_ext = |p: [Val; 2]| Challenge::from_basis_coefficients_fn(|i| p[i]);
    let (alpha_p, zeta_p, _, _, _) = full_transcript_challenges(config, proof, pvs);
    let alpha = to_ext(alpha_p);
    let zeta = to_ext(zeta_p);
    let pcs = config.pcs();
    let degree_bits = proof.degree_bits;
    let (_, degree) = validate_degree_bits(None, degree_bits, 0, <MyPcs as Pcs<Challenge, Chal>>::log_max_lde_height(pcs)).unwrap();
    let trace_domain = <MyPcs as Pcs<Challenge, Chal>>::natural_domain_for_degree(pcs, degree);
    let layout = AirLayout::from_air::<Val>(air);
    let log_nqc = get_log_num_quotient_chunks::<Val, A>(air, layout, 0);
    let nqc = 1usize << log_nqc;
    let qd = trace_domain.create_disjoint_domain(1 << (degree_bits + log_nqc));
    let qcd = qd.split_domains(nqc);
    let quotient = recompose_quotient_from_chunks::<MyConfig>(&qcd, &proof.opened_values.quotient_chunks, zeta);
    let local = proof.opened_values.trace_local.clone();
    let next = proof.opened_values.trace_next.clone().unwrap();
    let sel = trace_domain.selectors_at_point(zeta);
    // the AIR's periodic columns evaluated at ζ (verifier-computed, deterministic in ζ) — the Periodic leaves.
    let periodic: Vec<Challenge> = air.periodic_columns().iter().map(|col| trace_domain.evaluate_periodic_column_at(col, zeta)).collect();
    (local, next, sel.is_first_row, sel.is_last_row, sel.is_transition, sel.inv_vanishing, quotient, alpha, zeta, periodic)
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

/// Aggregation domain tag for the per-inner statement digest — the SAME `DOM_TXROOT` the batch uses, so the
/// aggregator's emitted root is node-seam compatible.
#[cfg(test)]
pub(crate) const DOM_AGG: u64 = crate::batch_joinsplit_air::DOM_TXROOT;

/// Native aggregation oracle (Phase 6.3): the reference block **tx-root** for K inner proofs. Verifies each
/// inner (via `p3::verify` — the ground truth the in-circuit monolith reproduces), forms its per-inner
/// statement digest `s_k = merge([DOM_AGG,0,0,0], [pvs[0],0,0,0])` (a minimal MD-chain over the 1-value
/// ConstAir statement — the placeholder for the real 26-field join-split `tx_statement_digest`), and folds
/// into a running root exactly as `batch_joinsplit_air::batch_root`: IV=0, `root = merge(root, s_k)`, padded
/// to a power of two with a dummy `s_k`. Returns the tx-root the aggregator AIR must emit.
#[cfg(test)]
pub(crate) fn agg_statement_digest(pv0: Val) -> [Val; 4] {
    use crate::joinsplit_air::merge;
    merge([Val::from_u64(DOM_AGG), Val::ZERO, Val::ZERO, Val::ZERO], [pv0, Val::ZERO, Val::ZERO, Val::ZERO])
}

#[cfg(test)]
pub(crate) fn agg_root(config: &MyConfig, inners: &[(Proof<MyConfig>, Vec<Val>)]) -> [Val; 4] {
    use crate::joinsplit_air::merge;
    let dummy = agg_statement_digest(Val::ZERO); // canonical padding statement (pv0 = 0)
    let mut root = [Val::ZERO; 4]; // IV = 0
    for (proof, pvs) in inners {
        assert!(p3_uni_stark::verify(config, &ConstAir, proof, pvs).is_ok(), "aggregated inner proof must verify");
        root = merge(root, agg_statement_digest(pvs[0]));
    }
    let n_pad = inners.len().max(1).next_power_of_two();
    for _ in inners.len()..n_pad {
        root = merge(root, dummy);
    }
    root
}

/// GENERAL-ARITY fold CHAIN oracle (Phase 5 re-fusion): the full commit-phase fold for query `q` as the
/// monolith runs it — the initial reduced opening `ro`, then per round `(evals, beta, xs, slot, folded)`
/// where `slot = index % arity` is the running eval's position in the group, and finally `final_poly[0]`
/// (the accept value the chain must reach: for final_poly_len=1, `eval_final_poly` is that constant). This
/// is the reference for the in-circuit arity-2^la fold chain E_0=ro → E_1 → … → E_N == final_poly[0].
#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(crate) fn general_fold_chain_oracle(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
    q: usize,
) -> (Challenge, Vec<(Vec<Challenge>, Challenge, Vec<Val>, usize, Challenge)>, Challenge) {
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
        let slot = index % arity;
        let mut evals = Challenge::zero_vec(arity);
        evals[slot] = e;
        let mut sib = 0;
        for (j, ev) in evals.iter_mut().enumerate() {
            if j != slot {
                *ev = step.sibling_values[sib];
                sib += 1;
            }
        }
        let log_folded = log_current - la;
        index >>= la;
        let subgroup_start = Val::two_adic_generator(log_folded + la).exp_u64(reverse_bits_len(index, log_folded) as u64);
        let g_la = Val::two_adic_generator(la);
        let mut xs: Vec<Val> = (0..arity).map(|i| subgroup_start * g_la.exp_u64(i as u64)).collect();
        reverse_slice_index_bits(&mut xs);
        let folded = <TwoAdicFriFolding<(), <ChallengeMmcs as Mmcs<Challenge>>::Error> as FriFoldingStrategy<Val, Challenge>>::fold_row(
            &folding, index, log_folded, la, betas[r], evals.iter().copied(),
        );
        out.push((evals.clone(), betas[r], xs, slot, folded));
        e = folded;
        log_current = log_folded;
    }
    // final_poly_len = 1 for the milestone ⇒ eval_final_poly(x) = final_poly[0] (constant); the chain's last
    // folded eval must equal it (the native `eval_final_poly(final_query_point) == folded` accept check).
    (ro, out, fri.final_poly[0])
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

    /// Phase 7 (arbitrary-inner epilogue, native reference): the GENERAL multi-column OOD α-fold on a real
    /// `FibonacciAir` proof reproduces p3's `verify_constraints`, and breaks on a tampered public value.
    #[test]
    #[ignore = "slow: Phase 7 general OOD fold (multi-column FibonacciAir) vs p3::verify_constraints"]
    fn phase7_fib_general_fold_matches_p3() {
        use super::super::native_verify::FibonacciAir;
        let config = make_config(1, 32);
        let (proof, pvs) = gen_fib_proof(&config, 1, 1, 6);
        // p3 accepts the multi-column proof.
        assert!(verify(&config, &FibonacciAir, &proof, &pvs).is_ok(), "p3::verify should accept the Fibonacci proof");
        // the hand-written GENERAL Horner α-fold reproduces p3's verify_constraints (internal assert of the
        // oracle: folded·inv_van == quotient(ζ)); the three selectors at ζ are distinct (all constraint types
        // genuinely exercised).
        let (_l, _n, is_first, is_trans, is_last, ..) = fib_epilogue_oracle(&config, &proof, &pvs);
        assert!(is_first != is_trans && is_trans != is_last && is_first != is_last, "distinct is_first/is_trans/is_last at ζ");
        // tampered public (wrong seed) ⇒ p3 rejects AND the general fold relation breaks.
        let bad = vec![pvs[0] + Val::ONE, pvs[1], pvs[2]];
        assert!(verify(&config, &FibonacciAir, &proof, &bad).is_err(), "p3 rejects wrong public value");
        let prev = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| fib_epilogue_oracle(&config, &proof, &bad)));
        std::panic::set_hook(prev);
        assert!(r.is_err(), "general fold relation must break on a tampered public value");
    }

    /// Phase 7.5 (native): the GENERIC symbolic-constraint fold — extract the inner AIR's constraint trees via
    /// p3's `get_symbolic_constraints` and evaluate them with `eval_symbolic_native` (data-driven, no hardcoded
    /// per-AIR fold) — reproduces p3's `verify_constraints` for the multi-column Fibonacci, matching the
    /// hand-written 7.1 fold. This is the AIR-independent path the monolith epilogue generalizes to.
    #[test]
    #[ignore = "slow: Phase 7.5 generic symbolic-constraint fold (get_symbolic_constraints) vs p3"]
    fn phase7_fib_symbolic_fold_matches_p3() {
        use super::super::native_verify::FibonacciAir;
        use super::eval_symbolic_native;
        use p3_uni_stark::{get_symbolic_constraints, AirLayout};
        let config = make_config(1, 32);
        let (proof, pvs) = gen_fib_proof(&config, 1, 1, 6);
        let (local, next, is_first, is_trans, is_last, inv_van, quotient, alpha, _z) = fib_epilogue_oracle(&config, &proof, &pvs);
        let pubs: Vec<Challenge> = pvs.iter().map(|&p| Challenge::from(p)).collect();
        // extract the constraint trees (selectors baked in) directly from the AIR — no per-AIR hardcoding.
        let layout = AirLayout::from_air::<Val>(&FibonacciAir);
        let constraints = get_symbolic_constraints::<Val, FibonacciAir>(&FibonacciAir, layout);
        assert_eq!(constraints.len(), 5, "FibonacciAir emits 5 constraints");
        // Horner α-fold over the extracted constraints (emission order, first-emitted highest power).
        let mut folded = Challenge::ZERO;
        for c in &constraints {
            folded = folded * alpha + eval_symbolic_native(c, &local, &next, &pubs, &[], is_first, is_last, is_trans);
        }
        assert_eq!(folded * inv_van, quotient, "GENERIC symbolic fold reproduces p3::verify_constraints (Fibonacci)");
        println!("Phase 7.5: generic symbolic-constraint fold == p3 for Fibonacci ({} constraints, data-driven, no hardcoded fold)", constraints.len());
    }

    /// Phase 7.5 (native, DEGREE-2): the generic symbolic fold handles a NON-AFFINE inner — `MulAir`'s
    /// `c = a·b` constraint is a Mul of two trace variables (degree 2), exercising the evaluator's
    /// variable·variable path (which Fibonacci's all-affine constraints don't). Uses the AIR-generic
    /// `epilogue_openings` + `get_symbolic_constraints`, and reproduces p3::verify_constraints.
    #[test]
    #[ignore = "slow: Phase 7.5 generic symbolic fold on a degree-2 inner (MulAir) vs p3"]
    fn phase7_mul_symbolic_fold_matches_p3() {
        use super::super::native_verify::MulAir;
        use super::{epilogue_openings, eval_symbolic_native};
        use p3_uni_stark::{get_symbolic_constraints, verify, AirLayout};
        let config = make_config(1, 32);
        let (proof, pvs) = gen_mul_proof(&config, 3, 5, 6);
        assert!(verify(&config, &MulAir, &proof, &pvs).is_ok(), "p3 accepts the degree-2 MulAir proof");
        let (local, next, is_first, is_last, is_trans, inv_van, quotient, alpha, _z, periodic) = epilogue_openings(&config, &MulAir, &proof, &pvs);
        let pubs: Vec<Challenge> = pvs.iter().map(|&p| Challenge::from(p)).collect();
        let layout = AirLayout::from_air::<Val>(&MulAir);
        let constraints = get_symbolic_constraints::<Val, MulAir>(&MulAir, layout);
        assert_eq!(constraints.len(), 5, "MulAir emits 5 constraints (incl. the degree-2 product)");
        let mut folded = Challenge::ZERO;
        for c in &constraints {
            folded = folded * alpha + eval_symbolic_native(c, &local, &next, &pubs, &periodic, is_first, is_last, is_trans);
        }
        assert_eq!(folded * inv_van, quotient, "generic symbolic fold reproduces p3 for a DEGREE-2 (variable·variable) AIR");
        println!("Phase 7.5: generic symbolic fold == p3 for the degree-2 MulAir (c=a·b exercises the Mul-of-variables path)");
    }

    /// Phase 7.7 (native): the generic symbolic fold handles a PERIODIC-column inner — `PeriodicAir`'s
    /// transition `a' = a + p` references a periodic value (BaseEntry::Periodic). `epilogue_openings` returns
    /// the periodic column evaluated at ζ; the evaluator's Periodic leaf reads it. Reproduces p3.
    #[test]
    #[ignore = "slow: Phase 7.7 generic symbolic fold on a periodic-column inner (PeriodicAir) vs p3"]
    fn phase7_periodic_symbolic_fold_matches_p3() {
        use super::super::native_verify::PeriodicAir;
        use super::{epilogue_openings, eval_symbolic_native};
        use p3_uni_stark::{get_symbolic_constraints, verify, AirLayout};
        let config = make_config(1, 32);
        let (proof, pvs) = gen_periodic_proof(&config, 5, 6);
        assert!(verify(&config, &PeriodicAir, &proof, &pvs).is_ok(), "p3 accepts the periodic-column proof");
        let (local, next, is_first, is_last, is_trans, inv_van, quotient, alpha, _z, periodic) = epilogue_openings(&config, &PeriodicAir, &proof, &pvs);
        assert_eq!(periodic.len(), 1, "PeriodicAir has 1 periodic column");
        let pubs: Vec<Challenge> = pvs.iter().map(|&p| Challenge::from(p)).collect();
        let layout = AirLayout::from_air::<Val>(&PeriodicAir);
        let constraints = get_symbolic_constraints::<Val, PeriodicAir>(&PeriodicAir, layout);
        let mut folded = Challenge::ZERO;
        for c in &constraints {
            folded = folded * alpha + eval_symbolic_native(c, &local, &next, &pubs, &periodic, is_first, is_last, is_trans);
        }
        assert_eq!(folded * inv_van, quotient, "generic symbolic fold reproduces p3 for a PERIODIC-column AIR");
        println!("Phase 7.7: generic symbolic fold == p3 for PeriodicAir (a'=a+p reads the periodic value at ζ)");
    }

    /// Phase 7.8 (native): the symbolic epilogue scales to the REAL production `JoinSplitAir` — W=19 columns,
    /// 33 periodic columns (round constants), 26 public inputs, degree-7 Poseidon constraints, degree_bits=12.
    /// Proven NON-HIDING (the recursion path) + extracted via `epilogue_openings`/`get_symbolic_constraints`;
    /// the generic Horner fold over ALL its constraint trees reproduces p3's `verify_constraints`. This is the
    /// production inner's constraint set — the same evaluator that handled Fibonacci/Mul/Periodic.
    #[test]
    #[ignore = "slow: Phase 7.8 symbolic epilogue on the REAL JoinSplitAir vs p3"]
    fn phase7_joinsplit_symbolic_fold_matches_p3() {
        use super::{epilogue_openings, eval_symbolic_native};
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
        use p3_uni_stark::{get_symbolic_constraints, prove, verify, AirLayout};
        let config = make_config(1, 16); // recursion NON-HIDING config (arity-2); the monolith's verify path
        let w = demo_witness();
        let pis = public_values(&w);
        let trace = build_trace(&w);
        let proof = prove(&config, &JoinSplitAir, trace, &pis);
        assert!(verify(&config, &JoinSplitAir, &proof, &pis).is_ok(), "p3 accepts the (non-hiding) join-split proof");
        let (local, next, is_first, is_last, is_trans, inv_van, quotient, alpha, _z, periodic) = epilogue_openings(&config, &JoinSplitAir, &proof, &pis);
        assert_eq!(local.len(), WIDTH, "W=19 trace openings");
        assert_eq!(periodic.len(), N_PERIODIC, "33 periodic columns at ζ");
        assert_eq!(pis.len(), N_PUBLIC, "26 public inputs");
        let pubs: Vec<Challenge> = pis.iter().map(|&p| Challenge::from(p)).collect();
        let layout = AirLayout::from_air::<Val>(&JoinSplitAir);
        let constraints = get_symbolic_constraints::<Val, JoinSplitAir>(&JoinSplitAir, layout);
        let mut folded = Challenge::ZERO;
        for c in &constraints {
            folded = folded * alpha + eval_symbolic_native(c, &local, &next, &pubs, &periodic, is_first, is_last, is_trans);
        }
        assert_eq!(folded * inv_van, quotient, "generic symbolic fold reproduces p3 for the REAL JoinSplitAir");
        println!(
            "Phase 7.8: symbolic epilogue == p3 for the REAL JoinSplitAir — {} constraints, W={WIDTH}, {N_PERIODIC} periodic, {N_PUBLIC} pubs, degree_bits={}",
            constraints.len(),
            proof.degree_bits
        );
    }
}
