//! B3b WIRING — native FRI verify (re-implementing `p3-fri::verify_fri`), the blueprint to port to the
//! in-circuit AIR.  ⚠️ WORK IN PROGRESS — this is NOT yet a complete or validated verifier.
//!
//! The in-circuit verifier's last and largest part is the FRI query loop. It can only be validated as a
//! whole (against `pcs.verify`), so it is built as ONE native re-implementation first (the algorithm),
//! then ported to constraints (every operation it performs already has a validated in-circuit gadget).
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
//! ## Status
//! - `verify_query` (step 3): implemented natively below, mirroring p3 (uses `mmcs.verify_batch` +
//!   `TwoAdicFriFolding::fold_row`, the latter validated == our `fri_fold::native_fold`).
//! - `open_input` (step 2) + the `verify_fri` driver (steps 1, 4): the remaining native implementation;
//!   then end-to-end validation vs `pcs.verify` (accept real / reject tampered), then the AIR port.

use p3_commit::Mmcs;
use p3_field::extension::BinomialExtensionField;
use p3_field::{PrimeCharacteristicRing, TwoAdicField};
use p3_fri::{CommitPhaseProofStep, FriParameters, TwoAdicFriFolding};
use p3_goldilocks::Goldilocks;
use p3_matrix::Dimensions;

type Val = Goldilocks;
type Challenge = BinomialExtensionField<Val, 2>;

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

fn reverse_bits_len(mut x: usize, bits: usize) -> usize {
    let mut r = 0;
    for _ in 0..bits {
        r = (r << 1) | (x & 1);
        x >>= 1;
    }
    r
}

// TODO (wiring continuation): `open_input` (reduced openings from the batch MMCS openings + the DEEP
// combination, with the GENERATOR shift + bit-reversal + α-by-height accumulation) and the `verify_fri`
// driver (transcript → per-query open_input + verify_query + final-poly check), then end-to-end
// validation vs `pcs.verify` (accept real proof / reject tampered), then the AIR port.
