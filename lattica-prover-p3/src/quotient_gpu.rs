//! GPU quotient offload (opt-in via `--features gpu`) — a fork of `p3_uni_stark::prove`.
//!
//! The quotient evaluation (`quotient_values`) is the one heavy proving step that is NOT behind a trait
//! seam in p3 — it is inline in `prove()`. To move it to the GPU we fork `prove`: this module is a
//! faithful copy of `p3_uni_stark::prove_with_preprocessed` (specialized to `preprocessed = None`, which
//! is all our production circuits use) that reuses **every** other p3 public function verbatim and swaps
//! only the `quotient_values` call for a GPU evaluator.
//!
//! **Safety.** This is prove-only and validated by the UNCHANGED verifier: a proof from `prove_gpu`
//! deserializes as `Proof<SC>` and must pass `p3_uni_stark::verify` / the production `verify_bytes` — a
//! wrong fork simply fails to verify (the same argument as `GpuDft` / `GpuHidingMerkleMmcs`). Under a
//! deterministic (non-hiding) config it is additionally **byte-identical** to p3's `prove`.
//!
//! **Audit note.** This duplicates the consensus prover's control flow; it must track upstream p3's
//! `prove_with_preprocessed`. Kept in this one clearly-labeled file for that reason.

use p3_air::symbolic::{AirLayout, SymbolicAirBuilder};
use p3_air::{Air, DebugConstraintBuilder};
use p3_challenger::{CanObserve, FieldChallenger};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_uni_stark::{
    get_log_num_quotient_chunks, quotient_values, Commitments, OpenedValues, Proof,
    ProverConstraintFolder, StarkGenericConfig, Val,
};

/// A fork of `p3_uni_stark::prove` (preprocessed = None) whose quotient evaluation runs on the GPU.
/// Every step other than the quotient reuses p3's public API verbatim; see the module docs for the
/// safety/audit rationale. Generic over any `StarkGenericConfig` so it serves joinsplit + htlc.
pub fn prove_gpu<SC, A>(
    config: &SC,
    air: &A,
    trace: RowMajorMatrix<Val<SC>>,
    public_values: &[Val<SC>],
) -> Proof<SC>
where
    SC: StarkGenericConfig,
    A: Air<SymbolicAirBuilder<Val<SC>>>
        + for<'a> Air<ProverConstraintFolder<'a, SC>>
        + for<'a> Air<DebugConstraintBuilder<'a, Val<SC>>>,
{
    #[cfg(debug_assertions)]
    p3_air::check_constraints(air, &trace, public_values);

    let degree = trace.height();
    let log_degree = degree.trailing_zeros() as usize; // degree is a power of two
    let log_ext_degree = log_degree + config.is_zk();

    // Our production circuits define no preprocessed columns (fork is specialized to that case).
    assert_eq!(air.preprocessed_width(), 0, "prove_gpu: preprocessed columns unsupported");
    let preprocessed_width = 0usize;

    let layout = AirLayout {
        preprocessed_width,
        main_width: air.width(),
        num_public_values: air.num_public_values(),
        num_periodic_columns: air.num_periodic_columns(),
        ..Default::default()
    };

    let log_num_quotient_chunks = get_log_num_quotient_chunks::<Val<SC>, A>(air, layout, config.is_zk());
    let num_quotient_chunks = 1 << (log_num_quotient_chunks + config.is_zk());

    let pcs = config.pcs();
    let mut challenger = config.initialise_challenger();

    let trace_domain = pcs.natural_domain_for_degree(degree);
    let ext_trace_domain = pcs.natural_domain_for_degree(degree * (config.is_zk() + 1));

    let (trace_commit, trace_data) = pcs.commit([(ext_trace_domain, trace)]);

    challenger.observe(Val::<SC>::from_u8(log_ext_degree as u8));
    challenger.observe(Val::<SC>::from_u8(log_degree as u8));
    challenger.observe(Val::<SC>::from_usize(preprocessed_width));
    challenger.observe(trace_commit.clone());
    challenger.observe_slice(public_values);

    let alpha: SC::Challenge = challenger.sample_algebra_element();

    let quotient_domain =
        ext_trace_domain.create_disjoint_domain(1 << (log_ext_degree + log_num_quotient_chunks));
    let trace_on_quotient_domain = pcs.get_evaluations_on_domain(&trace_data, 0, quotient_domain);

    // === THE ONLY SWAP vs p3 === (Q1: p3's CPU quotient_values; Q2/Q3 replace with the GPU evaluator).
    let quotient_values = quotient_values(
        pcs,
        air,
        public_values,
        layout,
        trace_domain,
        quotient_domain,
        &trace_on_quotient_domain,
        None,
        alpha,
    );

    let quotient_flat = RowMajorMatrix::new_col(quotient_values).flatten_to_base();
    let (quotient_commit, quotient_data) =
        pcs.commit_quotient(quotient_domain, quotient_flat, num_quotient_chunks);
    challenger.observe(quotient_commit.clone());

    let (opt_r_commit, opt_r_data) = if SC::Pcs::ZK {
        let (r_commit, r_data) = pcs
            .get_opt_randomization_poly_commitment(core::iter::once(ext_trace_domain))
            .expect("ZK is enabled, so we should have randomization commitments");
        (Some(r_commit), Some(r_data))
    } else {
        (None, None)
    };

    let commitments = Commitments {
        trace: trace_commit,
        quotient_chunks: quotient_commit,
        random: opt_r_commit.clone(),
    };
    if let Some(r_commit) = opt_r_commit {
        challenger.observe(r_commit);
    }

    let zeta: SC::Challenge = challenger.sample_algebra_element();
    let zeta_next = trace_domain.next_point(zeta).expect("domain should support next_point");

    let is_random = opt_r_data.is_some();
    let main_next = !air.main_next_row_columns().is_empty();
    let (opened_values, opening_proof) = {
        let round0 = opt_r_data.as_ref().map(|r_data| (r_data, vec![vec![zeta]]));
        let round1_points = if main_next { vec![zeta, zeta_next] } else { vec![zeta] };
        let round1 = (&trace_data, vec![round1_points]);
        let round2 = (&quotient_data, vec![vec![zeta]; num_quotient_chunks]);
        let rounds = round0.into_iter().chain([round1, round2]).collect();
        pcs.open_with_preprocessing(rounds, &mut challenger, false)
    };

    let trace_idx = SC::Pcs::TRACE_IDX;
    let quotient_idx = SC::Pcs::QUOTIENT_IDX;
    let trace_local = opened_values[trace_idx][0][0].clone();
    let trace_next = if main_next { Some(opened_values[trace_idx][0][1].clone()) } else { None };
    let quotient_chunks = opened_values[quotient_idx].iter().map(|v| v[0].clone()).collect();
    let random = if is_random { Some(opened_values[0][0][0].clone()) } else { None };

    let opened_values = OpenedValues {
        trace_local,
        trace_next,
        preprocessed_local: None,
        preprocessed_next: None,
        quotient_chunks,
        random,
    };
    Proof { commitments, opened_values, opening_proof, degree_bits: log_ext_degree }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::joinsplit_air::{self, JoinSplitAir};
    use p3_uni_stark::prove;

    /// Q1 gate: `prove_gpu` (still calling p3's `quotient_values`) is a FAITHFUL fork — byte-identical to
    /// `p3_uni_stark::prove` under a deterministic (non-hiding) config. This pins an exact baseline before
    /// the quotient swap, and runs on CPU (no GPU needed — the bench-CPU config is all-CPU).
    #[test]
    fn prove_gpu_byte_identical_to_p3() {
        let w = joinsplit_air::demo_witness();
        let pis = joinsplit_air::public_values(&w);
        let cfg = crate::config::gpu::make_bench_config_cpu();
        let p_ref = prove(&cfg, &JoinSplitAir, joinsplit_air::build_trace(&w), &pis);
        let p_fork = prove_gpu(&cfg, &JoinSplitAir, joinsplit_air::build_trace(&w), &pis);
        assert_eq!(
            postcard::to_allocvec(&p_ref).unwrap(),
            postcard::to_allocvec(&p_fork).unwrap(),
            "prove_gpu must be byte-identical to p3::prove under a deterministic config"
        );
    }
}
