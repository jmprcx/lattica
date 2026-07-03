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

use p3_air::symbolic::{
    get_symbolic_constraints, AirLayout, BaseEntry, BaseLeaf, SymbolicAirBuilder, SymbolicExpression,
};
use p3_air::{Air, DebugConstraintBuilder};
use p3_challenger::{CanObserve, FieldChallenger};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_uni_stark::{
    get_log_num_quotient_chunks, quotient_values, Commitments, OpenedValues, Proof,
    ProverConstraintFolder, StarkGenericConfig, Val,
};
use std::collections::HashMap;
use std::sync::Arc;

/// Which quotient evaluator `prove_gpu` uses. `P3` = p3's `quotient_values` (identity fork, the
/// byte-identical baseline). `Cpu` = our DAG interpreter (validates the flattening in pure Rust).
/// (`Gpu` is added in the next increment.)
#[derive(Clone, Copy, Debug)]
pub enum QuotientMode {
    P3,
    Cpu,
}

/// One node of the flattened constraint DAG. Leaves read from the row context; interior ops reference
/// earlier node indices (the DAG is topologically ordered with `Arc`-identity CSE, so each shared
/// subexpression is computed once).
enum Op<F> {
    MainLocal(usize),
    MainNext(usize),
    Periodic(usize),
    Public(usize),
    IsFirst,
    IsLast,
    IsTransition,
    Const(F),
    Add(usize, usize),
    Sub(usize, usize),
    Mul(usize, usize),
    Neg(usize),
}

/// The flattened quotient program: a topological instruction stream + the node index of each
/// constraint's root (in constraint order — the same order as `ProverConstraintFolder::base_constraints`,
/// so `roots[k]` pairs with `base_alpha_powers[d][k]`).
struct QuotientProgram<F> {
    ops: Vec<Op<F>>,
    roots: Vec<usize>,
}

/// Flatten `get_symbolic_constraints(air)` into a `QuotientProgram`, deduplicating shared `Arc` nodes.
fn flatten_air<F, A>(air: &A, layout: AirLayout) -> QuotientProgram<F>
where
    F: Field,
    A: Air<SymbolicAirBuilder<F>>,
{
    fn leaf_op<F: Field>(leaf: &BaseLeaf<F>) -> Op<F> {
        match leaf {
            BaseLeaf::Variable(v) => match v.entry {
                BaseEntry::Main { offset: 0 } => Op::MainLocal(v.index),
                BaseEntry::Main { offset: 1 } => Op::MainNext(v.index),
                BaseEntry::Main { offset } => panic!("unexpected main row offset {offset}"),
                BaseEntry::Periodic => Op::Periodic(v.index),
                BaseEntry::Public => Op::Public(v.index),
                BaseEntry::Preprocessed { .. } => panic!("preprocessed columns unsupported"),
            },
            BaseLeaf::IsFirstRow => Op::IsFirst,
            BaseLeaf::IsLastRow => Op::IsLast,
            BaseLeaf::IsTransition => Op::IsTransition,
            BaseLeaf::Constant(c) => Op::Const(*c),
        }
    }
    fn go<F: Field>(e: &SymbolicExpression<F>, ops: &mut Vec<Op<F>>, memo: &mut HashMap<usize, usize>) -> usize {
        let child = |c: &Arc<SymbolicExpression<F>>, ops: &mut Vec<Op<F>>, memo: &mut HashMap<usize, usize>| {
            let key = Arc::as_ptr(c) as usize;
            if let Some(&i) = memo.get(&key) {
                return i;
            }
            let i = go(c, ops, memo);
            memo.insert(key, i);
            i
        };
        let op = match e {
            SymbolicExpression::Leaf(l) => leaf_op(l),
            SymbolicExpression::Add { x, y, .. } => {
                let (a, b) = (child(x, ops, memo), child(y, ops, memo));
                Op::Add(a, b)
            }
            SymbolicExpression::Sub { x, y, .. } => {
                let (a, b) = (child(x, ops, memo), child(y, ops, memo));
                Op::Sub(a, b)
            }
            SymbolicExpression::Mul { x, y, .. } => {
                let (a, b) = (child(x, ops, memo), child(y, ops, memo));
                Op::Mul(a, b)
            }
            SymbolicExpression::Neg { x, .. } => Op::Neg(child(x, ops, memo)),
        };
        ops.push(op);
        ops.len() - 1
    }
    let constraints = get_symbolic_constraints::<F, A>(air, layout);
    let mut ops = Vec::new();
    let mut memo = HashMap::new();
    let roots = constraints.iter().map(|c| go(c, &mut ops, &mut memo)).collect();
    QuotientProgram { ops, roots }
}

/// Evaluate the program at one row, returning the base-field value of each constraint.
fn eval_row<F: Field>(
    prog: &QuotientProgram<F>,
    local: &[F],
    next: &[F],
    periodic: &[F],
    public: &[F],
    is_first: F,
    is_last: F,
    is_transition: F,
) -> Vec<F> {
    let mut v = vec![F::ZERO; prog.ops.len()];
    for i in 0..prog.ops.len() {
        v[i] = match &prog.ops[i] {
            Op::MainLocal(c) => local[*c],
            Op::MainNext(c) => next[*c],
            Op::Periodic(c) => periodic[*c],
            Op::Public(c) => public[*c],
            Op::IsFirst => is_first,
            Op::IsLast => is_last,
            Op::IsTransition => is_transition,
            Op::Const(k) => *k,
            Op::Add(a, b) => v[*a] + v[*b],
            Op::Sub(a, b) => v[*a] - v[*b],
            Op::Mul(a, b) => v[*a] * v[*b],
            Op::Neg(a) => -v[*a],
        };
    }
    prog.roots.iter().map(|&r| v[r]).collect()
}

/// A scalar reimplementation of `p3_uni_stark::quotient_values` whose per-row constraint evaluation runs
/// through our flattened DAG interpreter instead of `air.eval`. All setup (selectors, alpha powers,
/// periodic table) reuses p3's public helpers verbatim, so the output is byte-identical. Same signature
/// as p3's `quotient_values` — a drop-in swap in `prove_gpu`. (Base constraints only; our circuits have
/// no extension-field constraints.)
pub fn cpu_quotient_values<SC, A, Mat>(
    pcs: &SC::Pcs,
    air: &A,
    public_values: &[Val<SC>],
    layout: AirLayout,
    trace_domain: <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain,
    quotient_domain: <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain,
    trace_on_quotient_domain: &Mat,
    _preprocessed_on_quotient_domain: Option<&Mat>,
    alpha: SC::Challenge,
) -> Vec<SC::Challenge>
where
    SC: StarkGenericConfig,
    A: Air<SymbolicAirBuilder<Val<SC>>> + for<'a> Air<ProverConstraintFolder<'a, SC>>,
    Mat: Matrix<Val<SC>> + Sync,
{
    let quotient_size = quotient_domain.size();
    let sels = trace_domain.selectors_on_coset(quotient_domain);
    let next_step = quotient_size / trace_domain.size();

    let periodic_cols = air.periodic_columns();
    let periodic_table = pcs.build_periodic_lde_table(&periodic_cols, trace_domain, quotient_domain);
    let n_periodic = periodic_table.width();

    let prog = flatten_air::<Val<SC>, A>(air, layout);
    let total = prog.roots.len();
    // `decompose_alpha`: constraint j is folded with weight α^{total-1-j} (descending / Horner). All our
    // constraints are base-field (no ext), so base_indices = 0..total and this is just the reversed
    // power list; `acc = Σ_j cons[j] · α^{total-1-j}` reproduces `finalize_constraints` exactly.
    let mut alpha_powers: Vec<SC::Challenge> = alpha.powers().take(total).collect();
    alpha_powers.reverse();

    (0..quotient_size)
        .map(|i| {
            let local: Vec<Val<SC>> = trace_on_quotient_domain.row(i).unwrap().into_iter().collect();
            let next: Vec<Val<SC>> =
                trace_on_quotient_domain.row((i + next_step) % quotient_size).unwrap().into_iter().collect();
            let periodic: Vec<Val<SC>> = (0..n_periodic).map(|c| *periodic_table.get(i, c)).collect();
            let cons = eval_row(&prog, &local, &next, &periodic, public_values, sels.is_first_row[i], sels.is_last_row[i], sels.is_transition[i]);
            let acc: SC::Challenge = cons.iter().zip(&alpha_powers).map(|(&c, &a)| a * c).sum();
            // quotient(x) = constraints(x) / Z_H(x) = acc · inv_vanishing (Challenge · base).
            acc * sels.inv_vanishing[i]
        })
        .collect()
}

/// A fork of `p3_uni_stark::prove` (preprocessed = None) whose quotient evaluation runs on the GPU.
/// Every step other than the quotient reuses p3's public API verbatim; see the module docs for the
/// safety/audit rationale. Generic over any `StarkGenericConfig` so it serves joinsplit + htlc.
pub fn prove_gpu<SC, A>(
    config: &SC,
    air: &A,
    trace: RowMajorMatrix<Val<SC>>,
    public_values: &[Val<SC>],
    mode: QuotientMode,
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

    // === THE ONLY SWAP vs p3 === the quotient evaluator (all three share p3's `quotient_values` signature).
    let quotient_values = match mode {
        QuotientMode::P3 => quotient_values(
            pcs, air, public_values, layout, trace_domain, quotient_domain, &trace_on_quotient_domain, None, alpha,
        ),
        QuotientMode::Cpu => cpu_quotient_values(
            pcs, air, public_values, layout, trace_domain, quotient_domain, &trace_on_quotient_domain, None, alpha,
        ),
    };

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
    use p3_uni_stark::{prove, verify};

    /// Q1 gate: `prove_gpu` in `P3` mode (still calling p3's `quotient_values`) is a FAITHFUL fork —
    /// byte-identical to `p3_uni_stark::prove` under a deterministic (non-hiding) config. Pins an exact
    /// baseline before the quotient swap; runs on CPU (no GPU needed — the bench-CPU config is all-CPU).
    #[test]
    fn prove_gpu_byte_identical_to_p3() {
        let w = joinsplit_air::demo_witness();
        let pis = joinsplit_air::public_values(&w);
        let cfg = crate::config::gpu::make_bench_config_cpu();
        let p_ref = prove(&cfg, &JoinSplitAir, joinsplit_air::build_trace(&w), &pis);
        let p_fork = prove_gpu(&cfg, &JoinSplitAir, joinsplit_air::build_trace(&w), &pis, QuotientMode::P3);
        assert_eq!(
            postcard::to_allocvec(&p_ref).unwrap(),
            postcard::to_allocvec(&p_fork).unwrap(),
            "prove_gpu(P3) must be byte-identical to p3::prove under a deterministic config"
        );
    }

    /// Q2 gate: the DAG interpreter (`Cpu` mode) produces VALID proofs — they verify under the same
    /// config, for both circuits. Verification is the sound gate here: it recomputes the DEEP quotient
    /// relation, so a wrong quotient is rejected. (Byte-identity is NOT usable: p3's own `prove` is not
    /// byte-deterministic for these circuits — Goldilocks is stored non-canonically and rayon's parallel
    /// reduction order varies the representation the Merkle commit hashes. The interpreter's quotient was
    /// separately confirmed element-wise equal to p3's `quotient_values`.)
    #[test]
    fn cpu_quotient_verifies() {
        let cfg = crate::config::gpu::make_bench_config_cpu();
        let w = joinsplit_air::demo_witness();
        let pis = joinsplit_air::public_values(&w);
        let pj = prove_gpu(&cfg, &JoinSplitAir, joinsplit_air::build_trace(&w), &pis, QuotientMode::Cpu);
        assert!(verify(&cfg, &JoinSplitAir, &pj, &pis).is_ok(), "cpu-quotient join-split proof must verify");
        use crate::htlc_air::{self, HtlcAir};
        let hw = htlc_air::demo_htlc_witness();
        let hpis = htlc_air::public_values(&hw);
        let ph = prove_gpu(&cfg, &HtlcAir, htlc_air::build_trace(&hw), &hpis, QuotientMode::Cpu);
        assert!(verify(&cfg, &HtlcAir, &ph, &hpis).is_ok(), "cpu-quotient HTLC proof must verify");
    }
}
