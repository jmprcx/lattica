//! Research recursive aggregation API for the validated R4 flat JoinSplit aggregator.
//!
//! This is intentionally not wired to the C ABI or Zig node seam.  It promotes the
//! existing non-hiding R4 test builder into reusable crate code, with an optimized
//! streaming outer-prover option when the `stream` feature is enabled.

use crate::batch_joinsplit_air::{dummy_sk, tx_statement_digest, DOM_TXROOT};
use crate::joinsplit_air::{merge, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
use crate::poseidon2_air::{native_permute, native_steps, BLOCK, W};
#[cfg(feature = "stream")]
use crate::recursion::monolith::MonolithTracePart;
use crate::recursion::monolith::{
    monolith_build_trace, CommitRoundData, HidingWitness, MonolithAir, MonolithQuery,
    MonolithTraceRowRange, MonolithTraceSource, MAX_AGG_TILES,
};
use crate::recursion::native_fri::{
    cap_felts, epilogue_openings, eval_symbolic_native, make_config_cap, multicol_query_terms,
    preamble_challenges, query_commit_merkle_all, query_fold_data, query_input_merkle,
    query_quotient_merkle, quotient_recompose_weights, Challenge, MyConfig, Val,
};
use crate::recursion::native_verify::{
    hiding_epilogue_openings, hiding_multicol_query_terms, hiding_query_commit_merkle_all,
    hiding_query_fold_data, hiding_query_input_merkle, hiding_query_quotient_merkle,
    hiding_quotient_recompose_weights,
};
#[cfg(feature = "stream")]
use crate::stream_prove::{LeafSource, MmapLdeStore};
use p3_air::Air;
use p3_commit::{Mmcs, Pcs};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField64};
use p3_matrix::dense::RowMajorMatrix;
use p3_uni_stark::{
    get_log_num_quotient_chunks, get_symbolic_constraints, prove, validate_degree_bits, verify,
    AirLayout, Proof, StarkGenericConfig,
};
#[cfg(feature = "stream")]
use rand::RngExt;

const RATE: usize = 4;
const CAP_LANE: usize = RATE;
const DEFAULT_MAX_TRACE_FELTS: usize = 128 * 1024 * 1024;
const MAX_TRACE_FELTS_ENV: &str = "LATTICA_RECURSION_AGG_MAX_TRACE_FELTS";

#[derive(Clone, Copy, Debug)]
pub enum AggregationBackend {
    InMemory,
    Stream { c_block: usize },
}

#[derive(Clone, Copy, Debug)]
pub struct ResearchAggregationOptions {
    pub inner_max_log_arity: usize,
    pub inner_num_queries: usize,
    pub inner_cap_height: usize,
    pub backend: AggregationBackend,
}

#[derive(Clone, Copy, Debug)]
pub struct ProductionAggregationOptions {
    pub backend: AggregationBackend,
    pub inner_profile: ProductionInnerFriProfile,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProductionInnerFriProfile {
    /// Current node proof profile: q96/lb4/cap6, max FRI log-arity 4.
    NodeProduction,
    /// Recursion-compatible profile: q96/lb4/cap6, binary FRI commit rounds.
    BinaryRecursion,
}

impl Default for ProductionAggregationOptions {
    fn default() -> Self {
        Self {
            backend: default_backend(),
            inner_profile: ProductionInnerFriProfile::NodeProduction,
        }
    }
}

impl ProductionAggregationOptions {
    pub fn binary_recursion() -> Self {
        Self {
            inner_profile: ProductionInnerFriProfile::BinaryRecursion,
            ..Self::default()
        }
    }
}

impl Default for ResearchAggregationOptions {
    fn default() -> Self {
        Self {
            inner_max_log_arity: 1,
            inner_num_queries: 8,
            inner_cap_height: 2,
            backend: default_backend(),
        }
    }
}

#[cfg(feature = "stream")]
fn default_backend() -> AggregationBackend {
    AggregationBackend::Stream { c_block: 4 }
}

#[cfg(not(feature = "stream"))]
fn default_backend() -> AggregationBackend {
    AggregationBackend::InMemory
}

#[derive(Clone, Copy)]
pub struct JoinSplitAggregateInput<'a> {
    pub proof_bytes: &'a [u8],
    pub public_values: &'a [Val],
}

#[derive(Debug)]
pub struct JoinSplitAggregateProof {
    pub proof_bytes: Vec<u8>,
    pub tx_root: [Val; 4],
    pub n_inputs: usize,
    pub width: usize,
    pub log_rows: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProductionAggregateAdmission {
    pub tx_root: [Val; 4],
    pub n_inputs: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TraceResourceEstimate {
    pub height: usize,
    pub width: usize,
    pub required_felts: usize,
    pub limit_felts: usize,
    pub within_limit: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProductionAggregateStreamSpillEstimate {
    pub trace_bytes: usize,
    pub randomized_trace_bytes: usize,
    pub committed_trace_lde_bytes: usize,
    pub trace_commit_peak_bytes: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProductionAggregateResourcePlan {
    pub n_inputs: usize,
    pub inner_trace: TraceResourceEstimate,
    pub inner_query_segment: TraceResourceEstimate,
    pub aggregate_trace: TraceResourceEstimate,
    pub aggregate_query_segment: TraceResourceEstimate,
}

impl ProductionAggregateResourcePlan {
    pub fn check_limits(&self) -> Result<(), AggregationError> {
        self.check_limits_for_backend(AggregationBackend::InMemory)
    }

    pub fn check_limits_for_backend(
        &self,
        backend: AggregationBackend,
    ) -> Result<(), AggregationError> {
        let (inner, what) = match backend {
            AggregationBackend::InMemory => (self.inner_trace, "hiding inner monolith trace"),
            AggregationBackend::Stream { .. } => (
                self.inner_query_segment,
                "hiding inner monolith query segment",
            ),
        };
        if !inner.within_limit {
            return Err(AggregationError::ResourceLimit {
                what,
                required_felts: inner.required_felts,
                limit_felts: inner.limit_felts,
            });
        }
        let (aggregate, aggregate_what) = match backend {
            AggregationBackend::InMemory => {
                (self.aggregate_trace, "production aggregate folded trace")
            }
            AggregationBackend::Stream { .. } => (
                self.aggregate_query_segment,
                "production aggregate query segment",
            ),
        };
        if !aggregate.within_limit {
            return Err(AggregationError::ResourceLimit {
                what: aggregate_what,
                required_felts: aggregate.required_felts,
                limit_felts: aggregate.limit_felts,
            });
        }
        if matches!(backend, AggregationBackend::Stream { .. }) {
            if let Some(limit_bytes) = stream_spill_available_bytes() {
                let required_bytes = self.aggregate_stream_spill_required_bytes()?;
                if required_bytes > limit_bytes {
                    return Err(AggregationError::ResourceLimit {
                        what: "production aggregate stream spill bytes",
                        required_felts: required_bytes,
                        limit_felts: limit_bytes,
                    });
                }
            }
        }
        Ok(())
    }

    pub fn stream_spill_estimate(
        &self,
    ) -> Result<ProductionAggregateStreamSpillEstimate, AggregationError> {
        let h = self.aggregate_trace.height;
        let w = self.aggregate_trace.width;
        let randomized_w = w
            .checked_add(crate::config::NUM_RANDOM_CODEWORDS)
            .ok_or_else(|| {
                AggregationError::TraceLayout(
                    "production aggregate stream randomized width overflows usize".into(),
                )
            })?;
        let trace_felts = h.checked_mul(w).ok_or_else(|| {
            AggregationError::TraceLayout("production aggregate trace store overflows usize".into())
        })?;
        let randomized_h = h.checked_mul(2).ok_or_else(|| {
            AggregationError::TraceLayout(
                "production aggregate randomized height overflows usize".into(),
            )
        })?;
        let randomized_felts = randomized_h.checked_mul(randomized_w).ok_or_else(|| {
            AggregationError::TraceLayout(
                "production aggregate randomized store overflows usize".into(),
            )
        })?;
        let lde_h = randomized_h
            .checked_shl(crate::config::LOG_BLOWUP as u32)
            .ok_or_else(|| {
                AggregationError::TraceLayout(
                    "production aggregate LDE height overflows usize".into(),
                )
            })?;
        let lde_felts = lde_h.checked_mul(randomized_w).ok_or_else(|| {
            AggregationError::TraceLayout("production aggregate LDE store overflows usize".into())
        })?;
        let trace_bytes = felts_to_spill_bytes(
            trace_felts,
            "production aggregate trace store byte estimate overflows usize",
        )?;
        let randomized_trace_bytes = felts_to_spill_bytes(
            randomized_felts,
            "production aggregate randomized store byte estimate overflows usize",
        )?;
        let committed_trace_lde_bytes = felts_to_spill_bytes(
            lde_felts,
            "production aggregate LDE store byte estimate overflows usize",
        )?;
        let randomization_peak_bytes =
            trace_bytes
                .checked_add(randomized_trace_bytes)
                .ok_or_else(|| {
                    AggregationError::TraceLayout(
                    "production aggregate stream randomization peak byte estimate overflows usize"
                        .into(),
                )
                })?;
        let committed_lde_peak_bytes = randomized_trace_bytes
            .checked_add(committed_trace_lde_bytes)
            .ok_or_else(|| {
                AggregationError::TraceLayout(
                    "production aggregate stream spill byte estimate overflows usize".into(),
                )
            })?;
        let trace_commit_peak_bytes = randomization_peak_bytes.max(committed_lde_peak_bytes);
        Ok(ProductionAggregateStreamSpillEstimate {
            trace_bytes,
            randomized_trace_bytes,
            committed_trace_lde_bytes,
            trace_commit_peak_bytes,
        })
    }

    fn aggregate_stream_spill_required_bytes(&self) -> Result<usize, AggregationError> {
        Ok(self.stream_spill_estimate()?.trace_commit_peak_bytes)
    }
}

fn felts_to_spill_bytes(
    felts: usize,
    overflow_message: &'static str,
) -> Result<usize, AggregationError> {
    felts
        .checked_mul(core::mem::size_of::<Val>())
        .ok_or_else(|| AggregationError::TraceLayout(overflow_message.into()))
}

#[cfg(all(unix, feature = "stream"))]
fn stream_spill_available_bytes() -> Option<usize> {
    let dir = std::env::var("LATTICA_SPILL_DIR")
        .ok()
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| std::env::temp_dir().to_string_lossy().into_owned());
    let c_dir = std::ffi::CString::new(dir).ok()?;
    let mut stat = core::mem::MaybeUninit::<libc::statvfs>::uninit();
    let rc = unsafe { libc::statvfs(c_dir.as_ptr(), stat.as_mut_ptr()) };
    if rc != 0 {
        return None;
    }
    let stat = unsafe { stat.assume_init() };
    let bytes = (stat.f_bavail as u128).checked_mul(stat.f_frsize as u128)?;
    usize::try_from(bytes).ok()
}

#[cfg(not(all(unix, feature = "stream")))]
fn stream_spill_available_bytes() -> Option<usize> {
    None
}

#[derive(Debug)]
pub enum AggregationError {
    Empty,
    InvalidFanIn {
        n: usize,
    },
    TooManyInputs {
        n: usize,
    },
    WrongPublicValueCount {
        got: usize,
    },
    MalformedInnerProof,
    InnerQueryCount {
        expected: usize,
        got: usize,
    },
    InnerCapHeight {
        expected: usize,
        got: usize,
    },
    NonHidingInnerProof,
    InvalidDummyPadding,
    UnsupportedFriArity {
        log_arity: usize,
    },
    InnerProofRejected,
    MismatchedInnerShape,
    ResourceLimit {
        what: &'static str,
        required_felts: usize,
        limit_felts: usize,
    },
    TraceLayout(String),
    BackendUnavailable(&'static str),
    ProverIo(std::io::Error),
    MalformedAggregateProof,
}

impl From<std::io::Error> for AggregationError {
    fn from(value: std::io::Error) -> Self {
        Self::ProverIo(value)
    }
}

struct ParsedInput<'a> {
    proof: Proof<MyConfig>,
    public_values: &'a [Val],
}

struct ParsedProductionInput<'a> {
    proof: Proof<crate::config::MyConfig>,
    public_values: &'a [Val],
}

struct PlannedProductionInnerShape {
    counts: Vec<u8>,
    binds: Vec<usize>,
    index_binds: Vec<(usize, usize)>,
    n_terms: usize,
    cap_height: usize,
    trace: TraceResourceEstimate,
    query_segment: TraceResourceEstimate,
}

struct AggregateInstance {
    air: MonolithAir,
    trace: RowMajorMatrix<Val>,
    tx_root: [Val; 4],
}

#[cfg(feature = "stream")]
struct AggregateStoreInstance {
    air: MonolithAir,
    trace: MmapLdeStore,
    tx_root: [Val; 4],
}

fn aggregation_progress(args: core::fmt::Arguments<'_>) {
    if std::env::var_os("LATTICA_RECURSION_AGG_PROGRESS").is_some() {
        eprintln!("{args}");
    }
}

fn max_trace_felts() -> usize {
    std::env::var(MAX_TRACE_FELTS_ENV)
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(DEFAULT_MAX_TRACE_FELTS)
}

fn checked_trace_felts(
    what: &'static str,
    height: usize,
    width: usize,
) -> Result<usize, AggregationError> {
    checked_trace_felts_with_limit(what, height, width, max_trace_felts())
}

fn checked_trace_felts_with_limit(
    what: &'static str,
    height: usize,
    width: usize,
    limit_felts: usize,
) -> Result<usize, AggregationError> {
    let estimate = trace_resource_estimate_with_limit(what, height, width, limit_felts)?;
    if !estimate.within_limit {
        return Err(AggregationError::ResourceLimit {
            what,
            required_felts: estimate.required_felts,
            limit_felts: estimate.limit_felts,
        });
    }
    Ok(estimate.required_felts)
}

fn trace_resource_estimate(
    what: &'static str,
    height: usize,
    width: usize,
) -> Result<TraceResourceEstimate, AggregationError> {
    trace_resource_estimate_with_limit(what, height, width, max_trace_felts())
}

fn trace_resource_estimate_with_limit(
    what: &'static str,
    height: usize,
    width: usize,
    limit_felts: usize,
) -> Result<TraceResourceEstimate, AggregationError> {
    let required_felts = height
        .checked_mul(width)
        .ok_or_else(|| AggregationError::TraceLayout(format!("{what} size overflows usize")))?;
    Ok(TraceResourceEstimate {
        height,
        width,
        required_felts,
        limit_felts,
        within_limit: required_felts <= limit_felts,
    })
}

fn validate_production_outer_shape(instance: &AggregateInstance) -> Result<(), AggregationError> {
    let height = instance.trace.values.len() / instance.trace.width;
    validate_production_outer_dimensions(&instance.air, height)
}

fn validate_production_outer_dimensions(
    air: &MonolithAir,
    height: usize,
) -> Result<(), AggregationError> {
    if !height.is_power_of_two() {
        return Err(AggregationError::TraceLayout(
            "aggregate trace height is not a power of two".into(),
        ));
    }

    let verifier_config = crate::config::make_config();
    let layout = AirLayout::from_air::<Val>(air);
    let log_num_quotient_chunks =
        get_log_num_quotient_chunks::<Val, _>(air, layout, verifier_config.is_zk());
    if log_num_quotient_chunks > crate::config::LOG_BLOWUP {
        return Err(AggregationError::TraceLayout(format!(
            "aggregate quotient chunks exceed production blowup: log_nqc={log_num_quotient_chunks}, log_blowup={}",
            crate::config::LOG_BLOWUP
        )));
    }

    let log_rows = height.trailing_zeros() as usize;
    let degree_bits = log_rows + log_num_quotient_chunks;
    validate_degree_bits(
        None,
        degree_bits,
        verifier_config.is_zk(),
        <crate::config::MyPcs as Pcs<Challenge, crate::config::Challenger>>::log_max_lde_height(
            verifier_config.pcs(),
        ),
    )
    .map_err(|err| {
        AggregationError::TraceLayout(format!(
            "aggregate degree bits invalid for production verifier: {err:?}"
        ))
    })?;

    Ok(())
}

fn validate_production_joinsplit_shape(
    config: &crate::config::MyConfig,
    proof_degree_bits: usize,
) -> Result<(), AggregationError> {
    let layout = AirLayout::from_air::<Val>(&JoinSplitAir);
    let log_num_quotient_chunks =
        get_log_num_quotient_chunks::<Val, _>(&JoinSplitAir, layout, config.is_zk());
    if log_num_quotient_chunks > crate::config::LOG_BLOWUP {
        return Err(AggregationError::TraceLayout(format!(
            "JoinSplit quotient chunks exceed production blowup: log_nqc={log_num_quotient_chunks}, log_blowup={}",
            crate::config::LOG_BLOWUP
        )));
    }

    validate_degree_bits(
        None,
        proof_degree_bits,
        config.is_zk(),
        <crate::config::MyPcs as Pcs<Challenge, crate::config::Challenger>>::log_max_lde_height(
            config.pcs(),
        ),
    )
    .map_err(|err| {
        AggregationError::TraceLayout(format!(
            "JoinSplit degree bits invalid for production verifier: {err:?}"
        ))
    })?;

    Ok(())
}

struct Sim {
    state: [Val; W],
    input: Vec<Val>,
    output: Vec<Val>,
    block_inputs: Vec<[Val; W]>,
    counts: Vec<u8>,
}

impl Sim {
    fn new() -> Self {
        Self {
            state: [Val::ZERO; W],
            input: Vec::new(),
            output: Vec::new(),
            block_inputs: Vec::new(),
            counts: Vec::new(),
        }
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
        for &c in x.as_basis_coefficients_slice() {
            self.observe(c);
        }
    }

    fn sample_base(&mut self) -> (Val, usize, usize) {
        if !self.input.is_empty() || self.output.is_empty() {
            self.duplex();
        }
        let block = self.block_inputs.len() - 1;
        let lane = self.output.len() - 1;
        (self.output.pop().expect("duplex output"), block, lane)
    }

    fn sample_ext(&mut self) -> ([Val; 2], usize) {
        let (c0, block, _) = self.sample_base();
        let (c1, _, _) = self.sample_base();
        ([c0, c1], block)
    }
}

#[allow(clippy::type_complexity)]
fn sim_full(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
) -> (
    Vec<[Val; W]>,
    Vec<u8>,
    Vec<usize>,
    Vec<[Val; 2]>,
    Vec<(usize, usize)>,
    Vec<Val>,
) {
    let (instance, commitment, _, _) = preamble_challenges(config, proof, pvs);
    let mut sim = Sim::new();
    for &f in &instance {
        sim.observe(f);
    }
    let (alpha_stark, b0) = sim.sample_ext();
    for &f in &commitment {
        sim.observe(f);
    }
    let (zeta, b1) = sim.sample_ext();
    for &x in &proof.opened_values.trace_local {
        sim.observe_ext(x);
    }
    if let Some(trace_next) = &proof.opened_values.trace_next {
        for &x in trace_next {
            sim.observe_ext(x);
        }
    }
    for chunk in &proof.opened_values.quotient_chunks {
        for &x in chunk {
            sim.observe_ext(x);
        }
    }
    let (alpha_fri, b2) = sim.sample_ext();
    let mut binds = vec![b0, b1, b2];
    let mut challenges = vec![alpha_stark, zeta, alpha_fri];
    let fri = &proof.opening_proof;
    for commitment in &fri.commit_phase_commits {
        for f in cap_felts(commitment) {
            sim.observe(f);
        }
        let (beta, block) = sim.sample_ext();
        binds.push(block);
        challenges.push(beta);
    }
    for &x in &fri.final_poly {
        sim.observe_ext(x);
    }
    let log_arities: Vec<usize> = fri.query_proofs[0]
        .commit_phase_openings
        .iter()
        .map(|opening| opening.log_arity as usize)
        .collect();
    for &log_arity in &log_arities {
        sim.observe(Val::from_usize(log_arity));
    }
    sim.observe(fri.query_pow_witness);
    let _ = sim.sample_base();

    let mut index_binds = Vec::new();
    let mut index_felts = Vec::new();
    for _ in 0..fri.query_proofs.len() {
        let (felt, block, lane) = sim.sample_base();
        index_binds.push((block, lane));
        index_felts.push(felt);
    }

    (
        sim.block_inputs,
        sim.counts,
        binds,
        challenges,
        index_binds,
        index_felts,
    )
}

struct SymbolicHidingInnerWindow {
    air: MonolithAir,
    block_inputs: Vec<[Val; W]>,
    per_query: Vec<MonolithQuery>,
    alpha_fri: [Val; 2],
    index_felts: Vec<Val>,
    quotient_paths: Vec<Vec<([Val; 4], bool)>>,
    commit_data: Vec<Vec<CommitRoundData>>,
    pub_window: Vec<Val>,
    hiding_witnesses: Vec<HidingWitness>,
    selector_window: Vec<Val>,
    counts: Vec<u8>,
    binds: Vec<usize>,
    index_binds: Vec<(usize, usize)>,
    n_terms: usize,
}

impl SymbolicHidingInnerWindow {
    fn source(&self) -> MonolithTraceSource<'_> {
        MonolithTraceSource::new(
            &self.air,
            &self.block_inputs,
            &self.per_query,
            self.alpha_fri,
            &self.index_felts,
            &self.quotient_paths,
            &self.commit_data,
            &self.pub_window,
            Some(&self.hiding_witnesses),
        )
    }

    fn emit_range_with_selector(&self, range: MonolithTraceRowRange, out: &mut [Val]) {
        self.source().emit_range(range, out);
        self.apply_selector_window(range.width, out);
    }

    fn apply_selector_window(&self, width: usize, rows: &mut [Val]) {
        let selector_base = self.air.sel_base();
        let selector_end = selector_base + self.selector_window.len();
        for row in rows.chunks_exact_mut(width) {
            row[selector_base..selector_end].copy_from_slice(&self.selector_window);
        }
    }

    #[cfg(feature = "stream")]
    fn fill_padding_rows_with_selector(&self, width: usize, rows: &mut [Val]) {
        rows.fill(Val::ZERO);
        self.apply_global_columns(width, rows);
        self.apply_selector_window(width, rows);
    }

    #[cfg(feature = "stream")]
    fn apply_global_columns(&self, width: usize, rows: &mut [Val]) {
        debug_assert_eq!(width, self.air.fused_w());
        debug_assert_eq!(rows.len() % width, 0);
        let window = if self.air.column_window {
            let cc =
                |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
            let zeta = Challenge::from_basis_coefficients_fn(|k| self.pub_window[2 + k]);
            let mut schedule = Vec::with_capacity(self.pub_window.len() + 2 * self.air.cm_rounds());
            schedule.extend_from_slice(&self.pub_window);
            let mut s = zeta;
            for _ in 0..self.air.cm_rounds() {
                s *= s;
                schedule.extend_from_slice(&cc(s));
            }
            Some(schedule)
        } else {
            None
        };
        for row in rows.chunks_exact_mut(width) {
            row[self.air.carry()] = self.alpha_fri[0];
            row[self.air.carry() + 1] = self.alpha_fri[1];
            if let Some(window) = &window {
                let start = self.air.pw(0);
                row[start..start + window.len()].copy_from_slice(window);
            }
        }
    }

    #[allow(dead_code)]
    fn materialize_trace_values(&self) -> Result<Vec<Val>, AggregationError> {
        let trace_felts = checked_trace_felts(
            "hiding inner monolith trace",
            self.air.height(),
            self.air.fused_w(),
        )?;
        let mut values = vec![Val::ZERO; trace_felts];
        for range in self.source().ranges() {
            let mut emitted = vec![Val::ZERO; range.felt_len()];
            self.emit_range_with_selector(range, &mut emitted);
            for row in 0..range.rows {
                let dst = (range.start_row + row) * range.width;
                let src = row * range.width;
                values[dst..dst + range.width].copy_from_slice(&emitted[src..src + range.width]);
            }
        }
        Ok(values)
    }
}

#[allow(clippy::too_many_arguments)]
fn build_symbolic_inner_window<A>(
    config: &MyConfig,
    inner: &A,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
    w_inner: usize,
    n_pub: usize,
    n_periodic: usize,
) -> (Vec<Val>, Vec<u8>, Vec<usize>, Vec<(usize, usize)>, usize)
where
    A: Air<p3_uni_stark::SymbolicAirBuilder<Val>>,
{
    let n_queries = proof.opening_proof.query_proofs.len();
    let (block_inputs, counts, binds, challenges, index_binds, index_felts) =
        sim_full(config, proof, pvs);
    let log_global = proof.opening_proof.query_proofs[0]
        .commit_phase_openings
        .len()
        + 4;
    let mut per_query = Vec::new();
    let mut quotient_paths = Vec::new();
    let mut commit_data = Vec::new();
    let mut n_terms = 0;
    let mut final0 = Challenge::ZERO;

    for q in 0..n_queries {
        let (terms, _x, alpha, ro, _width) = multicol_query_terms(config, inner, proof, pvs, q);
        let (_ro2, rounds, _folded, f0) = query_fold_data(config, proof, pvs, q);
        let (_leaf, path, _cap_entry) = query_input_merkle(config, proof, pvs, q);
        let (_quot_leaf, quotient_path, _quot_cap_entry, _quot_width) =
            query_quotient_merkle(config, proof, pvs, q);
        let commit_merkle = query_commit_merkle_all(config, proof, pvs, q);
        if q == 0 {
            final0 = f0;
        }
        n_terms = terms.len();
        let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        per_query.push(((index, terms, alpha, ro, rounds), Val::ZERO, path));
        quotient_paths.push(quotient_path);
        commit_data.push(commit_merkle);
    }

    let constraints = get_symbolic_constraints::<Val, A>(inner, AirLayout::from_air::<Val>(inner));
    let cap_height = proof.commitments.trace.roots().len().trailing_zeros() as usize;
    let air = MonolithAir {
        counts: counts.clone(),
        binds: binds.clone(),
        index_binds: index_binds.clone(),
        n_queries,
        n_terms,
        inner_counter: false,
        column_window: true,
        k_instances: 1,
        fold: false,
        fold_txstmt: false,
        constraints,
        w_inner_f: w_inner,
        n_pub_f: n_pub,
        n_periodic_f: n_periodic,
        is_zk: 0,
        cap_height,
    };

    let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
    let (
        eo_local,
        eo_next,
        is_first,
        is_last,
        is_transition,
        inv_van,
        eo_quot,
        eo_alpha,
        _zeta,
        eo_periodic,
    ) = epilogue_openings(config, inner, proof, pvs);

    let mut pis = Vec::new();
    for challenge in &challenges {
        pis.push(challenge[0]);
        pis.push(challenge[1]);
    }
    for felt in &index_felts {
        pis.push(*felt);
    }
    let final0 = cc(final0);
    pis.push(final0[0]);
    pis.push(final0[1]);
    for felt in cap_felts(&proof.commitments.trace) {
        pis.push(felt);
    }
    for felt in cap_felts(&proof.commitments.quotient_chunks) {
        pis.push(felt);
    }
    pis.extend_from_slice(pvs);
    for commitment in &proof.opening_proof.commit_phase_commits {
        for felt in cap_felts(commitment) {
            pis.push(felt);
        }
    }
    for value in &eo_periodic {
        let value = cc(*value);
        pis.push(value[0]);
        pis.push(value[1]);
    }
    if air.nqc() > 1 {
        for weight in quotient_recompose_weights(config, inner, proof, pvs) {
            let weight = cc(weight);
            pis.push(weight[0]);
            pis.push(weight[1]);
        }
    }

    assert_eq!(
        pis.len(),
        air.pis_count(),
        "symbolic column-window public-input layout"
    );

    let mut trace = monolith_build_trace(
        &air,
        &block_inputs,
        &per_query,
        challenges[2],
        &index_felts,
        &quotient_paths,
        &commit_data,
        &pis,
        None,
    );

    let (is_first_f, is_last_f, inv_van_f) = (cc(is_first), cc(is_last), cc(inv_van));
    let width = air.fused_w();
    let selector_base = air.sel_base();
    let mut selector_window = Vec::with_capacity(6 + 2 * air.n_fold_acc());
    selector_window.extend_from_slice(&is_first_f);
    selector_window.extend_from_slice(&is_last_f);
    selector_window.extend_from_slice(&inv_van_f);

    if air.n_fold_acc() > 0 {
        let publics: Vec<Challenge> = pvs.iter().map(|&p| Challenge::from(p)).collect();
        let mut folded = Challenge::ZERO;
        let n_constraints = air.constraints.len();
        for (k, constraint) in air.constraints.iter().enumerate() {
            folded = folded * eo_alpha
                + eval_symbolic_native(
                    constraint,
                    &eo_local,
                    &eo_next,
                    &publics,
                    &eo_periodic,
                    is_first,
                    is_last,
                    is_transition,
                );
            if (k + 1) % MonolithAir::FOLD_CHUNK == 0 && k + 1 < n_constraints {
                let value = cc(folded);
                selector_window.extend_from_slice(&value);
            }
        }
        debug_assert_eq!(folded * inv_van, eo_quot);
    }

    for row in trace.values.chunks_exact_mut(width) {
        row[selector_base..selector_base + selector_window.len()].copy_from_slice(&selector_window);
    }
    (trace.values, counts, binds, index_binds, n_terms)
}

fn cap_felts_hiding(commit: &<crate::config::ValMmcs as Mmcs<Val>>::Commitment) -> Vec<Val> {
    commit.roots().iter().flatten().copied().collect()
}

#[allow(clippy::type_complexity)]
fn sim_full_hiding(
    config: &crate::config::MyConfig,
    proof: &Proof<crate::config::MyConfig>,
    pvs: &[Val],
) -> (
    Vec<[Val; W]>,
    Vec<u8>,
    Vec<usize>,
    Vec<[Val; 2]>,
    Vec<(usize, usize)>,
    Vec<Val>,
) {
    let pcs = config.pcs();
    let is_zk = config.is_zk();
    let degree_bits = proof.degree_bits;
    let (base_degree_bits, _) = validate_degree_bits(
        None,
        degree_bits,
        is_zk,
        <crate::config::MyPcs as Pcs<Challenge, crate::config::Challenger>>::log_max_lde_height(
            pcs,
        ),
    )
    .expect("degree bits");

    let mut sim = Sim::new();
    sim.observe(Val::from_usize(degree_bits));
    sim.observe(Val::from_usize(base_degree_bits));
    sim.observe(Val::from_usize(0));
    for felt in cap_felts_hiding(&proof.commitments.trace) {
        sim.observe(felt);
    }
    for &p in pvs {
        sim.observe(p);
    }
    let (alpha_stark, b0) = sim.sample_ext();
    for felt in cap_felts_hiding(&proof.commitments.quotient_chunks) {
        sim.observe(felt);
    }
    if let Some(random) = &proof.commitments.random {
        for felt in cap_felts_hiding(random) {
            sim.observe(felt);
        }
    }
    let (zeta, b1) = sim.sample_ext();

    let random_codewords = &proof.opening_proof.0;
    let mut round = 0usize;
    let observe_merged = |sim: &mut Sim, public: &[Challenge], codewords: &[Challenge]| {
        for &x in public {
            sim.observe_ext(x);
        }
        for &x in codewords {
            sim.observe_ext(x);
        }
    };
    if let Some(random_values) = &proof.opened_values.random {
        observe_merged(&mut sim, random_values, &random_codewords[round][0][0]);
        round += 1;
    }
    observe_merged(
        &mut sim,
        &proof.opened_values.trace_local,
        &random_codewords[round][0][0],
    );
    if let Some(trace_next) = &proof.opened_values.trace_next {
        observe_merged(&mut sim, trace_next, &random_codewords[round][0][1]);
    }
    round += 1;
    for (i, chunk) in proof.opened_values.quotient_chunks.iter().enumerate() {
        observe_merged(&mut sim, chunk, &random_codewords[round][i][0]);
    }
    let (alpha_fri, b2) = sim.sample_ext();
    let mut binds = vec![b0, b1, b2];
    let mut challenges = vec![alpha_stark, zeta, alpha_fri];

    let fri = &proof.opening_proof.1;
    for commitment in &fri.commit_phase_commits {
        for felt in cap_felts_hiding(commitment) {
            sim.observe(felt);
        }
        let (beta, block) = sim.sample_ext();
        binds.push(block);
        challenges.push(beta);
    }
    for &x in &fri.final_poly {
        sim.observe_ext(x);
    }
    let log_arities: Vec<usize> = fri.query_proofs[0]
        .commit_phase_openings
        .iter()
        .map(|opening| opening.log_arity as usize)
        .collect();
    for &log_arity in &log_arities {
        sim.observe(Val::from_usize(log_arity));
    }
    sim.observe(fri.query_pow_witness);
    let _ = sim.sample_base();

    let mut index_binds = Vec::new();
    let mut index_felts = Vec::new();
    for _ in 0..fri.query_proofs.len() {
        let (felt, block, lane) = sim.sample_base();
        index_binds.push((block, lane));
        index_felts.push(felt);
    }

    (
        sim.block_inputs,
        sim.counts,
        binds,
        challenges,
        index_binds,
        index_felts,
    )
}

fn validate_binary_fri_shape(
    proof: &Proof<crate::config::MyConfig>,
) -> Result<(), AggregationError> {
    // The fused MonolithAir query layout has one fold sibling/bit per commit round.
    // General-arity gadgets exist separately, but are not wired into this aggregate AIR.
    let fri = &proof.opening_proof.1;
    for query in &fri.query_proofs {
        for opening in &query.commit_phase_openings {
            let log_arity = opening.log_arity as usize;
            if log_arity != 1 {
                return Err(AggregationError::UnsupportedFriArity { log_arity });
            }
        }
    }
    Ok(())
}

fn salt4(salt: &[Val]) -> Result<[Val; 4], AggregationError> {
    salt.try_into()
        .map_err(|_| AggregationError::TraceLayout("hiding Merkle salt is not four felts".into()))
}

fn hiding_witness_for_query(
    proof: &Proof<crate::config::MyConfig>,
    q: usize,
    index: usize,
) -> Result<HidingWitness, AggregationError> {
    let query = &proof.opening_proof.1.query_proofs[q];
    if query.input_proof.len() < 3 {
        return Err(AggregationError::TraceLayout(
            "hiding proof missing random/trace/quotient input rounds".into(),
        ));
    }
    let random_batch = &query.input_proof[0];
    let trace_batch = &query.input_proof[1];
    let quotient_batch = &query.input_proof[2];
    let random_path = random_batch
        .opening_proof
        .1
        .iter()
        .enumerate()
        .map(|(level, &sibling)| (sibling, (index >> level) & 1 == 1))
        .collect();
    Ok(HidingWitness {
        trace_salt: salt4(&trace_batch.opening_proof.0[0])?,
        random_salt: salt4(&random_batch.opening_proof.0[0])?,
        random_path,
        quot_salts: quotient_batch
            .opening_proof
            .0
            .iter()
            .map(|salt| salt4(salt))
            .collect::<Result<Vec<_>, _>>()?,
        commit_salts: query
            .commit_phase_openings
            .iter()
            .map(|step| salt4(&step.opening_proof.0[0]))
            .collect::<Result<Vec<_>, _>>()?,
    })
}

#[allow(clippy::too_many_arguments)]
fn build_symbolic_hiding_inner_window_source<A>(
    config: &crate::config::MyConfig,
    inner: &A,
    proof: &Proof<crate::config::MyConfig>,
    pvs: &[Val],
    w_inner: usize,
    n_pub: usize,
    n_periodic: usize,
) -> Result<SymbolicHidingInnerWindow, AggregationError>
where
    A: Air<p3_uni_stark::SymbolicAirBuilder<Val>>,
{
    validate_binary_fri_shape(proof)?;
    let started = std::time::Instant::now();
    let n_queries = proof.opening_proof.1.query_proofs.len();
    aggregation_progress(format_args!(
        "hiding inner window: extracting q{n_queries} transcript/opening data"
    ));
    let (block_inputs, counts, binds, challenges, index_binds, index_felts) =
        sim_full_hiding(config, proof, pvs);
    if n_queries > 0 {
        let (terms0, _, _, _) = hiding_multicol_query_terms(config, inner, proof, pvs, 0);
        let constraints =
            get_symbolic_constraints::<Val, A>(inner, AirLayout::from_air::<Val>(inner));
        let cap_height = proof.commitments.trace.roots().len().trailing_zeros() as usize;
        let shape_air = MonolithAir {
            counts: counts.clone(),
            binds: binds.clone(),
            index_binds: index_binds.clone(),
            n_queries,
            n_terms: terms0.len(),
            inner_counter: false,
            column_window: true,
            k_instances: 1,
            fold: false,
            fold_txstmt: false,
            constraints,
            w_inner_f: w_inner,
            n_pub_f: n_pub,
            n_periodic_f: n_periodic,
            is_zk: 1,
            cap_height,
        };
        if shape_air.nqc() > (1 << crate::config::LOG_BLOWUP) {
            return Err(AggregationError::TraceLayout(
                "hiding quotient chunk count exceeds production blowup".into(),
            ));
        }
        checked_trace_felts(
            "hiding inner monolith query segment",
            shape_air.m_period(),
            shape_air.fused_w(),
        )?;
    }
    let mut per_query = Vec::new();
    let mut quotient_paths = Vec::new();
    let mut commit_data = Vec::new();
    let mut hiding_witnesses = Vec::new();
    let mut n_terms = 0;
    let mut final0 = Challenge::ZERO;

    for q in 0..n_queries {
        let (terms, _x, alpha, ro) = hiding_multicol_query_terms(config, inner, proof, pvs, q);
        let (_ro2, rounds, _folded, f0) = hiding_query_fold_data(config, inner, proof, pvs, q);
        let (_leaf, path, _cap_entry) = hiding_query_input_merkle(config, proof, pvs, q);
        let (_quot_leaf, quotient_path, _quot_cap_entry, _quot_width) =
            hiding_query_quotient_merkle(config, proof, pvs, q);
        let commit_merkle = hiding_query_commit_merkle_all(config, inner, proof, pvs, q);
        if q == 0 {
            final0 = f0;
            n_terms = terms.len();
        } else if terms.len() != n_terms {
            return Err(AggregationError::MismatchedInnerShape);
        }
        let log_global: usize = proof.opening_proof.1.query_proofs[q]
            .commit_phase_openings
            .iter()
            .map(|opening| opening.log_arity as usize)
            .sum::<usize>()
            + crate::config::LOG_BLOWUP;
        let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        hiding_witnesses.push(hiding_witness_for_query(proof, q, index)?);
        per_query.push(((index, terms, alpha, ro, rounds), Val::ZERO, path));
        quotient_paths.push(quotient_path);
        commit_data.push(commit_merkle);
    }

    let constraints = get_symbolic_constraints::<Val, A>(inner, AirLayout::from_air::<Val>(inner));
    let cap_height = proof.commitments.trace.roots().len().trailing_zeros() as usize;
    let air = MonolithAir {
        counts: counts.clone(),
        binds: binds.clone(),
        index_binds: index_binds.clone(),
        n_queries,
        n_terms,
        inner_counter: false,
        column_window: true,
        k_instances: 1,
        fold: false,
        fold_txstmt: false,
        constraints,
        w_inner_f: w_inner,
        n_pub_f: n_pub,
        n_periodic_f: n_periodic,
        is_zk: 1,
        cap_height,
    };
    if air.nqc() > (1 << crate::config::LOG_BLOWUP) {
        return Err(AggregationError::TraceLayout(
            "hiding quotient chunk count exceeds production blowup".into(),
        ));
    }

    let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
    let (
        eo_local,
        eo_next,
        is_first,
        is_last,
        is_transition,
        inv_van,
        eo_quot,
        eo_alpha,
        _zeta,
        eo_periodic,
    ) = hiding_epilogue_openings(config, inner, proof, pvs);
    let mut pis = Vec::with_capacity(air.pis_count());
    for challenge in &challenges {
        pis.push(challenge[0]);
        pis.push(challenge[1]);
    }
    for felt in &index_felts {
        pis.push(*felt);
    }
    let final0 = cc(final0);
    pis.push(final0[0]);
    pis.push(final0[1]);
    for felt in cap_felts_hiding(&proof.commitments.trace) {
        pis.push(felt);
    }
    for felt in cap_felts_hiding(&proof.commitments.quotient_chunks) {
        pis.push(felt);
    }
    pis.extend_from_slice(pvs);
    for commitment in &proof.opening_proof.1.commit_phase_commits {
        for felt in cap_felts_hiding(commitment) {
            pis.push(felt);
        }
    }
    for value in &eo_periodic {
        let value = cc(*value);
        pis.push(value[0]);
        pis.push(value[1]);
    }
    if air.nqc() > 1 {
        for weight in hiding_quotient_recompose_weights(config, inner, proof, pvs) {
            let weight = cc(weight);
            pis.push(weight[0]);
            pis.push(weight[1]);
        }
    }
    let random_cap = proof
        .commitments
        .random
        .as_ref()
        .ok_or(AggregationError::NonHidingInnerProof)?;
    for felt in cap_felts_hiding(random_cap) {
        pis.push(felt);
    }
    if pis.len() != air.pis_count() {
        return Err(AggregationError::TraceLayout(
            "hiding column-window public-input layout mismatch".into(),
        ));
    }

    aggregation_progress(format_args!(
        "hiding inner window: prepared source h={} w={} tr={} m_period={} n_terms={} nqc={} pis={} elapsed={:?}",
        air.height(),
        air.fused_w(),
        air.tr(),
        air.m_period(),
        n_terms,
        air.nqc(),
        pis.len(),
        started.elapsed()
    ));

    let (is_first_f, is_last_f, inv_van_f) = (cc(is_first), cc(is_last), cc(inv_van));
    let mut selector_window = Vec::with_capacity(6 + 2 * air.n_fold_acc());
    selector_window.extend_from_slice(&is_first_f);
    selector_window.extend_from_slice(&is_last_f);
    selector_window.extend_from_slice(&inv_van_f);

    if air.n_fold_acc() > 0 {
        let publics: Vec<Challenge> = pvs.iter().map(|&p| Challenge::from(p)).collect();
        let mut folded = Challenge::ZERO;
        let n_constraints = air.constraints.len();
        for (k, constraint) in air.constraints.iter().enumerate() {
            folded = folded * eo_alpha
                + eval_symbolic_native(
                    constraint,
                    &eo_local,
                    &eo_next,
                    &publics,
                    &eo_periodic,
                    is_first,
                    is_last,
                    is_transition,
                );
            if (k + 1) % MonolithAir::FOLD_CHUNK == 0 && k + 1 < n_constraints {
                let value = cc(folded);
                selector_window.extend_from_slice(&value);
            }
        }
        debug_assert_eq!(folded * inv_van, eo_quot);
    }

    aggregation_progress(format_args!(
        "hiding inner window: done source_rows={} elapsed={:?}",
        air.height(),
        started.elapsed()
    ));
    Ok(SymbolicHidingInnerWindow {
        air,
        block_inputs,
        per_query,
        alpha_fri: challenges[2],
        index_felts,
        quotient_paths,
        commit_data,
        pub_window: pis,
        hiding_witnesses,
        selector_window,
        counts,
        binds,
        index_binds,
        n_terms,
    })
}

#[allow(clippy::too_many_arguments, dead_code)]
fn build_symbolic_hiding_inner_window<A>(
    config: &crate::config::MyConfig,
    inner: &A,
    proof: &Proof<crate::config::MyConfig>,
    pvs: &[Val],
    w_inner: usize,
    n_pub: usize,
    n_periodic: usize,
) -> Result<(Vec<Val>, Vec<u8>, Vec<usize>, Vec<(usize, usize)>, usize), AggregationError>
where
    A: Air<p3_uni_stark::SymbolicAirBuilder<Val>>,
{
    let window = build_symbolic_hiding_inner_window_source(
        config, inner, proof, pvs, w_inner, n_pub, n_periodic,
    )?;
    let trace = window.materialize_trace_values()?;
    Ok((
        trace,
        window.counts,
        window.binds,
        window.index_binds,
        window.n_terms,
    ))
}

fn parse_and_verify_inputs<'a>(
    inputs: &'a [JoinSplitAggregateInput<'a>],
    options: ResearchAggregationOptions,
) -> Result<(MyConfig, Vec<ParsedInput<'a>>), AggregationError> {
    if inputs.is_empty() {
        return Err(AggregationError::Empty);
    }
    if !inputs.len().is_power_of_two() {
        return Err(AggregationError::InvalidFanIn { n: inputs.len() });
    }
    if inputs.len() > MAX_AGG_TILES {
        return Err(AggregationError::TooManyInputs { n: inputs.len() });
    }

    let config = make_config_cap(
        options.inner_max_log_arity,
        options.inner_num_queries,
        options.inner_cap_height,
    );
    let mut parsed = Vec::with_capacity(inputs.len());
    for input in inputs {
        if input.public_values.len() != N_PUBLIC {
            return Err(AggregationError::WrongPublicValueCount {
                got: input.public_values.len(),
            });
        }
        let proof: Proof<MyConfig> = postcard::from_bytes(input.proof_bytes)
            .map_err(|_| AggregationError::MalformedInnerProof)?;
        let got_queries = proof.opening_proof.query_proofs.len();
        if got_queries != options.inner_num_queries {
            return Err(AggregationError::InnerQueryCount {
                expected: options.inner_num_queries,
                got: got_queries,
            });
        }
        let got_cap = proof.commitments.trace.roots().len().trailing_zeros() as usize;
        if got_cap != options.inner_cap_height {
            return Err(AggregationError::InnerCapHeight {
                expected: options.inner_cap_height,
                got: got_cap,
            });
        }
        verify(&config, &JoinSplitAir, &proof, input.public_values)
            .map_err(|_| AggregationError::InnerProofRejected)?;
        parsed.push(ParsedInput {
            proof,
            public_values: input.public_values,
        });
    }
    Ok((config, parsed))
}

fn production_config_for_profile(profile: ProductionInnerFriProfile) -> crate::config::MyConfig {
    match profile {
        ProductionInnerFriProfile::NodeProduction => crate::config::make_config(),
        ProductionInnerFriProfile::BinaryRecursion => crate::config::make_recursion_binary_config(),
    }
}

fn parse_production_input_for_plan<'a>(
    input: &'a JoinSplitAggregateInput<'a>,
    config: &crate::config::MyConfig,
) -> Result<ParsedProductionInput<'a>, AggregationError> {
    if input.public_values.len() != N_PUBLIC {
        return Err(AggregationError::WrongPublicValueCount {
            got: input.public_values.len(),
        });
    }
    let proof: Proof<crate::config::MyConfig> = postcard::from_bytes(input.proof_bytes)
        .map_err(|_| AggregationError::MalformedInnerProof)?;
    let query_count = proof.opening_proof.1.query_proofs.len();
    if query_count != crate::config::NUM_QUERIES {
        return Err(AggregationError::InnerQueryCount {
            expected: crate::config::NUM_QUERIES,
            got: query_count,
        });
    }
    let cap_height = proof.commitments.trace.roots().len().trailing_zeros() as usize;
    if cap_height != crate::config::CAP_HEIGHT {
        return Err(AggregationError::InnerCapHeight {
            expected: crate::config::CAP_HEIGHT,
            got: cap_height,
        });
    }
    if proof.commitments.random.is_none() || proof.opened_values.random.is_none() {
        return Err(AggregationError::NonHidingInnerProof);
    }
    validate_binary_fri_shape(&proof)?;
    validate_production_joinsplit_shape(config, proof.degree_bits)?;
    Ok(ParsedProductionInput {
        proof,
        public_values: input.public_values,
    })
}

fn verify_production_input<'a>(
    input: &'a JoinSplitAggregateInput<'a>,
    config: &crate::config::MyConfig,
) -> Result<ParsedProductionInput<'a>, AggregationError> {
    let parsed = parse_production_input_for_plan(input, config)?;
    verify(config, &JoinSplitAir, &parsed.proof, parsed.public_values)
        .map_err(|_| AggregationError::InnerProofRejected)?;
    Ok(parsed)
}

fn parse_production_inputs<'a>(
    inputs: &'a [JoinSplitAggregateInput<'a>],
    profile: ProductionInnerFriProfile,
    verify_proofs: bool,
) -> Result<(crate::config::MyConfig, Vec<ParsedProductionInput<'a>>), AggregationError> {
    if inputs.is_empty() {
        return Err(AggregationError::Empty);
    }
    if !inputs.len().is_power_of_two() {
        return Err(AggregationError::InvalidFanIn { n: inputs.len() });
    }
    if inputs.len() > MAX_AGG_TILES {
        return Err(AggregationError::TooManyInputs { n: inputs.len() });
    }

    let config = production_config_for_profile(profile);
    let mut parsed = Vec::with_capacity(inputs.len());
    for input in inputs {
        parsed.push(if verify_proofs {
            verify_production_input(input, &config)?
        } else {
            parse_production_input_for_plan(input, &config)?
        });
    }

    Ok((config, parsed))
}

fn parse_and_verify_production_inputs<'a>(
    inputs: &'a [JoinSplitAggregateInput<'a>],
    profile: ProductionInnerFriProfile,
) -> Result<(crate::config::MyConfig, Vec<ParsedProductionInput<'a>>), AggregationError> {
    parse_production_inputs(inputs, profile, true)
}

fn parse_and_plan_production_inputs<'a>(
    inputs: &'a [JoinSplitAggregateInput<'a>],
    profile: ProductionInnerFriProfile,
) -> Result<(crate::config::MyConfig, Vec<ParsedProductionInput<'a>>), AggregationError> {
    parse_production_inputs(inputs, profile, false)
}

fn plan_production_inner_shape(
    config: &crate::config::MyConfig,
    input: &ParsedProductionInput<'_>,
    constraints: &[p3_uni_stark::SymbolicExpression<Val>],
) -> Result<PlannedProductionInnerShape, AggregationError> {
    validate_binary_fri_shape(&input.proof)?;
    let n_queries = input.proof.opening_proof.1.query_proofs.len();
    let (_block_inputs, counts, binds, _challenges, index_binds, _index_felts) =
        sim_full_hiding(config, &input.proof, input.public_values);
    let (terms0, _, _, _) =
        hiding_multicol_query_terms(config, &JoinSplitAir, &input.proof, input.public_values, 0);
    let cap_height = input.proof.commitments.trace.roots().len().trailing_zeros() as usize;
    let air = MonolithAir {
        counts: counts.clone(),
        binds: binds.clone(),
        index_binds: index_binds.clone(),
        n_queries,
        n_terms: terms0.len(),
        inner_counter: false,
        column_window: true,
        k_instances: 1,
        fold: false,
        fold_txstmt: false,
        constraints: constraints.to_vec(),
        w_inner_f: WIDTH,
        n_pub_f: N_PUBLIC,
        n_periodic_f: N_PERIODIC,
        is_zk: 1,
        cap_height,
    };
    if air.nqc() > (1 << crate::config::LOG_BLOWUP) {
        return Err(AggregationError::TraceLayout(
            "hiding quotient chunk count exceeds production blowup".into(),
        ));
    }
    let trace =
        trace_resource_estimate("hiding inner monolith trace", air.height(), air.fused_w())?;
    let query_segment = trace_resource_estimate(
        "hiding inner monolith query segment",
        air.m_period(),
        air.fused_w(),
    )?;
    Ok(PlannedProductionInnerShape {
        counts,
        binds,
        index_binds,
        n_terms: terms0.len(),
        cap_height,
        trace,
        query_segment,
    })
}

fn plan_production_aggregate_from_parsed(
    parsed: &[ParsedProductionInput<'_>],
    config: &crate::config::MyConfig,
) -> Result<ProductionAggregateResourcePlan, AggregationError> {
    if parsed.is_empty() {
        return Err(AggregationError::Empty);
    }
    let constraints = get_symbolic_constraints::<Val, JoinSplitAir>(
        &JoinSplitAir,
        AirLayout::from_air::<Val>(&JoinSplitAir),
    );
    let mut params: Option<(
        Vec<u8>,
        Vec<usize>,
        Vec<(usize, usize)>,
        usize,
        usize,
        TraceResourceEstimate,
        TraceResourceEstimate,
    )> = None;
    for input in parsed {
        let shape = plan_production_inner_shape(config, input, &constraints)?;
        let current = (
            shape.counts,
            shape.binds,
            shape.index_binds,
            shape.n_terms,
            shape.cap_height,
            shape.trace,
            shape.query_segment,
        );
        if let Some(expected) = &params {
            if expected.0 != current.0
                || expected.1 != current.1
                || expected.2 != current.2
                || expected.3 != current.3
                || expected.4 != current.4
            {
                return Err(AggregationError::MismatchedInnerShape);
            }
        } else {
            params = Some(current);
        }
    }
    let (counts, binds, index_binds, n_terms, cap_height, inner_trace, inner_query_segment) =
        params.ok_or(AggregationError::Empty)?;
    let air = MonolithAir {
        counts,
        binds,
        index_binds,
        n_queries: parsed[0].proof.opening_proof.1.query_proofs.len(),
        n_terms,
        inner_counter: false,
        column_window: true,
        k_instances: parsed.len(),
        fold: true,
        fold_txstmt: true,
        constraints,
        w_inner_f: WIDTH,
        n_pub_f: N_PUBLIC,
        n_periodic_f: N_PERIODIC,
        is_zk: 1,
        cap_height,
    };
    if air.fold_sk_block() * BLOCK < air.tr() + air.n_queries * air.m_period() {
        return Err(AggregationError::TraceLayout(
            "fold blocks overlap query region".into(),
        ));
    }
    let aggregate_trace = trace_resource_estimate(
        "production aggregate folded trace",
        air.height(),
        air.fold_w(),
    )?;
    let aggregate_query_segment = trace_resource_estimate(
        "production aggregate query segment",
        air.m_period(),
        air.fold_w(),
    )?;
    Ok(ProductionAggregateResourcePlan {
        n_inputs: parsed.len(),
        inner_trace,
        inner_query_segment,
        aggregate_trace,
        aggregate_query_segment,
    })
}

fn build_instance(
    parsed: &[ParsedInput<'_>],
    config: &MyConfig,
) -> Result<AggregateInstance, AggregationError> {
    let k = parsed.len();
    let mut insts = Vec::with_capacity(k);
    let mut params: Option<(Vec<u8>, Vec<usize>, Vec<(usize, usize)>, usize, usize)> = None;

    for input in parsed {
        let (trace, counts, binds, index_binds, n_terms) = build_symbolic_inner_window(
            config,
            &JoinSplitAir,
            &input.proof,
            input.public_values,
            WIDTH,
            N_PUBLIC,
            N_PERIODIC,
        );
        let cap_height = input.proof.commitments.trace.roots().len().trailing_zeros() as usize;
        let current = (counts, binds, index_binds, n_terms, cap_height);
        if let Some(expected) = &params {
            if expected != &current {
                return Err(AggregationError::MismatchedInnerShape);
            }
        } else {
            params = Some(current.clone());
        }
        insts.push(trace);
    }

    let (counts, binds, index_binds, n_terms, cap_height) =
        params.ok_or(AggregationError::Empty)?;
    let constraints = get_symbolic_constraints::<Val, JoinSplitAir>(
        &JoinSplitAir,
        AirLayout::from_air::<Val>(&JoinSplitAir),
    );
    let air = MonolithAir {
        counts,
        binds,
        index_binds,
        n_queries: parsed[0].proof.opening_proof.query_proofs.len(),
        n_terms,
        inner_counter: false,
        column_window: true,
        k_instances: k,
        fold: true,
        fold_txstmt: true,
        constraints,
        w_inner_f: WIDTH,
        n_pub_f: N_PUBLIC,
        n_periodic_f: N_PERIODIC,
        is_zk: 0,
        cap_height,
    };

    let fused_w = air.fused_w();
    let fold_w = air.fold_w();
    let inst_h = air.inst_h();
    let height = air.height();
    let fold_block = air.fold_sk_block();
    if fold_block * BLOCK < air.tr() + air.n_queries * air.m_period() {
        return Err(AggregationError::TraceLayout(
            "fold blocks overlap query region".into(),
        ));
    }
    let mut values = vec![Val::ZERO; height * fold_w];
    let mut root = [Val::ZERO; 4];
    let chunk_sources = air.fold_chunk_srcs();
    let n_sk_blocks = chunk_sources.len();

    for (i, trace) in insts.iter().enumerate() {
        for row in 0..inst_h {
            let dst = (i * inst_h + row) * fold_w;
            values[dst..dst + fused_w]
                .copy_from_slice(&trace[row * fused_w..row * fused_w + fused_w]);
            values[dst + air.af_root(0)..dst + air.af_root(0) + 4].copy_from_slice(&root);
        }

        let mut statement_digest = [Val::from_u64(DOM_TXROOT), Val::ZERO, Val::ZERO, Val::ZERO];
        for (block, sources) in chunk_sources.iter().enumerate() {
            let chunk: [Val; 4] = core::array::from_fn(|lane| {
                sources[lane]
                    .map(|offset| parsed[i].public_values[offset])
                    .unwrap_or(Val::ZERO)
            });
            let mut input = [Val::ZERO; W];
            input[..4].copy_from_slice(&statement_digest);
            input[4..].copy_from_slice(&chunk);
            let rows = native_steps(input);
            for (row, poseidon_row) in rows.iter().enumerate() {
                let base = (i * inst_h + (fold_block + block) * BLOCK + row) * fold_w + air.af_p(0);
                values[base..base + W].copy_from_slice(poseidon_row);
            }
            statement_digest = native_permute(input)[..4].try_into().unwrap();
        }

        let mut input = [Val::ZERO; W];
        input[..4].copy_from_slice(&root);
        input[4..].copy_from_slice(&statement_digest);
        let rows = native_steps(input);
        for (row, poseidon_row) in rows.iter().enumerate() {
            let base =
                (i * inst_h + (fold_block + n_sk_blocks) * BLOCK + row) * fold_w + air.af_p(0);
            values[base..base + W].copy_from_slice(poseidon_row);
        }
        root = native_permute(input)[..4].try_into().unwrap();
    }

    let mut expected = [Val::ZERO; 4];
    for input in parsed {
        expected = merge(expected, tx_statement_digest(input.public_values));
    }
    if root != expected {
        return Err(AggregationError::TraceLayout(
            "tx-root fold did not match batch root oracle".into(),
        ));
    }
    Ok(AggregateInstance {
        air,
        trace: RowMajorMatrix::new(values, fold_w),
        tx_root: root,
    })
}

fn build_production_instance(
    parsed: &[ParsedProductionInput<'_>],
    config: &crate::config::MyConfig,
) -> Result<AggregateInstance, AggregationError> {
    let k = parsed.len();
    let mut windows = Vec::with_capacity(k);
    let mut params: Option<(Vec<u8>, Vec<usize>, Vec<(usize, usize)>, usize, usize)> = None;

    let started = std::time::Instant::now();
    for (i, input) in parsed.iter().enumerate() {
        let inner_started = std::time::Instant::now();
        aggregation_progress(format_args!(
            "production aggregate: building hidden inner window {}/{}",
            i + 1,
            k
        ));
        let window = build_symbolic_hiding_inner_window_source(
            config,
            &JoinSplitAir,
            &input.proof,
            input.public_values,
            WIDTH,
            N_PUBLIC,
            N_PERIODIC,
        )?;
        let cap_height = input.proof.commitments.trace.roots().len().trailing_zeros() as usize;
        let current = (
            window.counts.clone(),
            window.binds.clone(),
            window.index_binds.clone(),
            window.n_terms,
            cap_height,
        );
        if let Some(expected) = &params {
            if expected != &current {
                return Err(AggregationError::MismatchedInnerShape);
            }
        } else {
            params = Some(current.clone());
        }
        let max_range_felts = window
            .source()
            .ranges()
            .iter()
            .map(MonolithTraceRowRange::felt_len)
            .max()
            .unwrap_or(0);
        aggregation_progress(format_args!(
            "production aggregate: hidden inner window {}/{} done rows={} max_range_felts={} elapsed={:?}",
            i + 1,
            k,
            window.air.height(),
            max_range_felts,
            inner_started.elapsed()
        ));
        windows.push(window);
    }

    let (counts, binds, index_binds, n_terms, cap_height) =
        params.ok_or(AggregationError::Empty)?;
    let constraints = get_symbolic_constraints::<Val, JoinSplitAir>(
        &JoinSplitAir,
        AirLayout::from_air::<Val>(&JoinSplitAir),
    );
    let air = MonolithAir {
        counts,
        binds,
        index_binds,
        n_queries: parsed[0].proof.opening_proof.1.query_proofs.len(),
        n_terms,
        inner_counter: false,
        column_window: true,
        k_instances: k,
        fold: true,
        fold_txstmt: true,
        constraints,
        w_inner_f: WIDTH,
        n_pub_f: N_PUBLIC,
        n_periodic_f: N_PERIODIC,
        is_zk: 1,
        cap_height,
    };

    let fused_w = air.fused_w();
    let fold_w = air.fold_w();
    let inst_h = air.inst_h();
    let height = air.height();
    let fold_block = air.fold_sk_block();
    if fold_block * BLOCK < air.tr() + air.n_queries * air.m_period() {
        return Err(AggregationError::TraceLayout(
            "fold blocks overlap query region".into(),
        ));
    }
    let tile_started = std::time::Instant::now();
    let total_felts = checked_trace_felts("production aggregate folded trace", height, fold_w)?;
    aggregation_progress(format_args!(
        "production aggregate: tiling k={} inst_h={} height={} fused_w={} fold_w={} total_felts={}",
        k, inst_h, height, fused_w, fold_w, total_felts
    ));

    let mut values = vec![Val::ZERO; total_felts];
    let mut root = [Val::ZERO; 4];
    let chunk_sources = air.fold_chunk_srcs();
    let n_sk_blocks = chunk_sources.len();

    for (i, window) in windows.iter().enumerate() {
        if window.air.height() != inst_h || window.air.fused_w() != fused_w {
            return Err(AggregationError::MismatchedInnerShape);
        }
        for range in window.source().ranges() {
            debug_assert_eq!(range.width, fused_w);
            let mut emitted = vec![Val::ZERO; range.felt_len()];
            window.emit_range_with_selector(range, &mut emitted);
            for row in 0..range.rows {
                let dst = (i * inst_h + range.start_row + row) * fold_w;
                let src = row * fused_w;
                values[dst..dst + fused_w].copy_from_slice(&emitted[src..src + fused_w]);
                values[dst + air.af_root(0)..dst + air.af_root(0) + 4].copy_from_slice(&root);
            }
        }

        let mut statement_digest = [Val::from_u64(DOM_TXROOT), Val::ZERO, Val::ZERO, Val::ZERO];
        for (block, sources) in chunk_sources.iter().enumerate() {
            let chunk: [Val; 4] = core::array::from_fn(|lane| {
                sources[lane]
                    .map(|offset| parsed[i].public_values[offset])
                    .unwrap_or(Val::ZERO)
            });
            let mut input = [Val::ZERO; W];
            input[..4].copy_from_slice(&statement_digest);
            input[4..].copy_from_slice(&chunk);
            let rows = native_steps(input);
            for (row, poseidon_row) in rows.iter().enumerate() {
                let base = (i * inst_h + (fold_block + block) * BLOCK + row) * fold_w + air.af_p(0);
                values[base..base + W].copy_from_slice(poseidon_row);
            }
            statement_digest = native_permute(input)[..4].try_into().unwrap();
        }

        let mut input = [Val::ZERO; W];
        input[..4].copy_from_slice(&root);
        input[4..].copy_from_slice(&statement_digest);
        let rows = native_steps(input);
        for (row, poseidon_row) in rows.iter().enumerate() {
            let base =
                (i * inst_h + (fold_block + n_sk_blocks) * BLOCK + row) * fold_w + air.af_p(0);
            values[base..base + W].copy_from_slice(poseidon_row);
        }
        root = native_permute(input)[..4].try_into().unwrap();
    }

    let mut expected = [Val::ZERO; 4];
    for input in parsed {
        expected = merge(expected, tx_statement_digest(input.public_values));
    }
    if root != expected {
        return Err(AggregationError::TraceLayout(
            "tx-root fold did not match batch root oracle".into(),
        ));
    }
    aggregation_progress(format_args!(
        "production aggregate: tiling done elapsed={:?} total_elapsed={:?}",
        tile_started.elapsed(),
        started.elapsed()
    ));

    Ok(AggregateInstance {
        air,
        trace: RowMajorMatrix::new(values, fold_w),
        tx_root: root,
    })
}

#[cfg(feature = "stream")]
fn build_production_store_instance(
    parsed: &[ParsedProductionInput<'_>],
    config: &crate::config::MyConfig,
) -> Result<AggregateStoreInstance, AggregationError> {
    let k = parsed.len();
    let mut windows = Vec::with_capacity(k);
    let mut params: Option<(Vec<u8>, Vec<usize>, Vec<(usize, usize)>, usize, usize)> = None;

    let started = std::time::Instant::now();
    for (i, input) in parsed.iter().enumerate() {
        let inner_started = std::time::Instant::now();
        aggregation_progress(format_args!(
            "production aggregate store: building hidden inner window {}/{}",
            i + 1,
            k
        ));
        let window = build_symbolic_hiding_inner_window_source(
            config,
            &JoinSplitAir,
            &input.proof,
            input.public_values,
            WIDTH,
            N_PUBLIC,
            N_PERIODIC,
        )?;
        let cap_height = input.proof.commitments.trace.roots().len().trailing_zeros() as usize;
        let current = (
            window.counts.clone(),
            window.binds.clone(),
            window.index_binds.clone(),
            window.n_terms,
            cap_height,
        );
        if let Some(expected) = &params {
            if expected != &current {
                return Err(AggregationError::MismatchedInnerShape);
            }
        } else {
            params = Some(current.clone());
        }
        let max_range_felts = window
            .source()
            .ranges()
            .iter()
            .map(MonolithTraceRowRange::felt_len)
            .max()
            .unwrap_or(0);
        aggregation_progress(format_args!(
            "production aggregate store: hidden inner window {}/{} done rows={} max_range_felts={} elapsed={:?}",
            i + 1,
            k,
            window.air.height(),
            max_range_felts,
            inner_started.elapsed()
        ));
        windows.push(window);
    }

    let (counts, binds, index_binds, n_terms, cap_height) =
        params.ok_or(AggregationError::Empty)?;
    let constraints = get_symbolic_constraints::<Val, JoinSplitAir>(
        &JoinSplitAir,
        AirLayout::from_air::<Val>(&JoinSplitAir),
    );
    let air = MonolithAir {
        counts,
        binds,
        index_binds,
        n_queries: parsed[0].proof.opening_proof.1.query_proofs.len(),
        n_terms,
        inner_counter: false,
        column_window: true,
        k_instances: k,
        fold: true,
        fold_txstmt: true,
        constraints,
        w_inner_f: WIDTH,
        n_pub_f: N_PUBLIC,
        n_periodic_f: N_PERIODIC,
        is_zk: 1,
        cap_height,
    };

    let fused_w = air.fused_w();
    let fold_w = air.fold_w();
    let inst_h = air.inst_h();
    let height = air.height();
    let fold_block = air.fold_sk_block();
    if fold_block * BLOCK < air.tr() + air.n_queries * air.m_period() {
        return Err(AggregationError::TraceLayout(
            "fold blocks overlap query region".into(),
        ));
    }
    let total_felts = height.checked_mul(fold_w).ok_or_else(|| {
        AggregationError::TraceLayout("production aggregate store size overflows usize".into())
    })?;
    let tile_started = std::time::Instant::now();
    aggregation_progress(format_args!(
        "production aggregate store: tiling k={} inst_h={} height={} fused_w={} fold_w={} total_felts={}",
        k, inst_h, height, fused_w, fold_w, total_felts
    ));

    let store = MmapLdeStore::new(height, fold_w)?;
    let mut row_buf = vec![Val::ZERO; fold_w];
    let mut root = [Val::ZERO; 4];
    let chunk_sources = air.fold_chunk_srcs();
    let n_sk_blocks = chunk_sources.len();

    for (i, window) in windows.iter().enumerate() {
        if window.air.height() != inst_h || window.air.fused_w() != fused_w {
            return Err(AggregationError::MismatchedInnerShape);
        }
        const AGG_EMIT_MAX_FELTS: usize = 32 * 1024 * 1024;
        for range in window.source().ranges() {
            debug_assert_eq!(range.width, fused_w);
            let rows_per_chunk = match range.kind {
                MonolithTracePart::Query { .. } => range.rows,
                _ => (AGG_EMIT_MAX_FELTS / fused_w).max(1).min(range.rows),
            };
            let mut local_start = 0usize;
            while local_start < range.rows {
                let rows = rows_per_chunk.min(range.rows - local_start);
                let chunk = MonolithTraceRowRange {
                    kind: range.kind,
                    start_row: range.start_row + local_start,
                    rows,
                    width: range.width,
                };
                let mut emitted = vec![Val::ZERO; chunk.felt_len()];
                match chunk.kind {
                    MonolithTracePart::Padding => {
                        window.fill_padding_rows_with_selector(fused_w, &mut emitted);
                    }
                    _ => window.emit_range_with_selector(chunk, &mut emitted),
                }
                for row in 0..rows {
                    row_buf.fill(Val::ZERO);
                    let src = row * fused_w;
                    row_buf[..fused_w].copy_from_slice(&emitted[src..src + fused_w]);
                    row_buf[air.af_root(0)..air.af_root(0) + 4].copy_from_slice(&root);
                    store.write_row(i * inst_h + chunk.start_row + row, &row_buf);
                }
                local_start += rows;
            }
        }

        let mut statement_digest = [Val::from_u64(DOM_TXROOT), Val::ZERO, Val::ZERO, Val::ZERO];
        for (block, sources) in chunk_sources.iter().enumerate() {
            let chunk: [Val; 4] = core::array::from_fn(|lane| {
                sources[lane]
                    .map(|offset| parsed[i].public_values[offset])
                    .unwrap_or(Val::ZERO)
            });
            let mut input = [Val::ZERO; W];
            input[..4].copy_from_slice(&statement_digest);
            input[4..].copy_from_slice(&chunk);
            let rows = native_steps(input);
            for (row, poseidon_row) in rows.iter().enumerate() {
                let global = i * inst_h + (fold_block + block) * BLOCK + row;
                store.fill_row(global, &mut row_buf);
                row_buf[air.af_p(0)..air.af_p(0) + W].copy_from_slice(poseidon_row);
                store.write_row(global, &row_buf);
            }
            statement_digest = native_permute(input)[..4].try_into().unwrap();
        }

        let mut input = [Val::ZERO; W];
        input[..4].copy_from_slice(&root);
        input[4..].copy_from_slice(&statement_digest);
        let rows = native_steps(input);
        for (row, poseidon_row) in rows.iter().enumerate() {
            let global = i * inst_h + (fold_block + n_sk_blocks) * BLOCK + row;
            store.fill_row(global, &mut row_buf);
            row_buf[air.af_p(0)..air.af_p(0) + W].copy_from_slice(poseidon_row);
            store.write_row(global, &row_buf);
        }
        root = native_permute(input)[..4].try_into().unwrap();
    }

    let mut expected = [Val::ZERO; 4];
    for input in parsed {
        expected = merge(expected, tx_statement_digest(input.public_values));
    }
    if root != expected {
        return Err(AggregationError::TraceLayout(
            "tx-root fold did not match batch root oracle".into(),
        ));
    }
    aggregation_progress(format_args!(
        "production aggregate store: tiling done elapsed={:?} total_elapsed={:?}",
        tile_started.elapsed(),
        started.elapsed()
    ));

    Ok(AggregateStoreInstance {
        air,
        trace: store,
        tx_root: root,
    })
}

pub fn prove_joinsplit_aggregate_research(
    inputs: &[JoinSplitAggregateInput<'_>],
    options: ResearchAggregationOptions,
) -> Result<JoinSplitAggregateProof, AggregationError> {
    let (inner_config, parsed) = parse_and_verify_inputs(inputs, options)?;
    let instance = build_instance(&parsed, &inner_config)?;
    let width = instance.trace.width;
    let log_rows = (instance.trace.values.len() / width).trailing_zeros();
    let proof = match options.backend {
        AggregationBackend::InMemory => {
            prove_outer_in_memory(&instance.air, instance.trace, &instance.tx_root)?
        }
        AggregationBackend::Stream { c_block } => {
            prove_outer_stream(&instance.air, instance.trace, &instance.tx_root, c_block)?
        }
    };
    Ok(JoinSplitAggregateProof {
        proof_bytes: proof,
        tx_root: instance.tx_root,
        n_inputs: inputs.len(),
        width,
        log_rows,
    })
}

/// Build and prove an R4 aggregate over real production-hiding JoinSplit proofs.
///
/// This remains a research API: it is feature-gated with recursion, not exposed
/// through the C ABI, and currently rejects non-binary FRI commit rounds because
/// the monolith query fold AIR is one-bit-per-round.
pub fn plan_joinsplit_aggregate_production(
    inputs: &[JoinSplitAggregateInput<'_>],
    options: ProductionAggregationOptions,
) -> Result<ProductionAggregateResourcePlan, AggregationError> {
    let (inner_config, parsed) = parse_and_plan_production_inputs(inputs, options.inner_profile)?;
    plan_production_aggregate_from_parsed(&parsed, &inner_config)
}

pub fn prove_joinsplit_aggregate_production_research(
    inputs: &[JoinSplitAggregateInput<'_>],
    options: ProductionAggregationOptions,
) -> Result<JoinSplitAggregateProof, AggregationError> {
    let (inner_config, parsed) = parse_and_verify_production_inputs(inputs, options.inner_profile)?;
    let plan = plan_production_aggregate_from_parsed(&parsed, &inner_config)?;
    plan.check_limits_for_backend(options.backend)?;
    match options.backend {
        AggregationBackend::InMemory => {
            let instance = build_production_instance(&parsed, &inner_config)?;
            validate_production_outer_shape(&instance)?;
            let width = instance.trace.width;
            let log_rows = (instance.trace.values.len() / width).trailing_zeros();
            let proof = prove_outer_in_memory(&instance.air, instance.trace, &instance.tx_root)?;
            Ok(JoinSplitAggregateProof {
                proof_bytes: proof,
                tx_root: instance.tx_root,
                n_inputs: inputs.len(),
                width,
                log_rows,
            })
        }
        AggregationBackend::Stream { c_block } => {
            #[cfg(feature = "stream")]
            {
                let instance = build_production_store_instance(&parsed, &inner_config)?;
                validate_production_outer_dimensions(&instance.air, instance.trace.height())?;
                let width = instance.trace.width();
                let log_rows = instance.trace.height().trailing_zeros();
                let AggregateStoreInstance {
                    air,
                    trace,
                    tx_root,
                } = instance;
                let proof = prove_outer_stream_store(&air, trace, &tx_root, c_block)?;
                Ok(JoinSplitAggregateProof {
                    proof_bytes: proof,
                    tx_root,
                    n_inputs: inputs.len(),
                    width,
                    log_rows,
                })
            }
            #[cfg(not(feature = "stream"))]
            {
                let _ = c_block;
                Err(AggregationError::BackendUnavailable(
                    "stream backend requires --features stream",
                ))
            }
        }
    }
}

/// Validate and pad production JoinSplit aggregate inputs with a real dummy proof.
///
/// The dummy must verify under the selected production input profile and its
/// public values must hash to `batch_joinsplit_air::dummy_sk()`, matching the
/// batch path's canonical padding statement.
pub fn pad_joinsplit_aggregate_production_inputs<'a>(
    inputs: &[JoinSplitAggregateInput<'a>],
    dummy: JoinSplitAggregateInput<'a>,
    profile: ProductionInnerFriProfile,
) -> Result<Vec<JoinSplitAggregateInput<'a>>, AggregationError> {
    if inputs.is_empty() {
        return Err(AggregationError::Empty);
    }
    if inputs.len() > MAX_AGG_TILES {
        return Err(AggregationError::TooManyInputs { n: inputs.len() });
    }
    let target = inputs.len().next_power_of_two();
    if target > MAX_AGG_TILES {
        return Err(AggregationError::TooManyInputs { n: target });
    }

    let config = production_config_for_profile(profile);
    for input in inputs {
        verify_production_input(input, &config)?;
    }
    verify_production_input(&dummy, &config)?;
    if tx_statement_digest(dummy.public_values) != dummy_sk() {
        return Err(AggregationError::InvalidDummyPadding);
    }

    let mut padded = inputs.to_vec();
    padded.resize(target, dummy);
    Ok(padded)
}

/// Prove a production-parameter aggregate after padding to a power-of-two fan-in
/// with a verifiable canonical dummy proof.
pub fn prove_joinsplit_aggregate_production_padded_research<'a>(
    inputs: &[JoinSplitAggregateInput<'a>],
    dummy: JoinSplitAggregateInput<'a>,
    options: ProductionAggregationOptions,
) -> Result<JoinSplitAggregateProof, AggregationError> {
    let padded = pad_joinsplit_aggregate_production_inputs(inputs, dummy, options.inner_profile)?;
    prove_joinsplit_aggregate_production_research(&padded, options)
}

pub fn verify_joinsplit_aggregate_production_research(
    inputs: &[JoinSplitAggregateInput<'_>],
    aggregate_proof_bytes: &[u8],
    tx_root: &[Val],
    options: ProductionAggregationOptions,
) -> Result<bool, AggregationError> {
    if tx_root.len() != 4 {
        return Err(AggregationError::WrongPublicValueCount { got: tx_root.len() });
    }
    let (inner_config, parsed) = parse_and_verify_production_inputs(inputs, options.inner_profile)?;
    let plan = plan_production_aggregate_from_parsed(&parsed, &inner_config)?;
    plan.check_limits_for_backend(options.backend)?;
    let instance = build_production_instance(&parsed, &inner_config)?;
    validate_production_outer_shape(&instance)?;
    let proof: Proof<crate::config::MyConfig> = postcard::from_bytes(aggregate_proof_bytes)
        .map_err(|_| AggregationError::MalformedAggregateProof)?;
    Ok(verify(
        &crate::config::make_config(),
        &instance.air,
        &proof,
        tx_root,
    )
    .is_ok())
}

/// Validate real production JoinSplit proofs for a future production recursive aggregate.
///
/// This is the admission gate for production-hiding R4 aggregation: every inner
/// proof must be a `crate::config::MyConfig` hiding proof, use the frozen q96
/// FRI parameters, verify against its public values, and fold to the same
/// tx-root as `batch_joinsplit_air::batch_root`.
pub fn admit_joinsplit_aggregate_production(
    inputs: &[JoinSplitAggregateInput<'_>],
) -> Result<ProductionAggregateAdmission, AggregationError> {
    if inputs.is_empty() {
        return Err(AggregationError::Empty);
    }
    if !inputs.len().is_power_of_two() {
        return Err(AggregationError::InvalidFanIn { n: inputs.len() });
    }
    if inputs.len() > MAX_AGG_TILES {
        return Err(AggregationError::TooManyInputs { n: inputs.len() });
    }

    let verifier_config = crate::config::make_config();
    let mut tx_root = [Val::ZERO; 4];
    for input in inputs {
        if input.public_values.len() != N_PUBLIC {
            return Err(AggregationError::WrongPublicValueCount {
                got: input.public_values.len(),
            });
        }
        let proof: Proof<crate::config::MyConfig> = postcard::from_bytes(input.proof_bytes)
            .map_err(|_| AggregationError::MalformedInnerProof)?;
        let query_count = proof.opening_proof.1.query_proofs.len();
        if query_count != crate::config::NUM_QUERIES {
            return Err(AggregationError::InnerQueryCount {
                expected: crate::config::NUM_QUERIES,
                got: query_count,
            });
        }
        let cap_height = proof.commitments.trace.roots().len().trailing_zeros() as usize;
        if cap_height != crate::config::CAP_HEIGHT {
            return Err(AggregationError::InnerCapHeight {
                expected: crate::config::CAP_HEIGHT,
                got: cap_height,
            });
        }
        if proof.commitments.random.is_none() || proof.opened_values.random.is_none() {
            return Err(AggregationError::NonHidingInnerProof);
        }
        validate_production_joinsplit_shape(&verifier_config, proof.degree_bits)?;
        verify(&verifier_config, &JoinSplitAir, &proof, input.public_values)
            .map_err(|_| AggregationError::InnerProofRejected)?;
        tx_root = merge(tx_root, tx_statement_digest(input.public_values));
    }

    Ok(ProductionAggregateAdmission {
        tx_root,
        n_inputs: inputs.len(),
    })
}

pub fn verify_joinsplit_aggregate_research(
    inputs: &[JoinSplitAggregateInput<'_>],
    aggregate_proof_bytes: &[u8],
    tx_root: &[Val],
    options: ResearchAggregationOptions,
) -> Result<bool, AggregationError> {
    if tx_root.len() != 4 {
        return Err(AggregationError::WrongPublicValueCount { got: tx_root.len() });
    }
    let (inner_config, parsed) = parse_and_verify_inputs(inputs, options)?;
    let instance = build_instance(&parsed, &inner_config)?;
    let proof: Proof<crate::config::MyConfig> = postcard::from_bytes(aggregate_proof_bytes)
        .map_err(|_| AggregationError::MalformedAggregateProof)?;
    Ok(verify(
        &crate::config::make_config(),
        &instance.air,
        &proof,
        tx_root,
    )
    .is_ok())
}

fn prove_outer_in_memory(
    air: &MonolithAir,
    trace: RowMajorMatrix<Val>,
    tx_root: &[Val],
) -> Result<Vec<u8>, AggregationError> {
    let proof = prove(&crate::config::make_config(), air, trace, tx_root);
    postcard::to_allocvec(&proof)
        .map_err(|_| AggregationError::TraceLayout("aggregate proof serialization failed".into()))
}

#[cfg(feature = "stream")]
fn prove_outer_stream(
    air: &MonolithAir,
    trace: RowMajorMatrix<Val>,
    tx_root: &[Val],
    c_block: usize,
) -> Result<Vec<u8>, AggregationError> {
    let mut rng = rand::rng();
    let pcs_seed = rng.random::<u64>();
    let mmcs_seed = rng.random::<u64>();
    let config = crate::config::make_config();
    let proof = crate::stream_prove::stream_prove(
        &config, air, trace, tx_root, pcs_seed, mmcs_seed, c_block,
    )?;
    postcard::to_allocvec(&proof)
        .map_err(|_| AggregationError::TraceLayout("aggregate proof serialization failed".into()))
}

#[cfg(feature = "stream")]
fn prove_outer_stream_store(
    air: &MonolithAir,
    trace: MmapLdeStore,
    tx_root: &[Val],
    c_block: usize,
) -> Result<Vec<u8>, AggregationError> {
    let mut rng = rand::rng();
    let pcs_seed = rng.random::<u64>();
    let mmcs_seed = rng.random::<u64>();
    let config = crate::config::make_config();
    let proof = crate::stream_prove::stream_prove_from_trace_store_owned(
        &config, air, trace, tx_root, pcs_seed, mmcs_seed, c_block,
    )?;
    postcard::to_allocvec(&proof)
        .map_err(|_| AggregationError::TraceLayout("aggregate proof serialization failed".into()))
}

#[cfg(not(feature = "stream"))]
fn prove_outer_stream(
    _air: &MonolithAir,
    _trace: RowMajorMatrix<Val>,
    _tx_root: &[Val],
    _c_block: usize,
) -> Result<Vec<u8>, AggregationError> {
    Err(AggregationError::BackendUnavailable(
        "stream backend requires --features stream",
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::batch_joinsplit_air::dummy_witness;
    use crate::joinsplit_air::{build_trace, demo_witness, public_values};

    fn demo_input(options: ResearchAggregationOptions) -> (Vec<u8>, Vec<Val>) {
        let config = make_config_cap(
            options.inner_max_log_arity,
            options.inner_num_queries,
            options.inner_cap_height,
        );
        let witness = demo_witness();
        let pvs = public_values(&witness);
        let proof = prove(&config, &JoinSplitAir, build_trace(&witness), &pvs);
        (postcard::to_allocvec(&proof).unwrap(), pvs)
    }

    fn small_hiding_binary_config(
        num_queries: usize,
        cap_height: usize,
    ) -> crate::config::MyConfig {
        use p3_fri::FriParameters;
        use p3_goldilocks::default_goldilocks_poseidon2_8;
        use rand::SeedableRng;
        use rand_chacha::ChaCha20Rng;

        let perm = default_goldilocks_poseidon2_8();
        let val_mmcs = crate::config::ValMmcs::new(
            crate::config::MyHash::new(perm.clone()),
            crate::config::MyCompress::new(perm.clone()),
            cap_height,
            ChaCha20Rng::from_rng(&mut rand::rng()),
        );
        let challenge_mmcs = crate::config::ChallengeMmcs::new(val_mmcs.clone());
        let fri = FriParameters {
            log_blowup: crate::config::LOG_BLOWUP,
            log_final_poly_len: 0,
            max_log_arity: 1,
            num_queries,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: crate::config::QUERY_POW_BITS,
            mmcs: challenge_mmcs,
        };
        let pcs = crate::config::MyPcs::new(
            crate::config::Dft::default(),
            val_mmcs,
            fri,
            crate::config::NUM_RANDOM_CODEWORDS,
            ChaCha20Rng::from_rng(&mut rand::rng()),
        );
        crate::config::MyConfig::new(pcs, crate::config::Challenger::new(perm))
    }

    #[test]
    fn symbolic_hiding_inner_window_source_matches_resident_trace() {
        let config = small_hiding_binary_config(2, 2);
        let witness = demo_witness();
        let pvs = public_values(&witness);
        let proof = prove(&config, &JoinSplitAir, build_trace(&witness), &pvs);

        let window = build_symbolic_hiding_inner_window_source(
            &config,
            &JoinSplitAir,
            &proof,
            &pvs,
            WIDTH,
            N_PUBLIC,
            N_PERIODIC,
        )
        .unwrap();
        let mut resident = monolith_build_trace(
            &window.air,
            &window.block_inputs,
            &window.per_query,
            window.alpha_fri,
            &window.index_felts,
            &window.quotient_paths,
            &window.commit_data,
            &window.pub_window,
            Some(&window.hiding_witnesses),
        );
        window.apply_selector_window(window.air.fused_w(), &mut resident.values);

        let mut streamed = vec![Val::ZERO; resident.values.len()];
        for range in window.source().ranges() {
            let mut emitted = vec![Val::ZERO; range.felt_len()];
            window.emit_range_with_selector(range, &mut emitted);
            for row in 0..range.rows {
                let dst = (range.start_row + row) * range.width;
                let src = row * range.width;
                streamed[dst..dst + range.width].copy_from_slice(&emitted[src..src + range.width]);
            }
        }
        assert_eq!(streamed, resident.values);
    }

    #[cfg(feature = "stream")]
    #[test]
    fn production_store_instance_matches_resident_instance_small() {
        let config = small_hiding_binary_config(2, 2);
        let witness = demo_witness();
        let pvs = public_values(&witness);
        let proof = prove(&config, &JoinSplitAir, build_trace(&witness), &pvs);
        let parsed = [ParsedProductionInput {
            proof,
            public_values: &pvs,
        }];

        let resident = build_production_instance(&parsed, &config).unwrap();
        let streamed = build_production_store_instance(&parsed, &config).unwrap();
        let resident_h = resident.trace.values.len() / resident.trace.width;
        assert_eq!(streamed.tx_root, resident.tx_root);
        assert_eq!(streamed.trace.height(), resident_h);
        assert_eq!(streamed.trace.width(), resident.trace.width);

        let mut streamed_values = vec![Val::ZERO; resident.trace.values.len()];
        streamed
            .trace
            .fill_row_block(0, streamed.trace.height(), &mut streamed_values);
        assert_eq!(streamed_values, resident.trace.values);
    }

    #[test]
    fn research_aggregator_builds_k2_trace() {
        let options = ResearchAggregationOptions {
            inner_num_queries: 2,
            backend: AggregationBackend::InMemory,
            ..Default::default()
        };
        let (proof_a, pvs_a) = demo_input(options);
        let (proof_b, pvs_b) = demo_input(options);
        let inputs = [
            JoinSplitAggregateInput {
                proof_bytes: &proof_a,
                public_values: &pvs_a,
            },
            JoinSplitAggregateInput {
                proof_bytes: &proof_b,
                public_values: &pvs_b,
            },
        ];
        let (config, parsed) = parse_and_verify_inputs(&inputs, options).unwrap();
        let instance = build_instance(&parsed, &config).unwrap();
        let mut expected = [Val::ZERO; 4];
        expected = merge(expected, tx_statement_digest(&pvs_a));
        expected = merge(expected, tx_statement_digest(&pvs_b));
        assert_eq!(instance.tx_root, expected);
        assert!(instance.trace.width > WIDTH);
    }

    #[test]
    fn research_aggregator_rejects_non_power_of_two() {
        let options = ResearchAggregationOptions {
            inner_num_queries: 2,
            backend: AggregationBackend::InMemory,
            ..Default::default()
        };
        let (proof, pvs) = demo_input(options);
        let inputs = [JoinSplitAggregateInput {
            proof_bytes: &proof,
            public_values: &pvs,
        }];
        assert!(parse_and_verify_inputs(&inputs[..0], options).is_err());
        let three = [
            JoinSplitAggregateInput {
                proof_bytes: &proof,
                public_values: &pvs,
            },
            JoinSplitAggregateInput {
                proof_bytes: &proof,
                public_values: &pvs,
            },
            JoinSplitAggregateInput {
                proof_bytes: &proof,
                public_values: &pvs,
            },
        ];
        assert!(matches!(
            parse_and_verify_inputs(&three, options),
            Err(AggregationError::InvalidFanIn { n: 3 })
        ));
    }

    #[test]
    fn production_admission_rejects_empty_and_bad_fan_in() {
        let err = admit_joinsplit_aggregate_production(&[]).unwrap_err();
        assert!(matches!(err, AggregationError::Empty));

        let pvs = vec![Val::ZERO; N_PUBLIC];
        let inputs = [
            JoinSplitAggregateInput {
                proof_bytes: b"bad",
                public_values: &pvs,
            },
            JoinSplitAggregateInput {
                proof_bytes: b"bad",
                public_values: &pvs,
            },
            JoinSplitAggregateInput {
                proof_bytes: b"bad",
                public_values: &pvs,
            },
        ];
        let err = admit_joinsplit_aggregate_production(&inputs).unwrap_err();
        assert!(matches!(err, AggregationError::InvalidFanIn { n: 3 }));
    }

    #[test]
    fn production_admission_rejects_bad_public_values_and_malformed_proof() {
        let bad_pvs = vec![Val::ZERO; N_PUBLIC - 1];
        let inputs = [JoinSplitAggregateInput {
            proof_bytes: b"bad",
            public_values: &bad_pvs,
        }];
        let err = admit_joinsplit_aggregate_production(&inputs).unwrap_err();
        assert!(matches!(
            err,
            AggregationError::WrongPublicValueCount { got } if got == N_PUBLIC - 1
        ));

        let pvs = vec![Val::ZERO; N_PUBLIC];
        let inputs = [JoinSplitAggregateInput {
            proof_bytes: b"bad",
            public_values: &pvs,
        }];
        let err = admit_joinsplit_aggregate_production(&inputs).unwrap_err();
        assert!(matches!(err, AggregationError::MalformedInnerProof));
    }

    #[test]
    fn production_research_prover_rejects_before_trace_build() {
        let err = prove_joinsplit_aggregate_production_research(
            &[],
            ProductionAggregationOptions::default(),
        )
        .unwrap_err();
        assert!(matches!(err, AggregationError::Empty));

        let pvs = vec![Val::ZERO; N_PUBLIC];
        let inputs = [
            JoinSplitAggregateInput {
                proof_bytes: b"bad",
                public_values: &pvs,
            },
            JoinSplitAggregateInput {
                proof_bytes: b"bad",
                public_values: &pvs,
            },
            JoinSplitAggregateInput {
                proof_bytes: b"bad",
                public_values: &pvs,
            },
        ];
        let err = prove_joinsplit_aggregate_production_research(
            &inputs,
            ProductionAggregationOptions::default(),
        )
        .unwrap_err();
        assert!(matches!(err, AggregationError::InvalidFanIn { n: 3 }));
    }

    #[test]
    fn production_options_default_to_node_profile() {
        assert_eq!(
            ProductionAggregationOptions::default().inner_profile,
            ProductionInnerFriProfile::NodeProduction
        );
        assert_eq!(
            ProductionAggregationOptions::binary_recursion().inner_profile,
            ProductionInnerFriProfile::BinaryRecursion
        );
    }

    #[test]
    fn production_joinsplit_shape_preflight_accepts_frozen_params() {
        let config = crate::config::make_config();
        let layout = AirLayout::from_air::<Val>(&JoinSplitAir);
        let log_num_quotient_chunks =
            get_log_num_quotient_chunks::<Val, _>(&JoinSplitAir, layout, config.is_zk());
        assert!(log_num_quotient_chunks <= crate::config::LOG_BLOWUP);
        validate_production_joinsplit_shape(&config, config.is_zk()).unwrap();
    }

    #[test]
    fn production_outer_shape_preflight_rejects_bad_trace_height() {
        let instance = AggregateInstance {
            air: MonolithAir {
                counts: Vec::new(),
                binds: Vec::new(),
                index_binds: Vec::new(),
                n_queries: 0,
                n_terms: 0,
                inner_counter: false,
                column_window: false,
                k_instances: 1,
                fold: false,
                fold_txstmt: false,
                constraints: Vec::new(),
                w_inner_f: 1,
                n_pub_f: 0,
                n_periodic_f: 0,
                is_zk: 1,
                cap_height: crate::config::CAP_HEIGHT,
            },
            trace: RowMajorMatrix::new(vec![Val::ZERO; 3], 1),
            tx_root: [Val::ZERO; 4],
        };

        assert!(matches!(
            validate_production_outer_shape(&instance),
            Err(AggregationError::TraceLayout(_))
        ));
    }

    #[test]
    fn trace_resource_preflight_rejects_oversized_allocation() {
        let err = checked_trace_felts_with_limit("unit-test trace", 9, 1, 8).unwrap_err();
        assert!(matches!(
            err,
            AggregationError::ResourceLimit {
                what: "unit-test trace",
                required_felts,
                limit_felts,
            } if required_felts == 9 && limit_felts == 8
        ));
    }

    #[test]
    fn production_resource_plan_checks_backend_limits() {
        let under = TraceResourceEstimate {
            height: 2,
            width: 2,
            required_felts: 4,
            limit_felts: 8,
            within_limit: true,
        };
        let over = TraceResourceEstimate {
            height: 3,
            width: 3,
            required_felts: 9,
            limit_felts: 8,
            within_limit: false,
        };
        let plan = ProductionAggregateResourcePlan {
            n_inputs: 2,
            inner_trace: over,
            inner_query_segment: under,
            aggregate_trace: under,
            aggregate_query_segment: under,
        };
        assert!(matches!(
            plan.check_limits(),
            Err(AggregationError::ResourceLimit {
                what: "hiding inner monolith trace",
                required_felts: 9,
                limit_felts: 8,
            })
        ));
        assert!(plan
            .check_limits_for_backend(AggregationBackend::Stream { c_block: 4 })
            .is_ok());

        let plan = ProductionAggregateResourcePlan {
            n_inputs: 2,
            inner_trace: under,
            inner_query_segment: over,
            aggregate_trace: under,
            aggregate_query_segment: under,
        };
        assert!(matches!(
            plan.check_limits_for_backend(AggregationBackend::Stream { c_block: 4 }),
            Err(AggregationError::ResourceLimit {
                what: "hiding inner monolith query segment",
                required_felts: 9,
                limit_felts: 8,
            })
        ));
        let plan = ProductionAggregateResourcePlan {
            n_inputs: 2,
            inner_trace: under,
            inner_query_segment: under,
            aggregate_trace: over,
            aggregate_query_segment: under,
        };
        assert!(matches!(
            plan.check_limits(),
            Err(AggregationError::ResourceLimit {
                what: "production aggregate folded trace",
                required_felts: 9,
                limit_felts: 8,
            })
        ));
        assert!(plan
            .check_limits_for_backend(AggregationBackend::Stream { c_block: 4 })
            .is_ok());
        let plan = ProductionAggregateResourcePlan {
            n_inputs: 2,
            inner_trace: under,
            inner_query_segment: under,
            aggregate_trace: under,
            aggregate_query_segment: over,
        };
        assert!(matches!(
            plan.check_limits_for_backend(AggregationBackend::Stream { c_block: 4 }),
            Err(AggregationError::ResourceLimit {
                what: "production aggregate query segment",
                required_felts: 9,
                limit_felts: 8,
            })
        ));

        let plan = ProductionAggregateResourcePlan {
            n_inputs: 2,
            inner_trace: under,
            inner_query_segment: under,
            aggregate_trace: under,
            aggregate_query_segment: under,
        };
        let spill = plan.stream_spill_estimate().unwrap();
        let felt_bytes = core::mem::size_of::<Val>();
        let randomized_height = under.height * 2;
        let randomized_width = under.width + crate::config::NUM_RANDOM_CODEWORDS;
        let trace_bytes = under.height * under.width * felt_bytes;
        let randomized_trace_bytes = randomized_height * randomized_width * felt_bytes;
        let committed_trace_lde_bytes =
            (randomized_height << crate::config::LOG_BLOWUP) * randomized_width * felt_bytes;
        assert_eq!(spill.trace_bytes, trace_bytes);
        assert_eq!(spill.randomized_trace_bytes, randomized_trace_bytes);
        assert_eq!(spill.committed_trace_lde_bytes, committed_trace_lde_bytes);
        assert_eq!(
            spill.trace_commit_peak_bytes,
            (trace_bytes + randomized_trace_bytes)
                .max(randomized_trace_bytes + committed_trace_lde_bytes)
        );
    }

    #[test]
    fn production_padding_rejects_empty_and_too_many_before_proof_parse() {
        let pvs = vec![Val::ZERO; N_PUBLIC];
        let dummy = JoinSplitAggregateInput {
            proof_bytes: b"bad",
            public_values: &pvs,
        };
        let err = pad_joinsplit_aggregate_production_inputs(
            &[],
            dummy,
            ProductionInnerFriProfile::NodeProduction,
        )
        .err()
        .unwrap();
        assert!(matches!(err, AggregationError::Empty));

        let inputs = vec![dummy; MAX_AGG_TILES + 1];
        let err = pad_joinsplit_aggregate_production_inputs(
            &inputs,
            dummy,
            ProductionInnerFriProfile::NodeProduction,
        )
        .err()
        .unwrap();
        assert!(matches!(
            err,
            AggregationError::TooManyInputs { n } if n == MAX_AGG_TILES + 1
        ));
    }

    #[test]
    fn production_research_verifier_rejects_bad_root_shape_before_parse() {
        let err = verify_joinsplit_aggregate_production_research(
            &[],
            b"bad",
            &[Val::ZERO; 3],
            ProductionAggregationOptions::default(),
        )
        .unwrap_err();
        assert!(matches!(
            err,
            AggregationError::WrongPublicValueCount { got } if got == 3
        ));
    }

    #[test]
    #[ignore = "slow: q96/cap6 binary-recursion dummy JoinSplit proof"]
    fn production_binary_recursion_dummy_proof_verifies() {
        eprintln!("binary-recursion smoke: building config");
        let config = crate::config::make_recursion_binary_config();
        let witness = dummy_witness();
        let pvs = public_values(&witness);

        eprintln!("binary-recursion smoke: proving one dummy JoinSplit proof");
        let proof = prove(&config, &JoinSplitAir, build_trace(&witness), &pvs);
        assert!(proof
            .opening_proof
            .1
            .query_proofs
            .iter()
            .flat_map(|query| &query.commit_phase_openings)
            .all(|opening| opening.log_arity == 1));

        eprintln!("binary-recursion smoke: verifying proof and dummy digest");
        verify(&config, &JoinSplitAir, &proof, &pvs).unwrap();
        assert_eq!(tx_statement_digest(&pvs), dummy_sk());
    }

    #[test]
    #[ignore = "slow: q96/cap6 hiding JoinSplit proofs under binary-FRI recursion profile"]
    fn production_binary_recursion_k2_trace_resource_gate() {
        eprintln!("binary-recursion k2: building config and witnesses");
        let config = crate::config::make_recursion_binary_config();
        let witness = demo_witness();
        let dummy_witness = dummy_witness();
        let pvs_a = public_values(&witness);
        let pvs_b = public_values(&witness);
        let dummy_pvs = public_values(&dummy_witness);
        eprintln!("binary-recursion k2: proving first real JoinSplit proof");
        let proof_a = prove(&config, &JoinSplitAir, build_trace(&witness), &pvs_a);
        eprintln!("binary-recursion k2: proving second real JoinSplit proof");
        let proof_b = prove(&config, &JoinSplitAir, build_trace(&witness), &pvs_b);
        eprintln!("binary-recursion k2: proving dummy padding proof");
        let dummy_proof = prove(
            &config,
            &JoinSplitAir,
            build_trace(&dummy_witness),
            &dummy_pvs,
        );
        assert!(proof_a
            .opening_proof
            .1
            .query_proofs
            .iter()
            .flat_map(|query| &query.commit_phase_openings)
            .all(|opening| opening.log_arity == 1));
        let proof_a = postcard::to_allocvec(&proof_a).unwrap();
        let proof_b = postcard::to_allocvec(&proof_b).unwrap();
        let dummy_proof = postcard::to_allocvec(&dummy_proof).unwrap();
        let inputs = [
            JoinSplitAggregateInput {
                proof_bytes: &proof_a,
                public_values: &pvs_a,
            },
            JoinSplitAggregateInput {
                proof_bytes: &proof_b,
                public_values: &pvs_b,
            },
        ];
        let dummy = JoinSplitAggregateInput {
            proof_bytes: &dummy_proof,
            public_values: &dummy_pvs,
        };
        eprintln!("binary-recursion k2: validating dummy padding");
        let padded = pad_joinsplit_aggregate_production_inputs(
            &[
                inputs[0],
                inputs[1],
                JoinSplitAggregateInput {
                    proof_bytes: &proof_a,
                    public_values: &pvs_a,
                },
            ],
            dummy,
            ProductionInnerFriProfile::BinaryRecursion,
        )
        .unwrap();
        assert_eq!(padded.len(), 4);
        assert_eq!(tx_statement_digest(padded[3].public_values), dummy_sk());
        eprintln!("binary-recursion k2: planning production inputs");
        let plan = plan_joinsplit_aggregate_production(
            &inputs,
            ProductionAggregationOptions::binary_recursion(),
        )
        .unwrap();
        assert_eq!(plan.n_inputs, 2);
        assert_eq!(plan.inner_trace.required_felts, 6_158_286_848);
        assert!(!plan.inner_trace.within_limit);
        assert_eq!(plan.inner_query_segment.required_felts, 31_009_440);
        assert!(plan.inner_query_segment.within_limit);
        assert!(plan.aggregate_query_segment.within_limit);
        let _ = stream_gate_available_or_report(&plan, AggregationBackend::Stream { c_block: 4 });
        let err = plan.check_limits().unwrap_err();
        match err {
            AggregationError::ResourceLimit {
                what,
                required_felts,
                limit_felts,
            } => {
                eprintln!(
                    "binary-recursion k2: resource gate hit for {what}: required_felts={required_felts} limit_felts={limit_felts}; raise {MAX_TRACE_FELTS_ENV} for an intentional bench"
                );
                assert_eq!(what, "hiding inner monolith trace");
                assert_eq!(required_felts, plan.inner_trace.required_felts);
                assert_eq!(limit_felts, plan.inner_trace.limit_felts);
            }
            err => panic!("unexpected production aggregate planning error: {err:?}"),
        }
    }

    #[cfg(feature = "stream")]
    #[test]
    #[ignore = "slow: proves/verifies q96 K=2 production aggregate through stream backend"]
    fn production_binary_recursion_k2_stream_proves_and_verifies() {
        let started = std::time::Instant::now();
        eprintln!("binary-recursion k2 stream: building config and witnesses");
        let config = crate::config::make_recursion_binary_config();
        let witness = demo_witness();
        let pvs_a = public_values(&witness);
        let pvs_b = public_values(&witness);

        eprintln!("binary-recursion k2 stream: proving first real JoinSplit proof");
        let proof_a = prove(&config, &JoinSplitAir, build_trace(&witness), &pvs_a);
        eprintln!("binary-recursion k2 stream: proving second real JoinSplit proof");
        let proof_b = prove(&config, &JoinSplitAir, build_trace(&witness), &pvs_b);
        assert!(proof_a
            .opening_proof
            .1
            .query_proofs
            .iter()
            .flat_map(|query| &query.commit_phase_openings)
            .all(|opening| opening.log_arity == 1));

        let proof_a = postcard::to_allocvec(&proof_a).unwrap();
        let proof_b = postcard::to_allocvec(&proof_b).unwrap();
        let inputs = [
            JoinSplitAggregateInput {
                proof_bytes: &proof_a,
                public_values: &pvs_a,
            },
            JoinSplitAggregateInput {
                proof_bytes: &proof_b,
                public_values: &pvs_b,
            },
        ];
        let options = ProductionAggregationOptions {
            backend: AggregationBackend::Stream { c_block: 4 },
            inner_profile: ProductionInnerFriProfile::BinaryRecursion,
        };

        eprintln!("binary-recursion k2 stream: planning production inputs");
        let plan = plan_joinsplit_aggregate_production(&inputs, options).unwrap();
        eprintln!(
            "binary-recursion k2 stream: plan inner_query={} aggregate_query={} aggregate_trace={}x{}",
            plan.inner_query_segment.required_felts,
            plan.aggregate_query_segment.required_felts,
            plan.aggregate_trace.height,
            plan.aggregate_trace.width,
        );
        if !stream_gate_available_or_report(&plan, options.backend) {
            return;
        }

        eprintln!("binary-recursion k2 stream: proving aggregate");
        let before_prove_rss = aggregation_peak_rss_bytes();
        let aggregate = prove_joinsplit_aggregate_production_research(&inputs, options).unwrap();
        let after_prove_rss = aggregation_peak_rss_bytes();
        eprintln!(
            "binary-recursion k2 stream: aggregate proof bytes={} width={} log_rows={} peak_rss_delta_mib={} total_elapsed={:?}",
            aggregate.proof_bytes.len(),
            aggregate.width,
            aggregate.log_rows,
            after_prove_rss.saturating_sub(before_prove_rss) / (1 << 20),
            started.elapsed(),
        );

        eprintln!("binary-recursion k2 stream: verifying aggregate");
        assert!(verify_joinsplit_aggregate_production_research(
            &inputs,
            &aggregate.proof_bytes,
            &aggregate.tx_root,
            options,
        )
        .unwrap());
    }

    fn aggregation_peak_rss_bytes() -> u64 {
        std::fs::read_to_string("/proc/self/status")
            .ok()
            .and_then(|s| {
                s.lines().find_map(|line| {
                    line.strip_prefix("VmHWM:")
                        .and_then(|rest| rest.split_whitespace().next()?.parse::<u64>().ok())
                })
            })
            .map(|kb| kb * 1024)
            .unwrap_or(0)
    }

    fn stream_gate_available_or_report(
        plan: &ProductionAggregateResourcePlan,
        backend: AggregationBackend,
    ) -> bool {
        match plan.check_limits_for_backend(backend) {
            Ok(()) => true,
            Err(AggregationError::ResourceLimit {
                what: "production aggregate stream spill bytes",
                required_felts,
                limit_felts,
            }) => {
                if let Ok(spill) = plan.stream_spill_estimate() {
                    eprintln!(
                    "binary-recursion k2 stream: spill breakdown: trace_bytes={} randomized_trace_bytes={} committed_trace_lde_bytes={} trace_commit_peak_bytes={}",
                    spill.trace_bytes,
                    spill.randomized_trace_bytes,
                    spill.committed_trace_lde_bytes,
                    spill.trace_commit_peak_bytes,
                );
                }
                eprintln!(
                "binary-recursion k2 stream: spill gate hit: required_bytes={required_felts} available_bytes={limit_felts}; set LATTICA_SPILL_DIR to a filesystem with enough space for an intentional full proof bench"
            );
                false
            }
            Err(err) => panic!("unexpected stream resource gate error: {err:?}"),
        }
    }

    #[test]
    #[ignore = "slow: proves and verifies the outer aggregate proof"]
    fn research_aggregator_proves_and_verifies_k2() {
        let options = ResearchAggregationOptions {
            inner_num_queries: 2,
            backend: AggregationBackend::InMemory,
            ..Default::default()
        };
        let (proof_a, pvs_a) = demo_input(options);
        let (proof_b, pvs_b) = demo_input(options);
        let inputs = [
            JoinSplitAggregateInput {
                proof_bytes: &proof_a,
                public_values: &pvs_a,
            },
            JoinSplitAggregateInput {
                proof_bytes: &proof_b,
                public_values: &pvs_b,
            },
        ];
        let aggregate = prove_joinsplit_aggregate_research(&inputs, options).unwrap();
        assert!(verify_joinsplit_aggregate_research(
            &inputs,
            &aggregate.proof_bytes,
            &aggregate.tx_root,
            options
        )
        .unwrap());
    }
}
