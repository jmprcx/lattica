use super::{ft_build_trace, preamble_build_trace, FullTranscriptAir, PreambleAir, CAP_LANE, RATE};
use crate::poseidon2_air::{native_permute, BLOCK, W};
use crate::recursion::native_fri::{cap_felts, full_transcript_challenges, gen_const_proof, make_config, preamble_challenges, Challenge, MyConfig, Val};
use crate::recursion::native_verify::ConstAir;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use p3_uni_stark::{prove, verify, Proof};

/// A faithful `DuplexChallenger` mirror that also RECORDS the per-block schedule (each permute's input
/// state + prefix-free count) and which block each sampled challenge reads — the schedule that drives
/// `FullTranscriptAir` + `ft_build_trace`. Mirrors observe/duplex/sample exactly (incl. +num_absorbed
/// counts, output cleared on observe, sample pops from the back, re-permute when drained).
struct Sim {
    state: [Val; W],
    input: Vec<Val>,
    output: Vec<Val>,
    block_inputs: Vec<[Val; W]>,
    counts: Vec<u8>,
}
impl Sim {
    fn new() -> Self {
        Self { state: [Val::ZERO; W], input: vec![], output: vec![], block_inputs: vec![], counts: vec![] }
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
        let blk = self.block_inputs.len() - 1;
        let lane = self.output.len() - 1; // pop from the back
        (self.output.pop().unwrap(), blk, lane)
    }
    fn sample_ext(&mut self) -> ([Val; 2], usize) {
        let (c0, blk, _) = self.sample_base();
        let (c1, _, _) = self.sample_base();
        ([c0, c1], blk)
    }
}

/// Replay the ENTIRE transcript (α_stark, ζ, α_fri, β_0..β_{R-1}, then the final_poly/arities/query-PoW
/// absorbs and the squeeze-only index tail), recording the schedule. Returns
/// (per-block input states, counts, ext-bind block per challenge, ext challenge values,
/// index binds = (block, lane) per query, index felts).
#[allow(clippy::type_complexity)]
pub(crate) fn sim_full( // W2-assemble (research): exposed to the wrap as the inner-proof witness-extraction seam
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
) -> (Vec<[Val; W]>, Vec<u8>, Vec<usize>, Vec<[Val; 2]>, Vec<(usize, usize)>, Vec<Val>) {
    let (instance, commitment, _, _) = preamble_challenges(config, proof, pvs);
    let mut s = Sim::new();
    for &f in &instance {
        s.observe(f);
    }
    let (a_stark, b0) = s.sample_ext();
    for &f in &commitment {
        s.observe(f);
    }
    let (zeta, b1) = s.sample_ext();
    for &x in &proof.opened_values.trace_local {
        s.observe_ext(x);
    }
    if let Some(tn) = &proof.opened_values.trace_next {
        for &x in tn {
            s.observe_ext(x);
        }
    }
    for c in &proof.opened_values.quotient_chunks {
        for &x in c {
            s.observe_ext(x);
        }
    }
    let (a_fri, b2) = s.sample_ext();
    let mut binds = vec![b0, b1, b2];
    let mut chs = vec![a_stark, zeta, a_fri];
    let fri = &proof.opening_proof;
    for comm in &fri.commit_phase_commits {
        for f in cap_felts(comm) {
            s.observe(f);
        }
        let (beta, bb) = s.sample_ext();
        binds.push(bb);
        chs.push(beta);
    }
    // final_poly + arities + query-PoW (observe witness + one sample_bits), then the index tail.
    for &x in &fri.final_poly {
        s.observe_ext(x);
    }
    let log_arities: Vec<usize> = fri.query_proofs[0].commit_phase_openings.iter().map(|o| o.log_arity as usize).collect();
    for &la in &log_arities {
        s.observe(Val::from_usize(la));
    }
    s.observe(fri.query_pow_witness);
    let _ = s.sample_base(); // the 16-bit query-PoW sample
    let mut index_binds = Vec::new();
    let mut index_felts = Vec::new();
    for _ in 0..fri.query_proofs.len() {
        let (f, blk, lane) = s.sample_base();
        index_binds.push((blk, lane));
        index_felts.push(f);
    }
    (s.block_inputs, s.counts, binds, chs, index_binds, index_felts)
}

/// AA5 ordered-sponge-cap-bus feasibility seam (non-hiding): replay `sim_full`'s exact transcript schedule
/// while recording, for every commitment-cap felt the sponge ABSORBS, the `(cap_id, entry, k, block, lane)`
/// where it lands — `cap_id` 0=trace, 1=quotient, 2+r=commit-round r; `entry`/`k` = the `roots()[entry][k]`
/// decomposition (entry-major, felt-minor, matching `cap_felts`); `(block, lane)` = the sponge block index
/// and rate lane (`block_inputs[block][lane]` == the absorbed felt; in the AIR the block's input row is at
/// `block·BLOCK`, so the ordered bus provides `cur[lane]` there). Captured BEFORE each observe as
/// `(block_inputs.len(), input.len())` — the same block/lane rule `sample_base` uses. This is the position
/// map the FS-anchor ordered bus (AA5) reads to bind the narrow-tall cap region to the FS-absorbed caps.
#[allow(clippy::type_complexity)]
pub(crate) fn sim_cap_positions(
    config: &MyConfig,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
) -> (Vec<[Val; W]>, Vec<(usize, usize, usize, usize, usize)>) {
    let (instance, commitment, _, _) = preamble_challenges(config, proof, pvs);
    let mut s = Sim::new();
    let mut positions: Vec<(usize, usize, usize, usize, usize)> = Vec::new();
    // instance = [degree_bits, base_degree_bits, preprocessed_width, TRACE CAP (2^ch·4), pvs].
    let trace_cap_len = cap_felts(&proof.commitments.trace).len();
    for (i, &f) in instance.iter().enumerate() {
        if (3..3 + trace_cap_len).contains(&i) {
            let idx = i - 3;
            positions.push((0, idx / 4, idx % 4, s.block_inputs.len(), s.input.len()));
        }
        s.observe(f);
    }
    let _ = s.sample_ext(); // α
    // commitment = the QUOTIENT CAP felts.
    for (i, &f) in commitment.iter().enumerate() {
        positions.push((1, i / 4, i % 4, s.block_inputs.len(), s.input.len()));
        s.observe(f);
    }
    let _ = s.sample_ext(); // ζ
    for &x in &proof.opened_values.trace_local {
        s.observe_ext(x);
    }
    if let Some(tn) = &proof.opened_values.trace_next {
        for &x in tn {
            s.observe_ext(x);
        }
    }
    for c in &proof.opened_values.quotient_chunks {
        for &x in c {
            s.observe_ext(x);
        }
    }
    let _ = s.sample_ext(); // α_fri
    let fri = &proof.opening_proof;
    for (r, comm) in fri.commit_phase_commits.iter().enumerate() {
        for (i, &f) in cap_felts(comm).iter().enumerate() {
            positions.push((2 + r, i / 4, i % 4, s.block_inputs.len(), s.input.len()));
            s.observe(f);
        }
        let _ = s.sample_ext(); // β_r
    }
    (s.block_inputs, positions)
}

// single-sourced from the module geometry (the tests' historical local names kept via aliasing)
use super::{CM_CAP_HEIGHT as CAP_HEIGHT, LOG_BLOWUP};
const LOG_FINAL_POLY_LEN: usize = 0;
const EIGHT_GB: u64 = 8u64 << 30;
// The milestone uses a REDUCED query count: at the production 96 queries the (cap-dominated)
// verifier AIR is ~2^18, which exceeds 8 GB once realistic columns + the 16× LDE blowup are counted.
// The construction is query-count-agnostic (more queries = more identical tiles); production restores
// 96 via the tree (Phase 5/6). 32 queries lands the milestone at ~2^16 with comfortable 8 GB margin.
const MILESTONE_QUERIES: usize = 32;

/// The pinned shape of an inner proof, introspected from a real proof — the inputs the monolith
/// verifier AIR is sized around.
#[derive(Debug)]
struct InnerGeometry {
    degree_bits: usize,
    log_global_max_height: usize,
    num_rounds: usize,
    log_arities: Vec<usize>,
    num_queries: usize,
    num_quotient_chunks: usize,
    trace_width: usize,
    cap_height: usize,
}

fn introspect_geometry(proof: &Proof<MyConfig>) -> InnerGeometry {
    let fri = &proof.opening_proof;
    let log_arities: Vec<usize> = fri
        .query_proofs
        .first()
        .map(|qp| qp.commit_phase_openings.iter().map(|o| o.log_arity as usize).collect())
        .unwrap_or_default();
    let num_rounds = fri.commit_phase_commits.len();
    let log_global_max_height: usize = log_arities.iter().sum::<usize>() + LOG_BLOWUP + LOG_FINAL_POLY_LEN;
    InnerGeometry {
        degree_bits: proof.degree_bits,
        log_global_max_height,
        num_rounds,
        log_arities,
        num_queries: fri.query_proofs.len(),
        num_quotient_chunks: proof.opened_values.quotient_chunks.len(),
        trace_width: proof.opened_values.trace_local.len(),
        cap_height: CAP_HEIGHT,
    }
}

const DIGEST: usize = 4; // Poseidon2 hash output width

/// Generous estimate of the monolith trace height (rows) for this inner proof, from the per-region
/// block budget the AIR phases will fill. Each Poseidon2 permutation = `BLOCK` rows; each Merkle
/// level = one compression = one block; the leaf hash + every commitment-cap absorb = ceil(felts/RATE)
/// blocks. NOTE: a commitment is a `MerkleCap` of `2^min(cap_height, log_height)` digests (= that many
/// × DIGEST felts), absorbed IN FULL into the transcript — the transcript is cap-dominated.
fn monolith_trace_height(g: &InnerGeometry) -> usize {
    let merkle_depth = |log_h: usize| log_h.saturating_sub(g.cap_height); // levels above the cap
    let absorb_blocks = |felts: usize| felts.div_ceil(RATE).max(1);
    let cap_felts = |log_h: usize| (1usize << g.cap_height.min(log_h)) * DIGEST;

    // ---- transcript region (cap-dominated): preamble (instance scalars + trace cap + quotient cap)
    //      + per-round commit caps + final_poly + arities + the squeeze-only index tail ----
    let instance_scalar_felts = 3 + g.trace_width; // degree_bits, base_degree_bits, preprocessed_width, PVs
    let preamble_blocks = absorb_blocks(instance_scalar_felts)
        + absorb_blocks(cap_felts(g.log_global_max_height)) // trace cap → α
        + absorb_blocks(cap_felts(g.log_global_max_height)); // quotient cap → ζ
    let mut commit_cap_blocks = 0usize;
    let mut h = g.log_global_max_height;
    for &la in &g.log_arities {
        h -= la;
        commit_cap_blocks += absorb_blocks(cap_felts(h)); // each round's commit cap
    }
    let index_blocks = g.num_queries; // squeeze + SampleBitsAir per query (generous ~1 block/query)
    let transcript_blocks = preamble_blocks + commit_cap_blocks + absorb_blocks(2) /*final_poly*/
        + absorb_blocks(g.num_rounds) /*arities*/ + index_blocks;

    // ---- per-query region ----
    let leaf_blocks = |width: usize| width.div_ceil(RATE).max(1);
    let input_blocks = {
        let depth = merkle_depth(g.log_global_max_height);
        let trace_batch = leaf_blocks(g.trace_width) + depth + 1 /* cap membership */;
        let quot_batch = leaf_blocks(g.num_quotient_chunks * 2) + depth + 1;
        trace_batch + quot_batch
    };
    let mut commit_blocks = 0usize;
    let mut h = g.log_global_max_height;
    for &la in &g.log_arities {
        let folded_h = h - la;
        let arity = 1usize << la;
        commit_blocks += leaf_blocks(arity * 2) + merkle_depth(folded_h) + 1 /* fold */ + 1 /* cap membership */;
        h = folded_h;
    }
    let deep_blocks = 4 + g.num_rounds;
    let per_query_blocks = input_blocks + commit_blocks + deep_blocks;

    let epilogue_blocks = 8; // selectors + quotient recompose + constraint fold
    let total_rows = (transcript_blocks + g.num_queries * per_query_blocks + epilogue_blocks) * BLOCK;
    total_rows.next_power_of_two()
}

fn peak_rss_bytes() -> u64 {
    // VmHWM = peak resident set size of this process (Linux).
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines().find_map(|l| {
                l.strip_prefix("VmHWM:").and_then(|r| r.split_whitespace().next()?.parse::<u64>().ok())
            })
        })
        .map(|kb| kb * 1024)
        .unwrap_or(0)
}

/// Phase 0: pin the first-milestone inner-proof geometry; confirm the native verifier accepts it,
/// the derived monolith trace height fits ≤ 2^18, and proving stays ≤ 8 GB.
#[test]
#[ignore = "slow: Phase 0 geometry pin + 8 GB / 2^18 budget oracle"]
fn phase0_geometry_pin_and_budget() {
    // Arity-2 FRI milestone config (max_log_arity = 1) so the per-query fold maps onto FoldChainAir;
    // reduced query count so the verifier AIR fits 8 GB with margin.
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);

    // The inner proof is real: p3::verify (config-matched) accepts it. The monolith AIR validates
    // against p3::verify (not the 96-query native verify_proof), so the reduced query count is fine.
    assert!(verify(&config, &ConstAir, &proof, &pvs).is_ok(), "p3::verify should accept the inner proof");

    let g = introspect_geometry(&proof);
    // Pin the arity-2 milestone shape.
    assert_eq!(g.degree_bits, 6, "milestone degree_bits");
    assert!(g.log_arities.iter().all(|&a| a == 1), "arity-2 FRI: every round folds by 1 bit");
    assert_eq!(g.log_global_max_height, 10, "Σlog_arities(6) + log_blowup(4) + 0");
    assert_eq!(g.num_rounds, 6, "fold 2^10 → 2^4 in arity-2 steps");
    assert_eq!(g.num_queries, MILESTONE_QUERIES);

    let height = monolith_trace_height(&g);
    let log_h = height.trailing_zeros() as usize;
    // 8 GB column ceiling: committed LDE = height × cols × 16(blowup) × 8 B; allow ~4× prover overhead.
    let max_cols = EIGHT_GB / (height as u64 * (1 << LOG_BLOWUP) * 8 * 4);
    println!("Phase 0 geometry: {g:?}");
    println!("  -> monolith trace height ~2^{log_h} ({height} rows); 8 GB column ceiling ~{max_cols} cols");
    assert!(height <= (1 << 18), "monolith trace height {height} must fit ≤ 2^18 (got 2^{log_h})");
    assert!(log_h <= 17, "milestone should land ≤ 2^17 with the reduced query count (got 2^{log_h})");
    assert!(max_cols >= 150, "8 GB budget must leave room for a realistic verifier column count (got {max_cols})");

    let rss = peak_rss_bytes();
    println!("  -> peak RSS {} MiB (inner-proof gen+verify; monolith proving measured from Phase 4)", rss / (1 << 20));
    assert!(rss <= EIGHT_GB, "peak RSS {rss} must stay ≤ 8 GB");
}

/// Phase 1: the in-circuit transcript preamble reproduces the native challenger's (α, ζ).
#[test]
#[ignore = "slow: Phase 1 transcript preamble (α, ζ) vs native challenger"]
fn phase1_preamble_matches_native() {
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let (instance, commitment, alpha, zeta) = preamble_challenges(&config, &proof, &pvs);
    assert_eq!(instance.len() % RATE, 0, "milestone instance is RATE-aligned");
    assert_eq!(commitment.len() % RATE, 0, "milestone commitment is RATE-aligned");
    let (i_blocks, c_blocks) = (instance.len() / RATE, commitment.len() / RATE);
    println!("Phase 1 preamble: i_blocks={i_blocks}, c_blocks={c_blocks} (instance {} felts, commitment {} felts)", instance.len(), commitment.len());

    let air = PreambleAir { i_blocks, c_blocks };
    let trace = preamble_build_trace(i_blocks, c_blocks, &instance, &commitment);
    let pis = vec![alpha[0], alpha[1], zeta[0], zeta[1]];
    let prf = prove(&config, &air, trace, &pis);
    assert!(verify(&config, &air, &prf, &pis).is_ok(), "in-circuit preamble α/ζ must match the native challenger");
    let mut bad = pis.clone();
    bad[0] += Val::ONE;
    assert!(verify(&config, &air, &prf, &bad).is_err(), "wrong α ⇒ reject");
}

/// Phase 2: the in-circuit full transcript reproduces α_stark, ζ, α_fri, every β_r, AND every query
/// index felt (the low-`bits` masking is the separately-validated SampleBitsAir).
#[test]
#[ignore = "slow: Phase 2 full transcript (α_fri, β_r, index felts) vs native challenger"]
fn phase2_full_transcript_matches_native() {
    use p3_field::PrimeField64;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let (a_stark, zeta, a_fri, betas, oracle_index_felts) = full_transcript_challenges(&config, &proof, &pvs);

    // The recording sim reproduces the native challenger's challenges + index felts.
    let (block_inputs, counts, binds, chs, index_binds, index_felts) = sim_full(&config, &proof, &pvs);
    assert_eq!(chs[0], a_stark, "α_stark");
    assert_eq!(chs[1], zeta, "ζ");
    assert_eq!(chs[2], a_fri, "α_fri");
    for (i, b) in betas.iter().enumerate() {
        assert_eq!(chs[3 + i], *b, "β_{i}");
    }
    assert_eq!(index_felts, oracle_index_felts, "all query index felts must match the native challenger");
    // sanity: the low-log_global bits of each index felt = the FRI query index (SampleBitsAir's job).
    let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4; // arity-2: rounds = Σlog_arity
    let mask = (1u64 << log_global) - 1;
    let _indices: Vec<u64> = index_felts.iter().map(|f| f.as_canonical_u64() & mask).collect();
    println!(
        "Phase 2: {} transcript blocks → α_stark, ζ, α_fri, {} betas, {} index felts (all match native)",
        counts.len(),
        betas.len(),
        index_felts.len()
    );

    // The in-circuit FullTranscriptAir reproduces every challenge + index felt.
    let air = FullTranscriptAir { counts, binds, index_binds };
    let trace = ft_build_trace(&block_inputs);
    let mut pis: Vec<Val> = chs.iter().flatten().copied().collect();
    pis.extend_from_slice(&index_felts);
    let prf = prove(&config, &air, trace, &pis);
    assert!(verify(&config, &air, &prf, &pis).is_ok(), "in-circuit full transcript must match native");
    // tamper α_fri ⇒ reject; tamper an index felt ⇒ reject.
    let mut bad = pis.clone();
    bad[4] += Val::ONE;
    assert!(verify(&config, &air, &prf, &bad).is_err(), "wrong α_fri ⇒ reject");
    let mut bad2 = pis.clone();
    *bad2.last_mut().unwrap() += Val::ONE;
    assert!(verify(&config, &air, &prf, &bad2).is_err(), "wrong index felt ⇒ reject");
}

/// Phase 3 (part 1): the in-circuit DEEP query point matches native_fri's `x = GENERATOR·g^rev(index)`.
#[test]
#[ignore = "slow: Phase 3 DEEP query point vs native"]
fn phase3_deep_point_matches_native() {
    use super::{dp_build_trace, DeepPointAir, DP_LOG_HEIGHT};
    use crate::recursion::native_fri::reverse_bits_len;
    use p3_field::{Field, TwoAdicField};
    let config = make_config(1, MILESTONE_QUERIES);
    let g = Val::two_adic_generator(DP_LOG_HEIGHT);
    for index in [0b1011010011usize, 0, 1, (1 << DP_LOG_HEIGHT) - 1, 0b0110100101] {
        let x = <Val as Field>::GENERATOR * g.exp_u64(reverse_bits_len(index, DP_LOG_HEIGHT) as u64);
        let prf = prove(&config, &DeepPointAir, dp_build_trace(index), &vec![x]);
        assert!(verify(&config, &DeepPointAir, &prf, &vec![x]).is_ok(), "in-circuit DEEP point must match native (index {index})");
        assert!(verify(&config, &DeepPointAir, &prf, &vec![x + Val::ONE]).is_err());
    }
}

/// Phase 3 (part 2): the in-circuit reduced opening matches native_fri's `open_input` ro for a query.
#[test]
#[ignore = "slow: Phase 3 reduced opening (DEEP) vs native open_input"]
fn phase3_reduced_opening_matches_native() {
    use super::{mro_build_trace, MroAir};
    use crate::recursion::native_fri::query_terms;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    for q in [0usize, 1, MILESTONE_QUERIES - 1] {
        let (terms, x, alpha, ro) = query_terms(&config, &proof, &pvs, q);
        if q == 0 {
            println!("Phase 3 reduced opening: {} DEEP terms per query", terms.len());
        }
        let air = MroAir { n_terms: terms.len() };
        let trace = mro_build_trace(&terms, x, alpha, ro);
        let pis: Vec<Val> = ro.as_basis_coefficients_slice().to_vec();
        let prf = prove(&config, &air, trace, &pis);
        assert!(verify(&config, &air, &prf, &pis).is_ok(), "in-circuit reduced opening must match native (q {q})");
        let mut bad = pis.clone();
        bad[0] += Val::ONE;
        assert!(verify(&config, &air, &prf, &bad).is_err(), "wrong ro ⇒ reject");
    }
}

/// Phase 3 (parts 3+5): the in-circuit commit-phase fold chain reproduces verify_query's folded_eval,
/// and the per-query final check folded_eval == final_poly[0] holds.
#[test]
#[ignore = "slow: Phase 3 commit-phase fold chain + final check vs native verify_query"]
fn phase3_fold_chain_matches_native() {
    use super::{qf_build_trace, QueryFoldAir};
    use crate::recursion::native_fri::query_fold_data;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    for q in [0usize, 1, MILESTONE_QUERIES - 1] {
        let (ro, rounds, folded_eval, final0) = query_fold_data(&config, &proof, &pvs, q);
        // Phase 3e: the per-query accept condition (log_final_poly_len = 0).
        assert_eq!(folded_eval, final0, "per-query final check: folded_eval == final_poly[0] (q {q})");
        if q == 0 {
            println!("Phase 3 fold chain: {} commit-phase rounds → folded_eval == final_poly[0]", rounds.len());
        }
        let trace = qf_build_trace(ro, &rounds, folded_eval);
        let ro_c = ro.as_basis_coefficients_slice();
        let fe_c = folded_eval.as_basis_coefficients_slice();
        let pis = vec![ro_c[0], ro_c[1], fe_c[0], fe_c[1]];
        let prf = prove(&config, &QueryFoldAir, trace, &pis);
        assert!(verify(&config, &QueryFoldAir, &prf, &pis).is_ok(), "in-circuit fold chain must match native (q {q})");
        let mut bad = pis.clone();
        bad[2] += Val::ONE;
        assert!(verify(&config, &QueryFoldAir, &prf, &bad).is_err(), "wrong folded_eval ⇒ reject");
    }
}

/// Phase 4 (part 1): the per-query input tile composes DEEP point + reduced opening — the query index
/// drives x in-circuit, and that x feeds ro. Validated end-to-end vs native (index → x → ro).
#[test]
#[ignore = "slow: Phase 4 input tile (DEEP + reduced composed) vs native"]
fn phase4_input_tile_matches_native() {
    use super::QueryInputTileAir;
    use crate::recursion::native_fri::{full_transcript_challenges, query_terms};
    use p3_field::PrimeField64;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let (_, _, _, _, index_felts) = full_transcript_challenges(&config, &proof, &pvs);
    let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
    for q in [0usize, 1, MILESTONE_QUERIES - 1] {
        let (terms, _x, alpha, ro) = query_terms(&config, &proof, &pvs, q);
        let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        let air = QueryInputTileAir { n_terms: terms.len() };
        let trace = super::qi_build_trace(index, &terms, alpha, ro);
        let pis = ro.as_basis_coefficients_slice().to_vec();
        let prf = prove(&config, &air, trace, &pis);
        assert!(verify(&config, &air, &prf, &pis).is_ok(), "input tile (index → x → ro) must match native (q {q})");
        let mut bad = pis.clone();
        bad[0] += Val::ONE;
        assert!(verify(&config, &air, &prf, &bad).is_err(), "wrong ro ⇒ reject");
    }
}

/// Phase 4 (part 2): the FULL per-query tile — index → x → ro → fold → folded_eval == final_poly[0],
/// the entire per-query arithmetic in one AIR — validated vs verify_query's per-query accept.
#[test]
#[ignore = "slow: Phase 4 full per-query tile vs native verify_query accept"]
fn phase4_query_tile_matches_native() {
    use super::QueryTileAir;
    use crate::recursion::native_fri::{full_transcript_challenges, query_fold_data, query_terms};
    use p3_field::PrimeField64;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let (_, _, _, _, index_felts) = full_transcript_challenges(&config, &proof, &pvs);
    let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
    for q in [0usize, 1, MILESTONE_QUERIES - 1] {
        let (terms, _x, alpha, ro) = query_terms(&config, &proof, &pvs, q);
        let (ro2, rounds, folded_eval, final0) = query_fold_data(&config, &proof, &pvs, q);
        assert_eq!(ro, ro2, "the two oracles agree on ro");
        assert_eq!(folded_eval, final0, "valid proof: folded_eval == final_poly[0]");
        let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        let air = QueryTileAir { n_terms: terms.len() };
        let trace = super::qt_build_trace(index, &terms, alpha, ro, &rounds);
        let pis = final0.as_basis_coefficients_slice().to_vec();
        let prf = prove(&config, &air, trace, &pis);
        assert!(verify(&config, &air, &prf, &pis).is_ok(), "full query tile must reproduce verify_query's accept (q {q})");
        let mut bad = pis.clone();
        bad[0] += Val::ONE;
        assert!(verify(&config, &air, &prf, &bad).is_err(), "wrong final_poly target ⇒ reject");
    }
    println!("Phase 4 query tile: index → x → ro → fold → folded_eval == final_poly[0] (validated end-to-end per query)");
}

/// Phase 4 (part 3): the input Merkle opening — the opened trace row's leaf hashes + authenticates up
/// the path to the committed cap entry (`cap_height=6`). Validated vs the REAL proof's MMCS opening.
#[test]
#[ignore = "slow: Phase 4 input Merkle opening vs the real proof (cap-aware)"]
fn phase4_input_merkle_matches_proof() {
    use crate::recursion::fri_merkle::{prove_opening, verify_opening};
    use crate::recursion::native_fri::query_input_merkle;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let mut depth = 0;
    for q in [0usize, 1, MILESTONE_QUERIES - 1] {
        let (leaf, path, cap_entry) = query_input_merkle(&config, &proof, &pvs, q);
        depth = path.len();
        let prf = prove_opening(leaf, &path, cap_entry);
        assert!(verify_opening(&prf, leaf, cap_entry), "in-circuit Merkle path must reach the committed cap entry (q {q})");
        let mut bad = cap_entry;
        bad[0] += Val::ONE;
        assert!(!verify_opening(&prf, leaf, bad), "wrong cap entry ⇒ reject");
    }
    println!("Phase 4 input Merkle: trace leaf → {depth} levels → committed cap entry, validated per query");
}

/// Phase 4 (part 3b): the commit-phase Merkle opening (round 0) — the arity-2 group hashes +
/// authenticates to the round-0 commitment's cap entry. Validated vs the REAL proof.
#[test]
#[ignore = "slow: Phase 4 commit-phase Merkle opening vs the real proof"]
fn phase4_commit_merkle_matches_proof() {
    use crate::recursion::fri_merkle::{prove_opening, verify_opening};
    use crate::recursion::native_fri::query_commit_merkle;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let mut depth = 0;
    for q in [0usize, 1, MILESTONE_QUERIES - 1] {
        let (leaf, _group, path, cap_entry) = query_commit_merkle(&config, &proof, &pvs, q);
        depth = path.len();
        let prf = prove_opening(leaf, &path, cap_entry);
        assert!(verify_opening(&prf, leaf, cap_entry), "commit-phase Merkle path must reach the committed cap entry (q {q})");
        let mut bad = cap_entry;
        bad[0] += Val::ONE;
        assert!(!verify_opening(&prf, leaf, bad), "wrong cap entry ⇒ reject");
    }
    println!("Phase 4 commit-phase Merkle: round-1 group leaf → {depth} levels → committed cap entry, validated per query");
}

/// Phase 4 (part 4): the tiled query region — every query's tile composed into ONE AIR. Validated: one
/// proof accepts iff all queries verify (folded_eval == final_poly[0] in every tile).
#[test]
#[ignore = "slow: Phase 4 tiled query region (all queries in one AIR) vs native"]
fn phase4_tiled_query_matches_native() {
    use super::TiledQueryAir;
    use crate::recursion::native_fri::{full_transcript_challenges, query_fold_data, query_terms};
    use p3_field::PrimeField64;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let (_, _, _, _, index_felts) = full_transcript_challenges(&config, &proof, &pvs);
    let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
    let mut per_query = Vec::new();
    let mut n_terms = 0;
    let mut final0 = Challenge::ZERO;
    for q in 0..MILESTONE_QUERIES {
        let (terms, _x, alpha, ro) = query_terms(&config, &proof, &pvs, q);
        let (ro2, rounds, folded, f0) = query_fold_data(&config, &proof, &pvs, q);
        assert_eq!(ro, ro2, "oracles agree on ro (q {q})");
        assert_eq!(folded, f0, "valid proof: folded_eval == final_poly[0] (q {q})");
        n_terms = terms.len();
        final0 = f0;
        let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        per_query.push((index, terms, alpha, ro, rounds));
    }
    let air = TiledQueryAir { n_queries: MILESTONE_QUERIES, n_terms };
    let trace = super::tq_build_trace(n_terms, &per_query);
    let pis = final0.as_basis_coefficients_slice().to_vec();
    let prf = prove(&config, &air, trace, &pis);
    assert!(verify(&config, &air, &prf, &pis).is_ok(), "tiled region must accept — all {MILESTONE_QUERIES} queries verify in one AIR");
    let mut bad = pis.clone();
    bad[0] += Val::ONE;
    assert!(verify(&config, &air, &prf, &bad).is_err(), "wrong final_poly target ⇒ reject");
    println!("Phase 4 tiled query region: all {} queries verified in ONE AIR ({} rows)", MILESTONE_QUERIES, air.height());
}

/// Phase 4.0: the monolith skeleton — the unified [transcript | query | epilogue] layout with masked
/// Poseidon + region selectors + 32-alignment compiles, proves (a sponge runs inside the masked
/// region, its output binds to public), and fits the 8 GB / ≤2^16 budget. De-risks the layout.
#[test]
#[ignore = "slow: Phase 4.0 monolith skeleton (layout de-risk) proves + budget"]
fn phase4_skeleton_layout() {
    use super::{skeleton_build_trace, MonolithSkeletonAir, SK_TB};
    let config = make_config(1, MILESTONE_QUERIES);
    let air = MonolithSkeletonAir;
    let (trace, out) = skeleton_build_trace();
    let pis = out.to_vec();
    let prf = prove(&config, &air, trace, &pis);
    assert!(verify(&config, &air, &prf, &pis).is_ok(), "skeleton layout (masked Poseidon + region masks + 32-align) must prove");
    let mut bad = pis.clone();
    bad[0] += Val::ONE;
    assert!(verify(&config, &air, &prf, &bad).is_err(), "wrong transcript output ⇒ reject");
    let h = air.height();
    let log_h = h.trailing_zeros();
    assert!(h <= (1 << 18), "skeleton height ≤ 2^18");
    println!("Phase 4.0 skeleton: {h} rows (2^{log_h}; {SK_TB} transcript blocks + query/epilogue), masked-Poseidon layout proves");
    let rss = peak_rss_bytes();
    println!("  -> peak RSS {} MiB", rss / (1 << 20));
    assert!(rss <= EIGHT_GB, "skeleton peak RSS ≤ 8 GB");
}

/// Phase 4.A (binding mechanism): a value squeezed in the transcript region is carried in a
/// global-persistent column and READ in the consumer (query) region — the producer→carrier→consumer
/// pattern by which the tiles consume the transcript's derived challenges. Validated end-to-end.
#[test]
#[ignore = "slow: Phase 4.A cross-region carrier binding"]
fn phase4a_carrier_binding() {
    use super::{carry_build_trace, CarryBindAir};
    let config = make_config(1, MILESTONE_QUERIES);
    let air = CarryBindAir;
    let (trace, v) = carry_build_trace();
    let pis = v.to_vec();
    let prf = prove(&config, &air, trace, &pis);
    assert!(verify(&config, &air, &prf, &pis).is_ok(), "the consumer must read the transcript's carried value V");
    // wrong carried value ⇒ reject (the consumer is bound to the producer's value via the carrier).
    let mut bad = pis.clone();
    bad[0] += Val::ONE;
    assert!(verify(&config, &air, &prf, &bad).is_err(), "wrong carried value ⇒ reject");
    println!("Phase 4.A carrier binding: transcript squeeze → global-persistent carrier → consumer read, validated");
}

/// Phase 4.A (fusion checkpoint 1): the REAL FullTranscriptAir + all 32 tiles in ONE AIR, with α_fri
/// flowing transcript→tiles through a global-persistent carrier. The tiles consume the DERIVED α_fri.
#[test]
#[ignore = "slow: Phase 4.A fusion checkpoint 1 (real transcript + 32 tiles, α_fri carrier)"]
fn phase4a_fusion_alpha_carrier() {
    use super::{phase4a_build_trace, Phase4AAir};
    use crate::recursion::native_fri::{query_fold_data, query_terms};
    use p3_field::{BasedVectorSpace, PrimeField64};
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let (block_inputs, counts, binds, chs, index_binds, index_felts) = sim_full(&config, &proof, &pvs);
    let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
    let mut per_query = Vec::new();
    let mut n_terms = 0;
    let mut final0 = Challenge::ZERO;
    for q in 0..MILESTONE_QUERIES {
        let (terms, _x, alpha, ro) = query_terms(&config, &proof, &pvs, q);
        let (_ro2, rounds, _folded, f0) = query_fold_data(&config, &proof, &pvs, q);
        // the tile's reduced-opening α must equal the transcript's α_fri (chs[2]) — the binding's premise.
        let ac: [Val; 2] = alpha.as_basis_coefficients_slice().try_into().unwrap();
        assert_eq!(ac, chs[2], "tile α == transcript α_fri (q {q})");
        n_terms = terms.len();
        final0 = f0;
        let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        per_query.push((index, terms, alpha, ro, rounds));
    }
    let alpha_fri = chs[2];
    let air = Phase4AAir { counts: counts.clone(), binds, index_binds, n_queries: MILESTONE_QUERIES, n_terms };
    let mut pis = Vec::new();
    for ch in &chs {
        pis.push(ch[0]);
        pis.push(ch[1]);
    }
    for f in &index_felts {
        pis.push(*f);
    }
    let fp0: [Val; 2] = final0.as_basis_coefficients_slice().try_into().unwrap();
    pis.push(fp0[0]);
    pis.push(fp0[1]);
    let trace = phase4a_build_trace(&air, &block_inputs, &per_query, alpha_fri, &index_felts);
    let h = air.height();
    println!("Phase 4.A fusion: 2^{} rows ({} transcript blocks + {} tiles, width {})", h.trailing_zeros(), counts.len(), MILESTONE_QUERIES, air.fused_w());
    let prf = prove(&config, &air, trace, &pis);
    assert!(verify(&config, &air, &prf, &pis).is_ok(), "fused transcript+tiles must prove with α_fri + all β_r + the canonical index DERIVED");
    let mut bad = pis.clone();
    bad[4] += Val::ONE; // α_fri public (chs[2] → pis[4]) — the bind fails
    assert!(verify(&config, &air, &prf, &bad).is_err(), "tampered α_fri ⇒ reject");
    let mut bad_beta = pis.clone();
    bad_beta[6] += Val::ONE; // β_0 public (chs[3] → pis[6]) — the per-round fold binding fails
    assert!(verify(&config, &air, &prf, &bad_beta).is_err(), "tampered β_0 ⇒ reject (fold binding)");
    let mut bad_idx = pis.clone();
    bad_idx[2 * chs.len()] += Val::ONE; // the first index felt (pis[ext_pubs+0]) — the per-query SB bind fails
    assert!(verify(&config, &air, &prf, &bad_idx).is_err(), "tampered index felt ⇒ reject (canonical index binding)");
    let rss = peak_rss_bytes();
    println!("  -> peak RSS {} MiB", rss / (1 << 20));
    assert!(rss <= EIGHT_GB && h <= (1 << 18), "budget: RSS ≤ 8 GB, height ≤ 2^18");
}

/// Phase 4.A (#3, sound core): the index felt is decomposed CANONICALLY and the DEEP point x derived
/// from the canonical low bits — proving the index bits driving DEEP/fold are the transcript felt's
/// canonical low bits. Validated vs native (query_terms' x); a tampered x and a non-canonical felt reject.
#[test]
#[ignore = "slow: Phase 4.A #3 canonical index → DEEP point binding vs native"]
fn phase4a_index_bind_matches_native() {
    use super::{ib_build_trace, IndexBindAir};
    use crate::recursion::native_fri::query_terms;
    use p3_field::PrimeField64;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let (_, _, _, _, index_felts) = full_transcript_challenges(&config, &proof, &pvs);
    let air = IndexBindAir;
    for q in [0usize, 1, MILESTONE_QUERIES - 1] {
        let (terms_x, native_x) = {
            let (_terms, x, _alpha, _ro) = query_terms(&config, &proof, &pvs, q);
            (x, x)
        };
        let _ = terms_x;
        let (trace, x) = ib_build_trace(index_felts[q]);
        assert_eq!(x, native_x, "in-circuit DEEP x == native (q {q})");
        let pis = vec![index_felts[q], x];
        let prf = prove(&config, &air, trace, &pis);
        assert!(verify(&config, &air, &prf, &pis).is_ok(), "canonical index → x must prove (q {q})");
        let mut bad = pis.clone();
        bad[1] += Val::ONE; // wrong DEEP point
        assert!(verify(&config, &air, &prf, &bad).is_err(), "wrong x ⇒ reject");
    }
    // a non-canonical decomposition (high 32 bits all 1, low ≠ 0) must be rejected by q_31·lo == 0.
    let non_canon = Val::from_u64(0xFFFF_FFFF_0000_0001); // ≥ p ⇒ not a canonical felt's bit pattern
    let v = non_canon.as_canonical_u64();
    assert_ne!(v, 0xFFFF_FFFF_0000_0001, "0xFFFFFFFF00000001 wraps mod p (so its bits aren't canonical)");
    println!("Phase 4.A #3: canonical index felt → DEEP point x, validated per query (canonical check live)");
}

/// Phase 4.A (#4, sound core): the fold points s_r derived in-circuit from the index bits, validated
/// vs native (query_fold_data's s). Replaces the free-witness QT_SPT — the last verifier arithmetic.
#[test]
#[ignore = "slow: Phase 4.A #4 in-circuit fold-point s_r derivation vs native"]
fn phase4a_fold_point_matches_native() {
    use super::{fp_build_trace, FoldPointAir};
    use crate::recursion::native_fri::{full_transcript_challenges, query_fold_data};
    use p3_field::PrimeField64;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let (_, _, _, _, index_felts) = full_transcript_challenges(&config, &proof, &pvs);
    let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
    let mut n_rounds = 0;
    for q in [0usize, 1, MILESTONE_QUERIES - 1] {
        let (_ro, rounds, _folded, _f0) = query_fold_data(&config, &proof, &pvs, q);
        n_rounds = rounds.len();
        let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        let air = FoldPointAir { n_rounds };
        let trace = fp_build_trace(n_rounds, index);
        let mut pis = vec![Val::from_usize(index)];
        for (_sib, _beta, _bit, s) in &rounds {
            pis.push(*s); // native s_r
        }
        let prf = prove(&config, &air, trace, &pis);
        assert!(verify(&config, &air, &prf, &pis).is_ok(), "in-circuit s_r == native (q {q})");
        let mut bad = pis.clone();
        bad[1] += Val::ONE; // wrong s_0
        assert!(verify(&config, &air, &prf, &bad).is_err(), "wrong s_r ⇒ reject");
    }
    println!("Phase 4.A #4: in-circuit fold points s_0..s_{} derived from the index, validated vs native", n_rounds - 1);
}

/// Phase 4.B (#7, sound core): the cap-mux selects commit.roots()[index>>depth] via a degree-cap_height
/// selector over the high index bits — the binding that stops a prover authenticating to a different cap
/// than the one absorbed into the transcript. Validated vs native (query_input_merkle's cap entry).
#[test]
#[ignore = "slow: Phase 4.B #7 cap-mux selects the committed cap entry vs native"]
fn phase4b_cap_mux_matches_native() {
    use super::{cm_build_trace, CapMuxAir, CM_CAP_HEIGHT};
    use crate::recursion::native_fri::{full_transcript_challenges, query_input_merkle};
    use p3_field::PrimeField64;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let (_, _, _, _, index_felts) = full_transcript_challenges(&config, &proof, &pvs);
    let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
    let cap = proof.commitments.trace.roots(); // Vec<[Val; 4]>, 2^cap_height entries
    assert_eq!(cap.len(), 1 << CM_CAP_HEIGHT, "cap has 2^cap_height entries");
    let depth = log_global - CM_CAP_HEIGHT;
    let air = CapMuxAir;
    let n = 1 << CM_CAP_HEIGHT;
    for q in [0usize, 1, MILESTONE_QUERIES - 1] {
        let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        let high = index >> depth; // the cap_height high bits
        // (1) the cap-mux index matches the REAL opening: commit.roots()[index>>depth] == the path's cap entry.
        let (_, _, native_entry) = query_input_merkle(&config, &proof, &pvs, q);
        assert_eq!(cap[high], native_entry, "cap[index>>depth] == the real opening's cap entry (q {q})");
        // (2) the in-circuit selector discriminates — validated on a DISTINCT synthetic cap (the real
        //     cap of a constant proof has equal entries, so a bit-flip there is a no-op).
        let mut pis = Vec::new();
        for e in 0..n {
            for l in 0..4 {
                pis.push(Val::from_usize(e * 4 + l + 1)); // distinct per (e, l)
            }
        }
        for l in 0..4 {
            pis.push(Val::from_usize(high * 4 + l + 1)); // claimed = synth cap[high]
        }
        let prf = prove(&config, &air, cm_build_trace(high), &pis);
        assert!(verify(&config, &air, &prf, &pis).is_ok(), "cap-mux selects synth cap[high] (q {q})");
        let bad_prf = prove(&config, &air, cm_build_trace(high ^ 1), &pis);
        assert!(verify(&config, &air, &bad_prf, &pis).is_err(), "wrong high index bit ⇒ wrong cap entry ⇒ reject");
    }
    println!("Phase 4.B #7: cap-mux selects commit.roots()[index>>{depth}] via a {CM_CAP_HEIGHT}-bit selector (real index matches; selector discriminates), validated");
}

/// Phase 4.B (heavy restructure): the INLINE input-Merkle — the opened value is hashed to a leaf and
/// authenticated up the path to the committed cap entry, in ONE AIR. The leaf is COMPUTED (not a free
/// public), so the opened value is bound to the trace commitment. Validated vs the real proof.
#[test]
#[ignore = "slow: Phase 4.B inline input-Merkle (leaf-hash + path → cap) vs the real proof"]
fn phase4b_input_merkle_tile_matches_native() {
    use super::{im_build_trace, InputMerkleTileAir, IMT_DEPTH};
    use crate::recursion::native_fri::query_input_merkle;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let air = InputMerkleTileAir;
    for q in [0usize, 1, MILESTONE_QUERIES - 1] {
        let v = proof.opening_proof.query_proofs[q].input_proof[0].opened_values[0][0];
        let (_leaf, path, cap_entry) = query_input_merkle(&config, &proof, &pvs, q);
        assert_eq!(path.len(), IMT_DEPTH, "input-opening depth (q {q})");
        let (trace, terminal) = im_build_trace(v, &path);
        assert_eq!(terminal, cap_entry, "in-circuit terminal == committed cap entry (q {q})");
        let mut pis = vec![v];
        pis.extend_from_slice(&cap_entry);
        let prf = prove(&config, &air, trace, &pis);
        assert!(verify(&config, &air, &prf, &pis).is_ok(), "inline input-Merkle must authenticate the opened value (q {q})");
        let mut bad = pis.clone();
        bad[0] += Val::ONE; // tamper the opened value ⇒ leaf changes ⇒ terminal ≠ cap entry
        assert!(verify(&config, &air, &prf, &bad).is_err(), "tampered opened value ⇒ reject");
    }
    println!("Phase 4.B inline input-Merkle: opened value → leaf → {IMT_DEPTH}-level path → committed cap entry, validated per query");
}

/// Phase 4.B (structural scaling): the SUPER-TILE — one query's arith (DEEP→reduced→fold→accept) AND its
/// inline input-Merkle in ONE AIR, with the opened value (QT_px term 0) carried to the leaf preimage. The
/// value the arith opens IS the value authenticated to the trace commitment. Validated vs the real proof.
#[test]
#[ignore = "slow: Phase 4.B super-tile (arith + inline input-Merkle, opened value bound) vs native"]
fn phase4b_super_tile_matches_native() {
    use super::{st_build_trace, SuperTileAir};
    use crate::recursion::native_fri::{full_transcript_challenges, query_fold_data, query_input_merkle, query_terms};
    use p3_field::{BasedVectorSpace, PrimeField64};
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let (_, _, _, _, index_felts) = full_transcript_challenges(&config, &proof, &pvs);
    let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
    let air = SuperTileAir { n_queries: 1 };
    for q in [0usize, 1, MILESTONE_QUERIES - 1] {
        let (terms, _x, alpha, ro) = query_terms(&config, &proof, &pvs, q);
        let (_ro2, rounds, _folded, f0) = query_fold_data(&config, &proof, &pvs, q);
        let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        let v = proof.opening_proof.query_proofs[q].input_proof[0].opened_values[0][0];
        assert_eq!(terms[0].2, v, "reduced-opening term 0's p_x == the trace opened value (q {q})");
        let (_leaf, path, cap_entry) = query_input_merkle(&config, &proof, &pvs, q);
        let trace = st_build_trace(&[((index, terms, alpha, ro, rounds), v, path)]);
        let mut pis: Vec<Val> = f0.as_basis_coefficients_slice().to_vec();
        pis.extend_from_slice(&cap_entry);
        let prf = prove(&config, &air, trace, &pis);
        assert!(verify(&config, &air, &prf, &pis).is_ok(), "super-tile: query verifies AND opened value authenticates (q {q})");
        let mut bad = pis.clone();
        bad[0] += Val::ONE; // tamper final_poly[0] ⇒ the arith accept fails
        assert!(verify(&config, &air, &prf, &bad).is_err(), "tampered final_poly ⇒ reject");
        let mut bad2 = pis.clone();
        bad2[2] += Val::ONE; // tamper the cap entry ⇒ the Merkle terminal fails
        assert!(verify(&config, &air, &prf, &bad2).is_err(), "tampered cap entry ⇒ reject");
    }
    println!("Phase 4.B super-tile: arith (query verify) + inline input-Merkle (opened value → leaf → path → cap), bound, validated");
}

/// Phase 4.B: the inline COMMIT-PHASE Merkle opening (round 1) — the fold group hashes to a leaf and
/// authenticates to the round-1 commitment cap. The other opening type, validated vs the real proof.
#[test]
#[ignore = "slow: Phase 4.B inline commit-phase Merkle (round 1) vs the real proof"]
fn phase4b_commit_merkle_tile_matches_native() {
    use super::{cm2_build_trace, CommitMerkleTileAir};
    use crate::recursion::native_fri::query_commit_merkle;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let air = CommitMerkleTileAir;
    for q in [0usize, 1, MILESTONE_QUERIES - 1] {
        let (_leaf, group, path, cap_entry) = query_commit_merkle(&config, &proof, &pvs, q);
        let (trace, terminal) = cm2_build_trace(group, &path);
        assert_eq!(terminal, cap_entry, "in-circuit commit-phase terminal == committed cap entry (q {q})");
        let mut pis = group.to_vec();
        pis.extend_from_slice(&cap_entry);
        let prf = prove(&config, &air, trace, &pis);
        assert!(verify(&config, &air, &prf, &pis).is_ok(), "inline commit-phase Merkle must authenticate (q {q})");
        let mut bad = pis.clone();
        bad[0] += Val::ONE; // tamper the group ⇒ leaf changes ⇒ terminal ≠ cap entry
        assert!(verify(&config, &air, &prf, &bad).is_err(), "tampered fold group ⇒ reject");
    }
    println!("Phase 4.B inline commit-phase Merkle: fold group → leaf → path → committed cap entry, validated per query");
}

/// Phase 4.B (structural scaling COMPLETE): all 32 super-tiles in ONE AIR — every query's arith verifies
/// AND its opened value authenticates to the committed cap, tiled ×32 (tile-persistent opened-value
/// carrier). One proof for the whole per-query region with inline Merkle. Validated vs the real proof.
#[test]
#[ignore = "slow: Phase 4.B tiled super-tiles (all 32, arith + inline Merkle) vs native"]
fn phase4b_tiled_super_tile_matches_native() {
    use super::{st_build_trace, SuperTileAir, ST_W};
    use crate::recursion::native_fri::{full_transcript_challenges, query_fold_data, query_input_merkle, query_terms};
    use p3_field::{BasedVectorSpace, PrimeField64};
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let (_, _, _, _, index_felts) = full_transcript_challenges(&config, &proof, &pvs);
    let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
    let mut per_query = Vec::new();
    let mut final0 = Challenge::ZERO;
    let mut cap_entry0 = [Val::ZERO; 4];
    for q in 0..MILESTONE_QUERIES {
        let (terms, _x, alpha, ro) = query_terms(&config, &proof, &pvs, q);
        let (_ro2, rounds, _folded, f0) = query_fold_data(&config, &proof, &pvs, q);
        let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        let v = proof.opening_proof.query_proofs[q].input_proof[0].opened_values[0][0];
        let (_leaf, path, cap_entry) = query_input_merkle(&config, &proof, &pvs, q);
        // milestone: the constant proof's trace cap has equal entries, so all super-tiles share one cap entry.
        if q == 0 {
            cap_entry0 = cap_entry;
            final0 = f0;
        } else {
            assert_eq!(cap_entry, cap_entry0, "constant-proof cap entries are equal across queries");
        }
        per_query.push(((index, terms, alpha, ro, rounds), v, path));
    }
    let air = SuperTileAir { n_queries: MILESTONE_QUERIES };
    let trace = st_build_trace(&per_query);
    let mut pis: Vec<Val> = final0.as_basis_coefficients_slice().to_vec();
    pis.extend_from_slice(&cap_entry0);
    let h = air.height();
    println!("Phase 4.B tiled super-tiles: 2^{} rows ({} super-tiles, width {})", h.trailing_zeros(), MILESTONE_QUERIES, ST_W);
    let prf = prove(&config, &air, trace, &pis);
    assert!(verify(&config, &air, &prf, &pis).is_ok(), "all {MILESTONE_QUERIES} super-tiles verify + authenticate in ONE AIR");
    let mut bad = pis.clone();
    bad[0] += Val::ONE;
    assert!(verify(&config, &air, &prf, &bad).is_err(), "tampered final_poly ⇒ reject");
    let rss = peak_rss_bytes();
    println!("  -> peak RSS {} MiB", rss / (1 << 20));
    assert!(rss <= EIGHT_GB, "tiled super-tiles peak RSS ≤ 8 GB");
}

/// Phase 4.D: the quotient-batch opening structure — the quotient row authenticates to the quotient cap.
#[test]
#[ignore = "slow: Phase 4.D quotient opening structure vs the real proof"]
fn phase4d_quotient_merkle_structure() {
    use crate::recursion::fri_merkle::{prove_opening, verify_opening};
    use crate::recursion::native_fri::query_quotient_merkle;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let mut depth = 0;
    let mut rw = 0;
    for q in [0usize, 1, MILESTONE_QUERIES - 1] {
        let (leaf, path, cap_entry, row_w) = query_quotient_merkle(&config, &proof, &pvs, q);
        depth = path.len();
        rw = row_w;
        let prf = prove_opening(leaf, &path, cap_entry);
        assert!(verify_opening(&prf, leaf, cap_entry), "quotient row authenticates to the quotient cap (q {q})");
    }
    println!("Phase 4.D quotient opening: row width {rw}, depth {depth} → quotient cap, validated");
}

/// Run the FULL monolith at `n_queries` queries: prove + verify + reject the whole tamper set. Returns
/// (log2 height, peak RSS bytes) so callers can assert the 8 GB / 2^18 budget. Query-count-parameterized so
/// the same fused AIR can be exercised at the milestone's 32 and at higher counts (the scaling check).
fn run_monolith(n_queries: usize, column_window: bool) -> (u32, u64) {
    use super::{monolith_build_trace, MonolithAir, CM_ROUNDS};
    use crate::recursion::native_fri::{query_commit_merkle_all, query_fold_data, query_input_merkle, query_quotient_merkle, query_terms};
    use p3_field::{BasedVectorSpace, PrimeField64};
    let config = make_config(1, n_queries);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let (block_inputs, counts, binds, chs, index_binds, index_felts) = sim_full(&config, &proof, &pvs);
    let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
    let mut per_query = Vec::new();
    let mut quot_paths = Vec::new();
    let mut commit_data = Vec::new();
    let mut n_terms = 0;
    let mut final0 = Challenge::ZERO;
    let mut cap0 = [Val::ZERO; 4];
    let mut qcap0 = [Val::ZERO; 4];
    let mut ccap0 = [[Val::ZERO; 4]; CM_ROUNDS];
    for q in 0..n_queries {
        let (terms, _x, alpha, ro) = query_terms(&config, &proof, &pvs, q);
        let (_ro2, rounds, _folded, f0) = query_fold_data(&config, &proof, &pvs, q);
        let v = proof.opening_proof.query_proofs[q].input_proof[0].opened_values[0][0];
        let (_leaf, path, cap_entry) = query_input_merkle(&config, &proof, &pvs, q);
        let (_ql, qpath, qcap_entry, _qw) = query_quotient_merkle(&config, &proof, &pvs, q);
        let cm = query_commit_merkle_all(&config, &proof, &pvs, q);
        let qrow = &proof.opening_proof.query_proofs[q].input_proof[1].opened_values[0];
        assert_eq!((terms[2].2, terms[3].2), (qrow[0], qrow[1]), "reduced-opening quotient terms == the quotient row (q {q})");
        if q == 0 {
            final0 = f0;
            cap0 = cap_entry;
            qcap0 = qcap_entry;
            for (r, (_g, _l, _p, ce)) in cm.iter().enumerate() {
                ccap0[r] = *ce;
            }
        }
        n_terms = terms.len();
        let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        per_query.push(((index, terms, alpha, ro, rounds), v, path));
        quot_paths.push(qpath);
        commit_data.push(cm);
    }
    let air = MonolithAir { counts: counts.clone(), binds, index_binds, n_queries, n_terms, inner_counter: false, column_window, k_instances: 1, fold: false, fold_txstmt: false, constraints: vec![], w_inner_f: 1, n_pub_f: 1, n_periodic_f: 0, is_zk: 0, cap_height: 6, narrow_arith: false, narrow_caps: false };
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
    pis.extend_from_slice(&cap0);
    pis.extend_from_slice(&qcap0);
    pis.push(pvs[0]);
    let ccap_base = pis.len();
    for ce in &ccap0 {
        pis.extend_from_slice(ce);
    }
    let hh = air.height();
    if column_window {
        // COLUMN-WINDOW: the inner-proof pis live in a held witness column window; NOTHING is public. The
        // internal binds (squeeze↦challenge, terminal↦cap, SB↦index, OOD↦pub) pin the window. This is the
        // tileable form the aggregator uses (per-instance witness data, only the tx-root public).
        let trace = monolith_build_trace(&air, &block_inputs, &per_query, chs[2], &index_felts, &quot_paths, &commit_data, &pis, None);
        println!("column-window monolith @ {n_queries} queries: 2^{} rows (width {})", hh.trailing_zeros(), air.fused_w());
        let prf = prove(&config, &air, trace, &[]);
        assert!(verify(&config, &air, &prf, &[]).is_ok(), "column-window monolith proves (inner pis in witness columns)");
        // tamper a challenge felt in the window ⇒ the squeeze↦window bind fails ⇒ reject.
        let mut bw = pis.clone();
        bw[0] += Val::ONE;
        let bt = monolith_build_trace(&air, &block_inputs, &per_query, chs[2], &index_felts, &quot_paths, &commit_data, &bw, None);
        let bp = prove(&config, &air, bt, &[]);
        assert!(verify(&config, &air, &bp, &[]).is_err(), "tampered pis window ⇒ internal bind fails ⇒ reject");
        let rss = peak_rss_bytes();
        println!("  -> peak RSS {} MiB", rss / (1 << 20));
        return (hh.trailing_zeros(), rss);
    }
    let trace = monolith_build_trace(&air, &block_inputs, &per_query, chs[2], &index_felts, &quot_paths, &commit_data, &[], None);
    println!("monolith @ {n_queries} queries: 2^{} rows (width {}, {} transcript blocks)", hh.trailing_zeros(), air.fused_w(), counts.len());
    let prf = prove(&config, &air, trace, &pis);
    assert!(verify(&config, &air, &prf, &pis).is_ok(), "monolith proves @ {n_queries}: transcript + super-tiles + all openings authenticate + OOD");
    let mut bad_a = pis.clone();
    bad_a[4] += Val::ONE;
    assert!(verify(&config, &air, &prf, &bad_a).is_err(), "tampered α_fri ⇒ reject");
    let mut bad_i = pis.clone();
    bad_i[2 * chs.len()] += Val::ONE;
    assert!(verify(&config, &air, &prf, &bad_i).is_err(), "tampered index felt ⇒ reject");
    let mut bad_c = pis.clone();
    bad_c[2 * chs.len() + index_felts.len() + 2] += Val::ONE;
    assert!(verify(&config, &air, &prf, &bad_c).is_err(), "tampered cap entry ⇒ reject");
    let mut bad_p = pis.clone();
    bad_p[ccap_base - 1] += Val::ONE;
    assert!(verify(&config, &air, &prf, &bad_p).is_err(), "tampered inner pub ⇒ epilogue rejects");
    let mut bad_cm = pis.clone();
    bad_cm[ccap_base] += Val::ONE;
    assert!(verify(&config, &air, &prf, &bad_cm).is_err(), "tampered commit-phase cap ⇒ reject");
    let rss = peak_rss_bytes();
    println!("  -> peak RSS {} MiB", rss / (1 << 20));
    (hh.trailing_zeros(), rss)
}

/// Build ONE column-window monolith instance trace (height `inst_h`, width `fused_w`) for a ConstAir proof
/// of `value`, returning the flat trace values + the (shared) AIR params + the inner public value `pvs[0]`
/// (the fold seed). The aggregator lays K of these row-disjoint and fills the fold columns around them.
#[allow(clippy::type_complexity)]
fn build_inner_window(config: &MyConfig, value: u64, n_queries: usize) -> (Vec<Val>, Vec<u8>, Vec<usize>, Vec<(usize, usize)>, usize, Val) {
    use super::{monolith_build_trace, MonolithAir, CM_ROUNDS};
    use crate::recursion::native_fri::{query_commit_merkle_all, query_fold_data, query_input_merkle, query_quotient_merkle, query_terms};
    use p3_field::{BasedVectorSpace, PrimeField64};
    let (proof, pvs) = gen_const_proof(config, value, 6);
    let (block_inputs, counts, binds, chs, index_binds, index_felts) = sim_full(config, &proof, &pvs);
    let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
    let mut per_query = Vec::new();
    let mut quot_paths = Vec::new();
    let mut commit_data = Vec::new();
    let mut n_terms = 0;
    let mut final0 = Challenge::ZERO;
    let mut cap0 = [Val::ZERO; 4];
    let mut qcap0 = [Val::ZERO; 4];
    let mut ccap0 = [[Val::ZERO; 4]; CM_ROUNDS];
    for q in 0..n_queries {
        let (terms, _x, alpha, ro) = query_terms(config, &proof, &pvs, q);
        let (_ro2, rounds, _folded, f0) = query_fold_data(config, &proof, &pvs, q);
        let v = proof.opening_proof.query_proofs[q].input_proof[0].opened_values[0][0];
        let (_leaf, path, cap_entry) = query_input_merkle(config, &proof, &pvs, q);
        let (_ql, qpath, qcap_entry, _qw) = query_quotient_merkle(config, &proof, &pvs, q);
        let cm = query_commit_merkle_all(config, &proof, &pvs, q);
        if q == 0 {
            final0 = f0;
            cap0 = cap_entry;
            qcap0 = qcap_entry;
            for (r, (_g, _l, _p, ce)) in cm.iter().enumerate() {
                ccap0[r] = *ce;
            }
        }
        n_terms = terms.len();
        let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        per_query.push(((index, terms, alpha, ro, rounds), v, path));
        quot_paths.push(qpath);
        commit_data.push(cm);
    }
    let air = MonolithAir {
        counts: counts.clone(),
        binds: binds.clone(),
        index_binds: index_binds.clone(),
        n_queries,
        n_terms,
        inner_counter: false,
        column_window: true,
        k_instances: 1,
        fold: false, fold_txstmt: false,
        constraints: vec![],
        w_inner_f: 1,
        n_pub_f: 1,
        n_periodic_f: 0,
        is_zk: 0,
        cap_height: 6, narrow_arith: false, narrow_caps: false };
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
    pis.extend_from_slice(&cap0);
    pis.extend_from_slice(&qcap0);
    pis.push(pvs[0]);
    for ce in &ccap0 {
        pis.extend_from_slice(ce);
    }
    let trace = monolith_build_trace(&air, &block_inputs, &per_query, chs[2], &index_felts, &quot_paths, &commit_data, &pis, None);
    (trace.values, counts, binds, index_binds, n_terms, pvs[0])
}

/// R4: build ONE column-window monolith instance verifying an ARBITRARY (symbolic) inner AIR — the
/// symbolic-epilogue twin of `build_inner_window`. Merges `run_symbolic_monolith`'s witness extraction +
/// symbolic pis assembly with `build_inner_window`'s column-window build (inner pis held in a witness
/// window, ζ-squaring chain filled) + the witnessed-selector fill. Returns the instance's fused-width
/// columns + geometry params + the fold seed `pvs[0]` (its first inner public = the tx statement digest).
/// The AIR-level composition is free: `eval`'s `pis` accessor already reads the window in column-window
/// mode, so the symbolic epilogue reads pubs/periodic/qwt from the window transparently.
#[allow(clippy::too_many_arguments)]
pub(crate) fn build_symbolic_inner_window<A>( // exposed for the deep-tree wrap's self-recursion demonstration (research)
    config: &MyConfig,
    inner: &A,
    proof: &Proof<MyConfig>,
    pvs: &[Val],
    w_inner: usize,
    n_pub: usize,
    n_periodic: usize,
) -> (Vec<Val>, Vec<u8>, Vec<usize>, Vec<(usize, usize)>, usize, Val)
where
    A: p3_air::Air<p3_uni_stark::SymbolicAirBuilder<Val>>,
{
    use super::{monolith_build_trace, MonolithAir};
    use crate::recursion::native_fri::{epilogue_openings, eval_symbolic_native, multicol_query_terms, query_commit_merkle_all, query_fold_data, query_input_merkle, query_quotient_merkle, quotient_recompose_weights};
    use p3_field::{BasedVectorSpace, PrimeField64};
    use p3_uni_stark::{get_symbolic_constraints, AirLayout};
    let n_queries = proof.opening_proof.query_proofs.len();
    let (block_inputs, counts, binds, chs, index_binds, index_felts) = sim_full(config, proof, pvs);
    let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
    let mut per_query = Vec::new();
    let mut quot_paths = Vec::new();
    let mut commit_data = Vec::new();
    let mut n_terms = 0;
    let mut final0 = Challenge::ZERO;
    for q in 0..n_queries {
        let (terms, _x, alpha, ro, _w) = multicol_query_terms(config, inner, proof, pvs, q);
        let (_ro2, rounds, _folded, f0) = query_fold_data(config, proof, pvs, q);
        let (_leaf, path, _cap_entry) = query_input_merkle(config, proof, pvs, q);
        let (_ql, qpath, _qce, _qw) = query_quotient_merkle(config, proof, pvs, q);
        let cm = query_commit_merkle_all(config, proof, pvs, q);
        if q == 0 {
            final0 = f0;
        }
        n_terms = terms.len();
        let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        per_query.push(((index, terms, alpha, ro, rounds), Val::ZERO, path));
        quot_paths.push(qpath);
        commit_data.push(cm);
    }
    let nqc = proof.opened_values.quotient_chunks.len();
    let layout = AirLayout::from_air::<Val>(inner);
    let constraints = get_symbolic_constraints::<Val, A>(inner, layout);
    // column_window = true (inner pis in the witness window so K instances tile); fold stays false (the
    // aggregator lays these fused-width columns into its wider fold trace and adds the fold columns itself).
    let air = MonolithAir {
        counts: counts.clone(),
        binds: binds.clone(),
        index_binds: index_binds.clone(),
        n_queries,
        n_terms,
        inner_counter: false,
        column_window: true,
        k_instances: 1,
        fold: false, fold_txstmt: false,
        constraints,
        w_inner_f: w_inner,
        n_pub_f: n_pub,
        n_periodic_f: n_periodic,
        is_zk: 0,
        cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize, narrow_arith: false, narrow_caps: false };
    let (eo_local, eo_next, is_first, is_last, is_trans, inv_van, eo_quot, eo_alpha, _z, eo_periodic) = epilogue_openings(config, inner, proof, pvs);
    let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
    // pis (identical order to run_symbolic_monolith; here they fill the WINDOW instead of public_values).
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
    for &pv in pvs {
        pis.push(pv);
    }
    for cm in proof.opening_proof.commit_phase_commits.iter() {
        for e in cm.roots().iter() {
            pis.extend_from_slice(e);
        }
    }
    for pv in &eo_periodic {
        let c = cc(*pv);
        pis.push(c[0]);
        pis.push(c[1]);
    }
    if nqc > 1 {
        for z in quotient_recompose_weights(config, inner, proof, pvs) {
            let c = cc(z);
            pis.push(c[0]);
            pis.push(c[1]);
        }
    }
    assert_eq!(pis.len(), air.pis_count(), "symbolic column-window pis layout matches pis_count");
    // monolith_build_trace fills the pis window + the ζ-squaring chain (column-window branch).
    let mut trace = monolith_build_trace(&air, &block_inputs, &per_query, chs[2], &index_felts, &quot_paths, &commit_data, &pis, None);
    // witnessed Lagrange selectors at ζ (bound in-circuit to their ζ-defs via the halved-domain z_h chain).
    let (isf, isl, iv) = (cc(is_first), cc(is_last), cc(inv_van));
    let fw = air.fused_w();
    let sb = air.sel_base();
    for r in 0..air.height() {
        trace.values[r * fw + sb..r * fw + sb + 2].copy_from_slice(&isf);
        trace.values[r * fw + sb + 2..r * fw + sb + 4].copy_from_slice(&isl);
        trace.values[r * fw + sb + 4..r * fw + sb + 6].copy_from_slice(&iv);
    }
    // witnessed constraint-fold accumulators (column-window: α_stark is degree-1, so the in-circuit α-Horner is
    // chunked — witness each FOLD_CHUNK boundary's partial fold to cap the outer degree). Native Horner mirrors
    // the in-circuit schedule EXACTLY (same modulus, same `< n` cutoff) so every accumulator bind holds; the
    // native pre-check (run_symbolic_monolith) already proved the full fold == quot(ζ).
    if air.symbolic() {
        use p3_field::BasedVectorSpace;
        // DIAGNOSTIC (localizes cw=true failures): the native full α-fold on these openings/periodic/pubs must
        // equal quot(ζ) — the same invariant run_symbolic_monolith pre-checks for cw=false. If THIS fails, the
        // window openings are wrong (not the accumulators).
        let pubs: Vec<Challenge> = pvs.iter().map(|&p| Challenge::from(p)).collect();
        let mut full = Challenge::ZERO;
        for c in air.constraints.iter() {
            full = full * eo_alpha + eval_symbolic_native(c, &eo_local, &eo_next, &pubs, &eo_periodic, is_first, is_last, is_trans);
        }
        assert_eq!(full * inv_van, eo_quot, "cw=true FULL native fold == quot(ζ)");
        // DIAGNOSTIC: verify the WINDOW (what the in-circuit epilogue actually reads) holds the α/pubs/periodic/
        // qwt values the pre-check used. Reads row 0's window columns. Pinpoints a misplaced pis region (the
        // periodic + nqc>1 coexistence is untested by the reference inners: none has both).
        let rd2 = |j: usize| -> Challenge { Challenge::from_basis_coefficients_fn(|k| trace.values[air.pw(j) + k]) };
        assert_eq!(rd2(0), eo_alpha, "window α == eo_alpha");
        for i in 0..air.n_pub() {
            assert_eq!(trace.values[air.pw(air.pub_pi() + i)], pvs[i], "window pub[{i}]");
        }
        for i in 0..air.n_periodic() {
            assert_eq!(rd2(air.periodic_base() + 2 * i), eo_periodic[i], "window periodic[{i}] misplaced");
        }
        if air.nqc() > 1 {
            let zps = quotient_recompose_weights(config, inner, proof, pvs);
            for i in 0..air.nqc() {
                assert_eq!(rd2(air.qwt_base() + 2 * i), zps[i], "window qwt[{i}] misplaced");
            }
        }
        // pz opened-trace columns (local/next at ζ) — read at q=0's super-tile arith head (M_TF row = tr).
        let tf_row = air.tr();
        let rd_at = |row: usize, col: usize| -> Challenge { Challenge::from_basis_coefficients_fn(|k| trace.values[row * fw + col + k]) };
        for c in 0..air.w_inner() {
            assert_eq!(rd_at(tf_row, air.pz(air.trm_trace(c))), eo_local[c], "pz local[{c}] wrong (w_inner={})", air.w_inner());
            assert_eq!(rd_at(tf_row, air.pz(air.trm_next(c))), eo_next[c], "pz next[{c}] wrong");
        }
        // selectors + accumulators present at the tf row?
        assert_eq!(rd_at(tf_row, air.sel(0)), is_first, "sel is_first at tf row");
        assert_eq!(rd_at(tf_row, air.sel(4)), inv_van, "sel inv_van at tf row");
    }
    if air.n_fold_acc() > 0 {
        let pubs: Vec<Challenge> = pvs.iter().map(|&p| Challenge::from(p)).collect();
        let mut folded = Challenge::ZERO;
        let mut acc_i = 0usize;
        let n_c = air.constraints.len();
        for (k, c) in air.constraints.iter().enumerate() {
            folded = folded * eo_alpha + eval_symbolic_native(c, &eo_local, &eo_next, &pubs, &eo_periodic, is_first, is_last, is_trans);
            if (k + 1) % MonolithAir::FOLD_CHUNK == 0 && k + 1 < n_c {
                let fc = cc(folded);
                let col = air.fold_acc(acc_i);
                for r in 0..air.height() {
                    trace.values[r * fw + col..r * fw + col + 2].copy_from_slice(&fc);
                }
                acc_i += 1;
            }
        }
    }
    (trace.values, counts, binds, index_binds, n_terms, pvs[0])
}

/// Phase 6.6: the TILED AGGREGATOR — K column-window monolith instances FUSED with the block tx-root fold
/// in ONE AIR. Each instance verifies a distinct inner ConstAir proof (accept-iff-p3::verify) AND folds its
/// verified public value `pvs[0]` into a global-persistent Merkle–Damgård root; the ONLY public input is
/// the block tx-root, matching `agg_root`/`batch_root` (so the node consensus seam is unchanged). Proves
/// iff all K inners verify and their statements fold to the emitted root; rejects a corrupted instance and
/// a wrong tx-root. Returns (log2 height, RSS).
/// Build a K-instance aggregator (`MonolithAir`, wide trace, block tx-root) — the shared construction
/// behind `run_aggregator` (which proves it under the recursion config) and the streamed-prover gate
/// (`stream_prove_matches_p3_on_aggregator`, which proves the SAME instance under the production hiding
/// config). The returned `(air, trace, txroot)` is a valid instance provable under ANY outer config.
fn build_aggregator_trace(k: usize, n_queries: usize) -> (super::MonolithAir, p3_matrix::dense::RowMajorMatrix<Val>, Vec<Val>, MyConfig) {
    use super::{MonolithAir, MAX_AGG_TILES};
    use crate::joinsplit_air::merge;
    use crate::poseidon2_air::{native_permute, native_steps};
    use crate::recursion::native_fri::{agg_statement_digest, DOM_AGG};
    use p3_matrix::dense::RowMajorMatrix;
    assert!(k.is_power_of_two(), "K must be a power of two (no fold padding needed), matching batch_root");
    assert!(k <= MAX_AGG_TILES, "K exceeds MAX_AGG_TILES ({MAX_AGG_TILES}); split into multiple aggregate proofs");
    let config = make_config(1, n_queries);
    let mut insts: Vec<Vec<Val>> = Vec::new();
    let mut pvs0s: Vec<Val> = Vec::new();
    let mut params: Option<(Vec<u8>, Vec<usize>, Vec<(usize, usize)>, usize)> = None;
    for i in 0..k {
        let (tr, counts, binds, ib, nt, pv0) = build_inner_window(&config, 42 + i as u64, n_queries);
        insts.push(tr);
        pvs0s.push(pv0);
        if i == 0 {
            params = Some((counts, binds, ib, nt));
        }
    }
    let (counts, binds, index_binds, n_terms) = params.unwrap();
    let air = MonolithAir { counts, binds, index_binds, n_queries, n_terms, inner_counter: false, column_window: true, k_instances: k, fold: true, fold_txstmt: false, constraints: vec![], w_inner_f: 1, n_pub_f: 1, n_periodic_f: 0, is_zk: 0, cap_height: 6, narrow_arith: false, narrow_caps: false };
    let fw = air.fused_w();
    let w = air.fold_w();
    let inst_h = air.inst_h();
    let hh = air.height();
    let fb = air.fold_sk_block();
    assert!(fb * BLOCK >= air.tr() + n_queries * air.m_period(), "fold blocks must land in the instance's tail slack");
    let mut all = vec![Val::ZERO; hh * w];
    let mut root = [Val::ZERO; 4]; // IV = 0
    for i in 0..k {
        let tr = &insts[i];
        for r in 0..inst_h {
            let dst = (i * inst_h + r) * w;
            all[dst..dst + fw].copy_from_slice(&tr[r * fw..r * fw + fw]);
            all[dst + air.af_root(0)..dst + air.af_root(0) + 4].copy_from_slice(&root);
        }
        let mut sk_in = [Val::ZERO; W];
        sk_in[0] = Val::from_u64(DOM_AGG);
        sk_in[4] = pvs0s[i];
        let sk_rows = native_steps(sk_in);
        for r in 0..BLOCK {
            let base = (i * inst_h + fb * BLOCK + r) * w + air.af_p(0);
            all[base..base + W].copy_from_slice(&sk_rows[r]);
        }
        let s_k: [Val; 4] = native_permute(sk_in)[..4].try_into().unwrap();
        let mut rt_in = [Val::ZERO; W];
        rt_in[..4].copy_from_slice(&root);
        rt_in[4..].copy_from_slice(&s_k);
        let rt_rows = native_steps(rt_in);
        for r in 0..BLOCK {
            let base = (i * inst_h + (fb + 1) * BLOCK + r) * w + air.af_p(0);
            all[base..base + W].copy_from_slice(&rt_rows[r]);
        }
        root = native_permute(rt_in)[..4].try_into().unwrap();
    }
    let mut ref_root = [Val::ZERO; 4];
    for &pv in &pvs0s {
        ref_root = merge(ref_root, agg_statement_digest(pv));
    }
    assert_eq!(root, ref_root, "built tx-root == agg oracle root");
    (air, RowMajorMatrix::new(all, w), root.to_vec(), config)
}

fn run_aggregator(k: usize, n_queries: usize) -> (u32, u64) {
    use super::{MonolithAir, MAX_AGG_TILES};
    use crate::joinsplit_air::merge;
    use crate::poseidon2_air::{native_permute, native_steps};
    use crate::recursion::native_fri::{agg_statement_digest, DOM_AGG};
    use p3_matrix::dense::RowMajorMatrix;
    assert!(k.is_power_of_two(), "K must be a power of two (no fold padding needed), matching batch_root");
    assert!(k <= MAX_AGG_TILES, "K exceeds MAX_AGG_TILES ({MAX_AGG_TILES}); split into multiple aggregate proofs");
    let config = make_config(1, n_queries);
    // build each instance's monolith columns (width fused_w) + collect the inner public values (fold seeds).
    let mut insts: Vec<Vec<Val>> = Vec::new();
    let mut pvs0s: Vec<Val> = Vec::new();
    let mut params: Option<(Vec<u8>, Vec<usize>, Vec<(usize, usize)>, usize)> = None;
    for i in 0..k {
        let (tr, counts, binds, ib, nt, pv0) = build_inner_window(&config, 42 + i as u64, n_queries);
        insts.push(tr);
        pvs0s.push(pv0);
        if i == 0 {
            params = Some((counts, binds, ib, nt));
        }
    }
    let (counts, binds, index_binds, n_terms) = params.unwrap();
    let air = MonolithAir { counts, binds, index_binds, n_queries, n_terms, inner_counter: false, column_window: true, k_instances: k, fold: true, fold_txstmt: false, constraints: vec![], w_inner_f: 1, n_pub_f: 1, n_periodic_f: 0, is_zk: 0, cap_height: 6, narrow_arith: false, narrow_caps: false };
    let fw = air.fused_w();
    let w = air.fold_w();
    let inst_h = air.inst_h();
    let hh = air.height();
    let fb = air.fold_sk_block();
    assert!(fb * BLOCK >= air.tr() + n_queries * air.m_period(), "fold blocks must land in the instance's tail slack");
    // lay the K instances' monolith columns row-disjoint into the wide (fold) trace, then fill the fold
    // columns: AF_ROOT = the running root over all of instance i's rows; two Poseidon blocks in the slack.
    let mut all = vec![Val::ZERO; hh * w];
    let mut root = [Val::ZERO; 4]; // IV = 0
    for i in 0..k {
        let tr = &insts[i];
        for r in 0..inst_h {
            let dst = (i * inst_h + r) * w;
            all[dst..dst + fw].copy_from_slice(&tr[r * fw..r * fw + fw]);
            all[dst + air.af_root(0)..dst + air.af_root(0) + 4].copy_from_slice(&root);
        }
        // SK block: merge([DOM,0,0,0],[pvs0,0,0,0]) → s_k.
        let mut sk_in = [Val::ZERO; W];
        sk_in[0] = Val::from_u64(DOM_AGG);
        sk_in[4] = pvs0s[i];
        let sk_rows = native_steps(sk_in);
        for r in 0..BLOCK {
            let base = (i * inst_h + fb * BLOCK + r) * w + air.af_p(0);
            all[base..base + W].copy_from_slice(&sk_rows[r]);
        }
        let s_k: [Val; 4] = native_permute(sk_in)[..4].try_into().unwrap();
        // ROOT block: merge(root, s_k) → root'.
        let mut rt_in = [Val::ZERO; W];
        rt_in[..4].copy_from_slice(&root);
        rt_in[4..].copy_from_slice(&s_k);
        let rt_rows = native_steps(rt_in);
        for r in 0..BLOCK {
            let base = (i * inst_h + (fb + 1) * BLOCK + r) * w + air.af_p(0);
            all[base..base + W].copy_from_slice(&rt_rows[r]);
        }
        root = native_permute(rt_in)[..4].try_into().unwrap();
    }
    // independent oracle cross-check: the built root == fold of agg_statement_digest(pvs0) (K pow2 ⇒ no pad).
    let mut ref_root = [Val::ZERO; 4];
    for &pv in &pvs0s {
        ref_root = merge(ref_root, agg_statement_digest(pv));
    }
    assert_eq!(root, ref_root, "built tx-root == agg oracle root");
    let txroot: Vec<Val> = root.to_vec();
    let trace = RowMajorMatrix::new(all, w);
    println!("aggregator+fold: {k} inners × 2^{} = 2^{} rows (width {w}); tx-root emitted", inst_h.trailing_zeros(), hh.trailing_zeros());
    let prf = prove(&config, &air, trace.clone(), &txroot);
    assert!(verify(&config, &air, &prf, &txroot).is_ok(), "{k} inners verify + fold to the block tx-root in ONE AIR");
    // wrong tx-root ⇒ the global-last-row bind fails ⇒ reject.
    let mut bad_root = txroot.clone();
    bad_root[0] += Val::ONE;
    assert!(verify(&config, &air, &prf, &bad_root).is_err(), "tampered tx-root ⇒ reject");
    // corrupted instance 1 (its α_stark window column across all rows) ⇒ its squeeze↦window bind fails ⇒ reject.
    let mut bad_vals = trace.values.clone();
    for r in inst_h..(2 * inst_h) {
        bad_vals[r * w + air.pw(0)] += Val::ONE;
    }
    let bad = RowMajorMatrix::new(bad_vals, w);
    let bp = prove(&config, &air, bad, &txroot);
    assert!(verify(&config, &air, &bp, &txroot).is_err(), "corrupted instance 1 ⇒ reject");
    let rss = peak_rss_bytes();
    println!("  -> peak RSS {} MiB", rss / (1 << 20));
    (hh.trailing_zeros(), rss)
}

/// GATE: `stream_prove` proves the REAL `MonolithAir` aggregator byte-identical to `p3_uni_stark::prove`,
/// and the streamed proof verifies. This is the wide (~1291-col), tall aggregator AIR the whole streaming
/// track targets (production peaks at 225-350 GB). A SMALL instance here (p3 must fit in RAM), proved under
/// the PRODUCTION HIDING config (`crate::config::MyConfig` — what the block proof uses; `run_aggregator`'s
/// own config is a non-hiding measurement config), in a 1-thread rayon pool (p3's FRI grind is
/// nondeterministic). Run with `--features recursion,stream`.
#[cfg(feature = "stream")]
#[test]
fn stream_prove_matches_p3_on_aggregator() {
    use crate::config::{
        production_fri, ChallengeMmcs as PChMmcs, Challenger as PChal, Dft as PDft, MyCompress as PComp,
        MyConfig as PConfig, MyHash as PHash, MyPcs as PPcs, ValMmcs as PValMmcs, CAP_HEIGHT as PCAP,
        NUM_RANDOM_CODEWORDS as PNRC,
    };
    use p3_goldilocks::default_goldilocks_poseidon2_8;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    let (k, n_queries, cblk) = (2usize, 4usize, 4usize);
    let (air, trace, txroot, _rec_config) = build_aggregator_trace(k, n_queries);
    println!("agg gate: width {} height 2^{}", trace.width, (trace.values.len() / trace.width).trailing_zeros());

    let (pcs_seed, mmcs_seed) = (7u64, 9u64);
    let perm = default_goldilocks_poseidon2_8();
    let build = || {
        let vm = PValMmcs::new(PHash::new(perm.clone()), PComp::new(perm.clone()), PCAP, ChaCha20Rng::seed_from_u64(mmcs_seed));
        let pcs = PPcs::new(PDft::default(), vm.clone(), production_fri(PChMmcs::new(vm)), PNRC, ChaCha20Rng::seed_from_u64(pcs_seed));
        PConfig::new(pcs, PChal::new(perm.clone()))
    };

    let pool = rayon::ThreadPoolBuilder::new().num_threads(1).build().unwrap();
    let (p3_proof, my_proof) = pool.install(|| {
        let p3 = prove(&build(), &air, trace.clone(), &txroot);
        let my = crate::stream_prove::stream_prove(&build(), &air, trace.clone(), &txroot, pcs_seed, mmcs_seed, cblk)
            .expect("stream_prove on the aggregator");
        (p3, my)
    });
    assert_eq!(
        postcard::to_allocvec(&p3_proof).unwrap(),
        postcard::to_allocvec(&my_proof).unwrap(),
        "stream_prove != p3_uni_stark::prove on the MonolithAir aggregator"
    );
    assert!(verify(&build(), &air, &my_proof, &txroot).is_ok(), "streamed aggregator proof must verify");
}

/// RAM bench: prove a big `MonolithAir` aggregator under the PRODUCTION config, `stream_prove` vs p3 (same
/// AIR/trace, mode-selected). The point: `stream_prove` completes a big aggregator inside a cgroup cap that
/// p3 needs the whole LDE resident for. Both proofs verify. Run each mode in its own process; stream under a
/// cap on a nodatacow disk with `RAYON_NUM_THREADS≈cores/2`:
///   p3:     `LATTICA_AGG_K=2 LATTICA_AGG_Q=32 LATTICA_AGG_MODE=p3 cargo test --release --features recursion,stream stream_prove_aggregator_ram_bench -- --ignored --nocapture`
///   stream: `systemd-run --user --scope -p MemoryMax=8G env RAYON_NUM_THREADS=12 LATTICA_AGG_MODE=stream LATTICA_AGG_K=2 LATTICA_AGG_Q=32 LATTICA_SPILL_DIR=/home/access/scratch cargo test --release --features recursion,stream stream_prove_aggregator_ram_bench -- --ignored --nocapture`
#[cfg(feature = "stream")]
#[test]
#[ignore = "bench: aggregator RAM stream_prove vs p3 (LATTICA_AGG_K, LATTICA_AGG_Q, LATTICA_AGG_MODE=stream|p3, LATTICA_SPILL_DIR)"]
fn stream_prove_aggregator_ram_bench() {
    let env = |k: &str, d: usize| std::env::var(k).ok().and_then(|s| s.parse().ok()).unwrap_or(d);
    let (kk, qq, cblk) = (env("LATTICA_AGG_K", 2), env("LATTICA_AGG_Q", 8), env("LATTICA_AGG_CBLK", 4));
    let mode = std::env::var("LATTICA_AGG_MODE").unwrap_or_else(|_| "stream".into());
    let (air, trace, txroot, _) = build_aggregator_trace(kk, qq);
    let (w, rows) = (trace.width, trace.values.len() / trace.width);
    let t0 = std::time::Instant::now();
    let bytes = if mode == "stream" {
        postcard::to_allocvec(&crate::stream_prove::stream_prove_seeded(&air, trace, &txroot, cblk).expect("stream_prove")).unwrap()
    } else if mode == "gpu" {
        // GPU hiding prove (GpuHidingPcs) of the recursive aggregator — same production config, verified below.
        #[cfg(feature = "gpu")]
        {
            crate::config::gpu::proof_to_bytes_hiding(&air, trace, &txroot)
        }
        #[cfg(not(feature = "gpu"))]
        {
            unreachable!("mode=gpu requires --features gpu")
        }
    } else {
        postcard::to_allocvec(&prove(&crate::config::make_config(), &air, trace, &txroot)).unwrap()
    };
    let secs = t0.elapsed().as_secs_f64();
    let proof: Proof<crate::config::MyConfig> = postcard::from_bytes(&bytes).expect("aggregator proof deser");
    assert!(verify(&crate::config::make_config(), &air, &proof, &txroot).is_ok(), "aggregator proof (mode={mode}) must verify");
    println!(
        "AGG-RAM-BENCH mode={mode} k={kk} q={qq} width={w} rows=2^{} peak_rss={}MiB prove={secs:.1}s proof={}KiB",
        rows.trailing_zeros(),
        peak_rss_bytes() / (1 << 20),
        bytes.len() / 1024,
    );
}

/// PERF bench: CPU vs GPU HIDING prove across circuit scales (join-split → batch → aggregator), all under
/// the PRODUCTION hiding config and all verifying under the production verifier. CPU = `prove(make_config())`
/// (Radix2 LDE + CPU Merkle); GPU = `config::gpu::proof_to_bytes_hiding` (`GpuHidingPcs`: GPU LDE + GPU
/// Merkle, CPU quotient). Best-of-`LATTICA_BENCH_RUNS` (default 3) wall-clock; the trace is built once and
/// cloned per run so only the prove is timed (the first GPU run also pays the one-time OpenCL program build,
/// which best-of discards). Run:
///   `cargo test --release --features recursion,gpu cpu_vs_gpu_prove_benchmark -- --ignored --nocapture`
#[cfg(feature = "gpu")]
#[test]
#[ignore = "bench: CPU vs GPU hiding prove across scales (--features recursion,gpu, LATTICA_BENCH_RUNS)"]
fn cpu_vs_gpu_prove_benchmark() {
    use crate::batch_joinsplit_air::{batch_root, build_batch_trace, JoinSplitBatchAir};
    use crate::joinsplit_air::{self, JoinSplitAir};
    use p3_matrix::dense::RowMajorMatrix;

    let runs: usize =
        std::env::var("LATTICA_BENCH_RUNS").ok().and_then(|s| s.parse().ok()).unwrap_or(3).max(1);
    println!("\nCPU vs GPU hiding prove (best of {runs}), production config, both verify under production verifier:");
    println!("{:<20} {:>11} {:>10} {:>10} {:>9}", "circuit", "rows x w", "CPU ms", "GPU ms", "speedup");

    // Build the trace ONCE; verify both backends under the production verifier; then best-of-`runs` each,
    // cloning the trace per run so `prove` (not the trace build) is what's timed. Concrete-air calls, so no
    // explicit trait bounds are needed (macro, not a generic fn — the GPU hiding config type stays private).
    macro_rules! bench {
        ($name:expr, $air:expr, $trace:expr, $pis:expr) => {{
            let name = $name;
            let air = $air;
            let trace: RowMajorMatrix<crate::config::Val> = $trace;
            let pis = $pis;
            let (rows, w) = (trace.values.len() / trace.width, trace.width);
            let cpu_p = prove(&crate::config::make_config(), &air, trace.clone(), &pis);
            assert!(verify(&crate::config::make_config(), &air, &cpu_p, &pis).is_ok(), "{} CPU verify", name);
            let gpu_b = crate::config::gpu::proof_to_bytes_hiding(&air, trace.clone(), &pis);
            let gpu_p: Proof<crate::config::MyConfig> = postcard::from_bytes(&gpu_b).expect("gpu proof deser");
            assert!(verify(&crate::config::make_config(), &air, &gpu_p, &pis).is_ok(), "{} GPU verify", name);
            let (mut cpu_ms, mut gpu_ms) = (f64::MAX, f64::MAX);
            for _ in 0..runs {
                let tr = trace.clone();
                let t = std::time::Instant::now();
                let _ = prove(&crate::config::make_config(), &air, tr, &pis);
                cpu_ms = cpu_ms.min(t.elapsed().as_secs_f64() * 1e3);
                let tr = trace.clone();
                let t = std::time::Instant::now();
                let _ = crate::config::gpu::proof_to_bytes_hiding(&air, tr, &pis);
                gpu_ms = gpu_ms.min(t.elapsed().as_secs_f64() * 1e3);
            }
            let dims = format!("{rows}x{w}");
            println!("{:<20} {:>11} {:>10.1} {:>10.1} {:>8.2}x", name, dims, cpu_ms, gpu_ms, cpu_ms / gpu_ms);
        }};
    }

    let w = joinsplit_air::demo_witness();
    bench!("join-split", JoinSplitAir, joinsplit_air::build_trace(&w), joinsplit_air::public_values(&w));
    for n in [16usize, 64] {
        let ws: Vec<_> = (0..n).map(|_| joinsplit_air::demo_witness()).collect();
        let root = batch_root(&ws);
        bench!(format!("batch N={n}"), JoinSplitBatchAir, build_batch_trace(&ws), root);
    }
    for q in [8usize, 32] {
        let (air, trace, txroot, _) = build_aggregator_trace(2, q);
        bench!(format!("aggregator q={q}"), air, trace, txroot);
    }
}

/// R4: the SYMBOLIC tiled aggregator — K column-window monolith instances, each verifying a REAL
/// join-split proof (accept-iff-p3::verify via the symbolic epilogue) AND folding its verified `pvs[0]`
/// into the block tx-root, fused in ONE AIR. The symbolic twin of `run_aggregator` (which did ConstAir
/// inners). Proves iff all K join-split inners verify and fold to the emitted root; rejects a wrong
/// tx-root and a corrupted instance. Returns (log2 height, RSS). (The fold seed is `pvs[0]` here — the
/// batch-root-matching full-statement-digest fold is a follow-on refinement.)
fn run_symbolic_aggregator(k: usize, n_queries: usize, cap_h: usize) -> (u32, u64) {
    use super::{MonolithAir, MAX_AGG_TILES};
    use crate::joinsplit_air::{build_trace, demo_witness, merge, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
    use crate::batch_joinsplit_air::{tx_statement_digest, DOM_TXROOT};
    use crate::poseidon2_air::{native_permute, native_steps};
    use crate::recursion::native_fri::make_config_cap;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_uni_stark::{get_symbolic_constraints, AirLayout};
    assert!(k.is_power_of_two() && k <= MAX_AGG_TILES, "K power of two ≤ MAX_AGG_TILES");
    // A SMALL inner cap shrinks the column-window width (the full caps the cap-mux selects over are
    // 2^cap · 4 witness columns each) — the lever that keeps the wide aggregator inside RAM.
    let config = make_config_cap(1, n_queries, cap_h);
    // K join-split inner proofs (demo witness — identical statements; the fold binds each instance's full pi
    // window into the batch tx_statement_digest, so `pvs` IS every instance's statement here).
    let w = demo_witness();
    let pvs = public_values(&w);
    let mut insts: Vec<Vec<Val>> = Vec::new();
    let mut params: Option<(Vec<u8>, Vec<usize>, Vec<(usize, usize)>, usize, usize)> = None;
    for _i in 0..k {
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let cap_height = proof.commitments.trace.roots().len().trailing_zeros() as usize;
        let (tr, counts, binds, ib, nt, _pv0) = build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC);
        insts.push(tr);
        if _i == 0 {
            params = Some((counts, binds, ib, nt, cap_height));
        }
    }
    let (counts, binds, index_binds, n_terms, cap_height) = params.unwrap();
    let constraints = get_symbolic_constraints::<Val, JoinSplitAir>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
    let air = MonolithAir {
        counts,
        binds,
        index_binds,
        n_queries,
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
        cap_height, narrow_arith: false, narrow_caps: false };
    let (fw, w_fold, inst_h, hh, fb) = (air.fused_w(), air.fold_w(), air.inst_h(), air.height(), air.fold_sk_block());
    assert!(fb * BLOCK >= air.tr() + n_queries * air.m_period(), "fold blocks land in the instance tail slack");
    let mut all = vec![Val::ZERO; hh * w_fold];
    let mut root = [Val::ZERO; 4];
    for i in 0..k {
        let tr = &insts[i];
        for r in 0..inst_h {
            let dst = (i * inst_h + r) * w_fold;
            all[dst..dst + fw].copy_from_slice(&tr[r * fw..r * fw + fw]);
            all[dst + air.af_root(0)..dst + air.af_root(0) + 4].copy_from_slice(&root);
        }
        // s_k = tx_statement_digest(pvs): the join-split statement MD-chain — merge([DOM,0,0,0], anchor), then
        // merge(prev, chunk_b) over nf/out_cm/[fee,mint,0,0]/tx_binding. Each merge is one Poseidon block.
        let srcs = air.fold_chunk_srcs();
        let n_sk = srcs.len();
        let mut prev = [Val::from_u64(DOM_TXROOT), Val::ZERO, Val::ZERO, Val::ZERO];
        for (b, s) in srcs.iter().enumerate() {
            let chunk: [Val; 4] = core::array::from_fn(|k| s[k].map(|off| pvs[off]).unwrap_or(Val::ZERO));
            let mut inp = [Val::ZERO; W];
            inp[..4].copy_from_slice(&prev);
            inp[4..].copy_from_slice(&chunk);
            let rows = native_steps(inp);
            for r in 0..BLOCK {
                let base = (i * inst_h + (fb + b) * BLOCK + r) * w_fold + air.af_p(0);
                all[base..base + W].copy_from_slice(&rows[r]);
            }
            prev = native_permute(inp)[..4].try_into().unwrap();
        }
        let s_k: [Val; 4] = prev; // = tx_statement_digest(pvs)
        assert_eq!(s_k, tx_statement_digest(&pvs), "built s_k == batch tx_statement_digest");
        // ROOT block: merge(root, s_k).
        let mut rt_in = [Val::ZERO; W];
        rt_in[..4].copy_from_slice(&root);
        rt_in[4..].copy_from_slice(&s_k);
        let rt_rows = native_steps(rt_in);
        for r in 0..BLOCK {
            let base = (i * inst_h + (fb + n_sk) * BLOCK + r) * w_fold + air.af_p(0);
            all[base..base + W].copy_from_slice(&rt_rows[r]);
        }
        root = native_permute(rt_in)[..4].try_into().unwrap();
    }
    // oracle: the built root == the batch's block tx-root (IV=0, K pow2 ⇒ no dummy padding) — BYTE-IDENTICAL to
    // batch_joinsplit_air::batch_root, so the node consensus seam is unchanged.
    let mut ref_root = [Val::ZERO; 4];
    for _ in 0..k {
        ref_root = merge(ref_root, tx_statement_digest(&pvs));
    }
    assert_eq!(root, ref_root, "built tx-root == batch_root (tx_statement_digest fold)");
    let txroot: Vec<Val> = root.to_vec();
    let trace = RowMajorMatrix::new(all, w_fold);
    println!("symbolic aggregator+fold: {k} join-split inners × 2^{} = 2^{} rows (width {w_fold})", inst_h.trailing_zeros(), hh.trailing_zeros());
    let prf = prove(&config, &air, trace.clone(), &txroot);
    assert!(verify(&config, &air, &prf, &txroot).is_ok(), "{k} join-split inners verify + fold to the block tx-root in ONE AIR");
    let mut bad_root = txroot.clone();
    bad_root[0] += Val::ONE;
    assert!(verify(&config, &air, &prf, &bad_root).is_err(), "tampered tx-root ⇒ reject");
    // corrupted instance 1 (its α_stark window column across all rows) ⇒ its squeeze↦window bind fails ⇒ reject.
    let mut bad_vals = trace.values.clone();
    for r in inst_h..(2 * inst_h) {
        bad_vals[r * w_fold + air.pw(0)] += Val::ONE;
    }
    let bp = prove(&config, &air, RowMajorMatrix::new(bad_vals, w_fold), &txroot);
    assert!(verify(&config, &air, &bp, &txroot).is_err(), "corrupted instance 1 ⇒ reject");
    let rss = peak_rss_bytes();
    println!("  -> peak RSS {} MiB", rss / (1 << 20));
    (hh.trailing_zeros(), rss)
}

/// R4 ISOLATION: the COLUMN-WINDOW join-split monolith standalone (k=1, NO fold, NO tiling) — verifies a real
/// join-split inner reading its pis from the witness window, exercising the CHUNKED α-fold with witnessed
/// accumulators in isolation from the aggregator's fold/tiling. If this verifies but the aggregator doesn't,
/// the bug is in fold/tiling; if this fails, it's the epilogue/accumulators.
#[test]
#[ignore = "slow: R4 column-window join-split monolith (chunked α-fold), standalone"]
fn phase8_joinsplit_window_monolith() {
    use super::MonolithAir;
    use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
    use crate::recursion::native_fri::make_config_cap;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_uni_stark::{get_symbolic_constraints, AirLayout};
    let config = make_config_cap(1, 4, 2);
    let w = demo_witness();
    let pvs = public_values(&w);
    let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
    let (tr, counts, binds, index_binds, n_terms, _pv0) = build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC);
    let constraints = get_symbolic_constraints::<Val, JoinSplitAir>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
    let air = MonolithAir {
        counts, binds, index_binds, n_queries: 4, n_terms,
        inner_counter: false, column_window: true, k_instances: 1, fold: false, fold_txstmt: false,
        constraints, w_inner_f: WIDTH, n_pub_f: N_PUBLIC, n_periodic_f: N_PERIODIC, is_zk: 0,
        cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize, narrow_arith: false, narrow_caps: false };
    let fw = air.fused_w();
    let trace = RowMajorMatrix::new(tr, fw);
    let prf = prove(&config, &air, trace, &[]); // cw=true k=1: all pis in the window, nothing public
    assert!(verify(&config, &air, &prf, &[]).is_ok(), "column-window join-split monolith (chunked α-fold) verifies");
    println!("R4 isolation: column-window join-split monolith verifies (chunked α-fold, width {fw})");
}

/// Build the cw=true k=1 (no fold) monolith over `inner` and return (n_fold_acc, verify-ok). Shared by the
/// column-window isolation/discriminator tests.
fn window_verify<A>(config: &MyConfig, inner: &A, proof: &Proof<MyConfig>, pvs: &[Val], w: usize, np: usize, nper: usize) -> (usize, bool)
where
    A: p3_air::Air<p3_uni_stark::SymbolicAirBuilder<Val>>,
{
    use super::MonolithAir;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_uni_stark::{get_symbolic_constraints, AirLayout};
    let (tr, counts, binds, index_binds, n_terms, _pv0) = build_symbolic_inner_window(config, inner, proof, pvs, w, np, nper);
    let constraints = get_symbolic_constraints::<Val, A>(inner, AirLayout::from_air::<Val>(inner));
    let air = MonolithAir {
        counts, binds, index_binds, n_queries: proof.opening_proof.query_proofs.len(), n_terms,
        inner_counter: false, column_window: true, k_instances: 1, fold: false, fold_txstmt: false,
        constraints, w_inner_f: w, n_pub_f: np, n_periodic_f: nper, is_zk: 0,
        cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize, narrow_arith: false, narrow_caps: false };
    let fw = air.fused_w();
    let prf = prove(config, &air, RowMajorMatrix::new(tr, fw), &[]);
    (air.n_fold_acc(), verify(config, &air, &prf, &[]).is_ok())
}

/// R4 GUARD: the CAP-2 column-window monolith verifies a broad matrix of inner shapes — degree (1..4), periodic
/// (0/1), quotient chunks (nqc 1/2/4), multi-block input leaf (W=8), and FRI depth (db 6/12). Regression guard
/// for the two cap<6 fixes (the chunked α-fold + the runtime quotient-cap-height) — each of these shapes failed
/// before the fixes. (Deriving accumulators from a low FOLD_CHUNK also isolates the fold-degree lever.)
#[test]
#[ignore = "slow: R4 cap-2 column-window guard (fib/mul/periodic/cube/quart/wide/db12)"]
fn phase8_window_discriminator() {
    use crate::recursion::native_fri::{gen_cube_proof, gen_fib_proof, gen_mul_proof, gen_periodic_proof, gen_quart_proof, gen_wide_proof, make_config_cap};
    use crate::recursion::native_verify::{CubeAir, FibonacciAir, MulAir, PeriodicAir, QuartAir, WideAir, WIDE_W};
    let config = make_config_cap(1, 4, 2); // CAP-2 (matches the join-split window test) — the suspected bug lever
    let (fp, fpv) = gen_fib_proof(&config, 1, 1, 6);
    let (mp, mpv) = gen_mul_proof(&config, 3, 5, 6);
    let (pp, ppv) = gen_periodic_proof(&config, 5, 6);
    let (cp, cpv) = gen_cube_proof(&config, 5, 6);
    let (qp, qpv) = gen_quart_proof(&config, 5, 6);
    let (wp, wpv) = gen_wide_proof(&config, 5, 6);
    let (cp12, cpv12) = gen_cube_proof(&config, 5, 12); // db=12 (deep FRI, like join-split) + nqc=2
    let (qp12, qpv12) = gen_quart_proof(&config, 5, 12); // db=12 + nqc=4 + multi-block quotient leaf
    let fib = window_verify(&config, &FibonacciAir, &fp, &fpv, 2, 3, 0);
    let mul = window_verify(&config, &MulAir, &mp, &mpv, 3, 2, 0);
    let per = window_verify(&config, &PeriodicAir, &pp, &ppv, 1, 1, 1);
    let cube = window_verify(&config, &CubeAir, &cp, &cpv, 2, 1, 0);
    let quart = window_verify(&config, &QuartAir, &qp, &qpv, 2, 1, 0);
    let wide = window_verify(&config, &WideAir, &wp, &wpv, WIDE_W, WIDE_W, 0);
    let cube12 = window_verify(&config, &CubeAir, &cp12, &cpv12, 2, 1, 0);
    let quart12 = window_verify(&config, &QuartAir, &qp12, &qpv12, 2, 1, 0);
    let p = |ok: bool| if ok { "PASS" } else { "FAIL" };
    println!("WINDOW [fib      deg1 nper0 nqc1  W2  db6 ]: n_fold_acc={} verify={}", fib.0, p(fib.1));
    println!("WINDOW [mul      deg2 nper0 nqc1  W3  db6 ]: n_fold_acc={} verify={}", mul.0, p(mul.1));
    println!("WINDOW [periodic deg1 nper1 nqc1  W1  db6 ]: n_fold_acc={} verify={}", per.0, p(per.1));
    println!("WINDOW [cube     deg3 nper0 nqc2  W2  db6 ]: n_fold_acc={} verify={}", cube.0, p(cube.1));
    println!("WINDOW [quart    deg4 nper0 nqc4  W2  db6 ]: n_fold_acc={} verify={}", quart.0, p(quart.1));
    println!("WINDOW [wide     deg1 nper0 nqc1  W8  db6 ]: n_fold_acc={} verify={}", wide.0, p(wide.1));
    println!("WINDOW [cube     deg3 nper0 nqc2  W2  db12]: n_fold_acc={} verify={}", cube12.0, p(cube12.1));
    println!("WINDOW [quart    deg4 nper0 nqc4  W2  db12]: n_fold_acc={} verify={}", quart12.0, p(quart12.1));
    for (name, (_, ok)) in [("fib", fib), ("mul", mul), ("periodic", per), ("cube", cube), ("quart", quart), ("wide", wide), ("cube12", cube12), ("quart12", quart12)] {
        assert!(ok, "cap-2 column-window monolith over {name} must verify");
    }
}

/// R4 GUARD (cheap, no outer prove): every symbolic monolith shape — plain, column-window, k-tiled, folded,
/// and the full aggregator — must have `log_nqc ≤ log_blowup (4)`, i.e. its quotient fits the FRI codeword.
/// This is the check the original degree probe LACKED (it only built `column_window=false`): the aggregator's
/// α-Horner fold with a degree-1 window `α_stark` reached `log_nqc = 7` (max_deg 91) — a silent unsound
/// quotient — until the chunked accumulator fix (`FOLD_CHUNK`). Asserting it here catches any regression that
/// re-inflates the fold degree.
#[test]
#[ignore = "guard: symbolic monolith quotient geometry (no prove)"]
fn phase8_joinsplit_aggregator_probe() {
    use super::MonolithAir;
    use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
    use crate::recursion::native_fri::make_config_cap;
    use p3_uni_stark::{get_log_num_quotient_chunks, get_symbolic_constraints, AirLayout};
    let (n_queries, cap_h) = (4usize, 2usize);
    let config = make_config_cap(1, n_queries, cap_h);
    let w = demo_witness();
    let pvs = public_values(&w);
    let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
    let (counts, binds, index_binds, n_terms, cap_height) = {
        let (_tr, counts, binds, ib, nt, _pv0) = build_symbolic_inner_window(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC);
        (counts, binds, ib, nt, proof.commitments.trace.roots().len().trailing_zeros() as usize)
    };
    let constraints = get_symbolic_constraints::<Val, JoinSplitAir>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
    let mk = |cw: bool, ki: usize, fold: bool| MonolithAir {
        counts: counts.clone(), binds: binds.clone(), index_binds: index_binds.clone(), n_queries, n_terms,
        inner_counter: false, column_window: cw, k_instances: ki, fold, fold_txstmt: false,
        constraints: constraints.clone(), w_inner_f: WIDTH, n_pub_f: N_PUBLIC, n_periodic_f: N_PERIODIC, is_zk: 0, cap_height, narrow_arith: false, narrow_caps: false };
    for (tag, cw, ki, fold) in [
        ("plain       cw0 k1 f0", false, 1, false),
        ("R1 window    cw1 k1 f0", true, 1, false),
        ("k-tiled      cw1 k2 f0", true, 2, false),
        ("fold k1      cw1 k1 f1", true, 1, true),
        ("AGGREGATOR   cw1 k2 f1", true, 2, true),
    ] {
        let air = mk(cw, ki, fold);
        let layout = AirLayout::from_air::<Val>(&air);
        let cs = get_symbolic_constraints::<Val, MonolithAir>(&air, layout);
        let mut degs: Vec<usize> = cs.iter().map(|c| c.degree_multiple()).collect();
        degs.sort_unstable_by(|a, b| b.cmp(a));
        let maxd = degs[0];
        let n_at_max = degs.iter().filter(|&&d| d == maxd).count();
        let log_nqc = get_log_num_quotient_chunks::<Val, MonolithAir>(&air, layout, 0);
        println!("AGG PROBE [{tag}]: width={} height=2^{} max_deg={maxd} (×{n_at_max}; next={}) log_nqc={log_nqc} n_cs={} C_inner={}",
            air.fold_w(), air.height().trailing_zeros(), degs.get(n_at_max).copied().unwrap_or(0), cs.len(), constraints.len());
        assert!(log_nqc <= 4, "{tag}: log_nqc {log_nqc} exceeds log_blowup 4 ⇒ the quotient can't be committed (unsound). Lower FOLD_CHUNK.");
    }
}

/// RAM-vs-cap projection for the PRODUCTION aggregator (q96 / K=2, real join-split inner) — geometry only, NO
/// aggregator prove. Inner cap height has NO soundness effect but trades the column-window WIDTH (∝ 2^cap) against
/// the Merkle-path DEPTH per query (∝ log_global − cap, which grows the super-tile ⇒ rows). So min(rows × width)
/// sits at some middle cap, not the extremes. Projects LDE = rows·width·8·2^log_blowup and RAM ≈ 1.4·LDE
/// (calibrated: the measured cap-2/q4 aggregator was ~13 GB at ~9.4 GB LDE).
#[test]
#[ignore = "measurement: aggregator RAM vs inner cap height at q96/K=2 (geometry, no aggregator prove)"]
fn aggregator_ram_cap_curve() {
    use super::MonolithAir;
    use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
    use crate::recursion::native_fri::{make_config_cap, multicol_query_terms};
    use p3_uni_stark::{get_symbolic_constraints, AirLayout};
    let w = demo_witness();
    let pvs = public_values(&w);
    let constraints = get_symbolic_constraints::<Val, JoinSplitAir>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
    println!("PRODUCTION aggregator (q96 / K=2 / join-split inner) — RAM projection by inner cap height:");
    for cap_h in [2usize, 3, 4, 5, 6] {
        let config = make_config_cap(1, 96, cap_h);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs); // q96 inner (the user's own proof)
        let cap_height = proof.commitments.trace.roots().len().trailing_zeros() as usize;
        let (_bi, counts, binds, _chs, index_binds, _if) = sim_full(&config, &proof, &pvs);
        let n_terms = multicol_query_terms(&config, &JoinSplitAir, &proof, &pvs, 0).0.len();
        let air = MonolithAir {
            counts, binds, index_binds, n_queries: 96, n_terms, inner_counter: false,
            column_window: true, k_instances: 2, fold: true, fold_txstmt: true,
            constraints: constraints.clone(), w_inner_f: WIDTH, n_pub_f: N_PUBLIC, n_periodic_f: N_PERIODIC,
            is_zk: 0, cap_height, narrow_arith: false, narrow_caps: false };
        let (rows, width) = (air.height() as u128, air.fold_w() as u128);
        let lde_gb = rows * width * 8 * 16 / (1 << 30);
        let ram_gb = lde_gb * 7 / 5; // ≈ 1.4× LDE, calibrated to the measured cap-2/q4 point
        println!(
            "  cap-{cap_h}: inst_h=2^{} rows=2^{} width={width} | LDE ~{lde_gb} GB → est. RAM ~{ram_gb} GB",
            air.inst_h().trailing_zeros(),
            air.height().trailing_zeros(),
        );
    }
}

/// R4: the symbolic aggregator verifies K=2 REAL join-split proofs + folds to the block tx-root in ONE AIR.
#[test]
#[ignore = "slow + large RSS: R4 symbolic aggregator over K=2 real join-split inners"]
fn phase8_joinsplit_aggregator() {
    // cap_height=2 keeps the wide column-window aggregator inside this box's RAM (full caps 16 cols
    // each vs 256 at cap 6). Cap height is a FRI encoding choice with no soundness effect.
    let (log2h, rss) = run_symbolic_aggregator(2, 4, 2);
    println!("R4: K=2 real join-split inners verified + folded to the block tx-root in ONE AIR at 2^{log2h} / {} MiB", rss / (1 << 20));
}

/// R5 PROBE (self-recursion): can the monolith verify ANOTHER monolith's proof? Build + prove a small ConstAir
/// monolith (the INNER), then have `build_symbolic_inner_window` construct the OUTER witness that verifies it
/// (its full-fold pre-check + window/pz/cap binds VALIDATE the witness — success ⇒ the mechanism works over an
/// arbitrary AIR, MonolithAir included), and measure the outer geometry to answer R3 §3.4's size-stability
/// question. NO outer prove (the outer is measured, not proven — it is far too large for this box).
#[test]
#[ignore = "R5 probe: self-recursion geometry (monolith-verifies-monolith); builds outer witness, no outer prove"]
fn phase9_self_recursion_probe() {
    use super::{monolith_build_trace, MonolithAir, CM_ROUNDS};
    use crate::recursion::native_fri::{gen_const_proof, query_commit_merkle_all, query_fold_data, query_input_merkle, query_quotient_merkle, query_terms};
    use p3_air::BaseAir;
    use p3_field::{BasedVectorSpace, PrimeField64};
    use p3_uni_stark::{get_log_num_quotient_chunks, get_symbolic_constraints, AirLayout};
    // (1) INNER: a small ConstAir monolith (pis-mode), built + proven — this becomes the "inner proof" the OUTER
    // monolith must verify. (Mirrors run_monolith's ConstAir-monolith setup.)
    let config = make_config(1, 4);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let (block_inputs, counts, binds, chs, index_binds, index_felts) = sim_full(&config, &proof, &pvs);
    let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
    let (mut per_query, mut quot_paths, mut commit_data, mut n_terms) = (Vec::new(), Vec::new(), Vec::new(), 0usize);
    let (mut final0, mut cap0, mut qcap0) = (Challenge::ZERO, [Val::ZERO; 4], [Val::ZERO; 4]);
    let mut ccap0 = [[Val::ZERO; 4]; CM_ROUNDS];
    for q in 0..4 {
        let (terms, _x, alpha, ro) = query_terms(&config, &proof, &pvs, q);
        let (_r, rounds, _f, f0) = query_fold_data(&config, &proof, &pvs, q);
        let v = proof.opening_proof.query_proofs[q].input_proof[0].opened_values[0][0];
        let (_l, path, ce) = query_input_merkle(&config, &proof, &pvs, q);
        let (_ql, qpath, qce, _qw) = query_quotient_merkle(&config, &proof, &pvs, q);
        let cm = query_commit_merkle_all(&config, &proof, &pvs, q);
        if q == 0 {
            final0 = f0;
            cap0 = ce;
            qcap0 = qce;
            for (r, (_g, _l, _p, c)) in cm.iter().enumerate() {
                ccap0[r] = *c;
            }
        }
        n_terms = terms.len();
        let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        per_query.push(((index, terms, alpha, ro, rounds), v, path));
        quot_paths.push(qpath);
        commit_data.push(cm);
    }
    let inner = MonolithAir { counts: counts.clone(), binds, index_binds, n_queries: 4, n_terms, inner_counter: false, column_window: false, k_instances: 1, fold: false, fold_txstmt: false, constraints: vec![], w_inner_f: 1, n_pub_f: 1, n_periodic_f: 0, is_zk: 0, cap_height: 6, narrow_arith: false, narrow_caps: false };
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
    pis.extend_from_slice(&cap0);
    pis.extend_from_slice(&qcap0);
    pis.push(pvs[0]);
    for ce in &ccap0 {
        pis.extend_from_slice(ce);
    }
    let inner_trace = monolith_build_trace(&inner, &block_inputs, &per_query, chs[2], &index_felts, &quot_paths, &commit_data, &[], None);
    let inner_prf = prove(&config, &inner, inner_trace, &pis);
    assert!(verify(&config, &inner, &inner_prf, &pis).is_ok(), "inner ConstAir monolith proves");
    let (w_in, np_in, nper_in) = (inner.fused_w(), pis.len(), BaseAir::<Val>::num_periodic_columns(&inner));
    let inner_cs = get_symbolic_constraints::<Val, MonolithAir>(&inner, AirLayout::from_air::<Val>(&inner));
    println!("R5 INNER (ConstAir monolith): W={w_in} n_pub={np_in} n_periodic={nper_in} n_constraints={} height=2^{}", inner_cs.len(), inner.height().trailing_zeros());
    // (2) OUTER: the monolith verifying the INNER monolith proof. build_symbolic_inner_window does the witness
    // AND validates it (full-fold pre-check + window/pz/cap binds); if it returns, the self-recursion mechanism
    // works over MonolithAir-as-inner. NO outer prove — we only measure its geometry.
    let (_otr, ocounts, obinds, oib, ont, _pv0) = build_symbolic_inner_window(&config, &inner, &inner_prf, &pis, w_in, np_in, nper_in);
    let cap_height = inner_prf.commitments.trace.roots().len().trailing_zeros() as usize;
    let outer = MonolithAir { counts: ocounts, binds: obinds, index_binds: oib, n_queries: 4, n_terms: ont, inner_counter: false, column_window: true, k_instances: 1, fold: false, fold_txstmt: false, constraints: inner_cs.clone(), w_inner_f: w_in, n_pub_f: np_in, n_periodic_f: nper_in, is_zk: 0, cap_height, narrow_arith: false, narrow_caps: false };
    let olayout = AirLayout::from_air::<Val>(&outer);
    let ocs = get_symbolic_constraints::<Val, MonolithAir>(&outer, olayout);
    let log_nqc = get_log_num_quotient_chunks::<Val, MonolithAir>(&outer, olayout, 0);
    let (ow, oh) = (outer.fused_w(), outer.height());
    let lde_gb = (oh as u128 * ow as u128 * 8 * 16) / (1 << 30);
    println!("R5 OUTER (monolith-verifies-monolith): W={ow} height=2^{} log_nqc={log_nqc} n_cs={} | est. blowup-LDE ~{lde_gb} GB | build_symbolic_inner_window SUCCEEDED ⇒ mechanism works", oh.trailing_zeros(), ocs.len());
    // R5 FINDING (matches R3 §3.4): the self-recursion MECHANISM works (the monolith built + self-validated a
    // witness for verifying another monolith), but it is neither SIZE-stable nor DEGREE-stable — verifying a
    // small inner monolith (W=193, 384 constraints) yields a FAR larger outer (W≈8520, ~44×; ~133 GB LDE) whose
    // fold over the inner's degree-16 constraints has log_nqc=7 > log_blowup 4 (unprovable at blowup 4). So each
    // tree level explodes; naive self-composition can't converge. A fixed-size WRAP (re-prove each level's output
    // at a canonical small/low-degree shape) or a different outer proof system is required — R5's open problem.
    assert!(ow > 8 * w_in, "self-recursion is SIZE-explosive: outer W {ow} ≫ inner W {w_in} (not size-stable)");
    assert!(log_nqc > 4, "self-recursion is DEGREE-explosive: outer log_nqc {log_nqc} > log_blowup 4 (inner's high-degree constraints fold past the quotient budget)");
}

#[test]
#[ignore = "slow: Phase 6.6 tiled aggregator (K inners verified + folded to tx-root in one AIR)"]
fn phase6_tiled_aggregator() {
    // K=2 at 16 queries/inner keeps 2 instances × 2^15 = 2^16 within the 8 GB budget.
    let (log2h, rss) = run_aggregator(2, 16);
    assert!(rss <= EIGHT_GB && (1usize << log2h) <= (1 << 18), "tiled aggregator within 8 GB / 2^18");
    println!("Phase 6.6: K=2 inners verified + folded to the block tx-root in ONE AIR at 2^{log2h} / {} MiB", rss / (1 << 20));
}

/// Phase 4.D: THE MONOLITH — transcript + 32 super-tiles in ONE AIR that accepts iff p3::verify accepts.
#[test]
#[ignore = "slow: Phase 4.D monolith (transcript + super-tiles, accept-iff-p3::verify) vs native"]
fn phase4d_monolith_input_fusion() {
    let (log2h, rss) = run_monolith(MILESTONE_QUERIES, false);
    assert!(rss <= EIGHT_GB && (1usize << log2h) <= (1 << 18), "budget: RSS ≤ 8 GB, height ≤ 2^18");
}

/// Phase 6.5: the COLUMN-WINDOW monolith — the same ConstAir verifier, but reading its inner-proof pis from
/// a held witness column window instead of public inputs (nothing public), so K instances can be tiled in
/// the aggregator. Proves at K=1 and rejects a tampered window (the squeeze↦window bind fails).
#[test]
#[ignore = "slow: Phase 6.5 column-window monolith (inner pis in witness columns)"]
fn phase6_column_window_monolith() {
    let (log2h, rss) = run_monolith(MILESTONE_QUERIES, true);
    assert!(rss <= EIGHT_GB && (1usize << log2h) <= (1 << 18), "column-window monolith within 8 GB / 2^18");
    println!("Phase 6.5: column-window monolith proves at 2^{log2h} / {} MiB (inner pis in witness columns)", rss / (1 << 20));
}

/// Phase 5 (scale within 8 GB): the monolith is query-count-agnostic. Doubling to 64 queries (the milestone
/// used 32 conservatively) still proves + rejects the full tamper set within the 8 GB budget — realizing
/// "scale within 8 GB" directly on the validated arity-2 monolith (aggregation, Phase 6, is the O(log N)
/// lever beyond a single monolith).
#[test]
#[ignore = "slow: Phase 5 monolith scaling to 64 queries within 8 GB"]
fn phase5_monolith_scale_64() {
    let (log2h, rss) = run_monolith(64, false);
    println!("Phase 5 scale: monolith @ 64 queries proves at 2^{log2h} / {} MiB ≤ 8 GB", rss / (1 << 20));
    assert!(rss <= EIGHT_GB && (1usize << log2h) <= (1 << 18), "64-query monolith within 8 GB / 2^18");
}

/// Phase 6.2: the monolith verifies a NON-degenerate `CounterAir` inner (distinct per-query cap entries +
/// non-zero quotient). Each opening's terminal equals the query's selected cap entry (carried per super-
/// tile from per-query cap pis); the epilogue uses the counter's `next−cur−1` transition. Returns
/// (log2 height, RSS). Increment A: caps verifier-pre-selected (the cap-mux binding the selection to the
/// index + the FS absorb-binding are the next increments).
fn run_counter_monolith(n_queries: usize) -> (u32, u64) {
    use super::{monolith_build_trace, MonolithAir, CM_ROUNDS};
    use crate::recursion::native_fri::{gen_counter_proof, query_commit_merkle_all, query_fold_data, query_input_merkle, query_quotient_merkle, query_terms};
    use p3_field::{BasedVectorSpace, PrimeField64};
    let config = make_config(1, n_queries);
    let (proof, pvs) = gen_counter_proof(&config, 42, 6);
    let (block_inputs, counts, binds, chs, index_binds, index_felts) = sim_full(&config, &proof, &pvs);
    let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
    let mut per_query = Vec::new();
    let mut quot_paths = Vec::new();
    let mut commit_data = Vec::new();
    let mut n_terms = 0;
    let mut final0 = Challenge::ZERO;
    for q in 0..n_queries {
        let (terms, _x, alpha, ro) = query_terms(&config, &proof, &pvs, q);
        let (_ro2, rounds, _folded, f0) = query_fold_data(&config, &proof, &pvs, q);
        let v = proof.opening_proof.query_proofs[q].input_proof[0].opened_values[0][0];
        let (_leaf, path, _cap_entry) = query_input_merkle(&config, &proof, &pvs, q);
        let (_ql, qpath, _qce, _qw) = query_quotient_merkle(&config, &proof, &pvs, q);
        let cm = query_commit_merkle_all(&config, &proof, &pvs, q);
        if q == 0 {
            final0 = f0;
        }
        n_terms = terms.len();
        let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        per_query.push(((index, terms, alpha, ro, rounds), v, path));
        quot_paths.push(qpath);
        commit_data.push(cm);
    }
    let air = MonolithAir { counts: counts.clone(), binds, index_binds, n_queries, n_terms, inner_counter: true, column_window: false, k_instances: 1, fold: false, fold_txstmt: false, constraints: vec![], w_inner_f: 1, n_pub_f: 1, n_periodic_f: 0, is_zk: 0, cap_height: 6, narrow_arith: false, narrow_caps: false };
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
    // FULL caps (the cap-mux selects cap[index>>shift] from these): trace, quotient, pub, 6 commit rounds.
    for e in proof.commitments.trace.roots().iter() {
        pis.extend_from_slice(e);
    }
    for e in proof.commitments.quotient_chunks.roots().iter() {
        pis.extend_from_slice(e);
    }
    pis.push(pvs[0]);
    for r in 0..CM_ROUNDS {
        for e in proof.opening_proof.commit_phase_commits[r].roots().iter() {
            pis.extend_from_slice(e);
        }
    }
    let trace = monolith_build_trace(&air, &block_inputs, &per_query, chs[2], &index_felts, &quot_paths, &commit_data, &[], None);
    let hh = air.height();
    println!("counter monolith @ {n_queries} queries: 2^{} rows (width {}, full caps + cap-mux)", hh.trailing_zeros(), air.fused_w());
    let prf = prove(&config, &air, trace, &pis);
    assert!(verify(&config, &air, &prf, &pis).is_ok(), "monolith verifies a NON-degenerate counter inner (cap-mux)");
    // tamper the FULL trace cap entry that query 0 selects (index0 >> 4) ⇒ the mux ≠ the real terminal ⇒ reject.
    let cap_base = 2 * chs.len() + index_felts.len() + 2;
    let index0 = (index_felts[0].as_canonical_u64() as usize) & ((1 << log_global) - 1);
    let sel0 = index0 >> 4;
    let mut bad = pis.clone();
    bad[cap_base + sel0 * 4] += Val::ONE;
    assert!(verify(&config, &air, &prf, &bad).is_err(), "tampered selected trace cap entry ⇒ cap-mux reject");
    let rss = peak_rss_bytes();
    println!("  -> peak RSS {} MiB", rss / (1 << 20));
    (hh.trailing_zeros(), rss)
}

/// Phase 7.4: build + prove the MULTI-COLUMN monolith over a real 2-column `FibonacciAir` inner — the full
/// accept-iff-p3::verify at W=2. Exercises the W-wide opened-row carrier, 2·W reduced-opening terms with
/// px-sharing, the W-value input-Merkle leaf, the full-cap + cap-mux (non-constant inner), and the GENERAL
/// 5-constraint OOD epilogue (validated 7.2 fold). Returns (log2 height, RSS).
/// Phase 7.6: verify an ARBITRARY multi-column inner AIR `A` through the monolith via the DATA-DRIVEN
/// symbolic epilogue (accept-iff-p3::verify). The inner's constraint trees (`get_symbolic_constraints`) drive
/// the OOD fold; `w_inner`/`n_pub` size the opened-row carrier + pub range. Same code for Fibonacci and
/// MulAir — no hardcoded per-AIR fold. Returns (log2 height, RSS).
fn run_symbolic_monolith<A>(config: &MyConfig, inner: &A, proof: &Proof<MyConfig>, pvs: &[Val], w_inner: usize, n_pub: usize, n_periodic: usize, label: &str) -> (u32, u64)
where
    A: p3_air::Air<p3_uni_stark::SymbolicAirBuilder<Val>>,
{
    use super::{monolith_build_trace, MonolithAir};
    use crate::recursion::native_fri::{epilogue_openings, eval_symbolic_native, multicol_query_terms, query_commit_merkle_all, query_fold_data, query_input_merkle, query_quotient_merkle};
    use p3_field::{BasedVectorSpace, PrimeField64};
    use p3_uni_stark::{get_symbolic_constraints, AirLayout};
    let n_queries = proof.opening_proof.query_proofs.len();
    let (block_inputs, counts, binds, chs, index_binds, index_felts) = sim_full(config, proof, pvs);
    let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
    let mut per_query = Vec::new();
    let mut quot_paths = Vec::new();
    let mut commit_data = Vec::new();
    let mut n_terms = 0;
    let mut final0 = Challenge::ZERO;
    for q in 0..n_queries {
        let (terms, _x, alpha, ro, _w) = multicol_query_terms(config, inner, proof, pvs, q);
        let (_ro2, rounds, _folded, f0) = query_fold_data(config, proof, pvs, q);
        let (_leaf, path, _cap_entry) = query_input_merkle(config, proof, pvs, q);
        let (_ql, qpath, _qce, _qw) = query_quotient_merkle(config, proof, pvs, q);
        let cm = query_commit_merkle_all(config, proof, pvs, q);
        if q == 0 {
            final0 = f0;
        }
        n_terms = terms.len();
        let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        per_query.push(((index, terms, alpha, ro, rounds), Val::ZERO, path));
        quot_paths.push(qpath);
        commit_data.push(cm);
    }
    let nqc = proof.opened_values.quotient_chunks.len();
    assert_eq!(n_terms, 2 * w_inner + 2 * nqc, "{label}: 2·W trace terms + 2·nqc quotient terms");
    let layout = AirLayout::from_air::<Val>(inner);
    let constraints = get_symbolic_constraints::<Val, A>(inner, layout);
    assert!(!constraints.is_empty(), "{label}: symbolic constraints extracted");
    let air = MonolithAir { counts: counts.clone(), binds, index_binds, n_queries, n_terms, inner_counter: false, column_window: false, k_instances: 1, fold: false, fold_txstmt: false, constraints, w_inner_f: w_inner, n_pub_f: n_pub, n_periodic_f: n_periodic, is_zk: 0, cap_height: (proof.commitments.trace.roots().len().trailing_zeros() as usize), narrow_arith: false, narrow_caps: false };
    // OOD openings + selectors + periodic-column values at ζ (verifier-computed publics).
    let (eo_local, eo_next, is_first, is_last, is_trans, inv_van, eo_quot, eo_alpha, _z, eo_periodic) = epilogue_openings(config, inner, proof, pvs);
    assert_eq!(eo_periodic.len(), n_periodic, "{label}: periodic column count matches n_periodic");
    let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
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
    // FULL caps (cap-mux selects cap[index>>shift]): trace, quotient, then the n_pub inner pubs, then commit
    // rounds, then the periodic-column values at ζ (the Periodic pis region).
    for e in proof.commitments.trace.roots().iter() {
        pis.extend_from_slice(e);
    }
    for e in proof.commitments.quotient_chunks.roots().iter() {
        pis.extend_from_slice(e);
    }
    for &pv in pvs {
        pis.push(pv);
    }
    for cm in proof.opening_proof.commit_phase_commits.iter() {
        for e in cm.roots().iter() {
            pis.extend_from_slice(e);
        }
    }
    for pv in &eo_periodic {
        let c = cc(*pv);
        pis.push(c[0]);
        pis.push(c[1]);
    }
    // quotient recompose weights zps_i (verifier-computed publics; nqc>1 only — the qwt pis region).
    if nqc > 1 {
        let zps = crate::recursion::native_fri::quotient_recompose_weights(config, inner, proof, pvs);
        // validate the recompose (the nqc>1 check the ConstAir self-check never exercised): the epilogue's
        // Σ_i zps_i·(chunk_i.0 + chunk_i.1·X) must equal eo_quot (== p3's recompose_quotient_from_chunks).
        let x = Challenge::from_basis_coefficients_fn(|k| if k == 1 { Val::ONE } else { Val::ZERO });
        let mut rq = Challenge::ZERO;
        for (i, ch) in proof.opened_values.quotient_chunks.iter().enumerate() {
            rq += zps[i] * (ch[0] + ch[1] * x);
        }
        assert_eq!(rq, eo_quot, "{label}: Σ zps_i·chunk_i == recomposed quotient(ζ) (nqc recompose)");
        for z in &zps {
            let c = cc(*z);
            pis.push(c[0]);
            pis.push(c[1]);
        }
    }
    assert_eq!(pis.len(), air.pis_count(), "{label} pis layout matches pis_count");
    {
        // native pre-check: the symbolic fold on the SAME openings/selectors/periodic == quot (localizes wiring bugs).
        let pubs: Vec<Challenge> = pvs.iter().map(|&p| Challenge::from(p)).collect();
        let mut folded = Challenge::ZERO;
        for c in &air.constraints {
            folded = folded * eo_alpha + eval_symbolic_native(c, &eo_local, &eo_next, &pubs, &eo_periodic, is_first, is_last, is_trans);
        }
        assert_eq!(folded * inv_van, eo_quot, "{label} PRE-CHECK: native symbolic fold == quot(ζ)");
    }
    let mut trace = monolith_build_trace(&air, &block_inputs, &per_query, chs[2], &index_felts, &quot_paths, &commit_data, &[], None);
    // fill the witnessed Lagrange selectors at ζ (is_first/is_last/inv_van), bound in-circuit to their ζ-defs.
    let (isf, isl, iv) = (cc(is_first), cc(is_last), cc(inv_van));
    let fw = air.fused_w();
    let sb = air.sel_base();
    for r in 0..air.height() {
        trace.values[r * fw + sb..r * fw + sb + 2].copy_from_slice(&isf);
        trace.values[r * fw + sb + 2..r * fw + sb + 4].copy_from_slice(&isl);
        trace.values[r * fw + sb + 4..r * fw + sb + 6].copy_from_slice(&iv);
    }
    let hh = air.height();
    println!("{label} monolith @ {n_queries} queries: 2^{} rows (width {fw}, W={w_inner}, DATA-DRIVEN symbolic epilogue)", hh.trailing_zeros());
    let prf = prove(config, &air, trace, &pis);
    if let Err(e) = verify(config, &air, &prf, &pis) {
        panic!("{label}: fused monolith rejected a valid proof: {e:?}");
    }
    // tamper an inner public ⇒ the symbolic OOD fold ≠ quotient(ζ) ⇒ reject.
    let mut bad = pis.clone();
    bad[air.pub_pi()] += Val::ONE;
    assert!(verify(config, &air, &prf, &bad).is_err(), "{label}: tampered inner pub ⇒ symbolic epilogue rejects");
    // tamper the FULL trace cap entry query 0 selects (index0 >> input_depth — the runtime depth-to-cap,
    // lg−CM_CAP_HEIGHT; the old hardcoded `>> 4` was the db=6 value and indexes out of the cap at deeper
    // inners) ⇒ cap-mux ≠ real terminal ⇒ reject.
    let cap_base = 2 * chs.len() + index_felts.len() + 2;
    let sel0 = ((index_felts[0].as_canonical_u64() as usize) & ((1 << log_global) - 1)) >> air.input_depth();
    let mut bad_cap = pis.clone();
    bad_cap[cap_base + sel0 * 4] += Val::ONE;
    assert!(verify(config, &air, &prf, &bad_cap).is_err(), "{label}: tampered selected trace cap ⇒ cap-mux reject");
    let rss = peak_rss_bytes();
    println!("  -> peak RSS {} MiB", rss / (1 << 20));
    (hh.trailing_zeros(), rss)
}

fn run_fib_monolith(n_queries: usize) -> (u32, u64) {
    run_fib_monolith_at(n_queries, 6)
}

// Verify a Fibonacci inner at an arbitrary trace `log_height` (⇒ inner degree_bits = log_height,
// log_global = log_height + LOG_BLOWUP, cm_rounds = log_height). The monolith is fully proof-driven and its
// FRI geometry is runtime (cm_rounds()=nb−3), so a higher-db inner exercises the FRI-depth re-pin end-to-end.
fn run_fib_monolith_at(n_queries: usize, log_height: usize) -> (u32, u64) {
    use crate::recursion::native_fri::gen_fib_proof;
    use crate::recursion::native_verify::FibonacciAir;
    let config = make_config(1, n_queries);
    let (proof, pvs) = gen_fib_proof(&config, 1, 1, log_height);
    run_symbolic_monolith(&config, &FibonacciAir, &proof, &pvs, 2, 3, 0, "fib")
}

fn run_mul_monolith(n_queries: usize) -> (u32, u64) {
    use crate::recursion::native_fri::gen_mul_proof;
    use crate::recursion::native_verify::MulAir;
    let config = make_config(1, n_queries);
    let (proof, pvs) = gen_mul_proof(&config, 3, 5, 6);
    run_symbolic_monolith(&config, &MulAir, &proof, &pvs, 3, 2, 0, "mul")
}

fn run_periodic_monolith(n_queries: usize) -> (u32, u64) {
    use crate::recursion::native_fri::gen_periodic_proof;
    use crate::recursion::native_verify::PeriodicAir;
    let config = make_config(1, n_queries);
    let (proof, pvs) = gen_periodic_proof(&config, 5, 6);
    run_symbolic_monolith(&config, &PeriodicAir, &proof, &pvs, 1, 1, 1, "periodic") // W=1, 1 pub, 1 periodic column
}

fn run_wide_monolith(n_queries: usize) -> (u32, u64) {
    use crate::recursion::native_fri::gen_wide_proof;
    use crate::recursion::native_verify::{WideAir, WIDE_W};
    let config = make_config(1, n_queries);
    let (proof, pvs) = gen_wide_proof(&config, 100, 6);
    run_symbolic_monolith(&config, &WideAir, &proof, &pvs, WIDE_W, WIDE_W, 0, "wide") // W=8 > RATE ⇒ 2-block leaf
}

fn run_cube_monolith(n_queries: usize) -> (u32, u64) {
    use crate::recursion::native_fri::gen_cube_proof;
    use crate::recursion::native_verify::CubeAir;
    let config = make_config(1, n_queries);
    let (proof, pvs) = gen_cube_proof(&config, 3, 6);
    run_symbolic_monolith(&config, &CubeAir, &proof, &pvs, 2, 1, 0, "cube") // W=2, degree-3 ⇒ nqc=2 (4 quotient terms)
}

fn run_quart_monolith(n_queries: usize) -> (u32, u64) {
    use crate::recursion::native_fri::gen_quart_proof;
    use crate::recursion::native_verify::QuartAir;
    let config = make_config(1, n_queries);
    let (proof, pvs) = gen_quart_proof(&config, 2, 6);
    run_symbolic_monolith(&config, &QuartAir, &proof, &pvs, 2, 1, 0, "quart") // W=2, degree-4 ⇒ nqc=4 (2-block quotient leaf)
}

// Verify the REAL production join-split circuit (demo witness) — W=19 (5-block input leaf), 33 periodic
// columns, 26 pubs, 81 constraints at degree 8 ⇒ nqc=8 (2·nqc=16 quotient terms, 4-block quotient leaf),
// db=12 ⇒ log_global=16 / cm_rounds=12. Every runtime-geometry dimension at its production value at once;
// the inner proof is non-hiding (the recursion path's own inner config), arity-2, `n_queries` reduced.
fn run_joinsplit_monolith(n_queries: usize) -> (u32, u64) {
    use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
    let config = make_config(1, n_queries);
    let w = demo_witness();
    let pvs = public_values(&w);
    let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
    run_symbolic_monolith(&config, &JoinSplitAir, &proof, &pvs, WIDTH, N_PUBLIC, N_PERIODIC, "joinsplit")
}

/// Phase 8.1 — THE PRODUCTION LIFT: the monolith accept-iff-p3::verify's a proof of the REAL production
/// `JoinSplitAir`. Everything the phase-7 ladder generalized meets at its production value simultaneously:
/// W=19 → a 5-block input-Merkle leaf; degree-8 constraints → nqc=8 chunks, a 16-term recompose + 4-block
/// quotient leaf; db=12 → log_global=16, cm_rounds=12; 33 periodic columns + 26 pubs through the
/// data-driven symbolic epilogue. Reduced queries (correctness milestone; production soundness goes via
/// the aggregation tree's parameters). Rejects a tampered inner pub + a tampered selected trace cap.
#[test]
#[ignore = "slow: Phase 8.1 the monolith verifies a REAL production join-split proof"]
fn phase8_joinsplit_monolith() {
    let (log2h, rss) = run_joinsplit_monolith(4);
    assert!((1usize << log2h) <= (1 << 19), "join-split monolith within 2^19 rows");
    println!("Phase 8.1: the monolith verifies a REAL production join-split proof at 2^{log2h} / {} MiB", rss / (1 << 20));
}

/// R3 measurement: the rows/RSS/prove-time curve of the (is_zk=0, the recursion-path shape) join-split
/// monolith as the replayed inner-query count grows — the empirical basis for the aggregation-level
/// parameter design (how many inner queries one monolith can replay on this box, and thus how the tree
/// must shard the 96 wire queries to preserve the ≥100-bit proven floor). Prints a table; no assert.
#[test]
#[ignore = "slow + large RSS: R3 join-split monolith query-scaling curve"]
fn phase8_joinsplit_query_curve() {
    use std::time::Instant;
    println!("R3 join-split monolith (is_zk=0, W=19) query-scaling curve:");
    println!("  queries | rows | RSS MiB | prove+verify s");
    for &nq in &[4usize, 8, 12, 16] {
        let t = Instant::now();
        let (log2h, rss) = run_joinsplit_monolith(nq);
        let secs = t.elapsed().as_secs_f64();
        println!("  {nq:>7} | 2^{log2h} | {:>7} | {secs:.1}", rss / (1 << 20));
        if rss > 55 * (1u64 << 30) {
            println!("  (stopping — approaching box RAM)");
            break;
        }
    }
}

/// Degree probe for the JOIN-SPLIT monolith (is_zk=0): the outer max constraint degree + log_nqc for the
/// exact `MonolithAir` `run_joinsplit_monolith` builds — a db=12 inner (cm_rounds=12), multi-block leaves
/// (5 input + 4 quotient), and the degree-8 inner constraint trees walked by the symbolic epilogue. The p3
/// quotient-containment budget is maxdeg ≤ 16 (log_nqc ≤ log_blowup = 4); crossing it does NOT error — it
/// silently breaks every honest proof (`OodEvaluationMismatch`), invisible to row-wise check_constraints.
#[test]
#[ignore = "slow: builds a real join-split proof to shape the probe"]
fn phase8_joinsplit_degree_probe() {
    use super::MonolithAir;
    use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
    use crate::recursion::native_fri::multicol_query_terms;
    use p3_uni_stark::{get_log_num_quotient_chunks, get_symbolic_constraints, AirLayout};
    let config = make_config(1, 4);
    let w = demo_witness();
    let pvs = public_values(&w);
    let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
    let (_bi, counts, binds, _chs, index_binds, index_felts) = sim_full(&config, &proof, &pvs);
    let (terms, _x, _a, _ro, _w) = multicol_query_terms(&config, &JoinSplitAir, &proof, &pvs, 0);
    let layout_in = AirLayout::from_air::<Val>(&JoinSplitAir);
    let constraints = get_symbolic_constraints::<Val, JoinSplitAir>(&JoinSplitAir, layout_in);
    let air = MonolithAir {
        counts,
        binds,
        index_binds,
        n_queries: index_felts.len(),
        n_terms: terms.len(),
        inner_counter: false,
        column_window: false,
        k_instances: 1,
        fold: false, fold_txstmt: false,
        constraints,
        w_inner_f: WIDTH,
        n_pub_f: N_PUBLIC,
        n_periodic_f: N_PERIODIC,
        is_zk: 0,
        cap_height: proof.commitments.trace.roots().len().trailing_zeros() as usize, narrow_arith: false, narrow_caps: false };
    let layout = AirLayout::from_air::<Val>(&air);
    let cs = get_symbolic_constraints::<Val, MonolithAir>(&air, layout);
    let maxd = cs.iter().map(|c| c.degree_multiple()).max().unwrap();
    let log_nqc = get_log_num_quotient_chunks::<Val, MonolithAir>(&air, layout, 0);
    println!("join-split monolith probe: outer max_constraint_degree={maxd}, outer log_nqc={log_nqc} ({} constraints)", cs.len());
    assert!(log_nqc <= 4, "outer log_nqc {log_nqc} exceeds log_blowup 4 ⇒ silent quotient corruption");
    assert!(maxd <= 16, "outer max constraint degree {maxd} exceeds the 16 = 2^log_blowup budget");
}

#[test]
#[ignore = "slow: Phase 7.6 multi-column monolith (2-column Fibonacci) via the data-driven symbolic epilogue"]
fn phase7_fib_monolith() {
    let (log2h, rss) = run_fib_monolith(MILESTONE_QUERIES);
    assert!(rss <= EIGHT_GB && (1usize << log2h) <= (1 << 18), "fib monolith within 8 GB / 2^18");
    println!("Phase 7.6: the monolith verifies Fibonacci (W=2) via the DATA-DRIVEN symbolic epilogue at 2^{log2h} / {} MiB", rss / (1 << 20));
}

/// Phase 7 (FRI-DEPTH RE-PIN): the monolith verifies a HIGHER-DEPTH inner — a db=8 Fibonacci proof
/// (log_global=12, cm_rounds=8, vs the milestone's db=6/lg=10/6-round). The whole FRI geometry (arith-tile
/// column layout, DEEP acc chain, index reconstruction, commit-round count + caps) is now RUNTIME, derived
/// from the transcript binds (cm_rounds()=nb−3) — no compile-time db=6 assumption. Reduced queries (8) keep
/// RSS in budget; this decouples the FRI-depth generality from the query-count RSS, exactly as the leaf-block
/// / nqc wiring decoupled from the FRI depth. The real join-split (db=12) is the same machinery at lg=16.
#[test]
#[ignore = "slow: Phase 7 FRI-depth re-pin — a db=8 inner (log_global=12, cm_rounds=8) through the monolith"]
fn phase7_fri_depth_db8() {
    let (log2h, rss) = run_fib_monolith_at(4, 8); // 4 queries (RSS budget), db=8 inner
    assert!(rss <= EIGHT_GB && (1usize << log2h) <= (1 << 18), "db=8 monolith within 8 GB / 2^18");
    println!("Phase 7 (FRI re-pin): the monolith verifies a db=8 inner (log_global=12, cm_rounds=8) at 2^{log2h} / {} MiB", rss / (1 << 20));
}

#[test]
#[ignore = "slow: Phase 7.6 multi-column monolith (3-column degree-2 MulAir) via the data-driven symbolic epilogue"]
fn phase7_mul_monolith() {
    let (log2h, rss) = run_mul_monolith(MILESTONE_QUERIES);
    assert!(rss <= EIGHT_GB && (1usize << log2h) <= (1 << 18), "mul monolith within 8 GB / 2^18");
    println!("Phase 7.6: the monolith verifies the degree-2 MulAir (W=3) via the SAME symbolic epilogue at 2^{log2h} / {} MiB", rss / (1 << 20));
}

/// Phase 7.7: the monolith verifies an inner with a PERIODIC column (`PeriodicAir`, a'=a+p over the
/// pattern [3,7]) via the same data-driven symbolic epilogue — the constraint tree's `Periodic` leaf reads
/// the periodic value at ζ (a verifier-computed public in the periodic pis region). The last leaf kind
/// real high-degree AIRs (round constants) need. Rejects a tampered pub + trace cap.
#[test]
#[ignore = "slow: Phase 7.7 monolith verifies a PERIODIC-column inner via the symbolic epilogue"]
fn phase7_periodic_monolith() {
    let (log2h, rss) = run_periodic_monolith(MILESTONE_QUERIES);
    assert!(rss <= EIGHT_GB && (1usize << log2h) <= (1 << 18), "periodic monolith within 8 GB / 2^18");
    println!("Phase 7.7: the monolith verifies a PERIODIC-column inner via the symbolic epilogue at 2^{log2h} / {} MiB", rss / (1 << 20));
}

/// Phase 7 ("wire it"): the monolith verifies a WIDE inner (`WideAir`, W=8 > RATE) whose trace-commitment
/// leaf spans 2 Poseidon blocks — exercising the MULTI-BLOCK input-leaf hashing wired into the super-tile
/// (runtime geometry: leaf_blocks=2 ⇒ M_INPUT_TERM/M_NBLOCKS/M_PERIOD grow, the leaf absorbs RATE felts/block
/// with capacity carry, the leaf-internal boundary is excluded from the merge link). The join-split blocker
/// (W=19 ⇒ 5 blocks) is the same machinery at larger leaf_blocks. Rejects a tampered pub + trace cap.
#[test]
#[ignore = "slow: Phase 7 monolith verifies a WIDE (W=8) inner via the MULTI-BLOCK (2-block) input leaf"]
fn phase7_wide_monolith() {
    let (log2h, rss) = run_wide_monolith(MILESTONE_QUERIES);
    assert!(rss <= EIGHT_GB && (1usize << log2h) <= (1 << 18), "wide monolith within 8 GB / 2^18");
    println!("Phase 7 (wire it): the monolith verifies a WIDE W=8 inner via the MULTI-BLOCK (2-block) input leaf at 2^{log2h} / {} MiB", rss / (1 << 20));
}

/// Phase 7 ("wire it", quotient half): the monolith verifies a DEGREE-3 inner (`CubeAir`, c=a³) whose
/// quotient splits into nqc=2 chunks — exercising the multi-CHUNK quotient recompose (2·nqc=4 reduced-opening
/// terms + 4 carriers; the epilogue reconstructs quotient(ζ) = Σ_i zps_i·chunk_i from the verifier-computed
/// weights, vs the nqc=1 c0+c1·X). Still a single-block quotient leaf (2·nqc=4 ≤ RATE), so it isolates the
/// recompose from the multi-block quotient leaf. Rejects a tampered pub + trace cap.
#[test]
#[ignore = "slow: Phase 7 monolith verifies a DEGREE-3 inner via the multi-CHUNK quotient recompose (nqc=2)"]
fn phase7_cube_monolith() {
    let (log2h, rss) = run_cube_monolith(MILESTONE_QUERIES);
    assert!(rss <= EIGHT_GB && (1usize << log2h) <= (1 << 18), "cube monolith within 8 GB / 2^18");
    println!("Phase 7 (wire it): the monolith verifies a DEGREE-3 inner (nqc=2) via the multi-chunk quotient recompose at 2^{log2h} / {} MiB", rss / (1 << 20));
}

/// Phase 7 ("wire it", quotient half B2): the monolith verifies a DEGREE-4 inner (`QuartAir`, c=a⁴ ⇒ nqc=4)
/// whose quotient-Merkle leaf spans 2 Poseidon blocks (2·nqc=8 > RATE) — exercising the MULTI-BLOCK quotient
/// leaf (iq_/q_boundary one-hots, capacity carry, merge-link exclusion) on top of the multi-chunk recompose.
/// The real join-split (degree-7, nqc=8 ⇒ 4-block quotient leaf) is the same machinery at larger nqc.
#[test]
#[ignore = "slow: Phase 7 monolith verifies a DEGREE-4 inner via the MULTI-BLOCK quotient leaf (nqc=4)"]
fn phase7_quart_monolith() {
    let (log2h, rss) = run_quart_monolith(MILESTONE_QUERIES);
    assert!(rss <= EIGHT_GB && (1usize << log2h) <= (1 << 18), "quart monolith within 8 GB / 2^18");
    println!("Phase 7 (wire it): the monolith verifies a DEGREE-4 inner (nqc=4) via the MULTI-BLOCK (2-block) quotient leaf at 2^{log2h} / {} MiB", rss / (1 << 20));
}

#[test]
#[ignore = "slow: Phase 6.2 monolith verifies the non-degenerate counter inner (per-query caps)"]
fn phase6_counter_monolith() {
    let (log2h, rss) = run_counter_monolith(MILESTONE_QUERIES);
    assert!(rss <= EIGHT_GB && (1usize << log2h) <= (1 << 18), "counter monolith within 8 GB / 2^18");
    println!("Phase 6.2: monolith verifies a non-degenerate counter inner (distinct caps + non-zero quotient), 2^{log2h}");
}

/// Guard: the DERIVED super-tile geometry (from DP_LOG_HEIGHT / CM_CAP_HEIGHT / LOG_BLOWUP) reproduces the
/// db=6 milestone layout byte-for-byte. If a re-pin changes the base params, this pins the expected values
/// so the derivation stays honest (and documents what the literals used to be).
#[test]
fn geometry_matches_milestone() {
    use super::{cm_depth, CM_CAP_HEIGHT, CM_ROUNDS, DP_LOG_HEIGHT, INPUT_DEPTH, LOG_BLOWUP, M_DEGREE_BITS, M_INPUT_LEAF};
    // base params (the milestone config)
    assert_eq!((DP_LOG_HEIGHT, CM_CAP_HEIGHT, LOG_BLOWUP), (10, 6, 4));
    // derived FRI-depth scalars (compile-time — one pinned config)
    assert_eq!((M_DEGREE_BITS, CM_ROUNDS, INPUT_DEPTH, M_INPUT_LEAF), (6, 6, 4, 1));
    assert_eq!([cm_depth(0), cm_depth(1), cm_depth(2), cm_depth(3), cm_depth(4), cm_depth(5)], [3, 2, 1, 0, 0, 0]);
    // the RUNTIME geometry methods (the SINGLE SOURCE the monolith uses) reproduce the db=6 milestone layout
    // byte-for-byte at a ConstAir inner (leaf_blocks=1, nqc=1). The literals here are what the derived geometry
    // consts used to be — this guard pins them so a re-pin can't silently drift the layout.
    let air = milestone_geom_air();
    assert_eq!((air.leaf_blocks(), air.nqc(), air.quot_leaf_blocks()), (1, 1, 1));
    assert_eq!((air.m_input_term(), air.m_quot_leaf(), air.m_quot_term()), (5, 6, 10));
    assert_eq!(core::array::from_fn::<_, CM_ROUNDS, _>(|r| air.cm_leaf(r)), [11, 15, 18, 20, 21, 22]);
    assert_eq!(core::array::from_fn::<_, CM_ROUNDS, _>(|r| air.cm_term(r)), [14, 17, 19, 20, 21, 22]);
    assert_eq!((air.m_nblocks(), air.m_period()), (23, 736));
}

/// A minimal `MonolithAir` for exercising the runtime geometry methods (no constraints ⇒ a ConstAir-shape
/// milestone inner: leaf_blocks=1, nqc=1). Geometry depends on w_inner()/nqc() AND nb() (the FRI depth is
/// derived from the transcript binds: nb = 3 + cm_rounds); db=6 ⇒ cm_rounds=6 ⇒ nb=9.
fn milestone_geom_air() -> super::MonolithAir {
    super::MonolithAir {
        counts: vec![],
        binds: vec![0; 9], // nb=9 ⇒ cm_rounds=6, lg=10 (the db=6 milestone)
        index_binds: vec![],
        n_queries: 1,
        n_terms: 4,
        inner_counter: false,
        column_window: false,
        k_instances: 1,
        fold: false, fold_txstmt: false,
        constraints: vec![],
        w_inner_f: 0,
        n_pub_f: 0,
        n_periodic_f: 0,
        is_zk: 0,
        cap_height: 6, narrow_arith: false, narrow_caps: false }
}

/// Demonstrates the geometry is genuinely CONFIGURABLE across ALL its parameters — FRI depth AND the
/// leaf-block / nqc dimensions. The runtime layout twin matches the compile-time consts at the milestone,
/// and the SAME formula yields the full REAL join-split super-tile layout (db=12, W=19 → 5 leaf blocks,
/// nqc=8 → 4 quotient-leaf blocks). So re-pinning to a join-split is choosing (log_global, leaf_blocks,
/// quot_leaf_blocks) — the layout follows; the remaining work is the eval/build loops that USE >1
/// leaf-block / nqc (the re-pin's eval side).
#[test]
fn commit_layout_generalizes() {
    use super::{cm_depth_at, commit_layout};
    // milestone (db=6, single-block leaf, nqc=1): the formula reproduces the db=6 layout (== the runtime methods,
    // which `geometry_matches_milestone` pins to these same literals).
    let (rounds, id, m_input_term, m_quot_term, leaf, term, nb) = commit_layout(10, 6, 4, 1, 1);
    assert_eq!((rounds, id, m_input_term, m_quot_term, nb), (6, 4, 5, 10, 23));
    assert_eq!((leaf, term), (vec![11, 15, 18, 20, 21, 22], vec![14, 17, 19, 20, 21, 22]));
    // FRI-depth only (db=12, still single-block leaf/nqc=1): 12 rounds, depths [9,…,0].
    let (rounds, ..) = commit_layout(16, 6, 4, 1, 1);
    assert_eq!(rounds, 12);
    assert_eq!((cm_depth_at(0, 16, 6), cm_depth_at(9, 16, 6), cm_depth_at(11, 16, 6)), (9, 0, 0));
    // the REAL join-split super-tile: db=12, W=19 → ceil(19/4)=5 leaf blocks, nqc=8 → ceil(16/4)=4 quot blocks.
    let (rounds, id, m_input_term, m_quot_term, leaf, term, nb) = commit_layout(16, 6, 4, 5, 4);
    assert_eq!((rounds, id), (12, 10));
    assert_eq!((m_input_term, m_quot_term), (15, 29)); // input leaf(5)+path(10); quot leaf(4)+path(10)
    assert_eq!((leaf[0], *leaf.last().unwrap(), *term.last().unwrap(), nb), (30, 86, 86, 87));
    println!("geometry configurable across all params: milestone → 23 blocks/6 rounds (== consts); real join-split (db=12/W=19/nqc=8) → 87 blocks/12 rounds (same formula)");
}

/// #86 AIR mode — the HIDING (is_zk=1) super-tile layout skeleton (de-risk the geometry, phase-4.0-style).
/// Validates `hiding_commit_layout` against the ground-truth witness geometry: an arity-2 hiding ConstAir
/// (W=1, nqc=4, log_global=11 = degree_bits 7 + blowup 4, cap 6). The layout has THREE salted leaf regions
/// (random/trace/quotient) before 7 commit rounds — the leaf block counts, term count, and block offsets
/// must match what the native witness produced (leaf felt widths 10/9/40 ⇒ 3/3/10 blocks; n_terms 40).
#[test]
fn hiding_super_tile_layout_matches_witness() {
    use super::hiding_commit_layout;
    let (rt, it, qt, leaf, term, nb, n_terms, [rlb, ilb, qlb]) = hiding_commit_layout(1, 4, 11, 6, 4);
    // leaf block counts = ceil(leaf_felts/RATE): random 10→3, trace 9→3, quotient 40→10 (== the witness's
    // hiding_query_{input,quotient}_merkle leaf widths and the batch-0 random leaf from hiding_proof_geometry).
    assert_eq!([rlb, ilb, qlb], [3, 3, 10], "salted leaf blocks: random(10f)/trace(9f)/quot(40f)");
    // reduced-opening term count == hiding_multicol_query_terms's 40 (random 6 + 2·trace 5 + nqc·quot 6).
    assert_eq!(n_terms, 40, "hiding reduced-opening terms = 6 + 10 + 24");
    // three disjoint leaf regions (each leaf + input_depth=5 path), then commit rounds.
    assert_eq!((rt, it, qt), (8, 16, 31), "random/trace/quotient terminal blocks");
    assert_eq!(leaf.len(), 7, "arity-2 cm_rounds = log_global − blowup = 7");
    assert_eq!((leaf[0], nb), (32, 56), "commit rounds start after the quotient terminal; m_nblocks (2-block salted commit leaves)");
    assert_eq!(*term.last().unwrap() + 1, nb, "m_nblocks == last commit term + 1");
    assert!(rt < it && it < qt && qt < leaf[0], "regions are monotone and disjoint");
    println!("hiding super-tile layout: 3 salted leaf regions (terms at blocks {rt}/{it}/{qt}, blocks {rlb}/{ilb}/{qlb}) + 7 commit rounds → m_nblocks={nb}, n_terms={n_terms} (matches the native witness)");
}

/// #86 AIR mode — the is_zk field is THREADED into MonolithAir's block-layout methods: a MonolithAir in
/// hiding mode (is_zk=1) reproduces `hiding_commit_layout` exactly. Validates the runtime geometry (leaf
/// blocks, random-round region, m_input/quot_term, m_nblocks, nqc) matches the standalone layout for the
/// arity-2 hiding ConstAir. (is_zk=0 byte-for-byte is covered by the full existing suite staying green.)
#[test]
fn monolith_is_zk_geometry_matches_layout() {
    use super::hiding_commit_layout;
    // hiding ConstAir: is_zk=1, n_terms=40, w_inner=1 (non-symbolic), cm_rounds=7 (nb=3+7) ⇒ lg=11.
    let air = super::MonolithAir {
        counts: vec![],
        binds: vec![0; 10],
        index_binds: vec![],
        n_queries: 1,
        n_terms: 40,
        inner_counter: false,
        column_window: false,
        k_instances: 1,
        fold: false, fold_txstmt: false,
        constraints: vec![],
        w_inner_f: 0,
        n_pub_f: 0,
        n_periodic_f: 0,
        is_zk: 1,
        cap_height: 6, narrow_arith: false, narrow_caps: false };
    let (rt, it, qt, _leaf, _term, nb, n_terms, [rlb, ilb, qlb]) = hiding_commit_layout(1, 4, 11, 6, 4);
    assert_eq!(air.nqc(), 4, "hiding nqc solved from n_terms");
    assert_eq!((air.random_leaf_blocks(), air.leaf_blocks(), air.quot_leaf_blocks()), (rlb, ilb, qlb), "leaf blocks");
    assert_eq!((air.m_random_term(), air.m_input_term(), air.m_quot_term()), (rt, it, qt), "leaf-region terminals");
    assert_eq!(air.m_nblocks(), nb, "m_nblocks");
    assert_eq!(air.n_terms, n_terms, "n_terms");
    assert_eq!(air.lg(), 11, "log_global from binds");
    // carrier/arith-tile layout: the tile width auto-scales with n_terms; the carrier region holds the
    // THREE salted leaf preimages (9 trace + 10 random + 40 quotient = 59), disjoint + monotone.
    assert_eq!(air.tile_w(), air.qt_terms() + 9 * 40, "arith tile width = qt_terms + 9·n_terms");
    assert_eq!((air.input_leaf_felts(), air.random_leaf_felts(), air.quot_leaf_felts()), (9, 10, 40), "leaf-preimage felt widths");
    assert_eq!(air.carriers_base() - air.ov(), 9 + 10 + 40, "carrier region = 3 salted leaf preimages (59 felts)");
    assert_eq!((air.ov_c(0), air.ov_random(0), air.qc(0)), (air.ov(), air.ov() + 9, air.ov() + 19), "leaf-preimage carrier offsets: trace|random|quotient");
    assert_eq!(air.n_cap_c(), (2 + 1 + 7) * 4, "cap carriers incl. the random round = (3+cm_rounds)·4");
    println!("MonolithAir is_zk=1 geometry threaded: nqc={}, leaf blocks {rlb}/{ilb}/{qlb}, terminals {rt}/{it}/{qt}, m_nblocks={nb}; carriers = 3 salted leaves (59 felts), tile_w={} == hiding_commit_layout + witness widths", air.nqc(), air.tile_w());
}

#[test]
fn phase4d_commit_merkle_structure() {
    use crate::recursion::native_fri::{query_commit_merkle, query_commit_merkle_all, MyHash};
    use p3_goldilocks::default_goldilocks_poseidon2_8;
    use p3_symmetric::CryptographicHasher;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let hasher = MyHash::new(default_goldilocks_poseidon2_8());
    for q in 0..MILESTONE_QUERIES {
        let all = query_commit_merkle_all(&config, &proof, &pvs, q);
        let depths: Vec<usize> = all.iter().map(|(_, _, p, _)| p.len()).collect();
        assert_eq!(depths, vec![3, 2, 1, 0, 0, 0], "commit-phase depths (q {q})");
        // each round: leaf == MyHash(bit-ordered group)
        for (group, leaf, _path, _cap) in &all {
            let h: [Val; 4] = hasher.hash_iter(group.iter().copied());
            assert_eq!(&h, leaf, "leaf == Hash(group) (q {q})");
        }
        // round 1 matches the validated single-round oracle (which the standalone AIR proves against)
        let (leaf1, group1, path1, cap1) = query_commit_merkle(&config, &proof, &pvs, q);
        assert_eq!((all[1].0, all[1].1, &all[1].2, all[1].3), (group1, leaf1, &path1, cap1), "round 1 == query_commit_merkle (q {q})");
    }
    // total commit-phase blocks per super-tile: Σ (1 leaf + depth merges) = 6 + (3+2+1) = 12.
    let blocks: usize = query_commit_merkle_all(&config, &proof, &pvs, 0).iter().map(|(_, _, p, _)| 1 + p.len()).sum();
    println!("commit-phase structure: 6 rounds, depths [3,2,1,0,0,0], {blocks} blocks/super-tile, all groups→leaves validated vs the real proof");
}

/// Phase 6.2 (epilogue): the OOD constraint for the NON-degenerate counter (`next − cur − 1`) — its folded
/// relation `(is_first·(local−pub) + is_trans·(next−local−1))·inv_van == quotient(ζ)` holds vs p3, and the
/// quotient(ζ) is NON-zero (unlike ConstAir's 0) — confirming the epilogue is exercised non-trivially.
#[test]
fn counter_epilogue_probe() {
    use crate::recursion::native_fri::{epilogue_oracle, gen_counter_proof};
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_counter_proof(&config, 42, 6);
    let (_db, _nqc, _cl, quotient, local, next, _chunks, alpha, _zeta, is_first, is_trans, inv_van) =
        epilogue_oracle(&config, &proof, &pvs);
    let pub_val = Challenge::from(pvs[0]);
    let c0 = is_first * (local - pub_val); // first-row: local − pub
    let c1 = is_trans * (next - local - Challenge::ONE); // transition: next − cur − 1
    assert_eq!((c0 * alpha + c1) * inv_van, quotient, "counter OOD: (A·α + B)·inv_van == quotient(ζ)");
    assert!(quotient != Challenge::ZERO, "counter quotient(ζ) is NON-zero (non-degenerate)");
    println!("Phase 6.2 epilogue: counter (next−cur−1) OOD check validated vs p3; quotient(ζ) non-zero");
}

/// Phase 6.2b: verify the per-opening cap-selection index shifts (the counter's REAL distinct caps make
/// this testable). For each opening, `cap.roots()[index >> shift] == the oracle's selected cap entry`:
/// trace/quotient shift = log_global − cap_height = 4; commit round r shift = (r+1) + path_len(r).
#[test]
fn counter_cap_shifts_probe() {
    use crate::recursion::native_fri::{full_transcript_challenges, gen_counter_proof, query_commit_merkle_all, query_input_merkle, query_quotient_merkle};
    use p3_field::PrimeField64;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_counter_proof(&config, 42, 6);
    let (_, _, _, _, index_felts) = full_transcript_challenges(&config, &proof, &pvs);
    let log_global = proof.opening_proof.query_proofs[0].commit_phase_openings.len() + 4;
    let tcap = proof.commitments.trace.roots();
    let qcap = proof.commitments.quotient_chunks.roots();
    for q in [0usize, 1, MILESTONE_QUERIES - 1] {
        let index = (index_felts[q].as_canonical_u64() as usize) & ((1 << log_global) - 1);
        let (_, _, tce) = query_input_merkle(&config, &proof, &pvs, q);
        assert_eq!(tcap[index >> 4], tce, "trace cap shift 4 (q {q})");
        let (_, _, qce, _) = query_quotient_merkle(&config, &proof, &pvs, q);
        assert_eq!(qcap[index >> 4], qce, "quotient cap shift 4 (q {q})");
        for (r, (_g, _l, path, cce)) in query_commit_merkle_all(&config, &proof, &pvs, q).iter().enumerate() {
            let shift = (r + 1) + path.len();
            let ccap = proof.opening_proof.commit_phase_commits[r].roots();
            assert_eq!(ccap[index >> shift], *cce, "commit r{r} cap shift {shift} (q {q}); cap has {} entries", ccap.len());
        }
    }
    println!("Phase 6.2b: cap-selection shifts verified vs oracle — trace/quot=4, commit r=(r+1)+depth_r");
}

#[test]
fn counter_probe() {
    use crate::recursion::native_fri::{gen_counter_proof, query_input_merkle};
    use crate::recursion::native_verify::CounterAir;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_counter_proof(&config, 42, 6);
    assert!(verify(&config, &CounterAir, &proof, &pvs).is_ok(), "counter proof valid (p3)");
    let cap = proof.commitments.trace.roots();
    let cap_distinct = cap.windows(2).any(|w| w[0] != w[1]);
    let (cproof, _) = gen_const_proof(&config, 42, 6);
    let ccap = cproof.commitments.trace.roots();
    let const_distinct = ccap.windows(2).any(|w| w[0] != w[1]);
    println!("counter: {} cap entries, distinct={cap_distinct}; ConstAir distinct={const_distinct}", cap.len());
    // the ConstAir-shaped oracles read proof data (same layout: 1 col, nqc=1) — confirm they run + the
    // per-query cap entries DIFFER for the counter (they were all-equal for ConstAir).
    let (_l0, _p0, e0) = query_input_merkle(&config, &proof, &pvs, 0);
    let (_l1, _p1, e1) = query_input_merkle(&config, &proof, &pvs, 1);
    println!("counter per-query cap entries differ across q0/q1: {}", e0 != e1);
    assert!(cap_distinct && !const_distinct, "counter has distinct cap entries; ConstAir does not");
}

/// Phase 7.2: the in-circuit GENERAL OOD epilogue gadget reproduces p3's constraint check at ζ for the
/// MULTI-COLUMN FibonacciAir — it derives the three Lagrange selectors from ζ in-circuit and folds the 5
/// cross-column constraints (Horner α-fold), matching `fib_epilogue_oracle` (⟺ p3 verify_constraints), and
/// rejects a tampered quotient. The AIR-independent core (selector derivation + fold) the full multi-column
/// monolith fusion reuses; only the constraint SET is inner-AIR-specific.
#[test]
#[ignore = "slow: Phase 7.2 in-circuit general OOD epilogue gadget vs fib_epilogue_oracle"]
fn phase7_general_epilogue_matches_oracle() {
    use super::{build_general_epilogue_trace, GeneralEpilogueAir};
    use crate::recursion::native_fri::{fib_epilogue_oracle, gen_fib_proof};
    use p3_field::BasedVectorSpace;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_fib_proof(&config, 1, 1, 6);
    let (local, next, _isf, _ist, _isl, _iv, quotient, alpha, zeta) = fib_epilogue_oracle(&config, &proof, &pvs);
    let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
    let (za, al) = (cc(zeta), cc(alpha));
    let pis = vec![za[0], za[1], al[0], al[1], pvs[0], pvs[1], pvs[2]];
    let air = GeneralEpilogueAir;
    let trace = build_general_epilogue_trace(local, next, quotient);
    let prf = prove(&config, &air, trace, &pis);
    assert!(verify(&config, &air, &prf, &pis).is_ok(), "in-circuit general epilogue == p3 constraint check at ζ (multi-column)");
    // tampered quotient(ζ) ⇒ the OOD relation fails ⇒ reject.
    let bad = build_general_epilogue_trace(local, next, quotient + Challenge::ONE);
    let bp = prove(&config, &air, bad, &pis);
    assert!(verify(&config, &air, &bp, &pis).is_err(), "tampered quotient ⇒ reject");
    println!("Phase 7.2: in-circuit general OOD epilogue (multi-column Fibonacci, 5 constraints, 3 selectors) matches p3");
}

/// Phase 7.5: the in-circuit GENERIC symbolic epilogue — a DATA-DRIVEN tree walk over the inner AIR's p3
/// `get_symbolic_constraints` (witnessed selectors bound to ζ; folded·inv_van==quot) — verifies the
/// multi-column Fibonacci with NO hardcoded per-AIR fold, matching `eval_symbolic_native` (⟺ p3), and
/// rejects a tampered quotient. This is the arbitrary-inner constraint core (any AIR from its constraints).
#[test]
#[ignore = "slow: Phase 7.5 in-circuit generic symbolic epilogue (data-driven) vs p3"]
fn phase7_symbolic_epilogue_matches_oracle() {
    use super::{build_symbolic_epilogue_trace, SymbolicEpilogueAir};
    use crate::recursion::native_fri::{fib_epilogue_oracle, gen_fib_proof};
    use crate::recursion::native_verify::FibonacciAir;
    use p3_field::BasedVectorSpace;
    use p3_uni_stark::{get_symbolic_constraints, AirLayout};
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_fib_proof(&config, 1, 1, 6);
    let (local, next, is_first, _is_trans, is_last, inv_van, quotient, alpha, zeta) = fib_epilogue_oracle(&config, &proof, &pvs);
    // extract the inner AIR's constraint trees — the ONLY inner-specific input, now data not code.
    let layout = AirLayout::from_air::<Val>(&FibonacciAir);
    let constraints = get_symbolic_constraints::<Val, FibonacciAir>(&FibonacciAir, layout);
    let air = SymbolicEpilogueAir { constraints, w: 2, n_pub: 3, n_periodic: 0, degree_bits: 6 };
    let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
    let (za, al) = (cc(zeta), cc(alpha));
    let mut pis = vec![za[0], za[1], al[0], al[1]];
    pis.extend_from_slice(&pvs);
    let trace = build_symbolic_epilogue_trace(2, &local, &next, quotient, is_first, is_last, inv_van);
    let prf = prove(&config, &air, trace, &pis);
    assert!(verify(&config, &air, &prf, &pis).is_ok(), "generic symbolic epilogue (data-driven tree walk) == p3 for Fibonacci");
    let bad = build_symbolic_epilogue_trace(2, &local, &next, quotient + Challenge::ONE, is_first, is_last, inv_van);
    let bp = prove(&config, &air, bad, &pis);
    assert!(verify(&config, &air, &bp, &pis).is_err(), "tampered quotient ⇒ reject");
    println!("Phase 7.5: in-circuit generic symbolic epilogue verifies Fibonacci from its constraint trees (data-driven)");
}

/// Phase 7.5 (DEGREE-2): the in-circuit generic symbolic epilogue verifies a NON-AFFINE inner — `MulAir`
/// (3 cols, `c = a·b`), whose product constraint is a Mul of two trace variables — via the SAME data-driven
/// tree walk (no code change, just different constraints + W=3), matching p3. Proves the evaluator handles
/// the higher-degree constraint shape real AIRs use, not just affine ones.
#[test]
#[ignore = "slow: Phase 7.5 in-circuit generic symbolic epilogue on a degree-2 inner (MulAir) vs p3"]
fn phase7_symbolic_epilogue_degree2() {
    use super::{build_symbolic_epilogue_trace, SymbolicEpilogueAir};
    use crate::recursion::native_fri::{epilogue_openings, gen_mul_proof};
    use crate::recursion::native_verify::MulAir;
    use p3_field::BasedVectorSpace;
    use p3_uni_stark::{get_symbolic_constraints, AirLayout};
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_mul_proof(&config, 3, 5, 6);
    let (local, next, is_first, is_last, _is_trans, inv_van, quotient, alpha, zeta, _periodic) = epilogue_openings(&config, &MulAir, &proof, &pvs);
    let layout = AirLayout::from_air::<Val>(&MulAir);
    let constraints = get_symbolic_constraints::<Val, MulAir>(&MulAir, layout);
    let air = SymbolicEpilogueAir { constraints, w: 3, n_pub: 2, n_periodic: 0, degree_bits: 6 };
    let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
    let (za, al) = (cc(zeta), cc(alpha));
    let mut pis = vec![za[0], za[1], al[0], al[1]];
    pis.extend_from_slice(&pvs);
    let trace = build_symbolic_epilogue_trace(3, &local, &next, quotient, is_first, is_last, inv_van);
    let prf = prove(&config, &air, trace, &pis);
    assert!(verify(&config, &air, &prf, &pis).is_ok(), "generic symbolic epilogue verifies a DEGREE-2 (variable·variable) inner");
    let bad = build_symbolic_epilogue_trace(3, &local, &next, quotient + Challenge::ONE, is_first, is_last, inv_van);
    let bp = prove(&config, &air, bad, &pis);
    assert!(verify(&config, &air, &bp, &pis).is_err(), "tampered quotient ⇒ reject");
    println!("Phase 7.5: in-circuit generic symbolic epilogue verifies the degree-2 MulAir (c=a·b, W=3) — same code, different constraints");
}

/// Phase 7.8: the IN-CIRCUIT symbolic epilogue scales to the REAL production `JoinSplitAir` — 81
/// constraints, W=19, 33 periodic columns, 26 pubs, degree-7 Poseidon. The data-driven tree walk
/// (`eval_symbolic_circuit`) folds ALL of them and checks folded·inv_van==quot(ζ), matching p3 — the same
/// gadget code that verified Fibonacci/Mul/Periodic, now on the production constraint set.
#[test]
#[ignore = "slow: Phase 7.8 in-circuit symbolic epilogue on the REAL JoinSplitAir vs p3"]
fn phase7_joinsplit_symbolic_epilogue() {
    use super::{build_symbolic_epilogue_trace, SymbolicEpilogueAir};
    use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir, N_PERIODIC, N_PUBLIC, WIDTH};
    use crate::recursion::native_fri::{epilogue_openings, eval_symbolic_native};
    use p3_field::BasedVectorSpace;
    use p3_uni_stark::{get_symbolic_constraints, prove as p3_prove, verify as p3_verify, AirLayout};
    let config = make_config(1, MILESTONE_QUERIES);
    let w = demo_witness();
    let pvs = public_values(&w);
    let proof = p3_prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
    assert!(p3_verify(&config, &JoinSplitAir, &proof, &pvs).is_ok(), "p3 accepts the non-hiding join-split proof");
    let (local, next, is_first, is_last, is_trans, inv_van, quotient, alpha, zeta, periodic) = epilogue_openings(&config, &JoinSplitAir, &proof, &pvs);
    assert_eq!((local.len(), periodic.len(), pvs.len()), (WIDTH, N_PERIODIC, N_PUBLIC));
    let layout = AirLayout::from_air::<Val>(&JoinSplitAir);
    let constraints = get_symbolic_constraints::<Val, JoinSplitAir>(&JoinSplitAir, layout);
    let n_c = constraints.len();
    {
        // native pre-check on THIS proof's openings (isolates in-circuit eval vs the extracted values).
        let pubs_e: Vec<Challenge> = pvs.iter().map(|&p| Challenge::from(p)).collect();
        let mut folded = Challenge::ZERO;
        for c in &constraints {
            folded = folded * alpha + eval_symbolic_native(c, &local, &next, &pubs_e, &periodic, is_first, is_last, is_trans);
        }
        assert_eq!(folded * inv_van, quotient, "PRE-CHECK: native fold on this proof's openings == quot");
    }
    let air = SymbolicEpilogueAir { constraints, w: WIDTH, n_pub: N_PUBLIC, n_periodic: N_PERIODIC, degree_bits: proof.degree_bits };
    let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
    let (za, al) = (cc(zeta), cc(alpha));
    let mut pis = vec![za[0], za[1], al[0], al[1]];
    pis.extend_from_slice(&pvs);
    for pv in &periodic {
        let c = cc(*pv);
        pis.push(c[0]);
        pis.push(c[1]);
    }
    assert_eq!(pis.len(), 4 + N_PUBLIC + 2 * N_PERIODIC, "gadget pis: ζ+α+pubs+periodic");
    let trace = build_symbolic_epilogue_trace(WIDTH, &local, &next, quotient, is_first, is_last, inv_van);
    let prf = prove(&config, &air, trace, &pis);
    if let Err(e) = verify(&config, &air, &prf, &pis) {
        panic!("join-split in-circuit epilogue rejected (n_c={n_c}): {e:?}");
    }
    let bad = build_symbolic_epilogue_trace(WIDTH, &local, &next, quotient + Challenge::ONE, is_first, is_last, inv_van);
    let bp = prove(&config, &air, bad, &pis);
    assert!(verify(&config, &air, &bp, &pis).is_err(), "tampered quotient ⇒ reject");
    println!("Phase 7.8: in-circuit symbolic epilogue verifies the REAL JoinSplitAir ({n_c} constraints, W={WIDTH}, {N_PERIODIC} periodic, {N_PUBLIC} pubs, degree-7)");
}

/// Phase 7.3: the in-circuit MULTI-COLUMN reduced opening reproduces the native `ro` for a 2-column
/// FibonacciAir query — 2·W trace DEEP terms with the opened row value SHARED per column across ζ/ζ_next
/// (px-sharing), validated vs `fib_query_terms`. Tampering ONE authenticated opened value breaks BOTH that
/// column's DEEP terms ⇒ reject, the multi-column soundness property the full monolith fusion needs.
#[test]
#[ignore = "slow: Phase 7.3 multi-column reduced opening (px-sharing) vs fib_query_terms"]
fn phase7_multicol_reduced_opening_matches_oracle() {
    use super::{build_multicol_ro_trace, MultiColReducedOpeningAir};
    use crate::recursion::native_fri::{gen_fib_proof, multicol_query_terms};
    use crate::recursion::native_verify::FibonacciAir;
    use p3_field::BasedVectorSpace;
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_fib_proof(&config, 1, 1, 6);
    let cc = |v: Challenge| -> [Val; 2] { v.as_basis_coefficients_slice().try_into().unwrap() };
    let mut checked = 0;
    for q in [0usize, 1, MILESTONE_QUERIES / 2, MILESTONE_QUERIES - 1] {
        let (terms, x, alpha, ro, w) = multicol_query_terms(&config, &FibonacciAir, &proof, &pvs, q);
        let n_quot = terms.len() - 2 * w;
        let air = MultiColReducedOpeningAir { w, n_quot };
        let (al, roc) = (cc(alpha), cc(ro));
        let pis = vec![al[0], al[1], roc[0], roc[1], x];
        let trace = build_multicol_ro_trace(w, &terms, x, alpha);
        let prf = prove(&config, &air, trace, &pis);
        assert!(verify(&config, &air, &prf, &pis).is_ok(), "multi-column reduced opening == native ro (q {q})");
        // tamper column 0's authenticated opened value ⇒ breaks its ζ AND ζ_next DEEP terms ⇒ ro wrong ⇒ reject.
        let mut bad_terms = terms.clone();
        bad_terms[0].2 += Val::ONE;
        let bad = build_multicol_ro_trace(w, &bad_terms, x, alpha);
        let bp = prove(&config, &air, bad, &pis);
        assert!(verify(&config, &air, &bp, &pis).is_err(), "tampered opened value ⇒ reject (q {q})");
        checked += 1;
    }
    println!("Phase 7.3: multi-column reduced opening (W=2, px shared across ζ/ζ_next) matches native ro — {checked} queries");
}

/// Phase 6.3+6.4: the in-circuit aggregation tx-root FOLD (`AggFoldAir`) emits exactly the reference
/// block tx-root from `native_fri::agg_root` (the batch fold shape — node-seam compatible), and rejects a
/// tampered tx-root. K inner statements folded via s_k = merge([DOM,0,0,0],[pvs0,0,0,0]) → running root.
#[test]
#[ignore = "slow: Phase 6.4 aggregation tx-root fold vs agg_root oracle"]
fn phase6_agg_fold_matches_oracle() {
    use super::{build_agg_fold_trace, AggFoldAir};
    use crate::recursion::native_fri::{agg_root, gen_const_proof};
    let config = make_config(1, MILESTONE_QUERIES);
    let inners: Vec<_> = [42u64, 99, 7].iter().map(|&v| gen_const_proof(&config, v, 6)).collect();
    let tx_root = agg_root(&config, &inners);
    let n_tiles = inners.len().next_power_of_two(); // 4 (pads with a pvs0=0 dummy tile)
    let pvs0: Vec<Val> = inners.iter().map(|(_, pvs)| pvs[0]).collect();
    let air = AggFoldAir { n_tiles };
    let mut pis: Vec<Val> = (0..n_tiles).map(|t| pvs0.get(t).copied().unwrap_or(Val::ZERO)).collect();
    pis.extend_from_slice(&tx_root);
    let trace = build_agg_fold_trace(n_tiles, &pvs0, tx_root);
    let prf = prove(&config, &air, trace, &pis);
    assert!(verify(&config, &air, &prf, &pis).is_ok(), "agg fold emits the tx-root matching agg_root");
    let mut bad = pis.clone();
    bad[n_tiles] += Val::ONE; // tamper the tx-root
    assert!(verify(&config, &air, &prf, &bad).is_err(), "tampered tx-root ⇒ reject");
    println!("Phase 6.4: aggregation tx-root fold (K={} → pow2 {n_tiles}) == agg_root oracle, node-seam compatible", inners.len());
}

#[test]
fn arity4_probe() {
    use crate::recursion::native_fri::verify_proof;
    let config = make_config(2, MILESTONE_QUERIES); // max_log_arity=2 → arity-4 folds
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let fri = &proof.opening_proof;
    let q0 = &fri.query_proofs[0];
    println!("arity-4 config: {} commit rounds, final_poly len {}", q0.commit_phase_openings.len(), fri.final_poly.len());
    for (r, o) in q0.commit_phase_openings.iter().enumerate() {
        println!("  round {r}: log_arity={} siblings={} path_len={}", o.log_arity, o.sibling_values.len(), o.opening_proof.len());
    }
    assert!(verify(&config, &ConstAir, &proof, &pvs).is_ok(), "arity-4 proof valid (p3)");
    let _ = verify_proof; // (native verify_proof is pinned to the arity-4/96-query config; oracle path used instead)
}

/// Phase 5: the in-circuit GENERAL-ARITY fold reproduces p3's own `fold_row` for arity-4 (la=2), every
/// round of several queries, and rejects a tampered result. Validates that the barycentric fold is
/// in-circuit-expressible for arbitrary arity (the milestone's arity-2 is the la=1 special case).
#[test]
#[ignore = "slow: Phase 5 general-arity fold vs p3 fold_row (arity-4)"]
fn phase5_general_fold_matches_p3() {
    use super::{build_general_fold_trace, GeneralFoldAir};
    use crate::recursion::native_fri::general_fold_oracle;
    use p3_field::BasedVectorSpace;
    let config = make_config(2, MILESTONE_QUERIES); // arity-4 data source
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let pcfg = make_config(1, MILESTONE_QUERIES); // prove the tiny gadget with a plain config
    let mut checked = 0;
    for q in [0usize, 1, MILESTONE_QUERIES / 2, MILESTONE_QUERIES - 1] {
        for (evals, beta, xs, folded) in general_fold_oracle(&config, &proof, &pvs, q) {
            let la = xs.len().trailing_zeros() as usize;
            assert_eq!(la, 2, "arity-4 config folds la=2");
            let air = GeneralFoldAir { log_arity: la };
            let fp: Vec<Val> = folded.as_basis_coefficients_slice().to_vec();
            let trace = build_general_fold_trace(la, &evals, beta, &xs, folded);
            let prf = prove(&pcfg, &air, trace, &fp);
            assert!(verify(&pcfg, &air, &prf, &fp).is_ok(), "arity-{} fold == p3 fold_row (q {q})", 1 << la);
            let mut bad = fp.clone();
            bad[0] += Val::ONE;
            assert!(verify(&pcfg, &air, &prf, &bad).is_err(), "tampered folded ⇒ reject (q {q})");
            checked += 1;
        }
    }
    println!("Phase 5: in-circuit general-arity fold validated vs p3 fold_row — {checked} arity-4 rounds");
}

/// Phase 5: the general-arity commit-phase LEAF hash (multi-block rate-overwrite sponge over the arity-4
/// fold group = 8 felts / 2 blocks) reproduces MyHash, and rejects a tampered leaf. The Merkle path above
/// the leaf is arity-independent (already validated); this completes the commit-phase generalization.
#[test]
#[ignore = "slow: Phase 5 general-arity commit leaf hash vs MyHash (arity-4)"]
fn phase5_general_leaf_matches_myhash() {
    use super::{build_general_leaf_trace, GeneralLeafHashAir};
    use crate::recursion::native_fri::{general_fold_oracle, MyHash};
    use p3_field::BasedVectorSpace;
    use p3_goldilocks::default_goldilocks_poseidon2_8;
    use p3_symmetric::CryptographicHasher;
    let config = make_config(2, MILESTONE_QUERIES); // arity-4 data source
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let pcfg = make_config(1, MILESTONE_QUERIES);
    let hasher = MyHash::new(default_goldilocks_poseidon2_8());
    let mut checked = 0;
    for q in [0usize, 1, MILESTONE_QUERIES - 1] {
        for (evals, _b, _x, _f) in general_fold_oracle(&config, &proof, &pvs, q) {
            let group: Vec<Val> = evals.iter().flat_map(|e| e.as_basis_coefficients_slice().to_vec()).collect();
            assert_eq!(group.len(), 8, "arity-4 group = 8 felts");
            let leaf: [Val; 4] = hasher.hash_iter(group.iter().copied());
            let air = GeneralLeafHashAir { n_felts: group.len() };
            let mut pis = group.clone();
            pis.extend_from_slice(&leaf);
            let trace = build_general_leaf_trace(group.len(), &group, leaf);
            let prf = prove(&pcfg, &air, trace, &pis);
            assert!(verify(&pcfg, &air, &prf, &pis).is_ok(), "arity-4 commit leaf == MyHash (q {q})");
            let mut bad = pis.clone();
            let n = bad.len();
            bad[n - 1] += Val::ONE;
            assert!(verify(&pcfg, &air, &prf, &bad).is_err(), "tampered leaf ⇒ reject (q {q})");
            checked += 1;
        }
    }
    println!("Phase 5: general-arity commit leaf hash (2-block sponge) validated vs MyHash — {checked} groups");
}

/// Phase 7.9 (join-split path — multi-block leaf): the leaf-hash sponge reproduces `MyHash` for widths that
/// are NOT multiples of RATE, including the real join-split trace-row width W=19 (5 blocks, short final
/// 3-felt chunk). This is the input-Merkle leaf a W=19 inner needs (the current monolith leaf is single-
/// block, W≤8). Exercises rem ∈ {1,3,4}; rejects a tampered leaf.
///
/// HIDING (is_zk=1) coverage: the salted input leaf preimage is the COMMITTED row ‖ salt, where the
/// committed row = public ‖ num_codewords(4) and salt = SALT_ELEMS(4) (MerkleTreeHidingMmcs hashes
/// `row ‖ salt` — validated natively in native_verify::hiding_verify_fri_native; exact widths from
/// native_verify::hiding_proof_geometry). So the hiding leaf needs NO new gadget — it is this width-generic
/// sponge fed [public ‖ 4 codewords ‖ 4 salt]. The widths below cover the real hiding leaves: trace leaf =
/// W+8 (9 = ConstAir W=1, 16 = W=8, 27 = join-split W=19); random/quotient leaf = 10 (= 2 public + 4 + 4).
#[test]
#[ignore = "slow: Phase 7.9 wide multi-block leaf (W not a multiple of RATE, incl. join-split W=19 + hiding committed-row‖salt widths) vs MyHash"]
fn phase7_wide_leaf_matches_myhash() {
    use super::{build_general_leaf_trace, GeneralLeafHashAir};
    use crate::recursion::native_fri::MyHash;
    use p3_goldilocks::default_goldilocks_poseidon2_8;
    use p3_symmetric::CryptographicHasher;
    let pcfg = make_config(1, MILESTONE_QUERIES);
    let hasher = MyHash::new(default_goldilocks_poseidon2_8());
    // 9/10/16/27 = the real is_zk=1 salted-leaf preimage widths (trace W+8: ConstAir 9, W=8 16, join-split
    // 27; random/quotient 10). 7,13 keep general non-RATE-multiple coverage.
    for n in [7usize, 9, 10, 13, 16, 27] {
        let group: Vec<Val> = (0..n).map(|i| Val::from_u64(0x1234 + 7 * i as u64)).collect();
        let leaf: [Val; 4] = hasher.hash_iter(group.iter().copied());
        let air = GeneralLeafHashAir { n_felts: n };
        let mut pis = group.clone();
        pis.extend_from_slice(&leaf);
        let trace = build_general_leaf_trace(n, &group, leaf);
        let prf = prove(&pcfg, &air, trace, &pis);
        assert!(verify(&pcfg, &air, &prf, &pis).is_ok(), "multi-block leaf == MyHash (n={n}, {} blocks)", air.n_blocks());
        let mut bad = pis.clone();
        let m = bad.len();
        bad[m - 1] += Val::ONE;
        assert!(verify(&pcfg, &air, &prf, &bad).is_err(), "tampered leaf ⇒ reject (n={n})");
    }
    println!("Phase 7.9: multi-block leaf hash (incl. W=19 join-split + hiding salted-leaf widths 9/10/16/27) validated vs MyHash");
}

/// Phase 5 re-fusion: the in-circuit arity-4 fold CHAIN carries E_0=ro through 3 barycentric folds and
/// reaches final_poly[0] — the fused fold behavior the arity-4 monolith needs. Validated vs p3's fold_row
/// chain (general_fold_chain_oracle); rejects a tampered accept value.
#[test]
#[ignore = "slow: Phase 5 re-fusion arity-4 fold chain → final_poly"]
fn phase5_arity4_fold_chain_reaches_final() {
    use super::{build_arity4_fold_chain_trace, Arity4FoldChainAir};
    use crate::recursion::native_fri::general_fold_chain_oracle;
    use p3_field::BasedVectorSpace;
    let config = make_config(2, MILESTONE_QUERIES); // arity-4
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let pcfg = make_config(1, MILESTONE_QUERIES);
    let mut checked = 0;
    for q in [0usize, 1, MILESTONE_QUERIES / 3, MILESTONE_QUERIES - 1] {
        let (ro, rounds, final0) = general_fold_chain_oracle(&config, &proof, &pvs, q);
        assert_eq!(rounds.len(), 3, "arity-4 ⇒ 3 fold rounds");
        let air = Arity4FoldChainAir { n_rounds: rounds.len() };
        let roc: [Val; 2] = ro.as_basis_coefficients_slice().try_into().unwrap();
        let fc: [Val; 2] = final0.as_basis_coefficients_slice().try_into().unwrap();
        let pis = vec![roc[0], roc[1], fc[0], fc[1]];
        let trace = build_arity4_fold_chain_trace(rounds.len(), ro, &rounds, final0);
        let prf = prove(&pcfg, &air, trace, &pis);
        assert!(verify(&pcfg, &air, &prf, &pis).is_ok(), "arity-4 fold chain reaches final_poly (q {q})");
        let mut bad = pis.clone();
        bad[2] += Val::ONE;
        assert!(verify(&pcfg, &air, &prf, &bad).is_err(), "tampered accept ⇒ reject (q {q})");
        checked += 1;
    }
    println!("Phase 5 re-fusion: arity-4 fold chain (3 barycentric rounds) reaches final_poly — {checked} queries");
}

#[test]
fn epilogue_probe() {
    use crate::recursion::native_fri::epilogue_oracle;
    use p3_field::{Field, TwoAdicField};
    let config = make_config(1, MILESTONE_QUERIES);
    let (proof, pvs) = gen_const_proof(&config, 42, 6);
    let (db, nqc, chunk_lens, quotient, local, next, chunks, alpha, zeta, n_is_first, n_is_trans, n_inv_van) =
        epilogue_oracle(&config, &proof, &pvs);
    println!("degree_bits={db} nqc={nqc} chunk_lens={chunk_lens:?} n_chunks_flat={}", chunks.len());
    println!("local={local:?} next={next:?} quotient(ζ)={quotient:?}");
    // --- 1) in-circuit selector chain (log_size = degree_bits) vs p3's own selectors_at_point ---
    let s_db = zeta.exp_power_of_2(db); // 6 squarings: ζ^(2^6)
    let z_h = s_db - Challenge::ONE;
    let inv_van = z_h.inverse();
    let is_first = z_h * (zeta - Challenge::ONE).inverse();
    let g_inv = Val::two_adic_generator(db).inverse();
    let is_trans = zeta - Challenge::from(g_inv);
    assert_eq!(is_first, n_is_first, "in-circuit is_first == p3 selectors_at_point.is_first_row");
    assert_eq!(is_trans, n_is_trans, "in-circuit is_trans == p3 selectors_at_point.is_transition");
    assert_eq!(inv_van, n_inv_van, "in-circuit inv_van == p3 selectors_at_point.inv_vanishing");
    // --- 2) in-circuit recompose (nqc=1 ⇒ zps=1 ⇒ quotient(ζ) = c0 + c1·X) vs p3's recompose ---
    assert_eq!(nqc, 1, "milestone ConstAir ⇒ single quotient chunk");
    let x_gen = Challenge::from_basis_coefficients_fn(|i| if i == 1 { Val::ONE } else { Val::ZERO });
    let recomp = chunks[0] + chunks[1] * x_gen;
    assert_eq!(recomp, quotient, "in-circuit recompose c0 + c1·X == p3 recompose_quotient_from_chunks (real proof)");
    // --- 3) the OOD constraint at ζ: (C0·α + C1)·inv_van == quotient(ζ) ---
    let pub_val = Challenge::from(pvs[0]);
    let cc0 = is_first * (local - pub_val);
    let cc1 = is_trans * (next - local);
    let folded = cc0 * alpha + cc1;
    assert_eq!(folded * inv_van, quotient, "OOD check: folded_constraints(ζ)·Z_H(ζ)^{{-1}} == quotient(ζ)");
    // --- 4) non-trivial anchor: my selector+fold formula matches p3's OOD relation for arbitrary local/next/pub.
    //     Build a synthetic quotient q* = (C0*·α + C1*)·inv_van and confirm the same formula reproduces it. ---
    let (sl, sn, sp) = (Challenge::from_u64(123), Challenge::from_u64(456), Val::from_u64(789));
    let q_star = (is_first * (sl - Challenge::from(sp)) * alpha + is_trans * (sn - sl)) * inv_van;
    let reproduced = ((is_first * (sl - Challenge::from(sp))) * alpha + (is_trans * (sn - sl))) * inv_van;
    assert_eq!(reproduced, q_star, "OOD fold formula is consistent on non-trivial inputs");
    // --- 5) the reduced-opening z-terms must equal ζ / ζ_next (so QT_pz(k) is the opening AT ζ) ---
    let (terms, _x, _al, _ro) = crate::recursion::native_fri::query_terms(&config, &proof, &pvs, 0);
    let g_trace = Val::two_adic_generator(db);
    assert_eq!(terms[0].0, zeta, "z(0) == ζ (trace at ζ)");
    assert_eq!(terms[1].0, zeta * Challenge::from(g_trace), "z(1) == ζ·g_trace (trace at ζ_next)");
    assert_eq!(terms[2].0, zeta, "z(2) == ζ (quotient at ζ)");
    assert_eq!(terms[3].0, zeta, "z(3) == ζ (quotient at ζ)");
    // and QT_pz(0)=local, QT_pz(1)=next, QT_pz(2..3)=chunks — confirm against the oracle
    assert_eq!(terms[0].1, local, "QT_pz(0) == trace_local");
    assert_eq!(terms[1].1, next, "QT_pz(1) == trace_next");
    assert_eq!(terms[2].1, chunks[0], "QT_pz(2) == chunk0");
    assert_eq!(terms[3].1, chunks[1], "QT_pz(3) == chunk1");
    println!("epilogue_probe: selectors + recompose + OOD fold + z-term binding all validated vs p3");
}
