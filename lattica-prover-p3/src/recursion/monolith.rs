//! Monolith — the in-circuit recursive STARK verifier AIR: the AIR PORT of the validated
//! `native_fri::verify_proof`. One AIR (transcript region + per-query tiles + constraint epilogue) whose
//! trace is satisfiable iff `p3::verify(inner)` accepts. Built phase-by-phase per the approved plan
//! (docs/recursion-verifier-audit.md §10). ⚠️ WORK IN PROGRESS — research, NOT production, NOT audited.
//!
//! Reuses the validated gadgets (`verifier_air`, `fri_merkle`, `fri_fold`, `transcript`) + the
//! `batch_*_air` tiling pattern (periodic selectors + staging + global-persistent columns). Proven with
//! the audited p3 single-AIR `prove`/`verify`; hard 8 GB peak-RSS budget enforced per phase.
//!
//! ## Phase 0 — geometry pin + budget oracle
//! Pins the first-milestone inner proof's shape (arity-2 `ConstAir`, `degree_bits=6`) and confirms the
//! derived monolith trace height fits ≤ 2^18 and proving stays ≤ 8 GB, before any AIR is built. The
//! per-query block budget below is the cost model the per-query tile (Phase 3) must hit.
//!
//! ## Phase 1 — AIR skeleton + transcript preamble (α, ζ)
//! `PreambleAir`: the duplex-sponge transcript preamble, generalizing the validated `TranscriptAir` to
//! the milestone's cap-sized absorbs (instance felts → α, commitment felts → ζ). Validated standalone vs
//! the native challenger (`preamble_challenges`); its eval is composed into the full MonolithAir in Phase 4.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::Goldilocks;
use p3_matrix::dense::RowMajorMatrix;

use crate::poseidon2_air::{ext_linear, int_linear, native_permute, native_steps, periodic_table, pow7, BLOCK, W};
use crate::recursion::native_fri::Val;

const RATE: usize = 4;
const CAP_LANE: usize = RATE;
const P_BLOCK_LAST: usize = 11; // periodic: one-hot at row BLOCK-1 of every block
const P_ALPHA: usize = 12; // periodic: full-height one-hot at the α-squeeze row
const P_ZETA: usize = 13; // periodic: full-height one-hot at the ζ-squeeze row
const N_PERIODIC: usize = 14;

/// The transcript preamble region: a Poseidon2 duplex sponge absorbing `i_blocks` instance blocks (→ α at
/// that block's output) then `c_blocks` commitment blocks (→ ζ at the last row). Same sponge mechanics as
/// the validated `TranscriptAir` (rate overwrite, capacity carry with the +RATE prefix-free count,
/// challenge = (rate[3], rate[2])), generalized to arbitrary block counts. Composed into MonolithAir later.
#[allow(dead_code)] // standalone-validated in Phase 1; its eval is reused by MonolithAir in Phase 4
pub(crate) struct PreambleAir {
    pub i_blocks: usize,
    pub c_blocks: usize,
}

#[allow(dead_code)]
impl PreambleAir {
    fn n_blocks(&self) -> usize {
        self.i_blocks + self.c_blocks
    }
    fn padded_blocks(&self) -> usize {
        self.n_blocks().next_power_of_two() // p3 trace height must be a power of two
    }
    fn height(&self) -> usize {
        self.padded_blocks() * BLOCK
    }
    fn alpha_row(&self) -> usize {
        self.i_blocks * BLOCK - 1 // output row of the last instance block
    }
    fn zeta_row(&self) -> usize {
        self.n_blocks() * BLOCK - 1 // output row of the last commitment block
    }
    fn periodic(&self) -> Vec<Vec<Val>> {
        let mut cols = periodic_table(); // 11 round cols, period BLOCK
        let mut block_last = vec![Val::ZERO; BLOCK];
        block_last[BLOCK - 1] = Val::ONE;
        cols.push(block_last);
        let mut alpha = vec![Val::ZERO; self.height()]; // full-height ⇒ fires once, at alpha_row
        alpha[self.alpha_row()] = Val::ONE;
        cols.push(alpha);
        let mut zeta = vec![Val::ZERO; self.height()];
        zeta[self.zeta_row()] = Val::ONE;
        cols.push(zeta);
        cols
    }
}

impl BaseAir<Goldilocks> for PreambleAir {
    fn width(&self) -> usize {
        W
    }
    fn num_public_values(&self) -> usize {
        4 // α(2) ‖ ζ(2)
    }
    fn num_periodic_columns(&self) -> usize {
        N_PERIODIC
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        self.periodic()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for PreambleAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let rate = AB::Expr::from(Goldilocks::from_u64(RATE as u64));

        // Poseidon2 round constraints per block (reused).
        let is_init = p[0].clone();
        let is_full = p[1].clone();
        let is_partial = p[2].clone();
        let rc: Vec<AB::Expr> = (0..W).map(|i| p[3 + i].clone()).collect();
        let mut init_s: [AB::Expr; W] = core::array::from_fn(|i| cur[i].clone());
        ext_linear(&mut init_s);
        let mut full_s: [AB::Expr; W] = core::array::from_fn(|i| pow7(cur[i].clone() + rc[i].clone()));
        ext_linear(&mut full_s);
        let mut part_s: [AB::Expr; W] =
            core::array::from_fn(|i| if i == 0 { pow7(cur[0].clone() + rc[0].clone()) } else { cur[i].clone() });
        int_linear(&mut part_s);
        for i in 0..W {
            let c = is_init.clone() * (nxt[i].clone() - init_s[i].clone())
                + is_full.clone() * (nxt[i].clone() - full_s[i].clone())
                + is_partial.clone() * (nxt[i].clone() - part_s[i].clone());
            builder.when_transition().assert_zero(c);
        }

        // block 0 starts from the zero capacity with the prefix-free count folded in.
        {
            let mut fr = builder.when_first_row();
            fr.assert_zero(cur[CAP_LANE].clone() - rate.clone());
            for i in (CAP_LANE + 1)..W {
                fr.assert_zero(cur[i].clone());
            }
        }
        // capacity carries across blocks (+RATE); rate lanes free (the next absorbed felts).
        {
            let bl = p[P_BLOCK_LAST].clone();
            builder.when_transition().assert_zero(bl.clone() * (nxt[CAP_LANE].clone() - (cur[CAP_LANE].clone() + rate.clone())));
            for i in (CAP_LANE + 1)..W {
                builder.when_transition().assert_zero(bl.clone() * (nxt[i].clone() - cur[i].clone()));
            }
        }
        // α squeeze at the last instance block's output: α = (rate[3], rate[2]).
        {
            let a = p[P_ALPHA].clone();
            builder.assert_zero(a.clone() * (cur[3].clone() - pis[0].clone()));
            builder.assert_zero(a.clone() * (cur[2].clone() - pis[1].clone()));
        }
        // ζ squeeze at the last commitment block's output (a one-hot, not when_last_row, since the trace
        // is padded to a power-of-two block count beyond the ζ row): ζ = (rate[3], rate[2]).
        {
            let z = p[P_ZETA].clone();
            builder.assert_zero(z.clone() * (cur[3].clone() - pis[2].clone()));
            builder.assert_zero(z * (cur[2].clone() - pis[3].clone()));
        }
    }
}

/// Fill the preamble trace by absorbing (instance ‖ commitment) felts blockwise (rate overwrite, capacity
/// carry with the +RATE prefix-free count), matching the duplex challenger.
#[allow(dead_code)]
pub(crate) fn preamble_build_trace(i_blocks: usize, c_blocks: usize, instance: &[Val], commitment: &[Val]) -> RowMajorMatrix<Val> {
    assert_eq!(instance.len(), i_blocks * RATE, "instance must be i_blocks·RATE felts");
    assert_eq!(commitment.len(), c_blocks * RATE, "commitment must be c_blocks·RATE felts");
    let n_blocks = i_blocks + c_blocks;
    let padded = n_blocks.next_power_of_two();
    let mut felts = instance.to_vec();
    felts.extend_from_slice(commitment);
    let mut t = vec![Val::ZERO; padded * BLOCK * W];
    let mut cap = [Val::ZERO; W - RATE];
    for blk in 0..padded {
        let mut input = [Val::ZERO; W];
        if blk < n_blocks {
            input[..RATE].copy_from_slice(&felts[blk * RATE..blk * RATE + RATE]);
        } // padding blocks (blk ≥ n_blocks) absorb zeros — a valid sponge continuation past the ζ row
        input[RATE..].copy_from_slice(&cap);
        input[CAP_LANE] += Val::from_u64(RATE as u64);
        let rows = native_steps(input);
        for r in 0..BLOCK {
            let base = (blk * BLOCK + r) * W;
            t[base..base + W].copy_from_slice(&rows[r]);
        }
        cap.copy_from_slice(&native_permute(input)[RATE..]);
    }
    RowMajorMatrix::new(t, W)
}

#[cfg(test)]
mod tests {
    use super::{preamble_build_trace, PreambleAir};
    use crate::poseidon2_air::BLOCK;
    use crate::recursion::native_fri::{gen_const_proof, make_config, preamble_challenges, MyConfig, Val};
    use crate::recursion::native_verify::ConstAir;
    use p3_field::PrimeCharacteristicRing;
    use p3_uni_stark::{prove, verify, Proof};

    const CAP_HEIGHT: usize = 6; // MerkleTreeMmcs cap (build_mmcs_and_params)
    const RATE: usize = 4; // PaddingFreeSponge rate
    const LOG_BLOWUP: usize = 4;
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
}
