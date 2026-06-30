//! Monolith — the in-circuit recursive STARK verifier AIR: the AIR PORT of the validated
//! `native_fri::verify_proof`. One AIR (transcript region + per-query tiles + constraint epilogue) whose
//! trace is satisfiable iff `p3::verify(inner)` accepts. Built phase-by-phase per the approved plan
//! (docs/recursion-verifier-audit.md §10). ⚠️ WORK IN PROGRESS — research, NOT production, NOT audited.
//!
//! Reuses the validated gadgets (`verifier_air`, `fri_merkle`, `fri_fold`, `transcript`) + the
//! `batch_*_air` tiling pattern (periodic selectors + staging + global-persistent columns). Proven with
//! the audited p3 single-AIR `prove`/`verify`; hard 8 GB peak-RSS budget enforced per phase.
//!
//! ## Phase 0 (this file) — geometry pin + budget oracle
//! Pins the first-milestone inner proof's shape (arity-2 `ConstAir`, `degree_bits=6`) and confirms the
//! derived monolith trace height fits ≤ 2^18 and proving stays ≤ 8 GB, before any AIR is built. The
//! per-query block budget below is the cost model the per-query tile (Phase 3) must hit.

#[cfg(test)]
mod tests {
    use crate::poseidon2_air::BLOCK;
    use crate::recursion::native_fri::{gen_const_proof, make_config, verify_proof, MyConfig};
    use crate::recursion::native_verify::ConstAir;
    use p3_uni_stark::{verify, Proof};

    const CAP_HEIGHT: usize = 6; // MerkleTreeMmcs cap (build_mmcs_and_params)
    const RATE: usize = 4; // PaddingFreeSponge rate
    const LOG_BLOWUP: usize = 4;
    const LOG_FINAL_POLY_LEN: usize = 0;
    const EIGHT_GB: u64 = 8u64 << 30;

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

    /// Generous estimate of the monolith trace height (rows) for this inner proof, from the per-region
    /// block budget the AIR phases will fill. Each Poseidon2 permutation = `BLOCK` rows; each Merkle
    /// level = one compression = one block; the leaf hash = ceil(width/RATE) blocks.
    fn monolith_trace_height(g: &InnerGeometry) -> usize {
        let merkle_depth = |log_h: usize| log_h.saturating_sub(g.cap_height); // levels above the cap
        let leaf_blocks = |width: usize| width.div_ceil(RATE).max(1);

        // Input opening: the trace batch (width = trace_width) + the quotient batch (num_quotient_chunks
        // ext columns = 2× base felts), each one Merkle opening at ~the global max height.
        let input_blocks = {
            let depth = merkle_depth(g.log_global_max_height);
            let trace_batch = leaf_blocks(g.trace_width) + depth;
            let quot_batch = leaf_blocks(g.num_quotient_chunks * 2) + depth;
            trace_batch + quot_batch
        };
        // Commit phase: per round, leaf-hash the arity group + Merkle path at the folded height + the fold.
        let mut commit_blocks = 0usize;
        let mut h = g.log_global_max_height;
        for &la in &g.log_arities {
            let folded_h = h - la;
            let arity = 1usize << la;
            commit_blocks += leaf_blocks(arity * 2) + merkle_depth(folded_h) + 1 /* fold */;
            h = folded_h;
        }
        // DEEP reduced-opening + roll-ins (generous).
        let deep_blocks = 4 + g.num_rounds;
        let per_query_blocks = input_blocks + commit_blocks + deep_blocks;

        let transcript_blocks = 24; // preamble + FRI rounds + squeeze-only index tail (Phase 1-2)
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
        // Arity-2 FRI milestone config (max_log_arity = 1) so the per-query fold maps onto FoldChainAir.
        let config = make_config(1);
        let (proof, pvs) = gen_const_proof(&config, 42, 6);

        // The inner proof is real: p3 + the validated native verifier both accept it.
        assert!(verify(&config, &ConstAir, &proof, &pvs).is_ok(), "p3::verify should accept the inner proof");
        assert!(verify_proof(&config, &proof, &pvs).is_ok(), "native verify_proof should accept the inner proof");

        let g = introspect_geometry(&proof);
        // Pin the arity-2 milestone shape.
        assert_eq!(g.degree_bits, 6, "milestone degree_bits");
        assert!(g.log_arities.iter().all(|&a| a == 1), "arity-2 FRI: every round folds by 1 bit");
        assert_eq!(g.log_global_max_height, 10, "Σlog_arities(6) + log_blowup(4) + 0");
        assert_eq!(g.num_rounds, 6, "fold 2^10 → 2^4 in arity-2 steps");
        assert_eq!(g.num_queries, 96);

        let height = monolith_trace_height(&g);
        println!("Phase 0 geometry: {g:?}\n  -> monolith trace height ~2^{} ({height} rows)", height.trailing_zeros());
        assert!(height <= (1 << 18), "monolith trace height {height} must fit ≤ 2^18 (got 2^{})", height.trailing_zeros());

        let rss = peak_rss_bytes();
        println!("  -> peak RSS {} MiB", rss / (1 << 20));
        assert!(rss <= EIGHT_GB, "peak RSS {rss} must stay ≤ 8 GB");
    }
}
