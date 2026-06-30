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
use p3_field::{Field, PrimeCharacteristicRing, TwoAdicField};
use p3_goldilocks::Goldilocks;
use p3_matrix::dense::RowMajorMatrix;

use crate::poseidon2_air::{ext_linear, int_linear, native_permute, native_steps, periodic_table, pow7, BLOCK, W};
use crate::recursion::native_fri::{Challenge, Val};

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

// =================================================================================================
// Phase 2 — the full transcript: a GENERAL schedule-driven duplex sponge that derives α_stark, ζ,
// α_fri, and every β_r (and, with the squeeze tail, the query indices). Each permutation block has a
// per-block prefix-free count (`count_b` = num_absorbed: 4 for full absorbs, the remainder before a
// sample, 0 for squeezes) folded into the capacity lane, and absorb blocks overwrite the rate while
// squeeze blocks carry it. Driven by the recorded schedule; bindings read (rate[3], rate[2]) at each
// challenge's block-output row (the duplex challenger pops from the back). Composed into MonolithAir later.
// =================================================================================================

const FT_P_BLOCK_LAST: usize = 11;
const FT_COUNT: usize = 12; // count_b at block b's rows (for the first-row capacity init)
const FT_COUNT_NEXT: usize = 13; // count_{b+1} at block b's rows (for the carry into the next block)
const FT_IS_SQ_NEXT: usize = 14; // 1 if block b+1 is a squeeze (count 0 ⇒ rate carries)
const FT_BIND_START: usize = 15; // one one-hot per bound challenge follows

/// The full-transcript duplex AIR. `counts[b]` = the prefix-free count for block b; `binds[j]` = the block
/// whose output row carries the j-th ext challenge (→ public[2j], public[2j+1] = rate[3], rate[2]).
/// `index_binds[k] = (block, lane)` locates the k-th query INDEX felt (a single rate lane popped from a
/// squeeze block) → public[2·binds.len() + k]. The low-`bits` masking of each index felt is the
/// separately-validated `SampleBitsAir`.
#[allow(dead_code)] // standalone-validated in Phase 2; composed into MonolithAir in Phase 4
pub(crate) struct FullTranscriptAir {
    pub counts: Vec<u8>,
    pub binds: Vec<usize>,
    pub index_binds: Vec<(usize, usize)>,
}

#[allow(dead_code)]
impl FullTranscriptAir {
    fn n_blocks(&self) -> usize {
        self.counts.len()
    }
    fn height(&self) -> usize {
        self.n_blocks().next_power_of_two() * BLOCK
    }
    fn periodic(&self) -> Vec<Vec<Val>> {
        let h = self.height();
        let nb = self.counts.len();
        let count_of = |b: usize| -> Val { if b < nb { Val::from_u64(self.counts[b] as u64) } else { Val::ZERO } };
        let mut cols = periodic_table(); // 11 round cols
        let mut block_last = vec![Val::ZERO; BLOCK];
        block_last[BLOCK - 1] = Val::ONE;
        cols.push(block_last);
        let mut count = vec![Val::ZERO; h];
        let mut count_next = vec![Val::ZERO; h];
        let mut is_sq_next = vec![Val::ZERO; h];
        for r in 0..h {
            let b = r / BLOCK;
            count[r] = count_of(b);
            count_next[r] = count_of(b + 1);
            is_sq_next[r] = if (b + 1 >= nb) || self.counts[b + 1] == 0 { Val::ONE } else { Val::ZERO };
        }
        cols.push(count);
        cols.push(count_next);
        cols.push(is_sq_next);
        for &blk in &self.binds {
            let mut col = vec![Val::ZERO; h];
            col[blk * BLOCK + BLOCK - 1] = Val::ONE; // the block's output row
            cols.push(col);
        }
        for &(blk, _lane) in &self.index_binds {
            let mut col = vec![Val::ZERO; h];
            col[blk * BLOCK + BLOCK - 1] = Val::ONE;
            cols.push(col);
        }
        cols
    }
}

impl BaseAir<Goldilocks> for FullTranscriptAir {
    fn width(&self) -> usize {
        W
    }
    fn num_public_values(&self) -> usize {
        2 * self.binds.len() + self.index_binds.len()
    }
    fn num_periodic_columns(&self) -> usize {
        FT_BIND_START + self.binds.len() + self.index_binds.len()
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        self.periodic()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for FullTranscriptAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();

        // Poseidon2 round constraints (periodic_table zeroes the selectors at the block-boundary row).
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

        // first block: capacity lane = count_0; other capacity lanes = 0.
        {
            let mut fr = builder.when_first_row();
            fr.assert_zero(cur[CAP_LANE].clone() - p[FT_COUNT].clone());
            for i in (CAP_LANE + 1)..W {
                fr.assert_zero(cur[i].clone());
            }
        }
        // block linkage at P_BLOCK_LAST: capacity carries (+count_next on the count lane); rate carries
        // only on squeeze blocks (absorb blocks' rate is free = the next absorbed felts).
        {
            let bl = p[FT_P_BLOCK_LAST].clone();
            builder.when_transition().assert_zero(bl.clone() * (nxt[CAP_LANE].clone() - cur[CAP_LANE].clone() - p[FT_COUNT_NEXT].clone()));
            for i in (CAP_LANE + 1)..W {
                builder.when_transition().assert_zero(bl.clone() * (nxt[i].clone() - cur[i].clone()));
            }
            for i in 0..RATE {
                builder.when_transition().assert_zero(bl.clone() * p[FT_IS_SQ_NEXT].clone() * (nxt[i].clone() - cur[i].clone()));
            }
        }
        // ext challenge bindings: at each bind block's output row, (rate[3], rate[2]) = the public challenge.
        for j in 0..self.binds.len() {
            let b = p[FT_BIND_START + j].clone();
            builder.assert_zero(b.clone() * (cur[3].clone() - pis[2 * j].clone()));
            builder.assert_zero(b * (cur[2].clone() - pis[2 * j + 1].clone()));
        }
        // index-felt bindings: at each (block, lane), the popped rate lane = the public index felt.
        let ext_pubs = 2 * self.binds.len();
        let idx_start = FT_BIND_START + self.binds.len();
        for (k, &(_blk, lane)) in self.index_binds.iter().enumerate() {
            let b = p[idx_start + k].clone();
            builder.assert_zero(b * (cur[lane].clone() - pis[ext_pubs + k].clone()));
        }
    }
}

/// Fill the full-transcript trace from the recorded per-block input states (each = the 8-lane state going
/// into that block's permute), padding to a power-of-two block count with squeeze (carry) continuation.
#[allow(dead_code)]
pub(crate) fn ft_build_trace(block_inputs: &[[Val; W]]) -> RowMajorMatrix<Val> {
    let n = block_inputs.len();
    let padded = n.next_power_of_two();
    let mut t = vec![Val::ZERO; padded * BLOCK * W];
    let mut last_out = [Val::ZERO; W];
    for b in 0..padded {
        let input = if b < n { block_inputs[b] } else { last_out }; // padding: squeeze (carry prev output)
        let rows = native_steps(input);
        for r in 0..BLOCK {
            let base = (b * BLOCK + r) * W;
            t[base..base + W].copy_from_slice(&rows[r]);
        }
        last_out = native_permute(input);
    }
    RowMajorMatrix::new(t, W)
}

// =================================================================================================
// Phase 3 (part 1) — the DEEP query point: x = GENERATOR · g^reverse_bits(index, log_height), where
// g = two_adic_generator(log_height). Computed in-circuit from the query index BITS as a product chain
// over the bit-reversed powers (x = GENERATOR · Π_i (b_i ? g^(2^(N-1-i)) : 1)), since the bit at
// position i of the index becomes bit (N-1-i) of the reversed exponent. Base-field arithmetic.
// Validated vs native_fri's `x` (open_input). The index bits come from the validated SampleBitsAir.
// =================================================================================================

const DP_LOG_HEIGHT: usize = 10; // milestone log_global_max_height (= degree_bits 6 + log_blowup 4)
const DP_BITS: usize = 0; // index bits b_0..b_{N-1}
const DP_ACC: usize = DP_LOG_HEIGHT; // product-chain accumulators acc_1..acc_N
const DP_WIDTH: usize = 2 * DP_LOG_HEIGHT;

#[allow(dead_code)] // standalone-validated in Phase 3; composed into MonolithAir's query region in Phase 4
pub(crate) struct DeepPointAir;

impl BaseAir<Goldilocks> for DeepPointAir {
    fn width(&self) -> usize {
        DP_WIDTH
    }
    fn num_public_values(&self) -> usize {
        1 // the DEEP point x
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for DeepPointAir {
    fn eval(&self, builder: &mut AB) {
        let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let g = Goldilocks::two_adic_generator(DP_LOG_HEIGHT);
        let mut fr = builder.when_first_row();

        // index bits are boolean
        for i in 0..DP_LOG_HEIGHT {
            let b = cur[DP_BITS + i].clone();
            fr.assert_zero(b.clone() * (one.clone() - b));
        }
        // product chain: acc_{i+1} = acc_i · (1 + b_i·(c_i − 1)),  c_i = g^(2^(N-1-i)),  acc_0 = 1.
        let mut prev = one.clone();
        for i in 0..DP_LOG_HEIGHT {
            let ci = AB::Expr::from(g.exp_power_of_2(DP_LOG_HEIGHT - 1 - i));
            let factor = one.clone() + cur[DP_BITS + i].clone() * (ci - one.clone());
            fr.assert_zero(cur[DP_ACC + i].clone() - prev * factor);
            prev = cur[DP_ACC + i].clone();
        }
        // x = GENERATOR · acc_N
        let gen = AB::Expr::from(<Goldilocks as Field>::GENERATOR);
        fr.assert_zero(gen * cur[DP_ACC + DP_LOG_HEIGHT - 1].clone() - pis[0].clone());
    }
}

#[allow(dead_code)]
pub(crate) fn dp_build_trace(index: usize) -> RowMajorMatrix<Val> {
    let g = Goldilocks::two_adic_generator(DP_LOG_HEIGHT);
    let mut r = [Val::ZERO; DP_WIDTH];
    let mut acc = Val::ONE;
    for i in 0..DP_LOG_HEIGHT {
        let bit = (index >> i) & 1;
        r[DP_BITS + i] = Val::from_u64(bit as u64);
        let ci = g.exp_power_of_2(DP_LOG_HEIGHT - 1 - i);
        acc *= if bit == 1 { ci } else { Val::ONE };
        r[DP_ACC + i] = acc;
    }
    let mut vals = Vec::with_capacity(8 * DP_WIDTH);
    for _ in 0..8 {
        vals.extend_from_slice(&r);
    }
    RowMajorMatrix::new(vals, DP_WIDTH)
}

// =================================================================================================
// Phase 3 (part 2) — the reduced opening (DEEP combination) for `open_input`'s real shape: a generic
// N-term `ro = Σ_k α^k·(p_z_k − p_x_k)/(z_k − x)`, where p_z (claimed eval) is F_p², p_x (opened row
// value) is base, x (the DEEP point) is base and shared across a height, and z_k are the opening points.
// The milestone has 3 terms: trace at ζ, trace at ζ·g (the next row), quotient at ζ. Witnessed α-powers
// and per-term inverse denominators (in-circuit inverse). Validated vs native_fri::query_terms's `ro`.
// =================================================================================================

const MRO_W_EXT: u64 = 7; // F_p² : X² = 7

#[allow(dead_code)] // standalone-validated in Phase 3; composed into MonolithAir's query region in Phase 4
pub(crate) struct MroAir {
    pub n_terms: usize,
}

impl MroAir {
    fn x(&self) -> usize {
        0
    }
    fn alpha(&self) -> usize {
        1
    }
    fn z(&self, k: usize) -> usize {
        3 + 2 * k
    }
    fn pz(&self, k: usize) -> usize {
        3 + 2 * self.n_terms + 2 * k
    }
    fn px(&self, k: usize) -> usize {
        3 + 4 * self.n_terms + k
    }
    fn inv(&self, k: usize) -> usize {
        3 + 5 * self.n_terms + 2 * k
    }
    fn apow(&self, k: usize) -> usize {
        3 + 7 * self.n_terms + 2 * k
    }
    fn w(&self) -> usize {
        3 + 9 * self.n_terms
    }
}

impl BaseAir<Goldilocks> for MroAir {
    fn width(&self) -> usize {
        self.w()
    }
    fn num_public_values(&self) -> usize {
        2 // the reduced opening
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for MroAir {
    fn eval(&self, builder: &mut AB) {
        let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let zero = AB::Expr::ZERO;
        let w = AB::Expr::from(Goldilocks::from_u64(MRO_W_EXT));
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(), a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone())
        };
        let g = |o: usize| (cur[o].clone(), cur[o + 1].clone());
        let mut fr = builder.when_first_row();

        let alpha = g(self.alpha());
        let xb = cur[self.x()].clone(); // DEEP point (base)

        // α-power chain: apow_0 = 1, apow_k = apow_{k-1} · α.
        fr.assert_zero(cur[self.apow(0)].clone() - one.clone());
        fr.assert_zero(cur[self.apow(0) + 1].clone());
        for k in 1..self.n_terms {
            let prod = emul(g(self.apow(k - 1)), alpha.clone());
            fr.assert_zero(cur[self.apow(k)].clone() - prod.0);
            fr.assert_zero(cur[self.apow(k) + 1].clone() - prod.1);
        }

        // ro = Σ_k apow_k · (p_z_k − p_x_k) · inv_k,  inv_k · (z_k − x) == 1.
        let mut ro = (zero.clone(), zero.clone());
        for k in 0..self.n_terms {
            let z = g(self.z(k));
            let inv = g(self.inv(k));
            let z_m_x = (z.0 - xb.clone(), z.1);
            let chk = emul(inv.clone(), z_m_x);
            fr.assert_zero(chk.0 - one.clone());
            fr.assert_zero(chk.1);
            let d = (cur[self.pz(k)].clone() - cur[self.px(k)].clone(), cur[self.pz(k) + 1].clone());
            let t = emul(emul(g(self.apow(k)), d), inv);
            ro = (ro.0 + t.0, ro.1 + t.1);
        }
        fr.assert_zero(ro.0 - pis[0].clone());
        fr.assert_zero(ro.1 - pis[1].clone());
    }
}

#[allow(dead_code)]
pub(crate) fn mro_build_trace(terms: &[(Challenge, Challenge, Val)], x: Val, alpha: Challenge, ro: Challenge) -> RowMajorMatrix<Val> {
    use p3_field::BasedVectorSpace;
    let c = |v: Challenge| -> [Val; 2] { v.as_basis_coefficients_slice().try_into().unwrap() };
    let air = MroAir { n_terms: terms.len() };
    let mut r = vec![Val::ZERO; air.w()];
    r[air.x()] = x;
    let ac = c(alpha);
    r[air.alpha()] = ac[0];
    r[air.alpha() + 1] = ac[1];
    let mut apow = Challenge::ONE;
    for (k, &(z, pz, px)) in terms.iter().enumerate() {
        let (zc, pzc) = (c(z), c(pz));
        r[air.z(k)] = zc[0];
        r[air.z(k) + 1] = zc[1];
        r[air.pz(k)] = pzc[0];
        r[air.pz(k) + 1] = pzc[1];
        r[air.px(k)] = px;
        let inv = c((z - x).inverse());
        r[air.inv(k)] = inv[0];
        r[air.inv(k) + 1] = inv[1];
        let ap = c(apow);
        r[air.apow(k)] = ap[0];
        r[air.apow(k) + 1] = ap[1];
        apow *= alpha;
    }
    let _ = ro;
    let mut vals = Vec::with_capacity(8 * air.w());
    for _ in 0..8 {
        vals.extend_from_slice(&r);
    }
    RowMajorMatrix::new(vals, air.w())
}

// =================================================================================================
// Phase 3 (parts 3+5) — the commit-phase fold chain + final check. Per round the running eval E folds
// with that round's sibling at β_r and the fold point s_r, BIT-AWARE (the index bit decides the arity-2
// group order): fold = (E+sib)/2 + (1−2·bit)·(E−sib)·β·inv(2s). The chain runs E0 = ro down to
// folded_eval; the per-query accept (log_final_poly_len = 0) is folded_eval == final_poly[0]. The fold
// points s_r are provided per round (their in-circuit derivation from the index is Phase-4 wiring).
// Validated vs native_fri::query_fold_data.
// =================================================================================================

const QF_E: usize = 0; // running eval (F_p²)
const QF_S: usize = 2; // sibling (F_p²)
const QF_B: usize = 4; // β_r (F_p²)
const QF_BIT: usize = 6; // arity-2 group slot of the running eval (boolean)
const QF_SPT: usize = 7; // fold point s_r (base)
const QF_I2S: usize = 8; // inv(2·s_r) (base)
const QF_WIDTH: usize = 9;

#[allow(dead_code)] // standalone-validated in Phase 3; composed into MonolithAir's query region in Phase 4
pub(crate) struct QueryFoldAir;

impl BaseAir<Goldilocks> for QueryFoldAir {
    fn width(&self) -> usize {
        QF_WIDTH
    }
    fn num_public_values(&self) -> usize {
        4 // ro (initial E) ‖ folded_eval (final E)
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for QueryFoldAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let two = AB::Expr::TWO;
        let half = AB::Expr::from(Goldilocks::ONE.halve());
        let w = AB::Expr::from(Goldilocks::from_u64(MRO_W_EXT));
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(), a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone())
        };

        // first row: running eval == public ro
        {
            let mut fr = builder.when_first_row();
            fr.assert_zero(cur[QF_E].clone() - pis[0].clone());
            fr.assert_zero(cur[QF_E + 1].clone() - pis[1].clone());
        }

        let bit = cur[QF_BIT].clone();
        let i2s = cur[QF_I2S].clone();
        let spt = cur[QF_SPT].clone();
        builder.when_transition().assert_zero(bit.clone() * (one.clone() - bit.clone())); // boolean
        builder.when_transition().assert_zero(i2s.clone() * (two.clone() * spt) - one.clone()); // inv(2s)
        let sign = one - two * bit; // 1 − 2·bit ∈ {+1, −1}
        let e = (cur[QF_E].clone(), cur[QF_E + 1].clone());
        let s = (cur[QF_S].clone(), cur[QF_S + 1].clone());
        let b = (cur[QF_B].clone(), cur[QF_B + 1].clone());
        let sum = (e.0.clone() + s.0.clone(), e.1.clone() + s.1.clone());
        let diff = (e.0 - s.0, e.1 - s.1);
        let prod = emul(diff, b);
        let fold0 = sum.0 * half.clone() + sign.clone() * prod.0 * i2s.clone();
        let fold1 = sum.1 * half.clone() + sign * prod.1 * i2s;
        builder.when_transition().assert_zero(nxt[QF_E].clone() - fold0);
        builder.when_transition().assert_zero(nxt[QF_E + 1].clone() - fold1);

        // last row: running eval == public folded_eval
        {
            let mut lr = builder.when_last_row();
            lr.assert_zero(cur[QF_E].clone() - pis[2].clone());
            lr.assert_zero(cur[QF_E + 1].clone() - pis[3].clone());
        }
    }
}

#[allow(dead_code)]
pub(crate) fn qf_build_trace(ro: Challenge, rounds: &[(Challenge, Challenge, bool, Val)], _folded_eval: Challenge) -> RowMajorMatrix<Val> {
    use crate::recursion::fri_fold::native_fold;
    use p3_field::BasedVectorSpace;
    let c = |v: Challenge| -> [Val; 2] { v.as_basis_coefficients_slice().try_into().unwrap() };
    let n = rounds.len();
    let height = (n + 1).next_power_of_two().max(2);
    let mut t = vec![Val::ZERO; height * QF_WIDTH];
    let mut e = ro;
    for r in 0..height {
        let base = r * QF_WIDTH;
        let ec = c(e);
        t[base + QF_E] = ec[0];
        t[base + QF_E + 1] = ec[1];
        if r < n {
            let (sib, beta, bit, s) = rounds[r];
            let (sc, bc) = (c(sib), c(beta));
            t[base + QF_S] = sc[0];
            t[base + QF_S + 1] = sc[1];
            t[base + QF_B] = bc[0];
            t[base + QF_B + 1] = bc[1];
            t[base + QF_BIT] = if bit { Val::ONE } else { Val::ZERO };
            t[base + QF_SPT] = s;
            t[base + QF_I2S] = (Val::TWO * s).inverse();
            let (e0, e1) = if bit { (sib, e) } else { (e, sib) };
            e = native_fold(e0, e1, beta, s);
        } else {
            // padding: sibling = running eval, β = 0, bit = 0 ⇒ fold = E (identity); s = 1.
            t[base + QF_S] = ec[0];
            t[base + QF_S + 1] = ec[1];
            t[base + QF_SPT] = Val::ONE;
            t[base + QF_I2S] = Val::TWO.inverse();
        }
    }
    RowMajorMatrix::new(t, QF_WIDTH)
}

// =================================================================================================
// Phase 4 (part 1) — the per-query INPUT TILE: compose the DEEP point (3a) + reduced opening (3b) into
// ONE AIR so x is no longer a separate input — the query index bits drive the DEEP product chain → x,
// and that same x feeds the reduced-opening denominators → ro. This is the first cross-gadget composition
// of the monolith's query region (column flow index → x → ro). Validated end-to-end vs native_fri's ro.
// (The fold chain + Merkle bindings + ×K tiling + the transcript wire — accept-iff-p3::verify — follow.)
// =================================================================================================

// layout: DEEP bits b_0..b_{N-1} ‖ acc_1..acc_N ‖ α ‖ per-term {z, p_z, p_x, inv, apow}
const QI_BITS: usize = 0;
const QI_ACC: usize = DP_LOG_HEIGHT;
const QI_ALPHA: usize = 2 * DP_LOG_HEIGHT;
const QI_TERMS: usize = 2 * DP_LOG_HEIGHT + 2;

#[allow(dead_code)]
pub(crate) struct QueryInputTileAir {
    pub n_terms: usize,
}

impl QueryInputTileAir {
    fn z(&self, k: usize) -> usize {
        QI_TERMS + 9 * k
    }
    fn pz(&self, k: usize) -> usize {
        self.z(k) + 2
    }
    fn px(&self, k: usize) -> usize {
        self.z(k) + 4
    }
    fn inv(&self, k: usize) -> usize {
        self.z(k) + 5
    }
    fn apow(&self, k: usize) -> usize {
        self.z(k) + 7
    }
    fn w(&self) -> usize {
        QI_TERMS + 9 * self.n_terms
    }
}

impl BaseAir<Goldilocks> for QueryInputTileAir {
    fn width(&self) -> usize {
        self.w()
    }
    fn num_public_values(&self) -> usize {
        2 // ro
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for QueryInputTileAir {
    fn eval(&self, builder: &mut AB) {
        let cur: Vec<AB::Expr> = builder.main().current_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let g = Goldilocks::two_adic_generator(DP_LOG_HEIGHT);
        let w = AB::Expr::from(Goldilocks::from_u64(MRO_W_EXT));
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(), a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone())
        };
        let gg = |o: usize| (cur[o].clone(), cur[o + 1].clone());
        let mut fr = builder.when_first_row();

        // --- DEEP point: index bits → x = GENERATOR · Π_i (b_i ? g^(2^(N-1-i)) : 1) ---
        for i in 0..DP_LOG_HEIGHT {
            let b = cur[QI_BITS + i].clone();
            fr.assert_zero(b.clone() * (one.clone() - b));
        }
        let mut prev = one.clone();
        for i in 0..DP_LOG_HEIGHT {
            let ci = AB::Expr::from(g.exp_power_of_2(DP_LOG_HEIGHT - 1 - i));
            let factor = one.clone() + cur[QI_BITS + i].clone() * (ci - one.clone());
            fr.assert_zero(cur[QI_ACC + i].clone() - prev * factor);
            prev = cur[QI_ACC + i].clone();
        }
        let x = AB::Expr::from(<Goldilocks as Field>::GENERATOR) * cur[QI_ACC + DP_LOG_HEIGHT - 1].clone();

        // --- reduced opening using THAT x: ro = Σ_k apow_k·(p_z_k − p_x_k)·inv_k, inv_k·(z_k − x) == 1 ---
        let alpha = gg(QI_ALPHA);
        fr.assert_zero(cur[self.apow(0)].clone() - one.clone());
        fr.assert_zero(cur[self.apow(0) + 1].clone());
        for k in 1..self.n_terms {
            let prod = emul(gg(self.apow(k - 1)), alpha.clone());
            fr.assert_zero(cur[self.apow(k)].clone() - prod.0);
            fr.assert_zero(cur[self.apow(k) + 1].clone() - prod.1);
        }
        let mut ro = (AB::Expr::ZERO, AB::Expr::ZERO);
        for k in 0..self.n_terms {
            let z = gg(self.z(k));
            let inv = gg(self.inv(k));
            let z_m_x = (z.0 - x.clone(), z.1);
            let chk = emul(inv.clone(), z_m_x);
            fr.assert_zero(chk.0 - one.clone());
            fr.assert_zero(chk.1);
            let d = (cur[self.pz(k)].clone() - cur[self.px(k)].clone(), cur[self.pz(k) + 1].clone());
            let t = emul(emul(gg(self.apow(k)), d), inv);
            ro = (ro.0 + t.0, ro.1 + t.1);
        }
        fr.assert_zero(ro.0 - pis[0].clone());
        fr.assert_zero(ro.1 - pis[1].clone());
    }
}

#[allow(dead_code)]
pub(crate) fn qi_build_trace(index: usize, terms: &[(Challenge, Challenge, Val)], alpha: Challenge, ro: Challenge) -> RowMajorMatrix<Val> {
    use p3_field::BasedVectorSpace;
    let c = |v: Challenge| -> [Val; 2] { v.as_basis_coefficients_slice().try_into().unwrap() };
    let air = QueryInputTileAir { n_terms: terms.len() };
    let g = Goldilocks::two_adic_generator(DP_LOG_HEIGHT);
    let mut r = vec![Val::ZERO; air.w()];
    // DEEP: bits + acc chain → x
    let mut acc = Val::ONE;
    for i in 0..DP_LOG_HEIGHT {
        let bit = (index >> i) & 1;
        r[QI_BITS + i] = Val::from_u64(bit as u64);
        acc *= if bit == 1 { g.exp_power_of_2(DP_LOG_HEIGHT - 1 - i) } else { Val::ONE };
        r[QI_ACC + i] = acc;
    }
    let x = <Goldilocks as Field>::GENERATOR * acc;
    // reduced opening terms
    let ac = c(alpha);
    r[QI_ALPHA] = ac[0];
    r[QI_ALPHA + 1] = ac[1];
    let mut apow = Challenge::ONE;
    for (k, &(z, pz, px)) in terms.iter().enumerate() {
        let (zc, pzc) = (c(z), c(pz));
        r[air.z(k)] = zc[0];
        r[air.z(k) + 1] = zc[1];
        r[air.pz(k)] = pzc[0];
        r[air.pz(k) + 1] = pzc[1];
        r[air.px(k)] = px;
        let inv = c((z - Challenge::from(x)).inverse());
        r[air.inv(k)] = inv[0];
        r[air.inv(k) + 1] = inv[1];
        let ap = c(apow);
        r[air.apow(k)] = ap[0];
        r[air.apow(k) + 1] = ap[1];
        apow *= alpha;
    }
    let _ = ro;
    let mut vals = Vec::with_capacity(8 * air.w());
    for _ in 0..8 {
        vals.extend_from_slice(&r);
    }
    RowMajorMatrix::new(vals, air.w())
}

// =================================================================================================
// Phase 4 (part 2) — the FULL per-query arithmetic tile: a multi-row AIR composing DEEP point + reduced
// opening (row 0) → ro = E_0, then the bit-aware commit-phase fold chain (all rows) → folded_eval, then
// the per-query accept folded_eval == final_poly[0] (last row). One AIR does the entire per-query
// arithmetic: index → x → ro → fold → accept. Validated vs verify_query's per-query accept. (The Merkle
// bindings authenticating the opened rows/siblings, and the ×K tiling + transcript wire, follow.)
// =================================================================================================

const QT_E: usize = 0; // fold: running eval
const QT_S: usize = 2; // fold: sibling
const QT_B: usize = 4; // fold: β_r
const QT_BIT: usize = 6; // fold: group-order bit
const QT_SPT: usize = 7; // fold: point s_r
const QT_I2S: usize = 8; // fold: inv(2 s_r)
const QT_DBITS: usize = 9; // DEEP index bits (row 0)
const QT_ACC: usize = QT_DBITS + DP_LOG_HEIGHT;
const QT_ALPHA: usize = QT_ACC + DP_LOG_HEIGHT;
const QT_TERMS: usize = QT_ALPHA + 2;

#[allow(dead_code)]
pub(crate) struct QueryTileAir {
    pub n_terms: usize,
}

impl QueryTileAir {
    fn z(&self, k: usize) -> usize {
        QT_TERMS + 9 * k
    }
    fn pz(&self, k: usize) -> usize {
        self.z(k) + 2
    }
    fn px(&self, k: usize) -> usize {
        self.z(k) + 4
    }
    fn inv(&self, k: usize) -> usize {
        self.z(k) + 5
    }
    fn apow(&self, k: usize) -> usize {
        self.z(k) + 7
    }
    fn w(&self) -> usize {
        QT_TERMS + 9 * self.n_terms
    }
}

impl BaseAir<Goldilocks> for QueryTileAir {
    fn width(&self) -> usize {
        self.w()
    }
    fn num_public_values(&self) -> usize {
        2 // final_poly[0] (the per-query accept target)
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for QueryTileAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let two = AB::Expr::TWO;
        let half = AB::Expr::from(Goldilocks::ONE.halve());
        let g = Goldilocks::two_adic_generator(DP_LOG_HEIGHT);
        let w = AB::Expr::from(Goldilocks::from_u64(MRO_W_EXT));
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(), a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone())
        };
        let gg = |o: usize| (cur[o].clone(), cur[o + 1].clone());

        // --- row 0: DEEP point + reduced opening → ro, and E_0 == ro ---
        {
            let mut fr = builder.when_first_row();
            for i in 0..DP_LOG_HEIGHT {
                let b = cur[QT_DBITS + i].clone();
                fr.assert_zero(b.clone() * (one.clone() - b));
            }
            let mut prev = one.clone();
            for i in 0..DP_LOG_HEIGHT {
                let ci = AB::Expr::from(g.exp_power_of_2(DP_LOG_HEIGHT - 1 - i));
                let factor = one.clone() + cur[QT_DBITS + i].clone() * (ci - one.clone());
                fr.assert_zero(cur[QT_ACC + i].clone() - prev * factor);
                prev = cur[QT_ACC + i].clone();
            }
            let x = AB::Expr::from(<Goldilocks as Field>::GENERATOR) * cur[QT_ACC + DP_LOG_HEIGHT - 1].clone();
            let alpha = gg(QT_ALPHA);
            fr.assert_zero(cur[self.apow(0)].clone() - one.clone());
            fr.assert_zero(cur[self.apow(0) + 1].clone());
            for k in 1..self.n_terms {
                let prod = emul(gg(self.apow(k - 1)), alpha.clone());
                fr.assert_zero(cur[self.apow(k)].clone() - prod.0);
                fr.assert_zero(cur[self.apow(k) + 1].clone() - prod.1);
            }
            let mut ro = (AB::Expr::ZERO, AB::Expr::ZERO);
            for k in 0..self.n_terms {
                let z = gg(self.z(k));
                let inv = gg(self.inv(k));
                let z_m_x = (z.0 - x.clone(), z.1);
                let chk = emul(inv.clone(), z_m_x);
                fr.assert_zero(chk.0 - one.clone());
                fr.assert_zero(chk.1);
                let d = (cur[self.pz(k)].clone() - cur[self.px(k)].clone(), cur[self.pz(k) + 1].clone());
                let t = emul(emul(gg(self.apow(k)), d), inv);
                ro = (ro.0 + t.0, ro.1 + t.1);
            }
            fr.assert_zero(cur[QT_E].clone() - ro.0); // E_0 == ro
            fr.assert_zero(cur[QT_E + 1].clone() - ro.1);
        }

        // --- all rows: bit-aware fold chain E → folded_eval ---
        let bit = cur[QT_BIT].clone();
        let i2s = cur[QT_I2S].clone();
        let spt = cur[QT_SPT].clone();
        builder.when_transition().assert_zero(bit.clone() * (one.clone() - bit.clone()));
        builder.when_transition().assert_zero(i2s.clone() * (two.clone() * spt) - one.clone());
        let sign = one - two * bit;
        let e = (cur[QT_E].clone(), cur[QT_E + 1].clone());
        let s = (cur[QT_S].clone(), cur[QT_S + 1].clone());
        let b = (cur[QT_B].clone(), cur[QT_B + 1].clone());
        let sum = (e.0.clone() + s.0.clone(), e.1.clone() + s.1.clone());
        let diff = (e.0 - s.0, e.1 - s.1);
        let prod = emul(diff, b);
        let fold0 = sum.0 * half.clone() + sign.clone() * prod.0 * i2s.clone();
        let fold1 = sum.1 * half.clone() + sign * prod.1 * i2s;
        builder.when_transition().assert_zero(nxt[QT_E].clone() - fold0);
        builder.when_transition().assert_zero(nxt[QT_E + 1].clone() - fold1);

        // --- last row: folded_eval == final_poly[0] (the per-query accept) ---
        {
            let mut lr = builder.when_last_row();
            lr.assert_zero(cur[QT_E].clone() - pis[0].clone());
            lr.assert_zero(cur[QT_E + 1].clone() - pis[1].clone());
        }
    }
}

#[allow(dead_code)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn qt_build_trace(
    index: usize,
    terms: &[(Challenge, Challenge, Val)],
    alpha: Challenge,
    ro: Challenge,
    rounds: &[(Challenge, Challenge, bool, Val)],
) -> RowMajorMatrix<Val> {
    use crate::recursion::fri_fold::native_fold;
    use p3_field::BasedVectorSpace;
    let c = |v: Challenge| -> [Val; 2] { v.as_basis_coefficients_slice().try_into().unwrap() };
    let air = QueryTileAir { n_terms: terms.len() };
    let g = Goldilocks::two_adic_generator(DP_LOG_HEIGHT);
    let n = rounds.len();
    let height = (n + 1).next_power_of_two().max(2);
    let mut t = vec![Val::ZERO; height * air.w()];

    // fold-chain columns (all rows) + the running eval.
    let mut e = ro;
    for r in 0..height {
        let base = r * air.w();
        let ec = c(e);
        t[base + QT_E] = ec[0];
        t[base + QT_E + 1] = ec[1];
        if r < n {
            let (sib, beta, bit, s) = rounds[r];
            let (sc, bc) = (c(sib), c(beta));
            t[base + QT_S] = sc[0];
            t[base + QT_S + 1] = sc[1];
            t[base + QT_B] = bc[0];
            t[base + QT_B + 1] = bc[1];
            t[base + QT_BIT] = if bit { Val::ONE } else { Val::ZERO };
            t[base + QT_SPT] = s;
            t[base + QT_I2S] = (Val::TWO * s).inverse();
            let (e0, e1) = if bit { (sib, e) } else { (e, sib) };
            e = native_fold(e0, e1, beta, s);
        } else {
            t[base + QT_S] = ec[0];
            t[base + QT_S + 1] = ec[1];
            t[base + QT_SPT] = Val::ONE;
            t[base + QT_I2S] = Val::TWO.inverse();
        }
    }

    // row 0: DEEP (bits + acc) + reduced (alpha + terms).
    let mut acc = Val::ONE;
    for i in 0..DP_LOG_HEIGHT {
        let bit = (index >> i) & 1;
        t[QT_DBITS + i] = Val::from_u64(bit as u64);
        acc *= if bit == 1 { g.exp_power_of_2(DP_LOG_HEIGHT - 1 - i) } else { Val::ONE };
        t[QT_ACC + i] = acc;
    }
    let x = <Goldilocks as Field>::GENERATOR * acc;
    let ac = c(alpha);
    t[QT_ALPHA] = ac[0];
    t[QT_ALPHA + 1] = ac[1];
    let mut apow = Challenge::ONE;
    for (k, &(z, pz, px)) in terms.iter().enumerate() {
        let (zc, pzc) = (c(z), c(pz));
        t[air.z(k)] = zc[0];
        t[air.z(k) + 1] = zc[1];
        t[air.pz(k)] = pzc[0];
        t[air.pz(k) + 1] = pzc[1];
        t[air.px(k)] = px;
        let inv = c((z - Challenge::from(x)).inverse());
        t[air.inv(k)] = inv[0];
        t[air.inv(k) + 1] = inv[1];
        let ap = c(apow);
        t[air.apow(k)] = ap[0];
        t[air.apow(k) + 1] = ap[1];
        apow *= alpha;
    }
    RowMajorMatrix::new(t, air.w())
}

// =================================================================================================
// Phase 4 (part 4) — the TILED query region: the per-query tile composed ×K into ONE AIR (the batch_*_air
// tiling pattern). Each tile occupies TILE_H rows; tile-periodic one-hots gate the per-tile work
// (P_TF at each tile's first row drives DEEP+reduced → E_0=ro; the fold runs on within-tile transitions
// gated by 1−P_TL; P_TL at each tile's last row checks E == final_poly[0]). One proof verifies every
// query. Validated: accepts the real proof (all queries verify) and rejects a tampered query.
// (The transcript wire feeding the shared challenges + the inline Merkle bindings are the final step.)
// =================================================================================================

const TILE_H: usize = 8; // fold chain height for the milestone's 6 rounds (rounds+1 padded to pow2)
const TQ_P_TF: usize = 0; // one-hot at each tile's first row
const TQ_P_TL: usize = 1; // one-hot at each tile's last row

#[allow(dead_code)]
pub(crate) struct TiledQueryAir {
    pub n_queries: usize,
    pub n_terms: usize,
}

impl TiledQueryAir {
    // per-tile column layout = the QueryTileAir layout (QT_* offsets reused).
    fn z(&self, k: usize) -> usize {
        QT_TERMS + 9 * k
    }
    fn pz(&self, k: usize) -> usize {
        self.z(k) + 2
    }
    fn px(&self, k: usize) -> usize {
        self.z(k) + 4
    }
    fn inv(&self, k: usize) -> usize {
        self.z(k) + 5
    }
    fn apow(&self, k: usize) -> usize {
        self.z(k) + 7
    }
    fn w(&self) -> usize {
        QT_TERMS + 9 * self.n_terms
    }
    fn height(&self) -> usize {
        (self.n_queries * TILE_H).next_power_of_two()
    }
    fn periodic(&self) -> Vec<Vec<Val>> {
        let h = self.height();
        let mut tf = vec![Val::ZERO; h];
        let mut tl = vec![Val::ZERO; h];
        for q in 0..self.n_queries {
            tf[q * TILE_H] = Val::ONE;
            tl[q * TILE_H + TILE_H - 1] = Val::ONE;
        }
        vec![tf, tl]
    }
}

impl BaseAir<Goldilocks> for TiledQueryAir {
    fn width(&self) -> usize {
        self.w()
    }
    fn num_public_values(&self) -> usize {
        2 // final_poly[0], shared across all tiles
    }
    fn num_periodic_columns(&self) -> usize {
        2
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        self.periodic()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for TiledQueryAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let two = AB::Expr::TWO;
        let half = AB::Expr::from(Goldilocks::ONE.halve());
        let g = Goldilocks::two_adic_generator(DP_LOG_HEIGHT);
        let w = AB::Expr::from(Goldilocks::from_u64(MRO_W_EXT));
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(), a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone())
        };
        let gg = |o: usize| (cur[o].clone(), cur[o + 1].clone());
        let tf = p[TQ_P_TF].clone();
        let tl = p[TQ_P_TL].clone();

        // --- per-tile first row (gated by TF): DEEP point + reduced opening → ro, E_0 == ro ---
        for i in 0..DP_LOG_HEIGHT {
            let b = cur[QT_DBITS + i].clone();
            builder.assert_zero(tf.clone() * (b.clone() * (one.clone() - b)));
        }
        let mut prev = one.clone();
        for i in 0..DP_LOG_HEIGHT {
            let ci = AB::Expr::from(g.exp_power_of_2(DP_LOG_HEIGHT - 1 - i));
            let factor = one.clone() + cur[QT_DBITS + i].clone() * (ci - one.clone());
            builder.assert_zero(tf.clone() * (cur[QT_ACC + i].clone() - prev * factor));
            prev = cur[QT_ACC + i].clone();
        }
        let x = AB::Expr::from(<Goldilocks as Field>::GENERATOR) * cur[QT_ACC + DP_LOG_HEIGHT - 1].clone();
        let alpha = gg(QT_ALPHA);
        builder.assert_zero(tf.clone() * (cur[self.apow(0)].clone() - one.clone()));
        builder.assert_zero(tf.clone() * cur[self.apow(0) + 1].clone());
        for k in 1..self.n_terms {
            let prod = emul(gg(self.apow(k - 1)), alpha.clone());
            builder.assert_zero(tf.clone() * (cur[self.apow(k)].clone() - prod.0));
            builder.assert_zero(tf.clone() * (cur[self.apow(k) + 1].clone() - prod.1));
        }
        let mut ro = (AB::Expr::ZERO, AB::Expr::ZERO);
        for k in 0..self.n_terms {
            let z = gg(self.z(k));
            let inv = gg(self.inv(k));
            let z_m_x = (z.0 - x.clone(), z.1);
            let chk = emul(inv.clone(), z_m_x);
            builder.assert_zero(tf.clone() * (chk.0 - one.clone()));
            builder.assert_zero(tf.clone() * chk.1);
            let d = (cur[self.pz(k)].clone() - cur[self.px(k)].clone(), cur[self.pz(k) + 1].clone());
            let t = emul(emul(gg(self.apow(k)), d), inv);
            ro = (ro.0 + t.0, ro.1 + t.1);
        }
        builder.assert_zero(tf.clone() * (cur[QT_E].clone() - ro.0));
        builder.assert_zero(tf * (cur[QT_E + 1].clone() - ro.1));

        // --- within-tile fold (transition gated by 1−TL): bit-aware fold E → folded_eval ---
        let not_last = one.clone() - tl.clone();
        let bit = cur[QT_BIT].clone();
        let i2s = cur[QT_I2S].clone();
        let spt = cur[QT_SPT].clone();
        builder.when_transition().assert_zero(not_last.clone() * (bit.clone() * (one.clone() - bit.clone())));
        builder.when_transition().assert_zero(not_last.clone() * (i2s.clone() * (two.clone() * spt) - one.clone()));
        let sign = one - two * bit;
        let e = (cur[QT_E].clone(), cur[QT_E + 1].clone());
        let s = (cur[QT_S].clone(), cur[QT_S + 1].clone());
        let b = (cur[QT_B].clone(), cur[QT_B + 1].clone());
        let sum = (e.0.clone() + s.0.clone(), e.1.clone() + s.1.clone());
        let diff = (e.0 - s.0, e.1 - s.1);
        let prod = emul(diff, b);
        let fold0 = sum.0 * half.clone() + sign.clone() * prod.0 * i2s.clone();
        let fold1 = sum.1 * half.clone() + sign * prod.1 * i2s;
        builder.when_transition().assert_zero(not_last.clone() * (nxt[QT_E].clone() - fold0));
        builder.when_transition().assert_zero(not_last * (nxt[QT_E + 1].clone() - fold1));

        // --- per-tile last row (gated by TL): folded_eval == final_poly[0] (the per-query accept) ---
        builder.assert_zero(tl.clone() * (cur[QT_E].clone() - pis[0].clone()));
        builder.assert_zero(tl * (cur[QT_E + 1].clone() - pis[1].clone()));
    }
}

#[allow(dead_code)]
#[allow(clippy::type_complexity)]
pub(crate) fn tq_build_trace(
    n_terms: usize,
    per_query: &[(usize, Vec<(Challenge, Challenge, Val)>, Challenge, Challenge, Vec<(Challenge, Challenge, bool, Val)>)],
) -> RowMajorMatrix<Val> {
    use crate::recursion::fri_fold::native_fold;
    use p3_field::BasedVectorSpace;
    let c = |v: Challenge| -> [Val; 2] { v.as_basis_coefficients_slice().try_into().unwrap() };
    let air = TiledQueryAir { n_queries: per_query.len(), n_terms };
    let g = Goldilocks::two_adic_generator(DP_LOG_HEIGHT);
    let h = air.height();
    let width = air.w();
    let mut t = vec![Val::ZERO; h * width];
    for (q, (index, terms, alpha, ro, rounds)) in per_query.iter().enumerate() {
        let tile = q * TILE_H;
        // fold-chain rows
        let mut e = *ro;
        for r in 0..TILE_H {
            let base = (tile + r) * width;
            let ec = c(e);
            t[base + QT_E] = ec[0];
            t[base + QT_E + 1] = ec[1];
            if r < rounds.len() {
                let (sib, beta, bit, s) = rounds[r];
                let (sc, bc) = (c(sib), c(beta));
                t[base + QT_S] = sc[0];
                t[base + QT_S + 1] = sc[1];
                t[base + QT_B] = bc[0];
                t[base + QT_B + 1] = bc[1];
                t[base + QT_BIT] = if bit { Val::ONE } else { Val::ZERO };
                t[base + QT_SPT] = s;
                t[base + QT_I2S] = (Val::TWO * s).inverse();
                let (e0, e1) = if bit { (sib, e) } else { (e, sib) };
                e = native_fold(e0, e1, beta, s);
            } else {
                t[base + QT_S] = ec[0];
                t[base + QT_S + 1] = ec[1];
                t[base + QT_SPT] = Val::ONE;
                t[base + QT_I2S] = Val::TWO.inverse();
            }
        }
        // tile row 0: DEEP + reduced
        let base0 = tile * width;
        let mut acc = Val::ONE;
        for i in 0..DP_LOG_HEIGHT {
            let bit = (index >> i) & 1;
            t[base0 + QT_DBITS + i] = Val::from_u64(bit as u64);
            acc *= if bit == 1 { g.exp_power_of_2(DP_LOG_HEIGHT - 1 - i) } else { Val::ONE };
            t[base0 + QT_ACC + i] = acc;
        }
        let x = <Goldilocks as Field>::GENERATOR * acc;
        let ac = c(*alpha);
        t[base0 + QT_ALPHA] = ac[0];
        t[base0 + QT_ALPHA + 1] = ac[1];
        let mut apow = Challenge::ONE;
        for (k, &(z, pz, px)) in terms.iter().enumerate() {
            let (zc, pzc) = (c(z), c(pz));
            t[base0 + air.z(k)] = zc[0];
            t[base0 + air.z(k) + 1] = zc[1];
            t[base0 + air.pz(k)] = pzc[0];
            t[base0 + air.pz(k) + 1] = pzc[1];
            t[base0 + air.px(k)] = px;
            let inv = c((z - Challenge::from(x)).inverse());
            t[base0 + air.inv(k)] = inv[0];
            t[base0 + air.inv(k) + 1] = inv[1];
            let ap = c(apow);
            t[base0 + air.apow(k)] = ap[0];
            t[base0 + air.apow(k) + 1] = ap[1];
            apow *= *alpha;
        }
    }
    RowMajorMatrix::new(t, width)
}

// =================================================================================================
// Phase 4.0 — the monolith SKELETON: de-risks the unified layout (the #1 assembly risk) BEFORE wiring
// logic. One trace with the [transcript | query | epilogue] region structure, period-32 Poseidon round
// columns, and full-height region masks (S_POSEIDON gates the round constraints to the transcript region;
// the query/epilogue rows ignore them). Confirms: the periodic schedule + masks + 32-alignment compile and
// prove, a Poseidon sponge runs correctly INSIDE a masked sub-region, and a transcript-output value binds
// to public via a one-hot (the binding mechanism Phase 4.A generalizes) — all within the 8 GB / ≤2^16 budget.
// =================================================================================================

const SK_TB: usize = 4; // transcript Poseidon blocks (skeleton size)
// periodic: 11 round cols + P_BLOCK_LAST (idx 11, present for alignment) + S_POSEIDON + P_OUT.
const SK_S_POSEIDON: usize = 12; // 1 on the transcript region's rows
const SK_P_OUT: usize = 13; // one-hot at the transcript's last block output row
const SK_N_PERIODIC: usize = 14;

#[allow(dead_code)]
pub(crate) struct MonolithSkeletonAir;

impl MonolithSkeletonAir {
    fn height(&self) -> usize {
        (SK_TB * BLOCK + BLOCK).next_power_of_two() // transcript region + a query/epilogue region, padded
    }
    fn periodic(&self) -> Vec<Vec<Val>> {
        let h = self.height();
        let mut cols = periodic_table(); // 11 round cols (period BLOCK)
        let mut block_last = vec![Val::ZERO; BLOCK];
        block_last[BLOCK - 1] = Val::ONE;
        cols.push(block_last);
        let mut s_pos = vec![Val::ZERO; h]; // transcript region = the first SK_TB blocks
        for r in 0..SK_TB * BLOCK {
            s_pos[r] = Val::ONE;
        }
        cols.push(s_pos);
        let mut p_out = vec![Val::ZERO; h];
        p_out[SK_TB * BLOCK - 1] = Val::ONE; // last transcript block's output row
        cols.push(p_out);
        cols
    }
}

impl BaseAir<Goldilocks> for MonolithSkeletonAir {
    fn width(&self) -> usize {
        W
    }
    fn num_public_values(&self) -> usize {
        2 // the bound transcript output (rate[3], rate[2])
    }
    fn num_periodic_columns(&self) -> usize {
        SK_N_PERIODIC
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        self.periodic()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for MonolithSkeletonAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let s_pos = p[SK_S_POSEIDON].clone();

        // Poseidon round constraints, GATED to the transcript region by S_POSEIDON (the query/epilogue rows
        // ignore the period-32 schedule). periodic_table zeroes the round selectors at each block's last row,
        // so the region-boundary transition is automatically vacuous.
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
            let step = is_init.clone() * (nxt[i].clone() - init_s[i].clone())
                + is_full.clone() * (nxt[i].clone() - full_s[i].clone())
                + is_partial.clone() * (nxt[i].clone() - part_s[i].clone());
            builder.when_transition().assert_zero(s_pos.clone() * step);
        }

        // transcript seed: the first block absorbs a fixed sponge input [1, 0, …].
        {
            let mut fr = builder.when_first_row();
            fr.assert_zero(cur[0].clone() - AB::Expr::ONE);
            for i in 1..W {
                fr.assert_zero(cur[i].clone());
            }
        }
        // bind the transcript output (rate[3], rate[2]) at the last block's output row → public.
        let out = p[SK_P_OUT].clone();
        builder.assert_zero(out.clone() * (cur[3].clone() - pis[0].clone()));
        builder.assert_zero(out * (cur[2].clone() - pis[1].clone()));
    }
}

#[allow(dead_code)]
pub(crate) fn skeleton_build_trace() -> (RowMajorMatrix<Val>, [Val; 2]) {
    let air = MonolithSkeletonAir;
    let h = air.height();
    let mut t = vec![Val::ZERO; h * W];
    // transcript region: a dummy duplex sponge (block 0 input [1,0,…], chained block-to-block).
    let mut input = [Val::ZERO; W];
    input[0] = Val::ONE;
    let mut last_out = [Val::ZERO; W];
    for blk in 0..SK_TB {
        let rows = native_steps(input);
        for r in 0..BLOCK {
            let base = (blk * BLOCK + r) * W;
            t[base..base + W].copy_from_slice(&rows[r]);
        }
        last_out = native_permute(input);
        input = last_out; // chain (squeeze-style)
    }
    // the bound output = (rate[3], rate[2]) of the last transcript block's output row.
    let out = [last_out[3], last_out[2]];
    (RowMajorMatrix::new(t, W), out)
}

// =================================================================================================
// Phase 4.A (binding mechanism) — the cross-region challenge carrier. A value squeezed in the transcript
// region (rate[3],rate[2] at the output bind row) is written to a GLOBAL-PERSISTENT carrier column, held
// constant across the whole trace, and READ in a later (query) region. This is the producer→carrier→
// consumer pattern (the `batch_*_air::ROOT` mechanism) by which the tiles consume the transcript's DERIVED
// challenges instead of free inputs — the soundness core of the full assembly. De-risked here on the
// skeleton's real Poseidon sponge before fusing the actual FullTranscriptAir + TiledQueryAir.
// =================================================================================================

const CA_CARRY: usize = W; // 2 global-persistent carrier lanes (the squeezed value V)
const CA_WIDTH: usize = W + 2;

#[allow(dead_code)]
pub(crate) struct CarryBindAir;

impl CarryBindAir {
    fn height(&self) -> usize {
        (SK_TB * BLOCK + BLOCK).next_power_of_two()
    }
    fn periodic(&self) -> Vec<Vec<Val>> {
        MonolithSkeletonAir.periodic() // reuse: round + block_last + S_POSEIDON + P_OUT
    }
}

impl BaseAir<Goldilocks> for CarryBindAir {
    fn width(&self) -> usize {
        CA_WIDTH
    }
    fn num_public_values(&self) -> usize {
        2 // the carrier value read in the consumer region
    }
    fn num_periodic_columns(&self) -> usize {
        SK_N_PERIODIC
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        self.periodic()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for CarryBindAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let s_pos = p[SK_S_POSEIDON].clone();

        // Poseidon sponge in the transcript region (gated by S_POSEIDON) — the producer.
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
            let step = is_init.clone() * (nxt[i].clone() - init_s[i].clone())
                + is_full.clone() * (nxt[i].clone() - full_s[i].clone())
                + is_partial.clone() * (nxt[i].clone() - part_s[i].clone());
            builder.when_transition().assert_zero(s_pos.clone() * step);
        }
        {
            let mut fr = builder.when_first_row();
            fr.assert_zero(cur[0].clone() - AB::Expr::ONE);
            for i in 1..W {
                fr.assert_zero(cur[i].clone());
            }
        }

        // The carrier: GLOBAL-PERSISTENT (held every transition), pinned to the squeezed value
        // (rate[3],rate[2]) at the transcript output row, read in the consumer (last) row → public.
        builder.when_transition().assert_zero(nxt[CA_CARRY].clone() - cur[CA_CARRY].clone());
        builder.when_transition().assert_zero(nxt[CA_CARRY + 1].clone() - cur[CA_CARRY + 1].clone());
        let out = p[SK_P_OUT].clone();
        builder.assert_zero(out.clone() * (cur[CA_CARRY].clone() - cur[3].clone()));
        builder.assert_zero(out * (cur[CA_CARRY + 1].clone() - cur[2].clone()));
        {
            let mut lr = builder.when_last_row();
            lr.assert_zero(cur[CA_CARRY].clone() - pis[0].clone());
            lr.assert_zero(cur[CA_CARRY + 1].clone() - pis[1].clone());
        }
    }
}

#[allow(dead_code)]
pub(crate) fn carry_build_trace() -> (RowMajorMatrix<Val>, [Val; 2]) {
    let air = CarryBindAir;
    let h = air.height();
    let mut t = vec![Val::ZERO; h * CA_WIDTH];
    let mut input = [Val::ZERO; W];
    input[0] = Val::ONE;
    let mut last_out = [Val::ZERO; W];
    for blk in 0..SK_TB {
        let rows = native_steps(input);
        for r in 0..BLOCK {
            let base = (blk * BLOCK + r) * CA_WIDTH;
            t[base..base + W].copy_from_slice(&rows[r]);
        }
        last_out = native_permute(input);
        input = last_out;
    }
    let v = [last_out[3], last_out[2]]; // the squeezed value V
    for r in 0..h {
        // carrier holds V across the WHOLE trace (constant; pinned at the output row, read at the last row)
        t[r * CA_WIDTH + CA_CARRY] = v[0];
        t[r * CA_WIDTH + CA_CARRY + 1] = v[1];
    }
    (RowMajorMatrix::new(t, CA_WIDTH), v)
}

// =================================================================================================
// Phase 4.A (fusion checkpoint 1) — the REAL FullTranscriptAir + TiledQueryAir in ONE AIR. The transcript
// region (rows [0,TR)) derives the challenges; the query region (rows [TR, TR+K·TILE_H)) runs the 32 tiles.
// α_fri flows transcript→tiles through a GLOBAL-PERSISTENT carrier (seeded from the squeeze at α_fri's bind
// row, held every transition, read by each tile as QT_ALPHA): the tiles consume the DERIVED α_fri, not a
// free input. Region gating: transcript nxt-constraints by S_TRANS_TRANS (1 on [0,TR-1), so block-linkage
// never leaks across the transcript→query boundary); tile fold by S_QUERY·(1-TL); tile DEEP/reduced by TF;
// tile accept by TL. (β_r/index/Merkle bindings are the next checkpoints; here they remain tile witness.)
// =================================================================================================

#[allow(dead_code)]
pub(crate) struct Phase4AAir {
    pub counts: Vec<u8>,
    pub binds: Vec<usize>,
    pub index_binds: Vec<(usize, usize)>,
    pub n_queries: usize,
    pub n_terms: usize,
}

#[allow(dead_code)]
impl Phase4AAir {
    fn nb(&self) -> usize {
        self.binds.len()
    }
    fn ni(&self) -> usize {
        self.index_binds.len()
    }
    fn n_rounds(&self) -> usize {
        self.nb() - 3 // binds = [α_stark, ζ, α_fri, β_0..β_{R-1}]
    }
    fn p_round(&self, r: usize) -> usize {
        FT_BIND_START + self.nb() + self.ni() + r // per-round one-hot: 1 at tile-row r of every tile
    }
    fn p_tf(&self) -> usize {
        FT_BIND_START + self.nb() + self.ni() + self.n_rounds()
    }
    fn p_tl(&self) -> usize {
        self.p_tf() + 1
    }
    fn p_strans(&self) -> usize {
        self.p_tf() + 2
    }
    fn p_squery(&self) -> usize {
        self.p_tf() + 3
    }
    fn tr(&self) -> usize {
        self.counts.len().next_power_of_two() * BLOCK
    }
    fn tile_w(&self) -> usize {
        QT_TERMS + 9 * self.n_terms
    }
    fn carry(&self) -> usize {
        self.tile_w()
    }
    // tile column accessors (= TiledQueryAir's QT_* layout)
    fn z(&self, k: usize) -> usize {
        QT_TERMS + 9 * k
    }
    fn pz(&self, k: usize) -> usize {
        self.z(k) + 2
    }
    fn px(&self, k: usize) -> usize {
        self.z(k) + 4
    }
    fn inv(&self, k: usize) -> usize {
        self.z(k) + 5
    }
    fn apow(&self, k: usize) -> usize {
        self.z(k) + 7
    }
    fn fused_w(&self) -> usize {
        self.tile_w() + 2 // + α_fri carrier
    }
    fn height(&self) -> usize {
        (self.tr() + self.n_queries * TILE_H).next_power_of_two()
    }
    fn periodic(&self) -> Vec<Vec<Val>> {
        let h = self.height();
        let nb_used = self.counts.len();
        let count_of = |b: usize| -> Val { if b < nb_used { Val::from_u64(self.counts[b] as u64) } else { Val::ZERO } };
        let mut cols = periodic_table(); // 11 round (period BLOCK)
        let mut block_last = vec![Val::ZERO; BLOCK];
        block_last[BLOCK - 1] = Val::ONE;
        cols.push(block_last);
        let mut count = vec![Val::ZERO; h];
        let mut count_next = vec![Val::ZERO; h];
        let mut is_sq_next = vec![Val::ZERO; h];
        for r in 0..h {
            let b = r / BLOCK;
            count[r] = count_of(b);
            count_next[r] = count_of(b + 1);
            is_sq_next[r] = if (b + 1 >= nb_used) || self.counts[b + 1] == 0 { Val::ONE } else { Val::ZERO };
        }
        cols.push(count);
        cols.push(count_next);
        cols.push(is_sq_next);
        for &blk in &self.binds {
            let mut col = vec![Val::ZERO; h];
            col[blk * BLOCK + BLOCK - 1] = Val::ONE;
            cols.push(col);
        }
        for &(blk, _lane) in &self.index_binds {
            let mut col = vec![Val::ZERO; h];
            col[blk * BLOCK + BLOCK - 1] = Val::ONE;
            cols.push(col);
        }
        let tr = self.tr();
        // per-round one-hots: P_ROUND_r = 1 at tile-row r of every tile (the fold row carrying β_r).
        for r in 0..self.n_rounds() {
            let mut col = vec![Val::ZERO; h];
            for q in 0..self.n_queries {
                col[tr + q * TILE_H + r] = Val::ONE;
            }
            cols.push(col);
        }
        let mut tf = vec![Val::ZERO; h];
        let mut tl = vec![Val::ZERO; h];
        for q in 0..self.n_queries {
            tf[tr + q * TILE_H] = Val::ONE;
            tl[tr + q * TILE_H + TILE_H - 1] = Val::ONE;
        }
        let mut s_trans_trans = vec![Val::ZERO; h]; // 1 where cur AND nxt are both in the transcript region
        for r in 0..tr.saturating_sub(1) {
            s_trans_trans[r] = Val::ONE;
        }
        let mut s_query = vec![Val::ZERO; h];
        for r in tr..(tr + self.n_queries * TILE_H) {
            s_query[r] = Val::ONE;
        }
        cols.push(tf);
        cols.push(tl);
        cols.push(s_trans_trans);
        cols.push(s_query);
        cols
    }
}

impl BaseAir<Goldilocks> for Phase4AAir {
    fn width(&self) -> usize {
        self.fused_w()
    }
    fn num_public_values(&self) -> usize {
        2 * self.nb() + self.ni() + 2 // transcript binds + index felts + final_poly[0]
    }
    fn num_periodic_columns(&self) -> usize {
        self.p_squery() + 1
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        self.periodic()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for Phase4AAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let two = AB::Expr::TWO;
        let stt = p[self.p_strans()].clone();
        let sq = p[self.p_squery()].clone();
        let tf = p[self.p_tf()].clone();
        let tl = p[self.p_tl()].clone();

        // ---------- transcript region (FullTranscriptAir, nxt-constraints gated by S_TRANS_TRANS) ----------
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
            let step = is_init.clone() * (nxt[i].clone() - init_s[i].clone())
                + is_full.clone() * (nxt[i].clone() - full_s[i].clone())
                + is_partial.clone() * (nxt[i].clone() - part_s[i].clone());
            builder.when_transition().assert_zero(stt.clone() * step);
        }
        {
            let mut fr = builder.when_first_row();
            fr.assert_zero(cur[CAP_LANE].clone() - p[FT_COUNT].clone());
            for i in (CAP_LANE + 1)..W {
                fr.assert_zero(cur[i].clone());
            }
        }
        {
            let bl = p[FT_P_BLOCK_LAST].clone();
            builder.when_transition().assert_zero(stt.clone() * bl.clone() * (nxt[CAP_LANE].clone() - cur[CAP_LANE].clone() - p[FT_COUNT_NEXT].clone()));
            for i in (CAP_LANE + 1)..W {
                builder.when_transition().assert_zero(stt.clone() * bl.clone() * (nxt[i].clone() - cur[i].clone()));
            }
            for i in 0..RATE {
                builder.when_transition().assert_zero(stt.clone() * bl.clone() * p[FT_IS_SQ_NEXT].clone() * (nxt[i].clone() - cur[i].clone()));
            }
        }
        for j in 0..self.nb() {
            let b = p[FT_BIND_START + j].clone();
            builder.assert_zero(b.clone() * (cur[3].clone() - pis[2 * j].clone()));
            builder.assert_zero(b * (cur[2].clone() - pis[2 * j + 1].clone()));
        }
        let ext_pubs = 2 * self.nb();
        let idx_start = FT_BIND_START + self.nb();
        for (k, &(_blk, lane)) in self.index_binds.iter().enumerate() {
            let b = p[idx_start + k].clone();
            builder.assert_zero(b * (cur[lane].clone() - pis[ext_pubs + k].clone()));
        }

        // ---------- α_fri carrier (global-persistent): held everywhere, pinned at α_fri's bind row ----------
        let carry = self.carry();
        builder.when_transition().assert_zero(nxt[carry].clone() - cur[carry].clone());
        builder.when_transition().assert_zero(nxt[carry + 1].clone() - cur[carry + 1].clone());
        let alpha_bind = p[FT_BIND_START + 2].clone(); // binds[2] = α_fri
        builder.assert_zero(alpha_bind.clone() * (cur[carry].clone() - cur[3].clone()));
        builder.assert_zero(alpha_bind * (cur[carry + 1].clone() - cur[2].clone()));

        // ---------- query region (TiledQueryAir) ----------
        let half = AB::Expr::from(Goldilocks::ONE.halve());
        let g = Goldilocks::two_adic_generator(DP_LOG_HEIGHT);
        let w = AB::Expr::from(Goldilocks::from_u64(MRO_W_EXT));
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(), a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone())
        };
        let gg = |o: usize| (cur[o].clone(), cur[o + 1].clone());

        // tile first row (TF): DEEP + reduced → ro; QT_ALPHA bound to the carried α_fri.
        for i in 0..DP_LOG_HEIGHT {
            let b = cur[QT_DBITS + i].clone();
            builder.assert_zero(tf.clone() * (b.clone() * (one.clone() - b)));
        }
        let mut prev = one.clone();
        for i in 0..DP_LOG_HEIGHT {
            let ci = AB::Expr::from(g.exp_power_of_2(DP_LOG_HEIGHT - 1 - i));
            let factor = one.clone() + cur[QT_DBITS + i].clone() * (ci - one.clone());
            builder.assert_zero(tf.clone() * (cur[QT_ACC + i].clone() - prev * factor));
            prev = cur[QT_ACC + i].clone();
        }
        let x = AB::Expr::from(<Goldilocks as Field>::GENERATOR) * cur[QT_ACC + DP_LOG_HEIGHT - 1].clone();
        // bind the tile's α to the DERIVED, carried α_fri (the cross-region binding).
        builder.assert_zero(tf.clone() * (cur[QT_ALPHA].clone() - cur[carry].clone()));
        builder.assert_zero(tf.clone() * (cur[QT_ALPHA + 1].clone() - cur[carry + 1].clone()));
        let alpha = gg(QT_ALPHA);
        builder.assert_zero(tf.clone() * (cur[self.apow(0)].clone() - one.clone()));
        builder.assert_zero(tf.clone() * cur[self.apow(0) + 1].clone());
        for k in 1..self.n_terms {
            let prod = emul(gg(self.apow(k - 1)), alpha.clone());
            builder.assert_zero(tf.clone() * (cur[self.apow(k)].clone() - prod.0));
            builder.assert_zero(tf.clone() * (cur[self.apow(k) + 1].clone() - prod.1));
        }
        let mut ro = (AB::Expr::ZERO, AB::Expr::ZERO);
        for k in 0..self.n_terms {
            let z = gg(self.z(k));
            let inv = gg(self.inv(k));
            let z_m_x = (z.0 - x.clone(), z.1);
            let chk = emul(inv.clone(), z_m_x);
            builder.assert_zero(tf.clone() * (chk.0 - one.clone()));
            builder.assert_zero(tf.clone() * chk.1);
            let d = (cur[self.pz(k)].clone() - cur[self.px(k)].clone(), cur[self.pz(k) + 1].clone());
            let t = emul(emul(gg(self.apow(k)), d), inv);
            ro = (ro.0 + t.0, ro.1 + t.1);
        }
        builder.assert_zero(tf.clone() * (cur[QT_E].clone() - ro.0));
        builder.assert_zero(tf.clone() * (cur[QT_E + 1].clone() - ro.1));

        // bind each fold-row's β_r to the DERIVED (public) β_r (binding #1, the fold challenges).
        // β_r = binds[3+r] → public[2(3+r)], public[2(3+r)+1]; P_ROUND_r selects the fold row.
        for r in 0..self.n_rounds() {
            let pr = p[self.p_round(r)].clone();
            let bidx = 3 + r;
            builder.assert_zero(pr.clone() * (cur[QT_B].clone() - pis[2 * bidx].clone()));
            builder.assert_zero(pr * (cur[QT_B + 1].clone() - pis[2 * bidx + 1].clone()));
        }

        // tile fold (transition gated by S_QUERY·(1-TL)).
        let fold_gate = sq.clone() * (one.clone() - tl.clone());
        let bit = cur[QT_BIT].clone();
        let i2s = cur[QT_I2S].clone();
        let spt = cur[QT_SPT].clone();
        builder.when_transition().assert_zero(fold_gate.clone() * (bit.clone() * (one.clone() - bit.clone())));
        builder.when_transition().assert_zero(fold_gate.clone() * (i2s.clone() * (two.clone() * spt) - one.clone()));
        let sign = one.clone() - two * bit;
        let e = (cur[QT_E].clone(), cur[QT_E + 1].clone());
        let s = (cur[QT_S].clone(), cur[QT_S + 1].clone());
        let bb = (cur[QT_B].clone(), cur[QT_B + 1].clone());
        let sum = (e.0.clone() + s.0.clone(), e.1.clone() + s.1.clone());
        let diff = (e.0 - s.0, e.1 - s.1);
        let prod = emul(diff, bb);
        let fold0 = sum.0 * half.clone() + sign.clone() * prod.0 * i2s.clone();
        let fold1 = sum.1 * half.clone() + sign * prod.1 * i2s;
        builder.when_transition().assert_zero(fold_gate.clone() * (nxt[QT_E].clone() - fold0));
        builder.when_transition().assert_zero(fold_gate * (nxt[QT_E + 1].clone() - fold1));

        // tile accept (TL): folded_eval == final_poly[0] (shared public).
        let fp0 = pis[2 * self.nb() + self.ni()].clone();
        let fp1 = pis[2 * self.nb() + self.ni() + 1].clone();
        builder.assert_zero(tl.clone() * (cur[QT_E].clone() - fp0));
        builder.assert_zero(tl * (cur[QT_E + 1].clone() - fp1));
    }
}

#[allow(dead_code)]
#[allow(clippy::type_complexity)]
pub(crate) fn phase4a_build_trace(
    air: &Phase4AAir,
    block_inputs: &[[Val; W]],
    per_query: &[(usize, Vec<(Challenge, Challenge, Val)>, Challenge, Challenge, Vec<(Challenge, Challenge, bool, Val)>)],
    alpha_fri: [Val; 2],
) -> RowMajorMatrix<Val> {
    let h = air.height();
    let w = air.fused_w();
    let tr = air.tr();
    let tw = air.tile_w();
    let mut t = vec![Val::ZERO; h * w];
    // transcript region: the FullTranscript trace embedded in lanes [0,W) of rows [0,TR).
    let ft = ft_build_trace(block_inputs);
    for r in 0..tr {
        for i in 0..W {
            t[r * w + i] = ft.values[r * W + i];
        }
    }
    // query region: the tiled-query trace embedded in lanes [0,tile_w) of rows [TR, TR+K·TILE_H).
    let tq = tq_build_trace(air.n_terms, per_query);
    let qrows = air.n_queries * TILE_H;
    for r in 0..qrows {
        for i in 0..tw {
            t[(tr + r) * w + i] = tq.values[r * tw + i];
        }
    }
    // α_fri carrier: held constant across the whole trace.
    for r in 0..h {
        t[r * w + air.carry()] = alpha_fri[0];
        t[r * w + air.carry() + 1] = alpha_fri[1];
    }
    RowMajorMatrix::new(t, w)
}

#[cfg(test)]
mod tests {
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
    fn sim_full(
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

    const CAP_HEIGHT: usize = 6; // MerkleTreeMmcs cap (build_mmcs_and_params)
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
            let (leaf, path, cap_entry) = query_commit_merkle(&config, &proof, &pvs, q);
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
        let trace = phase4a_build_trace(&air, &block_inputs, &per_query, alpha_fri);
        let h = air.height();
        println!("Phase 4.A fusion: 2^{} rows ({} transcript blocks + {} tiles, width {})", h.trailing_zeros(), counts.len(), MILESTONE_QUERIES, air.fused_w());
        let prf = prove(&config, &air, trace, &pis);
        assert!(verify(&config, &air, &prf, &pis).is_ok(), "fused transcript+tiles must prove with α_fri + all β_r DERIVED");
        let mut bad = pis.clone();
        bad[4] += Val::ONE; // α_fri public (chs[2] → pis[4]) — the bind fails
        assert!(verify(&config, &air, &prf, &bad).is_err(), "tampered α_fri ⇒ reject");
        let mut bad_beta = pis.clone();
        bad_beta[6] += Val::ONE; // β_0 public (chs[3] → pis[6]) — the per-round fold binding fails
        assert!(verify(&config, &air, &prf, &bad_beta).is_err(), "tampered β_0 ⇒ reject (fold binding)");
        let rss = peak_rss_bytes();
        println!("  -> peak RSS {} MiB", rss / (1 << 20));
        assert!(rss <= EIGHT_GB && h <= (1 << 18), "budget: RSS ≤ 8 GB, height ≤ 2^18");
    }
}
