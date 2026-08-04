use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
#[cfg(test)]
use p3_field::TwoAdicField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_goldilocks::Goldilocks;
use p3_matrix::dense::RowMajorMatrix;

use crate::poseidon2_air::{
    ext_linear, int_linear, native_permute, native_steps, periodic_table, pow7, BLOCK, W,
};
use crate::recursion::native_fri::{Challenge, Val};

use super::*;

// =================================================================================================
// Phase 5 — GENERAL-ARITY FRI fold. The milestone folds arity-2 (la=1); efficient/production configs fold
// arity-2^la (fewer, wider rounds). p3's `fold_row` interpolates the arity-2^la coset {xs_i} at β via the
// barycentric formula: folded = L(β)·Σ_i y_i·w_i/(β−x_i), where L(β)=Π_i(β−x_i), w_i = x_i/(n·x_0^n),
// n = arity. This gadget verifies that relation in-circuit for ANY arity (xs, inverses, weight-scale as
// witness — the same "point is witness in the gadget, derived in the monolith" split the arity-2 FriFoldAir
// uses), validated vs p3's OWN fold_row on a real arity-4 (`make_config(2,·)`) proof.
// =================================================================================================
#[allow(dead_code)]
pub(crate) struct GeneralFoldAir {
    pub log_arity: usize,
}
#[allow(dead_code)]
impl GeneralFoldAir {
    fn arity(&self) -> usize {
        1 << self.log_arity
    }
    fn c_eval(&self, i: usize) -> usize {
        2 * i // arity ext evals
    }
    fn c_beta(&self) -> usize {
        2 * self.arity()
    }
    fn c_xs(&self, i: usize) -> usize {
        2 * self.arity() + 2 + i // arity base coset points
    }
    fn c_inv(&self, i: usize) -> usize {
        3 * self.arity() + 2 + 2 * i // arity ext inverses of (β − xs_i)
    }
    fn c_wscale(&self) -> usize {
        5 * self.arity() + 2 // base: 1/(arity · xs_0^arity)
    }
    fn c_folded(&self) -> usize {
        5 * self.arity() + 3 // ext result
    }
    fn w(&self) -> usize {
        5 * self.arity() + 5
    }
}
impl BaseAir<Goldilocks> for GeneralFoldAir {
    fn width(&self) -> usize {
        self.w()
    }
    fn num_public_values(&self) -> usize {
        2 // the folded F_p² result
    }
}
impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for GeneralFoldAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let w = AB::Expr::from(Goldilocks::from_u64(MRO_W_EXT));
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (
                a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(),
                a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
            )
        };
        let arity = self.arity();
        let mut fr = builder.when_first_row();
        let beta = (cur[self.c_beta()].clone(), cur[self.c_beta() + 1].clone());
        // L(β) = Π_i (β − xs_i); each inv_i is the genuine ext inverse of (β − xs_i).
        let mut lz = (one.clone(), AB::Expr::ZERO);
        for i in 0..arity {
            let d = (beta.0.clone() - cur[self.c_xs(i)].clone(), beta.1.clone());
            let inv = (cur[self.c_inv(i)].clone(), cur[self.c_inv(i) + 1].clone());
            let chk = emul(inv, d.clone());
            fr.assert_zero(chk.0 - one.clone());
            fr.assert_zero(chk.1);
            lz = emul(lz, d);
        }
        // coset_power = xs_0^(2^la); weight_scale·(arity·coset_power) == 1.
        let mut cp = cur[self.c_xs(0)].clone();
        for _ in 0..self.log_arity {
            cp = cp.clone() * cp.clone();
        }
        let wscale = cur[self.c_wscale()].clone();
        fr.assert_zero(
            wscale.clone() * (AB::Expr::from(Goldilocks::from_usize(arity)) * cp) - one.clone(),
        );
        // acc = Σ_i y_i ⊗ inv_i · (xs_i · weight_scale); folded = L(β) ⊗ acc.
        let mut acc = (AB::Expr::ZERO, AB::Expr::ZERO);
        for i in 0..arity {
            let ev = (cur[self.c_eval(i)].clone(), cur[self.c_eval(i) + 1].clone());
            let inv = (cur[self.c_inv(i)].clone(), cur[self.c_inv(i) + 1].clone());
            let scal = cur[self.c_xs(i)].clone() * wscale.clone();
            let t = emul(ev, inv);
            acc = (acc.0 + t.0 * scal.clone(), acc.1 + t.1 * scal);
        }
        let res = emul(lz, acc);
        fr.assert_zero(cur[self.c_folded()].clone() - res.0.clone());
        fr.assert_zero(cur[self.c_folded() + 1].clone() - res.1.clone());
        fr.assert_zero(cur[self.c_folded()].clone() - pis[0].clone());
        fr.assert_zero(cur[self.c_folded() + 1].clone() - pis[1].clone());
    }
}

#[allow(dead_code)]
pub(crate) fn build_general_fold_trace(
    log_arity: usize,
    evals: &[Challenge],
    beta: Challenge,
    xs: &[Val],
    folded: Challenge,
) -> RowMajorMatrix<Val> {
    use p3_field::BasedVectorSpace;
    let air = GeneralFoldAir { log_arity };
    let arity = 1 << log_arity;
    let c = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
    let height = 16;
    let w = air.w();
    let mut r0 = vec![Val::ZERO; w];
    for i in 0..arity {
        let e = c(evals[i]);
        r0[air.c_eval(i)] = e[0];
        r0[air.c_eval(i) + 1] = e[1];
        r0[air.c_xs(i)] = xs[i];
        let inv = c((beta - Challenge::from(xs[i])).inverse());
        r0[air.c_inv(i)] = inv[0];
        r0[air.c_inv(i) + 1] = inv[1];
    }
    let bc = c(beta);
    r0[air.c_beta()] = bc[0];
    r0[air.c_beta() + 1] = bc[1];
    let cp = xs[0].exp_power_of_2(log_arity);
    r0[air.c_wscale()] = (Val::from_usize(arity) * cp).inverse();
    let fc = c(folded);
    r0[air.c_folded()] = fc[0];
    r0[air.c_folded() + 1] = fc[1];
    let mut vals = Vec::with_capacity(height * w);
    for _ in 0..height {
        vals.extend_from_slice(&r0);
    }
    RowMajorMatrix::new(vals, w)
}

// =================================================================================================
// Phase 5 — general-arity commit-phase LEAF hash. The commit-phase MMCS leaf is `MyHash(group)` over the
// arity-2^la fold group (2·arity = 2^(la+1) felts, always a multiple of RATE). The arity-2 leaf is the
// single-block case the monolith already inlines; higher arity needs a MULTI-block rate-overwrite sponge
// (absorb RATE felts, permute, overwrite rate + carry capacity, repeat). The Merkle PATH above the leaf is
// arity-independent (binary tree — already validated). Validated vs `MyHash` on a real arity-4 group.
// =================================================================================================
#[allow(dead_code)]
pub(crate) struct GeneralLeafHashAir {
    pub n_felts: usize, // = 2·arity, a multiple of RATE
}
#[allow(dead_code)]
impl GeneralLeafHashAir {
    // ceil(n_felts / RATE): the number of absorb permutations PaddingFreeSponge does. The LAST block absorbs
    // `rem` felts (1..=RATE); if rem < RATE the remaining rate lanes carry the previous block's output.
    pub(crate) fn n_blocks(&self) -> usize {
        self.n_felts.div_ceil(RATE)
    }
    fn rem(&self) -> usize {
        self.n_felts - (self.n_blocks() - 1) * RATE // final-block chunk length, 1..=RATE
    }
    fn chunk_len(&self, b: usize) -> usize {
        if b == self.n_blocks() - 1 {
            self.rem()
        } else {
            RATE
        }
    }
    fn height(&self) -> usize {
        (self.n_blocks() * BLOCK).next_power_of_two()
    }
    fn p_absorb(&self, b: usize) -> usize {
        12 + (b - 1) // absorb one-hots for blocks 1..n_blocks (after 11 round cols + P_BLOCK_LAST)
    }
    fn p_term(&self) -> usize {
        12 + (self.n_blocks() - 1) // terminal one-hot
    }
    // one-hot at the boundary INTO the short final block (its predecessor's last row), to carry the rate lanes
    // the short chunk doesn't overwrite. Present only when rem < RATE.
    fn p_last_carry(&self) -> usize {
        self.p_term() + 1
    }
    fn periodic(&self) -> Vec<Vec<Val>> {
        let h = self.height();
        let n = self.n_blocks();
        let mut cols = periodic_table(); // 11 round cols
        let mut bl = vec![Val::ZERO; h];
        for blk in 0..n {
            bl[blk * BLOCK + BLOCK - 1] = Val::ONE;
        }
        cols.push(bl); // P_BLOCK_LAST (index 11)
        for b in 1..n {
            let mut c = vec![Val::ZERO; h];
            c[b * BLOCK] = Val::ONE;
            cols.push(c); // P_ABSORB_b (block b first row)
        }
        let mut term = vec![Val::ZERO; h];
        term[(n - 1) * BLOCK + BLOCK - 1] = Val::ONE;
        cols.push(term); // P_TERM
        if self.rem() < RATE {
            let mut lc = vec![Val::ZERO; h];
            lc[(n - 2) * BLOCK + BLOCK - 1] = Val::ONE; // predecessor of the short final block, last row
            cols.push(lc); // P_LAST_CARRY
        }
        cols
    }
}
impl BaseAir<Goldilocks> for GeneralLeafHashAir {
    fn width(&self) -> usize {
        W
    }
    fn num_public_values(&self) -> usize {
        self.n_felts + 4 // the group preimage + the 4-felt leaf
    }
    fn num_periodic_columns(&self) -> usize {
        if self.rem() < RATE {
            self.p_last_carry() + 1
        } else {
            self.p_term() + 1
        }
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        self.periodic()
    }
}
impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for GeneralLeafHashAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder
            .periodic_values()
            .iter()
            .map(|&x| x.into())
            .collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        // Poseidon2 rounds (all blocks hash).
        let is_init = p[0].clone();
        let is_full = p[1].clone();
        let is_partial = p[2].clone();
        let rc: Vec<AB::Expr> = (0..W).map(|i| p[3 + i].clone()).collect();
        let mut init_s: [AB::Expr; W] = core::array::from_fn(|i| cur[i].clone());
        ext_linear(&mut init_s);
        let mut full_s: [AB::Expr; W] =
            core::array::from_fn(|i| pow7(cur[i].clone() + rc[i].clone()));
        ext_linear(&mut full_s);
        let mut part_s: [AB::Expr; W] = core::array::from_fn(|i| {
            if i == 0 {
                pow7(cur[0].clone() + rc[0].clone())
            } else {
                cur[i].clone()
            }
        });
        int_linear(&mut part_s);
        for i in 0..W {
            let step = is_init.clone() * (nxt[i].clone() - init_s[i].clone())
                + is_full.clone() * (nxt[i].clone() - full_s[i].clone())
                + is_partial.clone() * (nxt[i].clone() - part_s[i].clone());
            builder.when_transition().assert_zero(step);
        }
        // block 0: absorb group[0..RATE] into the rate, zero capacity.
        {
            let mut fr = builder.when_first_row();
            for k in 0..RATE {
                fr.assert_zero(cur[k].clone() - pis[k].clone());
            }
            for k in RATE..W {
                fr.assert_zero(cur[k].clone());
            }
        }
        // blocks 1..n: overwrite the rate with this block's group felts (P_ABSORB_b) + carry capacity
        // (P_BLOCK_LAST). The final block absorbs only `rem` felts (matching PaddingFreeSponge's short chunk).
        for b in 1..self.n_blocks() {
            let pa = p[self.p_absorb(b)].clone();
            for k in 0..self.chunk_len(b) {
                builder.assert_zero(pa.clone() * (cur[k].clone() - pis[b * RATE + k].clone()));
            }
        }
        {
            let bl = p[11].clone(); // P_BLOCK_LAST → capacity carry across every block boundary
            for k in RATE..W {
                builder
                    .when_transition()
                    .assert_zero(bl.clone() * (nxt[k].clone() - cur[k].clone()));
            }
        }
        // short final block: the rate lanes it does NOT overwrite (rem..RATE) carry the previous block's output.
        if self.rem() < RATE {
            let lc = p[self.p_last_carry()].clone();
            for k in self.rem()..RATE {
                builder
                    .when_transition()
                    .assert_zero(lc.clone() * (nxt[k].clone() - cur[k].clone()));
            }
        }
        // terminal: the last block's output rate == the committed leaf.
        let term = p[self.p_term()].clone();
        for k in 0..4 {
            builder.assert_zero(term.clone() * (cur[k].clone() - pis[self.n_felts + k].clone()));
        }
    }
}

#[allow(dead_code)]
pub(crate) fn build_general_leaf_trace(
    n_felts: usize,
    group: &[Val],
    leaf: [Val; 4],
) -> RowMajorMatrix<Val> {
    let air = GeneralLeafHashAir { n_felts };
    let n_blocks = air.n_blocks();
    let h = air.height();
    let mut t = vec![Val::ZERO; h * W];
    // PaddingFreeSponge: state starts at 0; each block overwrites rate[0..chunk_len] (rate[chunk_len..RATE] +
    // capacity carry the previous permutation output), then permutes. Blocks past n_blocks are PADDING (height
    // rounds to a power of two): they run a valid permutation continuation so the round constraints hold (only
    // the round schedule fires there — no absorb; the terminal is bound at the last REAL block).
    let n_total = h / BLOCK;
    let mut state = [Val::ZERO; W];
    for b in 0..n_total {
        if b < n_blocks {
            for k in 0..air.chunk_len(b) {
                state[k] = group[b * RATE + k];
            }
        }
        let rows = native_steps(state);
        for r in 0..BLOCK {
            let base = (b * BLOCK + r) * W;
            t[base..base + W].copy_from_slice(&rows[r]);
        }
        state = native_permute(state);
    }
    let _ = leaf; // (the terminal is bound to the public leaf; the trace's last-block output IS it)
    RowMajorMatrix::new(t, W)
}

// =================================================================================================
// Phase 5 re-fusion — the arity-4 fold CHAIN. The monolith's arity-2 fold does 6 rounds of the 2-point
// formula; at arity-4 it does 3 rounds of the barycentric 4-point fold (fewer, wider rounds → a smaller
// commit-phase super-tile). This AIR carries the running eval E across the chain E_0=ro → E_1 → … → E_N,
// each step the general-arity fold over the 4-eval group {E_r, siblings} (slotted at index%4 via the 2
// round bits), and checks the chain reaches final_poly[0] — the fused fold behavior the arity-4 monolith
// needs. The 4 group evals are witness (authenticated by the commit-phase Merkle in the full monolith);
// here the tie E_r == evals[slot] + the barycentric fold are validated vs p3's fold_row (general_fold_chain).
// =================================================================================================
const A4_E: usize = 0; // running eval (carried), 2 felts
const A4_EVALS: usize = 2; // the 4-eval group, 4 ext = 8 felts
const A4_B0: usize = 10;
const A4_B1: usize = 11;
const A4_BETA: usize = 12;
const A4_XS: usize = 14; // 4 base coset points
const A4_INV: usize = 18; // 4 ext inverses of (β − xs_i)
const A4_WSCALE: usize = 26;
const A4_W: usize = 27;
#[allow(dead_code)]
pub(crate) struct Arity4FoldChainAir {
    pub n_rounds: usize,
}
#[allow(dead_code)]
impl Arity4FoldChainAir {
    fn height(&self) -> usize {
        (self.n_rounds + 1).next_power_of_two().max(2)
    }
    fn periodic(&self) -> Vec<Vec<Val>> {
        let h = self.height();
        let mut fold = vec![Val::ZERO; h];
        for r in 0..self.n_rounds {
            fold[r] = Val::ONE;
        }
        let mut fin = vec![Val::ZERO; h];
        fin[self.n_rounds] = Val::ONE;
        vec![fold, fin]
    }
}
impl BaseAir<Goldilocks> for Arity4FoldChainAir {
    fn width(&self) -> usize {
        A4_W
    }
    fn num_public_values(&self) -> usize {
        4 // ro (2) + final_poly[0] (2)
    }
    fn num_periodic_columns(&self) -> usize {
        2
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        self.periodic()
    }
}
impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for Arity4FoldChainAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder
            .periodic_values()
            .iter()
            .map(|&x| x.into())
            .collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let w = AB::Expr::from(Goldilocks::from_u64(MRO_W_EXT));
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (
                a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(),
                a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
            )
        };
        let p_fold = p[0].clone();
        let p_fin = p[1].clone();
        let ev = |i: usize| {
            (
                cur[A4_EVALS + 2 * i].clone(),
                cur[A4_EVALS + 2 * i + 1].clone(),
            )
        };
        // E_0 == ro
        builder
            .when_first_row()
            .assert_zero(cur[A4_E].clone() - pis[0].clone());
        builder
            .when_first_row()
            .assert_zero(cur[A4_E + 1].clone() - pis[1].clone());
        // fold rows: slot bits, the running eval sits at slot, the barycentric fold → E_{r+1}.
        let b0 = cur[A4_B0].clone();
        let b1 = cur[A4_B1].clone();
        builder.assert_zero(p_fold.clone() * (b0.clone() * (one.clone() - b0.clone())));
        builder.assert_zero(p_fold.clone() * (b1.clone() * (one.clone() - b1.clone())));
        let sel = [
            (one.clone() - b0.clone()) * (one.clone() - b1.clone()),
            b0.clone() * (one.clone() - b1.clone()),
            (one.clone() - b0.clone()) * b1.clone(),
            b0.clone() * b1.clone(),
        ];
        // E == Σ sel_j · evals[j]  (the running eval occupies group slot = b0 + 2·b1)
        let mut e_slot = (AB::Expr::ZERO, AB::Expr::ZERO);
        for j in 0..4 {
            let e = ev(j);
            e_slot = (
                e_slot.0 + sel[j].clone() * e.0,
                e_slot.1 + sel[j].clone() * e.1,
            );
        }
        builder.assert_zero(p_fold.clone() * (cur[A4_E].clone() - e_slot.0));
        builder.assert_zero(p_fold.clone() * (cur[A4_E + 1].clone() - e_slot.1));
        // barycentric fold: L(β)·Σ_i y_i·(x_i·wscale)·inv_i, with inv_i·(β−x_i)==1, wscale·(4·x_0^4)==1.
        let beta = (cur[A4_BETA].clone(), cur[A4_BETA + 1].clone());
        let mut lz = (one.clone(), AB::Expr::ZERO);
        for i in 0..4 {
            let d = (beta.0.clone() - cur[A4_XS + i].clone(), beta.1.clone());
            let inv = (cur[A4_INV + 2 * i].clone(), cur[A4_INV + 2 * i + 1].clone());
            let chk = emul(inv, d.clone());
            builder.assert_zero(p_fold.clone() * (chk.0 - one.clone()));
            builder.assert_zero(p_fold.clone() * chk.1);
            lz = emul(lz, d);
        }
        let cp = {
            let x = cur[A4_XS].clone();
            let x2 = x.clone() * x;
            x2.clone() * x2
        };
        let wscale = cur[A4_WSCALE].clone();
        builder.assert_zero(
            p_fold.clone()
                * (wscale.clone() * (AB::Expr::from(Goldilocks::from_usize(4)) * cp) - one.clone()),
        );
        let mut acc = (AB::Expr::ZERO, AB::Expr::ZERO);
        for i in 0..4 {
            let y = ev(i);
            let inv = (cur[A4_INV + 2 * i].clone(), cur[A4_INV + 2 * i + 1].clone());
            let scal = cur[A4_XS + i].clone() * wscale.clone();
            let t = emul(y, inv);
            acc = (acc.0 + t.0 * scal.clone(), acc.1 + t.1 * scal);
        }
        let res = emul(lz, acc);
        // chain: next row's E == this round's folded result.
        builder
            .when_transition()
            .assert_zero(p_fold.clone() * (nxt[A4_E].clone() - res.0));
        builder
            .when_transition()
            .assert_zero(p_fold * (nxt[A4_E + 1].clone() - res.1));
        // accept: after N folds, E == final_poly[0].
        builder.assert_zero(p_fin.clone() * (cur[A4_E].clone() - pis[2].clone()));
        builder.assert_zero(p_fin * (cur[A4_E + 1].clone() - pis[3].clone()));
    }
}

#[allow(dead_code)]
#[allow(clippy::type_complexity)]
pub(crate) fn build_arity4_fold_chain_trace(
    n_rounds: usize,
    ro: Challenge,
    rounds: &[(Vec<Challenge>, Challenge, Vec<Val>, usize, Challenge)],
    final0: Challenge,
) -> RowMajorMatrix<Val> {
    use p3_field::BasedVectorSpace;
    let air = Arity4FoldChainAir { n_rounds };
    let c = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
    let h = air.height();
    let mut t = vec![Val::ZERO; h * A4_W];
    let mut e = ro;
    for (r, (evals, beta, xs, slot, folded)) in rounds.iter().enumerate() {
        let base = r * A4_W;
        let ec = c(e);
        t[base + A4_E] = ec[0];
        t[base + A4_E + 1] = ec[1];
        for i in 0..4 {
            let vc = c(evals[i]);
            t[base + A4_EVALS + 2 * i] = vc[0];
            t[base + A4_EVALS + 2 * i + 1] = vc[1];
            t[base + A4_XS + i] = xs[i];
            let inv = c((*beta - Challenge::from(xs[i])).inverse());
            t[base + A4_INV + 2 * i] = inv[0];
            t[base + A4_INV + 2 * i + 1] = inv[1];
        }
        t[base + A4_B0] = Val::from_u64((slot & 1) as u64);
        t[base + A4_B1] = Val::from_u64(((slot >> 1) & 1) as u64);
        let bc = c(*beta);
        t[base + A4_BETA] = bc[0];
        t[base + A4_BETA + 1] = bc[1];
        t[base + A4_WSCALE] = (Val::from_usize(4) * xs[0].exp_power_of_2(2)).inverse();
        e = *folded;
    }
    let ec = c(e); // == final0 after the last fold
    t[n_rounds * A4_W + A4_E] = ec[0];
    t[n_rounds * A4_W + A4_E + 1] = ec[1];
    let _ = final0;
    RowMajorMatrix::new(t, A4_W)
}

// =================================================================================================
// Phase 6.4 — the AGGREGATION tx-root FOLD AIR. Given K inner statements (each a single felt `pvs0`), emit
// the block tx-root EXACTLY as `batch_joinsplit_air::batch_root` / `native_fri::agg_root`: per tile a 2-block
// Merkle–Damgård fold — `s_k = merge([DOM,0,0,0], [pvs0,0,0,0])` then `root = merge(root, s_k)` — over a
// global-persistent ROOT column (IV=0), padded to a power of two (padding tiles use pvs0=0), with the tx-root
// bound as the SINGLE public input on the last row. This is the node-seam-compatible root, reusing the batch
// fold shape verbatim; validated vs `agg_root`. (In the full aggregator, each `pvs0` is the monolith tile's
// verified inner public value rather than a public input.)
// =================================================================================================
const AF_ROOT: usize = W; // global-persistent running root (4 lanes) after the 8 Poseidon lanes
const AF_W: usize = W + 4;
const AF_DOM: u64 = crate::domains::DOM_TXROOT; // the tx-root fold domain (normative table: crate::domains)
#[allow(dead_code)]
pub(crate) struct AggFoldAir {
    pub n_tiles: usize, // power of two
}
#[allow(dead_code)]
impl AggFoldAir {
    fn height(&self) -> usize {
        (2 * self.n_tiles * BLOCK).next_power_of_two()
    }
    fn p_sk(&self, t: usize) -> usize {
        12 + t // SK block (block 2t) first row, per tile
    }
    fn p_rootin(&self) -> usize {
        12 + self.n_tiles // ROOT block (2t+1) first row (all tiles)
    }
    fn p_sklast(&self) -> usize {
        self.p_rootin() + 1 // SK block last row (s_k → ROOT block rate-high link)
    }
    fn p_rootupd(&self) -> usize {
        self.p_rootin() + 2 // ROOT block last row (ROOT column update)
    }
    fn p_term(&self) -> usize {
        self.p_rootin() + 3 // last block last row (tx-root)
    }
    fn periodic(&self) -> Vec<Vec<Val>> {
        let h = self.height();
        let mut cols = periodic_table(); // 11 round cols
        let mut bl = vec![Val::ZERO; h];
        for blk in 0..(2 * self.n_tiles) {
            bl[blk * BLOCK + BLOCK - 1] = Val::ONE;
        }
        cols.push(bl); // P_BLOCK_LAST (11)
        for t in 0..self.n_tiles {
            let mut c = vec![Val::ZERO; h];
            c[(2 * t) * BLOCK] = Val::ONE;
            cols.push(c); // P_SK(t)
        }
        let mut rootin = vec![Val::ZERO; h];
        let mut sklast = vec![Val::ZERO; h];
        let mut rootupd = vec![Val::ZERO; h];
        for t in 0..self.n_tiles {
            rootin[(2 * t + 1) * BLOCK] = Val::ONE;
            sklast[(2 * t) * BLOCK + BLOCK - 1] = Val::ONE;
            rootupd[(2 * t + 1) * BLOCK + BLOCK - 1] = Val::ONE;
        }
        cols.push(rootin);
        cols.push(sklast);
        cols.push(rootupd);
        let mut term = vec![Val::ZERO; h];
        term[(2 * self.n_tiles - 1) * BLOCK + BLOCK - 1] = Val::ONE;
        cols.push(term); // P_TERM
        cols
    }
}
impl BaseAir<Goldilocks> for AggFoldAir {
    fn width(&self) -> usize {
        AF_W
    }
    fn num_public_values(&self) -> usize {
        self.n_tiles + 4 // K inner statements (pvs0) + the block tx-root
    }
    fn num_periodic_columns(&self) -> usize {
        self.p_term() + 1
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        self.periodic()
    }
}
impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for AggFoldAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder
            .periodic_values()
            .iter()
            .map(|&x| x.into())
            .collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let dom = AB::Expr::from(Goldilocks::from_u64(AF_DOM));
        // Poseidon2 rounds (every block hashes).
        let is_init = p[0].clone();
        let is_full = p[1].clone();
        let is_partial = p[2].clone();
        let rc: Vec<AB::Expr> = (0..W).map(|i| p[3 + i].clone()).collect();
        let mut init_s: [AB::Expr; W] = core::array::from_fn(|i| cur[i].clone());
        ext_linear(&mut init_s);
        let mut full_s: [AB::Expr; W] =
            core::array::from_fn(|i| pow7(cur[i].clone() + rc[i].clone()));
        ext_linear(&mut full_s);
        let mut part_s: [AB::Expr; W] = core::array::from_fn(|i| {
            if i == 0 {
                pow7(cur[0].clone() + rc[0].clone())
            } else {
                cur[i].clone()
            }
        });
        int_linear(&mut part_s);
        for i in 0..W {
            let step = is_init.clone() * (nxt[i].clone() - init_s[i].clone())
                + is_full.clone() * (nxt[i].clone() - full_s[i].clone())
                + is_partial.clone() * (nxt[i].clone() - part_s[i].clone());
            builder.when_transition().assert_zero(step);
        }
        // SK block seed: [DOM, 0, 0, 0, pvs0_t, 0, 0, 0] (P_SK(t) selects the t-th statement).
        for t in 0..self.n_tiles {
            let ps = p[self.p_sk(t)].clone();
            builder.assert_zero(ps.clone() * (cur[0].clone() - dom.clone()));
            builder.assert_zero(ps.clone() * (cur[4].clone() - pis[t].clone()));
            for i in [1usize, 2, 3, 5, 6, 7] {
                builder.assert_zero(ps.clone() * cur[i].clone());
            }
        }
        // SK block output → ROOT block rate-high (s_k link): nxt[4..8] == cur[0..4] on the SK block last row.
        let skl = p[self.p_sklast()].clone();
        for k in 0..4 {
            builder
                .when_transition()
                .assert_zero(skl.clone() * (nxt[4 + k].clone() - cur[k].clone()));
        }
        // ROOT block first row rate-low == the running ROOT column.
        let rin = p[self.p_rootin()].clone();
        for k in 0..4 {
            builder.assert_zero(rin.clone() * (cur[k].clone() - cur[AF_ROOT + k].clone()));
        }
        // ROOT column: IV = 0; updated to the ROOT block output at P_ROOT_UPDATE; held otherwise.
        for k in 0..4 {
            builder
                .when_first_row()
                .assert_zero(cur[AF_ROOT + k].clone());
        }
        let rupd = p[self.p_rootupd()].clone();
        for k in 0..4 {
            builder.when_transition().assert_zero(
                (AB::Expr::ONE - rupd.clone())
                    * (nxt[AF_ROOT + k].clone() - cur[AF_ROOT + k].clone()),
            );
            builder
                .when_transition()
                .assert_zero(rupd.clone() * (nxt[AF_ROOT + k].clone() - cur[k].clone()));
        }
        // tx-root: the last ROOT block output == the single public input.
        let term = p[self.p_term()].clone();
        for k in 0..4 {
            builder.assert_zero(term.clone() * (cur[k].clone() - pis[self.n_tiles + k].clone()));
        }
    }
}

#[allow(dead_code)]
pub(crate) fn build_agg_fold_trace(
    n_tiles: usize,
    pvs0: &[Val],
    tx_root: [Val; 4],
) -> RowMajorMatrix<Val> {
    let air = AggFoldAir { n_tiles };
    let h = air.height();
    let mut t = vec![Val::ZERO; h * AF_W];
    let mut root = [Val::ZERO; 4]; // IV = 0
    for tile in 0..n_tiles {
        let pv = pvs0.get(tile).copied().unwrap_or(Val::ZERO); // padding tiles fold pvs0 = 0
                                                               // SK block (2·tile): merge([DOM,0,0,0], [pv,0,0,0]) → s_k; ROOT column holds the running root.
        let mut sk_in = [Val::ZERO; W];
        sk_in[0] = Val::from_u64(AF_DOM);
        sk_in[4] = pv;
        let sk_rows = native_steps(sk_in);
        for r in 0..BLOCK {
            let base = ((2 * tile) * BLOCK + r) * AF_W;
            t[base..base + W].copy_from_slice(&sk_rows[r]);
            t[base + AF_ROOT..base + AF_ROOT + 4].copy_from_slice(&root);
        }
        let s_k: [Val; 4] = native_permute(sk_in)[..4].try_into().unwrap();
        // ROOT block (2·tile+1): merge(root, s_k) → root'; ROOT column still holds the OLD root here.
        let mut rt_in = [Val::ZERO; W];
        rt_in[..4].copy_from_slice(&root);
        rt_in[4..].copy_from_slice(&s_k);
        let rt_rows = native_steps(rt_in);
        for r in 0..BLOCK {
            let base = ((2 * tile + 1) * BLOCK + r) * AF_W;
            t[base..base + W].copy_from_slice(&rt_rows[r]);
            t[base + AF_ROOT..base + AF_ROOT + 4].copy_from_slice(&root);
        }
        root = native_permute(rt_in)[..4].try_into().unwrap(); // update for the next tile
    }
    debug_assert_eq!(root, tx_root, "built fold root == expected tx-root");
    RowMajorMatrix::new(t, AF_W)
}

// =================================================================================================
// GENERAL OOD EPILOGUE (Phase 7.2) — the α-folded constraint check at ζ for an ARBITRARY multi-column AIR, as
// a standalone gadget validated vs `fib_epilogue_oracle`. It DERIVES the Lagrange selectors from ζ in-circuit
// (z_h = ζ^(2^db) − 1 via squaring; is_trans = ζ − g^{-1}; is_first·(ζ−1) = z_h; is_last·(ζ−g^{-1}) = z_h) and
// checks the inverse-cleared relation for FibonacciAir's 5 constraints (Horner α-fold, EMISSION order — first
// gets the highest power): with D = (ζ−1)(ζ−g^{-1}),
//   α^4·z_h·(ζ−g^{-1})·(a−p0) + α^3·z_h·(ζ−g^{-1})·(b−p1)              [is_first·D = z_h·(ζ−g^{-1})]
//   + α^2·(ζ−1)(ζ−g^{-1})^2·(a'−b) + α^1·(ζ−1)(ζ−g^{-1})^2·(b'−a−b)   [is_trans·D = (ζ−1)(ζ−g^{-1})^2]
//   + z_h·(ζ−1)·(b−p2)                                               [is_last·D = z_h·(ζ−1)]
//   == quotient · z_h·(ζ−1)·(ζ−g^{-1}),
// which is exactly p3's `folded·inv_van == quotient`. Only the CONSTRAINT SET (the expr_i) is AIR-specific —
// the selector derivation + Horner fold structure are AIR-independent (the reusable core the full multi-column
// monolith fusion needs). ζ/α/pubs are public (degree 0) so the OOD openings + quotient stay degree 1.
// =================================================================================================
#[cfg(test)]
pub(crate) struct GeneralEpilogueAir;
#[cfg(test)]
impl GeneralEpilogueAir {
    fn c_la(&self) -> usize {
        0 // local column a (ext, 2 felts)
    }
    fn c_lb(&self) -> usize {
        2 // local column b
    }
    fn c_na(&self) -> usize {
        4 // next column a
    }
    fn c_nb(&self) -> usize {
        6 // next column b
    }
    fn c_q(&self) -> usize {
        8 // quotient(ζ)
    }
}
#[cfg(test)]
impl BaseAir<Goldilocks> for GeneralEpilogueAir {
    fn width(&self) -> usize {
        10
    }
    fn num_public_values(&self) -> usize {
        7 // ζ(2), α(2), p0, p1, p2
    }
}
#[cfg(test)]
impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for GeneralEpilogueAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let w = AB::Expr::from(Goldilocks::from_u64(MRO_W_EXT));
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (
                a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(),
                a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
            )
        };
        let zeta = (pis[0].clone(), pis[1].clone());
        let alpha = (pis[2].clone(), pis[3].clone());
        let p0 = pis[4].clone();
        let p1 = pis[5].clone();
        let p2 = pis[6].clone();
        let g_inv = AB::Expr::from(Goldilocks::two_adic_generator(M_DEGREE_BITS).inverse());
        // z_h = ζ^(2^db) − 1 (ζ public ⇒ inline squaring, degree 0).
        let mut s = zeta.clone();
        for _ in 0..M_DEGREE_BITS {
            s = emul(s.clone(), s.clone());
        }
        let z_h = (s.0 - one.clone(), s.1);
        let zmg = (zeta.0.clone() - g_inv, zeta.1.clone()); // ζ − g^{-1}
        let zm1 = (zeta.0.clone() - one.clone(), zeta.1.clone()); // ζ − 1
        let zmg2 = emul(zmg.clone(), zmg.clone());
        let mut ap = vec![(one.clone(), AB::Expr::ZERO)]; // α^0..α^4
        for k in 1..5 {
            ap.push(emul(ap[k - 1].clone(), alpha.clone()));
        }
        let coeff0 = emul(emul(ap[4].clone(), z_h.clone()), zmg.clone());
        let coeff1 = emul(emul(ap[3].clone(), z_h.clone()), zmg.clone());
        let coeff2 = emul(emul(ap[2].clone(), zm1.clone()), zmg2.clone());
        let coeff3 = emul(emul(ap[1].clone(), zm1.clone()), zmg2.clone());
        let coeff4 = emul(z_h.clone(), zm1.clone());
        let rhs_coeff = emul(emul(z_h.clone(), zm1.clone()), zmg.clone());
        let a = (cur[self.c_la()].clone(), cur[self.c_la() + 1].clone());
        let b = (cur[self.c_lb()].clone(), cur[self.c_lb() + 1].clone());
        let na = (cur[self.c_na()].clone(), cur[self.c_na() + 1].clone());
        let nb = (cur[self.c_nb()].clone(), cur[self.c_nb() + 1].clone());
        let q = (cur[self.c_q()].clone(), cur[self.c_q() + 1].clone());
        let t0 = emul(coeff0, (a.0.clone() - p0, a.1.clone()));
        let t1 = emul(coeff1, (b.0.clone() - p1, b.1.clone()));
        let t2 = emul(coeff2, (na.0 - b.0.clone(), na.1 - b.1.clone()));
        let t3 = emul(
            coeff3,
            (
                nb.0 - a.0.clone() - b.0.clone(),
                nb.1 - a.1.clone() - b.1.clone(),
            ),
        );
        let t4 = emul(coeff4, (b.0.clone() - p2, b.1.clone()));
        let rhs = emul(rhs_coeff, q);
        let mut fr = builder.when_first_row();
        fr.assert_zero(t0.0 + t1.0 + t2.0 + t3.0 + t4.0 - rhs.0);
        fr.assert_zero(t0.1 + t1.1 + t2.1 + t3.1 + t4.1 - rhs.1);
    }
}

// =================================================================================================
// MULTI-COLUMN REDUCED OPENING (Phase 7.3) — the DEEP reduced-opening `ro = Σ_k α^k·(p_z(k)−p_x(k))·inv(k)`
// for a W-column trace, as a standalone gadget validated vs `fib_query_terms`. The reduced-opening arithmetic
// is already n_terms-generic (the monolith's arith block); the genuinely NEW multi-column property is
// PX-SHARING: the trace batch contributes 2·W terms (W columns × {ζ, ζ_next}) and column c's two openings
// reuse the SAME authenticated row value (`opened_row[c]`) — so one Merkle-authenticated value feeds two DEEP
// terms. Modelled structurally (opened_row[c] is used directly for terms k with k%W==c), so tampering one
// opened value breaks BOTH that column's terms. α/ro/x are public; z/pz/inv (+ quotient px) are witness.
// =================================================================================================
#[cfg(test)]
pub(crate) struct MultiColReducedOpeningAir {
    pub(crate) w: usize,      // trace width (columns)
    pub(crate) n_quot: usize, // quotient DEEP terms
}
#[cfg(test)]
impl MultiColReducedOpeningAir {
    fn n_terms(&self) -> usize {
        2 * self.w + self.n_quot
    }
    fn trace_off(&self, k: usize) -> usize {
        self.w + k * 6 // trace term k: z(2), pz(2), inv(2)
    }
    fn quot_off(&self, j: usize) -> usize {
        self.w + 2 * self.w * 6 + j * 7 // quotient term j: z(2), pz(2), inv(2), px(1)
    }
    fn width(&self) -> usize {
        self.w + 2 * self.w * 6 + self.n_quot * 7
    }
}
#[cfg(test)]
impl BaseAir<Goldilocks> for MultiColReducedOpeningAir {
    fn width(&self) -> usize {
        MultiColReducedOpeningAir::width(self)
    }
    fn num_public_values(&self) -> usize {
        5 // α(2), ro(2), x
    }
}
#[cfg(test)]
impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for MultiColReducedOpeningAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let w_ext = AB::Expr::from(Goldilocks::from_u64(MRO_W_EXT));
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (
                a.0.clone() * b.0.clone() + w_ext.clone() * a.1.clone() * b.1.clone(),
                a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
            )
        };
        let alpha = (pis[0].clone(), pis[1].clone());
        let ro_pub = (pis[2].clone(), pis[3].clone());
        let x = pis[4].clone();
        // α powers 0..n_terms
        let mut ap = vec![(one.clone(), AB::Expr::ZERO)];
        for k in 1..self.n_terms() {
            ap.push(emul(ap[k - 1].clone(), alpha.clone()));
        }
        let mut fr = builder.when_first_row();
        let mut ro = (AB::Expr::ZERO, AB::Expr::ZERO);
        // per-term contribution given (z, pz, px, k): check inv·(z−x)==1, add α^k·(pz−px)·inv.
        let add_term = |fr: &mut _,
                        ro: &mut (AB::Expr, AB::Expr),
                        z: (AB::Expr, AB::Expr),
                        pz: (AB::Expr, AB::Expr),
                        inv: (AB::Expr, AB::Expr),
                        px: AB::Expr,
                        k: usize| {
            let chk = emul(inv.clone(), (z.0.clone() - x.clone(), z.1.clone()));
            AirBuilder::assert_zero(fr, chk.0 - one.clone());
            AirBuilder::assert_zero(fr, chk.1);
            let d = (pz.0.clone() - px, pz.1.clone());
            let t = emul(emul(ap[k].clone(), d), inv);
            *ro = (ro.0.clone() + t.0, ro.1.clone() + t.1);
        };
        // trace terms 0..2w — px = opened_row[k % w] (the SHARED authenticated value).
        for k in 0..(2 * self.w) {
            let off = self.trace_off(k);
            let z = (cur[off].clone(), cur[off + 1].clone());
            let pz = (cur[off + 2].clone(), cur[off + 3].clone());
            let inv = (cur[off + 4].clone(), cur[off + 5].clone());
            let px = cur[k % self.w].clone();
            add_term(&mut fr, &mut ro, z, pz, inv, px, k);
        }
        // quotient terms — px is a per-term witness (authenticated to the quotient commitment elsewhere).
        for j in 0..self.n_quot {
            let off = self.quot_off(j);
            let z = (cur[off].clone(), cur[off + 1].clone());
            let pz = (cur[off + 2].clone(), cur[off + 3].clone());
            let inv = (cur[off + 4].clone(), cur[off + 5].clone());
            let px = cur[off + 6].clone();
            add_term(&mut fr, &mut ro, z, pz, inv, px, 2 * self.w + j);
        }
        fr.assert_zero(ro.0 - ro_pub.0);
        fr.assert_zero(ro.1 - ro_pub.1);
    }
}

#[cfg(test)]
pub(crate) fn build_multicol_ro_trace(
    w: usize,
    terms: &[(Challenge, Challenge, Val)],
    x: Val,
    alpha: Challenge,
) -> RowMajorMatrix<Val> {
    use p3_field::BasedVectorSpace;
    let cc = |v: Challenge| -> [Val; 2] { v.as_basis_coefficients_slice().try_into().unwrap() };
    let n_quot = terms.len() - 2 * w;
    let air = MultiColReducedOpeningAir { w, n_quot };
    let width = BaseAir::<Goldilocks>::width(&air);
    let height = 16;
    let mut r0 = vec![Val::ZERO; width];
    // opened_row[c] = the authenticated row value = terms[c].px (shared with terms[w+c]).
    for c in 0..w {
        r0[c] = terms[c].2;
    }
    let fill = |r0: &mut [Val],
                off: usize,
                z: Challenge,
                pz: Challenge,
                px_col: Option<usize>,
                px: Val| {
        r0[off..off + 2].copy_from_slice(&cc(z));
        r0[off + 2..off + 4].copy_from_slice(&cc(pz));
        r0[off + 4..off + 6].copy_from_slice(&cc((z - Challenge::from(x)).inverse()));
        if let Some(pc) = px_col {
            r0[pc] = px;
        }
    };
    for k in 0..(2 * w) {
        let (z, pz, _px) = terms[k];
        fill(&mut r0, air.trace_off(k), z, pz, None, Val::ZERO);
    }
    for j in 0..n_quot {
        let (z, pz, px) = terms[2 * w + j];
        let off = air.quot_off(j);
        fill(&mut r0, off, z, pz, Some(off + 6), px);
    }
    let _ = alpha;
    let mut vals = Vec::with_capacity(height * width);
    for _ in 0..height {
        vals.extend_from_slice(&r0);
    }
    RowMajorMatrix::new(vals, width)
}

#[cfg(test)]
pub(crate) fn build_general_epilogue_trace(
    local: [Challenge; 2],
    next: [Challenge; 2],
    quotient: Challenge,
) -> RowMajorMatrix<Val> {
    use p3_field::BasedVectorSpace;
    let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
    let w = 10;
    let height = 16;
    let mut r0 = vec![Val::ZERO; w];
    r0[0..2].copy_from_slice(&cc(local[0]));
    r0[2..4].copy_from_slice(&cc(local[1]));
    r0[4..6].copy_from_slice(&cc(next[0]));
    r0[6..8].copy_from_slice(&cc(next[1]));
    r0[8..10].copy_from_slice(&cc(quotient));
    let mut vals = Vec::with_capacity(height * w);
    for _ in 0..height {
        vals.extend_from_slice(&r0);
    }
    RowMajorMatrix::new(vals, w)
}

// =================================================================================================
// GENERIC SYMBOLIC EPILOGUE (Phase 7.5) — a DATA-DRIVEN in-circuit OOD constraint check that verifies ANY
// inner AIR from its p3 `get_symbolic_constraints` trees (no hardcoded per-AIR fold). The three Lagrange
// selectors are WITNESSED (is_first/is_last/inv_van) and bound to their ζ-definitions (is_first·(ζ−1)=z_h;
// is_last·(ζ−g^{-1})=z_h; inv_van·z_h=1; is_trans=ζ−g^{-1}), so the constraint tree is evaluated directly
// (selectors as leaf VALUES — no per-constraint inverse-clearing) and the check is folded·inv_van == quot(ζ),
// exactly p3's verify_constraints. `eval_symbolic_circuit` mirrors `eval_symbolic_native`. Validated for
// Fibonacci. ζ/α/pubs are public; the openings + witnessed selectors are witness.
// =================================================================================================
// (not #[cfg(test)]: the fused monolith epilogue calls this when it verifies an inner from its symbolic
// constraints; in non-symbolic builds the monolith's `constraints` is empty so it is never invoked at runtime.)
#[allow(clippy::too_many_arguments)]
pub(crate) fn eval_symbolic_circuit<AB: AirBuilder<F = Goldilocks>>(
    e: &p3_uni_stark::SymbolicExpression<Val>,
    local: &[(AB::Expr, AB::Expr)],
    next: &[(AB::Expr, AB::Expr)],
    pubs: &[(AB::Expr, AB::Expr)],
    periodic: &[(AB::Expr, AB::Expr)],
    is_first: &(AB::Expr, AB::Expr),
    is_last: &(AB::Expr, AB::Expr),
    is_trans: &(AB::Expr, AB::Expr),
    w_ext: &AB::Expr,
) -> (AB::Expr, AB::Expr) {
    use p3_uni_stark::{BaseEntry, BaseLeaf, SymbolicExpr};
    let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
        (
            a.0.clone() * b.0.clone() + w_ext.clone() * a.1.clone() * b.1.clone(),
            a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
        )
    };
    match e {
        SymbolicExpr::Leaf(leaf) => match leaf {
            BaseLeaf::Variable(v) => match v.entry {
                BaseEntry::Main { offset } => {
                    if offset == 0 {
                        local[v.index].clone()
                    } else {
                        next[v.index].clone()
                    }
                }
                BaseEntry::Public => pubs[v.index].clone(),
                BaseEntry::Periodic => periodic[v.index].clone(), // periodic column value at ζ
                BaseEntry::Preprocessed { .. } => panic!("preprocessed columns unsupported"),
            },
            BaseLeaf::IsFirstRow => is_first.clone(),
            BaseLeaf::IsLastRow => is_last.clone(),
            BaseLeaf::IsTransition => is_trans.clone(),
            BaseLeaf::Constant(c) => (AB::Expr::from(*c), AB::Expr::ZERO),
        },
        SymbolicExpr::Add { x, y, .. } => {
            let a = eval_symbolic_circuit::<AB>(
                x, local, next, pubs, periodic, is_first, is_last, is_trans, w_ext,
            );
            let b = eval_symbolic_circuit::<AB>(
                y, local, next, pubs, periodic, is_first, is_last, is_trans, w_ext,
            );
            (a.0 + b.0, a.1 + b.1)
        }
        SymbolicExpr::Sub { x, y, .. } => {
            let a = eval_symbolic_circuit::<AB>(
                x, local, next, pubs, periodic, is_first, is_last, is_trans, w_ext,
            );
            let b = eval_symbolic_circuit::<AB>(
                y, local, next, pubs, periodic, is_first, is_last, is_trans, w_ext,
            );
            (a.0 - b.0, a.1 - b.1)
        }
        SymbolicExpr::Neg { x, .. } => {
            let a = eval_symbolic_circuit::<AB>(
                x, local, next, pubs, periodic, is_first, is_last, is_trans, w_ext,
            );
            (AB::Expr::ZERO - a.0, AB::Expr::ZERO - a.1)
        }
        SymbolicExpr::Mul { x, y, .. } => {
            let a = eval_symbolic_circuit::<AB>(
                x, local, next, pubs, periodic, is_first, is_last, is_trans, w_ext,
            );
            let b = eval_symbolic_circuit::<AB>(
                y, local, next, pubs, periodic, is_first, is_last, is_trans, w_ext,
            );
            emul(a, b)
        }
    }
}

#[cfg(test)]
pub(crate) struct SymbolicEpilogueAir {
    pub(crate) constraints: Vec<p3_uni_stark::SymbolicExpression<Val>>,
    pub(crate) w: usize,
    pub(crate) n_pub: usize,
    pub(crate) n_periodic: usize,
    pub(crate) degree_bits: usize, // the inner's degree_bits (for z_h = ζ^(2^db)−1 and g^{-1})
}
#[cfg(test)]
impl SymbolicEpilogueAir {
    fn c_local(&self, c: usize) -> usize {
        2 * c
    }
    fn c_next(&self, c: usize) -> usize {
        2 * self.w + 2 * c
    }
    fn c_quot(&self) -> usize {
        4 * self.w
    }
    fn c_isf(&self) -> usize {
        4 * self.w + 2
    }
    fn c_isl(&self) -> usize {
        4 * self.w + 4
    }
    fn c_iv(&self) -> usize {
        4 * self.w + 6
    }
    fn w_cols(&self) -> usize {
        4 * self.w + 8
    }
}
#[cfg(test)]
impl BaseAir<Goldilocks> for SymbolicEpilogueAir {
    fn width(&self) -> usize {
        self.w_cols()
    }
    fn num_public_values(&self) -> usize {
        4 + self.n_pub + 2 * self.n_periodic // ζ(2), α(2), pubs, periodic values at ζ
    }
}
#[cfg(test)]
impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for SymbolicEpilogueAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let w_ext = AB::Expr::from(Goldilocks::from_u64(MRO_W_EXT));
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (
                a.0.clone() * b.0.clone() + w_ext.clone() * a.1.clone() * b.1.clone(),
                a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
            )
        };
        let zeta = (pis[0].clone(), pis[1].clone());
        let alpha = (pis[2].clone(), pis[3].clone());
        let pubs: Vec<(AB::Expr, AB::Expr)> = (0..self.n_pub)
            .map(|i| (pis[4 + i].clone(), AB::Expr::ZERO))
            .collect();
        // z_h = ζ^(2^db) − 1 and g^{-1} use the INNER's degree_bits (the standalone gadget verifies inners at
        // any height, unlike the monolith which is pinned to M_DEGREE_BITS).
        let g_inv = AB::Expr::from(Goldilocks::two_adic_generator(self.degree_bits).inverse());
        let mut s = zeta.clone();
        for _ in 0..self.degree_bits {
            s = emul(s.clone(), s.clone());
        }
        let z_h = (s.0 - one.clone(), s.1);
        let is_trans = (zeta.0.clone() - g_inv, zeta.1.clone());
        let zm1 = (zeta.0.clone() - one.clone(), zeta.1.clone());
        let is_first = (cur[self.c_isf()].clone(), cur[self.c_isf() + 1].clone());
        let is_last = (cur[self.c_isl()].clone(), cur[self.c_isl() + 1].clone());
        let inv_van = (cur[self.c_iv()].clone(), cur[self.c_iv() + 1].clone());
        let local: Vec<(AB::Expr, AB::Expr)> = (0..self.w)
            .map(|c| {
                (
                    cur[self.c_local(c)].clone(),
                    cur[self.c_local(c) + 1].clone(),
                )
            })
            .collect();
        let next: Vec<(AB::Expr, AB::Expr)> = (0..self.w)
            .map(|c| (cur[self.c_next(c)].clone(), cur[self.c_next(c) + 1].clone()))
            .collect();
        let quot = (cur[self.c_quot()].clone(), cur[self.c_quot() + 1].clone());
        let mut fr = builder.when_first_row();
        // witnessed selectors bound to their ζ-definitions.
        let b_isf = emul(is_first.clone(), zm1.clone());
        fr.assert_zero(b_isf.0 - z_h.0.clone());
        fr.assert_zero(b_isf.1 - z_h.1.clone());
        let b_isl = emul(is_last.clone(), is_trans.clone());
        fr.assert_zero(b_isl.0 - z_h.0.clone());
        fr.assert_zero(b_isl.1 - z_h.1.clone());
        let b_iv = emul(inv_van.clone(), z_h.clone());
        fr.assert_zero(b_iv.0 - one.clone());
        fr.assert_zero(b_iv.1);
        // periodic column values at ζ (public, after ζ/α/pubs).
        let periodic: Vec<(AB::Expr, AB::Expr)> = (0..self.n_periodic)
            .map(|i| {
                (
                    pis[4 + self.n_pub + 2 * i].clone(),
                    pis[4 + self.n_pub + 2 * i + 1].clone(),
                )
            })
            .collect();
        // Horner α-fold over the extracted symbolic constraints (data-driven tree walk).
        let mut folded = (AB::Expr::ZERO, AB::Expr::ZERO);
        for c in &self.constraints {
            let ci = eval_symbolic_circuit::<AB>(
                c, &local, &next, &pubs, &periodic, &is_first, &is_last, &is_trans, &w_ext,
            );
            let fa = emul(folded.clone(), alpha.clone());
            folded = (fa.0 + ci.0, fa.1 + ci.1);
        }
        // folded·inv_van == quot(ζ).
        let chk = emul(folded, inv_van);
        fr.assert_zero(chk.0 - quot.0);
        fr.assert_zero(chk.1 - quot.1);
    }
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn build_symbolic_epilogue_trace(
    w: usize,
    local: &[Challenge],
    next: &[Challenge],
    quot: Challenge,
    is_first: Challenge,
    is_last: Challenge,
    inv_van: Challenge,
) -> RowMajorMatrix<Val> {
    use p3_field::BasedVectorSpace;
    let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
    let width = 4 * w + 8;
    let height = 16;
    let mut r0 = vec![Val::ZERO; width];
    for c in 0..w {
        r0[2 * c..2 * c + 2].copy_from_slice(&cc(local[c]));
        r0[2 * w + 2 * c..2 * w + 2 * c + 2].copy_from_slice(&cc(next[c]));
    }
    r0[4 * w..4 * w + 2].copy_from_slice(&cc(quot));
    r0[4 * w + 2..4 * w + 4].copy_from_slice(&cc(is_first));
    r0[4 * w + 4..4 * w + 6].copy_from_slice(&cc(is_last));
    r0[4 * w + 6..4 * w + 8].copy_from_slice(&cc(inv_van));
    let mut vals = Vec::with_capacity(height * width);
    for _ in 0..height {
        vals.extend_from_slice(&r0);
    }
    RowMajorMatrix::new(vals, width)
}
