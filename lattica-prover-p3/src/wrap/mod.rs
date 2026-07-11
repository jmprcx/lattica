//! W2 — the recursion **wrap** AIR (the deep-tree fixed point). RESEARCH; feature-gated behind `lookup`,
//! OFF by default, out of the audited staticlib. Built incrementally.
//!
//! The first brick isolates and MEASURES the **degree crux** — the load-bearing insight of
//! `docs/wrap-construction-plan.md`. The outer verifier's α_stark constraint-fold (the OOD epilogue B,
//! `recursion/monolith/air.rs:1310-1331`) is:
//! ```text
//!   for each inner constraint k:  c_k = eval_symbolic_circuit(constraint_k, opened_values)  // INLINE, deg ≤16
//!                                 folded = folded · α_stark + c_k                            // α-Horner
//!   check  folded · inv_vanishing == quotient(ζ)
//! ```
//! Because each `c_k` is evaluated **inline** (`gadgets.rs:919` `eval_symbolic_circuit` substitutes the
//! opened values into the degree-≤16 constraint expression), every fold step sits at degree ~16; chunking the
//! Horner (`FOLD_CHUNK = 7`, binding the running fold to a degree-1 witness column) caps the α-accumulation
//! but not the per-step `c_k` degree — so `base(16) + gating` exceeds the degree-16 / `log_nqc ≤ log_blowup`
//! cliff (p3-0.6.1 then silently produces unverifiable proofs; guarded in `native_verify.rs`). Measured:
//! `log_nqc = 7 > 4`.
//!
//! **The fix (B):** WITNESS each `c_k` in a degree-1 column (the outer AIR holds each inner-constraint value),
//! so the chunked Horner stays low-degree. This module measures that fix on a faithful model of the fold; the
//! *harder* companion — evaluating the `c_k` at low degree without the inline degree-16 expression (C, the
//! symbolic epilogue as a table / running-sum) — is the next W2 step.

use crate::config::Val;
use p3_air::symbolic::{AirLayout, SymbolicAirBuilder};
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::PrimeCharacteristicRing;
use p3_lookup::InteractionBuilder;
use p3_matrix::dense::RowMajorMatrix;
use p3_uni_stark::get_log_num_quotient_chunks;

pub mod air; // W2-assemble: the wrap AIR taking shape (the novel B/C/I regions fused, proven end-to-end)

/// A faithful model of the monolith's α_stark constraint-fold (B). Folds `n_constraints` inner-constraint
/// values `c_k` via the chunked α-Horner — `folded = folded·α + c_k`, binding the running fold to a degree-1
/// witness column (`fold_acc`) every `chunk` constraints — then checks `folded == target`.
///
/// Two knobs reproduce the degree behaviour and its fix:
/// - `c_cols_per_constraint` — how many trace columns each `c_k` multiplies. **1 models a WITNESSED `c_k`**
///   (degree 1 — the fix). **`d > 1` models the monolith's INLINE degree-`d` evaluation** (the explosion).
/// - `chunk` — the `FOLD_CHUNK` boundary. α_stark is a degree-1 witness column (column-window mode), so the
///   Horner accumulates α-degree; binding the partial fold every `chunk` steps caps *that* accumulation.
pub struct FoldAir {
    pub n_constraints: usize,
    pub chunk: usize,
    pub c_cols_per_constraint: usize,
}

impl FoldAir {
    /// Number of witnessed partial-fold columns = chunk boundaries = ⌈N / chunk⌉ − 1.
    fn n_fold_acc(&self) -> usize {
        self.n_constraints.div_ceil(self.chunk).saturating_sub(1)
    }
}

impl<F: p3_field::Field> BaseAir<F> for FoldAir {
    fn width(&self) -> usize {
        // [alpha, target, c_0..c_{N·cpc−1}, fold_acc_0..]
        2 + self.n_constraints * self.c_cols_per_constraint + self.n_fold_acc()
    }
}

impl<AB: AirBuilder<F = Val>> Air<AB> for FoldAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let alpha = local[0];
        let target = local[1];
        let c_base = 2;
        let cpc = self.c_cols_per_constraint;
        let acc_base = c_base + self.n_constraints * cpc;

        let mut folded: AB::Expr = AB::Expr::ZERO;
        let mut ai = 0;
        for k in 0..self.n_constraints {
            // c_k = ∏ of `cpc` columns (degree cpc); cpc = 1 ⇒ a single witnessed column (degree 1).
            let mut ck: AB::Expr = AB::Expr::ONE;
            for j in 0..cpc {
                ck = ck * local[c_base + k * cpc + j].into();
            }
            folded = folded * alpha.into() + ck;
            if (k + 1) % self.chunk == 0 && k + 1 < self.n_constraints {
                let acc = local[acc_base + ai];
                builder.assert_zero(acc.into() - folded.clone()); // bind the partial fold to a degree-1 column
                folded = acc.into();
                ai += 1;
            }
        }
        builder.assert_zero(folded - target.into());
    }
}

/// The `log_num_quotient_chunks` of a wrap AIR — the quantity that must stay ≤ `LOG_BLOWUP` (= 4). Above it,
/// p3-0.6.1 silently produces unverifiable proofs (the `native_verify.rs` degree guard). Computed symbolically
/// at the production `is_zk = 1`.
pub fn wrap_log_nqc<A>(air: &A) -> usize
where
    A: BaseAir<Val> + Air<SymbolicAirBuilder<Val>>,
{
    let layout = AirLayout::from_air::<Val>(air);
    get_log_num_quotient_chunks::<Val, A>(air, layout, 1)
}

/// `wrap_log_nqc` specialized to the α_stark fold model (kept for the W2-B tests).
pub fn fold_log_nqc(air: &FoldAir) -> usize {
    wrap_log_nqc(air)
}

/// **W2-C** — the combined constraint-evaluation-**and**-fold epilogue (C + B). For each of `n_constraints`
/// inner constraints, model its value `c_k` as a degree-`degree` product of opened columns, then α-fold the
/// `c_k` (chunked, à la [`FoldAir`]). The `witnessed` knob is the **C fix**:
/// - `witnessed = true` — evaluate each `c_k` through **degree-≤2 steps into witnessed intermediate columns**
///   (`t_0 = x_0·x_1`, `t_i = t_{i−1}·x_{i+1}`, …), so `c_k` is a *degree-1* column the fold consumes cheaply.
///   This is the low-degree analogue of `eval_symbolic_circuit` — "never re-evaluate the tree" as one
///   degree-`degree` expression. (A single degree-16 constraint is already `log_nqc = 4`; the explosion is the
///   fold stacking degree onto an inline degree-16 `c_k`, so witnessing the `c_k` is what lets B stay cheap.)
/// - `witnessed = false` — the monolith's INLINE evaluation: each `c_k` is one degree-`degree` expression fed
///   straight into the fold.
///
/// Soundness of the witnessed form: each intermediate is pinned by its own degree-2 constraint, so `c_k`
/// equals the product; a wrong intermediate fails its constraint. (Width cost — `2·degree − 1` columns per
/// constraint — is the SIZE lever addressed later by a shared op-table / lookup and Tip5, W3/W4; here we gate
/// only the DEGREE.)
pub struct DagFoldAir {
    pub n_constraints: usize,
    pub chunk: usize,
    pub degree: usize,
    pub witnessed: bool,
}

impl DagFoldAir {
    fn cols_per_constraint(&self) -> usize {
        if self.witnessed {
            2 * self.degree - 1 // `degree` inputs + `degree − 1` witnessed intermediates
        } else {
            self.degree // just the inputs; c_k is the inline product
        }
    }
    fn n_fold_acc(&self) -> usize {
        self.n_constraints.div_ceil(self.chunk).saturating_sub(1)
    }
}

impl<F: p3_field::Field> BaseAir<F> for DagFoldAir {
    fn width(&self) -> usize {
        2 + self.n_constraints * self.cols_per_constraint() + self.n_fold_acc()
    }
}

impl<AB: AirBuilder<F = Val>> Air<AB> for DagFoldAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let alpha = local[0];
        let target = local[1];
        let per = self.cols_per_constraint();
        let base = 2;
        let acc_base = base + self.n_constraints * per;

        let mut folded: AB::Expr = AB::Expr::ZERO;
        let mut ai = 0;
        for k in 0..self.n_constraints {
            let cb = base + k * per; // this constraint's column block
            let ck: AB::Expr = if self.witnessed {
                // C: evaluate the degree-`degree` product via degree-2 steps into witnessed intermediates.
                let t = cb + self.degree; // intermediate base
                builder.assert_zero(local[t].into() - local[cb].into() * local[cb + 1].into());
                for i in 1..self.degree - 1 {
                    builder.assert_zero(local[t + i].into() - local[t + i - 1].into() * local[cb + i + 1].into());
                }
                local[t + self.degree - 2].into() // c_k = final intermediate (degree-1 witnessed column)
            } else {
                // Inline (monolith): c_k is one degree-`degree` expression.
                let mut prod: AB::Expr = AB::Expr::ONE;
                for j in 0..self.degree {
                    prod = prod * local[cb + j].into();
                }
                prod
            };
            folded = folded * alpha.into() + ck;
            if (k + 1) % self.chunk == 0 && k + 1 < self.n_constraints {
                let acc = local[acc_base + ai];
                builder.assert_zero(acc.into() - folded.clone());
                folded = acc.into();
                ai += 1;
            }
        }
        builder.assert_zero(folded - target.into());
    }
}

/// **I (cap-mux)** — Merkle-cap membership as a LogUp lookup instead of the monolith's degree-`cap_height`
/// selector product over `2^cap_height` entries (`recursion/monolith/air.rs:1652-1664`). Columns
/// `[key, value, mult]` declare one 2-element `(key, value)` lookup carrying signed multiplicity `mult`: table
/// rows carry `−count[key]`, query rows `+1`, so the multiset balances iff every queried `(index, value)` is a
/// real `(j, cap[j])` pair — i.e. `value = cap[index]`. **Degree 3, width 3 (constant)** — killing both the
/// `cap_height`-degree product and the `2^cap_height` width. Proves + verifies through the W1 lookup prover.
///
/// (In the real wrap the cap table rows are bound to the transcript-committed cap; here they are trace rows,
/// so this validates the *mux mechanism* — that a query selects the right indexed entry — not that binding.)
pub struct CapMuxAir;

impl<F: p3_field::Field> BaseAir<F> for CapMuxAir {
    fn width(&self) -> usize {
        3
    }
}

impl<AB: AirBuilder<F = Val> + InteractionBuilder> Air<AB> for CapMuxAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let (key, value, mult) = (local[0], local[1], local[2]);
        // One 2-element (key, value) lookup tuple with signed multiplicity `mult` (LogUp "bus"): query rows
        // contribute +1, table rows −count[key]; balance ⇒ every queried (index, value) = a real (j, cap[j]).
        builder.push_local_interaction(vec![(vec![key.into(), value.into()], mult.into())]);
    }
}

/// Build a cap-mux trace: `cap.len()` table rows `(j, cap[j], −count[j])` plus one query row
/// `(index, cap[index], +1)` per query, padded (mult 0 ⇒ no contribution) to a power-of-two height.
pub fn cap_mux_trace(cap: &[Val], queries: &[usize]) -> RowMajorMatrix<Val> {
    let mut count = vec![0u64; cap.len()];
    for &q in queries {
        count[q] += 1;
    }
    let mut rows: Vec<[Val; 3]> = Vec::with_capacity(cap.len() + queries.len());
    for (j, &cj) in cap.iter().enumerate() {
        rows.push([Val::from_u64(j as u64), cj, -Val::from_u64(count[j])]); // table row: −count[j]
    }
    for &q in queries {
        rows.push([Val::from_u64(q as u64), cap[q], Val::ONE]); // query row: +1
    }
    rows.resize(rows.len().next_power_of_two(), [Val::ZERO, Val::ZERO, Val::ZERO]); // padding (mult 0)
    RowMajorMatrix::new(rows.into_iter().flatten().collect(), 3)
}

/// **W4 (Tip5 in-circuit) — the split-and-lookup S-box IS a cheap LogUp lookup.** The novel in-circuit Tip5
/// mechanism (`tip5.rs` doc: "a split-and-lookup S-box that a lookup argument verifies cheaply in-circuit"),
/// built as a real STARK: for a field element `x`, witness its 8 little-endian bytes `b₀..b₇`
/// (`x = Σ bᵢ·256ⁱ`, degree-1), map each through the real Tip5 offset-Fermat-cube byte map
/// `L(b) = ((b+1)³+256) mod 257`, and recombine `y = Σ L(bᵢ)·256ⁱ` — so `y = split_and_lookup(x)`. The byte map
/// is enforced by ONE LogUp channel against the 256-row table `(byte, L(byte))`: each S-box row READS its 8
/// `(bᵢ, oᵢ)` (+1), each table row PROVIDES `(byte, L(byte))` (−count). Balance ⇒ every `oᵢ = L(bᵢ)` AND every
/// `bᵢ ∈ [0,256)` (only bytes are table keys — the range is IMPLIED by the lookup). This VALIDATES
/// `cost_estimate`'s claim (the split lanes become degree-~1 lookups, not degree-7 x⁷) with an actual proof —
/// the foundational gadget of the in-circuit Tip5 hash (the full 5-round permutation AIR wraps this S-box + the
/// x⁷ lanes + the circulant MDS). (Canonical-decomposition variant, matching `tip5::split_and_lookup`; the
/// Goldilocks-canonicity of `x`'s split is the same range refinement the production Poseidon2/decomp gadgets use.)
#[cfg(feature = "tip5")]
pub struct Tip5SboxAir;

#[cfg(feature = "tip5")]
impl Tip5SboxAir {
    /// Bytes per field element (the split width).
    pub const NB: usize = 8;
    /// `[b₀..b₇, o₀..o₇, x, y, is_sbox, tm]` — 8 keys + 8 values + input + output + selector + table-mult.
    pub const W: usize = 2 * Self::NB + 4;
}

#[cfg(feature = "tip5")]
impl<F: p3_field::Field> BaseAir<F> for Tip5SboxAir {
    fn width(&self) -> usize {
        Self::W
    }
}

#[cfg(feature = "tip5")]
impl<AB: AirBuilder<F = Val> + InteractionBuilder> Air<AB> for Tip5SboxAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nb = Tip5SboxAir::NB;
        let (x, y) = (cur[2 * nb].clone(), cur[2 * nb + 1].clone());
        let (is_sbox, tm) = (cur[2 * nb + 2].clone(), cur[2 * nb + 3].clone());
        let one = AB::Expr::ONE;
        builder.assert_zero(is_sbox.clone() * (is_sbox.clone() - one.clone())); // selector boolean
        // decomposition x == Σ bᵢ·256ⁱ and recomposition y == Σ oᵢ·256ⁱ (both gated by is_sbox, both degree 1).
        let (mut xrec, mut yrec, mut base) = (AB::Expr::ZERO, AB::Expr::ZERO, AB::Expr::ONE);
        let b256 = AB::Expr::from(Val::from_u64(256));
        for i in 0..nb {
            xrec = xrec + cur[i].clone() * base.clone();
            yrec = yrec + cur[nb + i].clone() * base.clone();
            base = base * b256.clone();
        }
        builder.assert_zero(is_sbox.clone() * (x - xrec));
        builder.assert_zero(is_sbox.clone() * (y - yrec));
        // ONE LogUp channel: sbox rows READ 8 (bᵢ, oᵢ) (+is_sbox); table rows PROVIDE (byte, L(byte)) on slot 0
        // (−count via tm). mult₀ = is_sbox + tm, multᵢ≥₁ = is_sbox (0 on table/padding rows — dead tuples).
        let mut tuples: Vec<(Vec<AB::Expr>, AB::Expr)> = Vec::with_capacity(nb);
        for i in 0..nb {
            let mult = if i == 0 { is_sbox.clone() + tm.clone() } else { is_sbox.clone() };
            tuples.push((vec![cur[i].clone(), cur[nb + i].clone()], mult));
        }
        builder.push_local_interaction(tuples);
    }
}

/// The real Tip5 offset-Fermat-cube byte map `L(b) = ((b+1)³ + 256) mod 257` (== `tip5::LOOKUP_TABLE[b]`, per
/// `real_lookup_table_is_the_fermat_cube_bijection`). Bijective on `0..256`.
#[cfg(feature = "tip5")]
pub fn tip5_lookup(b: u64) -> u64 {
    let x = b + 1;
    (x * x * x + 256) % 257
}

/// Build a Tip5 S-box trace: 256 table rows `(byte, L(byte), −count)` + one S-box row per input (its 8 bytes +
/// their L-images + `x`/`y`), padded to a power of two. The lookup binds each S-box byte to the table ⇒ every
/// row's `y == split_and_lookup(x)`.
#[cfg(feature = "tip5")]
pub fn tip5_sbox_trace(inputs: &[u64]) -> RowMajorMatrix<Val> {
    let (nb, w) = (Tip5SboxAir::NB, Tip5SboxAir::W);
    let mut count = vec![0u64; 256];
    for &x in inputs {
        for byte in x.to_le_bytes() {
            count[byte as usize] += 1;
        }
    }
    let mut rows: Vec<Val> = Vec::new();
    // table rows: slot0 = (byte, L(byte)); tm = −count; is_sbox 0; x/y 0; slots 1..nb = 0.
    for b in 0..256u64 {
        let mut r = vec![Val::ZERO; w];
        r[0] = Val::from_u64(b);
        r[nb] = Val::from_u64(tip5_lookup(b));
        r[2 * nb + 3] = -Val::from_u64(count[b as usize]); // tm = −count[byte]
        rows.extend(r);
    }
    // sbox rows: bytes bᵢ = LE(x); oᵢ = L(bᵢ); y = Σ oᵢ·256ⁱ; is_sbox 1.
    for &x in inputs {
        let mut r = vec![Val::ZERO; w];
        let bytes = x.to_le_bytes();
        let mut y = 0u64;
        for i in 0..nb {
            let (bi, oi) = (bytes[i] as u64, tip5_lookup(bytes[i] as u64));
            r[i] = Val::from_u64(bi);
            r[nb + i] = Val::from_u64(oi);
            y = y.wrapping_add(oi << (8 * i)); // recombine (oᵢ < 256 ⇒ exact, no overflow to i=7)
        }
        r[2 * nb] = Val::from_u64(x);
        r[2 * nb + 1] = Val::from_u64(y);
        r[2 * nb + 2] = Val::ONE; // is_sbox
        rows.extend(r);
    }
    let h = (rows.len() / w).next_power_of_two();
    rows.resize(h * w, Val::ZERO); // padding rows: is_sbox 0, tm 0 ⇒ dead
    RowMajorMatrix::new(rows, w)
}

/// **W4 (Tip5 in-circuit) — a FULL Tip5 ROUND as a STARK** (S-box layer + circulant MDS + round constants). Wraps
/// the [`Tip5SboxAir`] S-box (the 4 split-and-lookup lanes) with the 12 `x⁷` power lanes (degree-7, ungated —
/// trivially `0=0` off the permutation rows), the real circulant MDS `out[i] = Σⱼ C[(i−j) mod 16]·sb[j]` (degree-1),
/// and the real round-0 constants — so one row computes `s ↦ MDS(sbox(s)) + RC₀`, the exact `Tip5::permute` round.
/// The split-lane byte maps are enforced by ONE LogUp vs the 256-row `(byte, L(byte))` table (32 reads/row = 4
/// lanes × 8 bytes). The full 5-round permutation threads 5 of these (each round's `so` feeding the next `s`); this
/// round AIR is the composed building block, proven end-to-end.
#[cfg(feature = "tip5")]
pub struct Tip5RoundAir;

#[cfg(feature = "tip5")]
impl Tip5RoundAir {
    /// State width (Tip5 = 16).
    pub const N: usize = crate::tip5::WIDTH;
    /// Split-and-lookup lanes (the rest are x⁷).
    pub const NS: usize = crate::tip5::NUM_SPLIT_LANES;
    /// Bytes per split lane.
    pub const NB: usize = 8;
    // layout: s[0..N] | ib[NS·NB] | ob[NS·NB] | sb[0..N] | so[0..N] | x2[N−NS] | is_perm | tm
    // x2 witnesses `s[i]²` for the power lanes so the x⁷ constraint is `x2³·s` (degree 4, not 7) — keeps log_nqc low.
    pub const IB: usize = Self::N;
    pub const OB: usize = Self::IB + Self::NS * Self::NB;
    pub const SB: usize = Self::OB + Self::NS * Self::NB;
    pub const SO: usize = Self::SB + Self::N;
    pub const X2: usize = Self::SO + Self::N;
    pub const IS_PERM: usize = Self::X2 + (Self::N - Self::NS);
    pub const TM: usize = Self::IS_PERM + 1;
    pub const W: usize = Self::TM + 1;
}

#[cfg(feature = "tip5")]
impl<F: p3_field::Field> BaseAir<F> for Tip5RoundAir {
    fn width(&self) -> usize {
        Self::W
    }
}

#[cfg(feature = "tip5")]
impl<AB: AirBuilder<F = Val> + InteractionBuilder> Air<AB> for Tip5RoundAir {
    fn eval(&self, builder: &mut AB) {
        use crate::tip5::{MDS_FIRST_COLUMN, ROUND_CONSTANTS};
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let (n, ns, nb) = (Tip5RoundAir::N, Tip5RoundAir::NS, Tip5RoundAir::NB);
        let (ib, ob, sb, so) = (Tip5RoundAir::IB, Tip5RoundAir::OB, Tip5RoundAir::SB, Tip5RoundAir::SO);
        let is_perm = cur[Tip5RoundAir::IS_PERM].clone();
        let tm = cur[Tip5RoundAir::TM].clone();
        let one = AB::Expr::ONE;
        builder.assert_zero(is_perm.clone() * (is_perm.clone() - one.clone()));
        let b256 = AB::Expr::from(Val::from_u64(256));

        // S-box layer. Split lanes i<NS: decompose s[i] into bytes, recompose sb[i] from their L-images (the LogUp
        // binds oᵢⱼ = L(ibᵢⱼ)). Power lanes i≥NS: sb[i] = s[i]⁷ (ungated — off the perm rows s=sb=0 ⇒ 0=0).
        for i in 0..ns {
            let (mut xrec, mut yrec, mut base) = (AB::Expr::ZERO, AB::Expr::ZERO, AB::Expr::ONE);
            for j in 0..nb {
                xrec = xrec + cur[ib + i * nb + j].clone() * base.clone();
                yrec = yrec + cur[ob + i * nb + j].clone() * base.clone();
                base = base * b256.clone();
            }
            builder.assert_zero(is_perm.clone() * (cur[i].clone() - xrec)); // s[i] = Σ ibᵢⱼ·256ʲ
            builder.assert_zero(is_perm.clone() * (cur[sb + i].clone() - yrec)); // sb[i] = Σ obᵢⱼ·256ʲ
        }
        for i in ns..n {
            let s = cur[i].clone();
            let x2 = cur[Tip5RoundAir::X2 + (i - ns)].clone();
            builder.assert_zero(x2.clone() - s.clone() * s.clone()); // x2 = s² (ungated; off perm s=x2=0 ⇒ 0=0)
            let x7 = x2.clone() * x2.clone() * x2.clone() * s; // x2³·s = s⁷ — DEGREE 4 (not 7) in committed cols
            builder.assert_zero(cur[sb + i].clone() - x7);
        }
        // MDS (circulant) + round-0 constants: so[i] = Σⱼ C[(i−j) mod N]·sb[j] + RC₀[i]  (gated; degree 1).
        for i in 0..n {
            let mut acc = AB::Expr::ZERO;
            for j in 0..n {
                let c = Val::from_u64(MDS_FIRST_COLUMN[(i + n - j) % n]);
                acc = acc + AB::Expr::from(c) * cur[sb + j].clone();
            }
            acc = acc + AB::Expr::from(ROUND_CONSTANTS[i]);
            builder.assert_zero(is_perm.clone() * (cur[so + i].clone() - acc));
        }
        // ONE LogUp channel: NS·NB byte reads (+is_perm); the table PROVIDES (byte, L(byte)) on slot 0 (−count via tm).
        let mut tuples: Vec<(Vec<AB::Expr>, AB::Expr)> = Vec::with_capacity(ns * nb);
        for k in 0..ns * nb {
            let mult = if k == 0 { is_perm.clone() + tm.clone() } else { is_perm.clone() };
            tuples.push((vec![cur[ib + k].clone(), cur[ob + k].clone()], mult));
        }
        builder.push_local_interaction(tuples);
    }
}

/// Build a Tip5 ROUND trace: 256 table rows `(byte, L(byte), −count)` + one row per input state computing
/// `so = MDS(sbox(s)) + RC₀`. Matches [`Tip5RoundAir`] exactly (so it proves).
#[cfg(feature = "tip5")]
pub fn tip5_round_trace(states: &[[u64; 16]]) -> RowMajorMatrix<Val> {
    use crate::tip5::{MDS_FIRST_COLUMN, ROUND_CONSTANTS};
    let (n, ns, nb, w) = (Tip5RoundAir::N, Tip5RoundAir::NS, Tip5RoundAir::NB, Tip5RoundAir::W);
    let pow7 = |x: Val| {
        let x2 = x * x;
        x2 * x2 * x2 * x
    };
    let mut count = vec![0u64; 256];
    for s in states {
        for i in 0..ns {
            for byte in s[i].to_le_bytes() {
                count[byte as usize] += 1;
            }
        }
    }
    let mut rows: Vec<Val> = Vec::new();
    for b in 0..256u64 {
        let mut r = vec![Val::ZERO; w];
        r[Tip5RoundAir::IB] = Val::from_u64(b); // slot-0 key
        r[Tip5RoundAir::OB] = Val::from_u64(tip5_lookup(b)); // slot-0 value
        r[Tip5RoundAir::TM] = -Val::from_u64(count[b as usize]);
        rows.extend(r);
    }
    for st in states {
        let mut r = vec![Val::ZERO; w];
        let s: [Val; 16] = core::array::from_fn(|i| Val::from_u64(st[i]));
        let mut sb = [Val::ZERO; 16];
        for i in 0..ns {
            let bytes = st[i].to_le_bytes();
            let mut y = 0u64;
            for j in 0..nb {
                let (bi, oi) = (bytes[j] as u64, tip5_lookup(bytes[j] as u64));
                r[Tip5RoundAir::IB + i * nb + j] = Val::from_u64(bi);
                r[Tip5RoundAir::OB + i * nb + j] = Val::from_u64(oi);
                y = y.wrapping_add(oi << (8 * j));
            }
            sb[i] = Val::from_u64(y);
        }
        for i in ns..n {
            sb[i] = pow7(s[i]);
            r[Tip5RoundAir::X2 + (i - ns)] = s[i] * s[i]; // witness s² (lowers the x⁷ constraint degree)
        }
        for i in 0..n {
            let mut acc = ROUND_CONSTANTS[i];
            for j in 0..n {
                acc += Val::from_u64(MDS_FIRST_COLUMN[(i + n - j) % n]) * sb[j];
            }
            r[Tip5RoundAir::SO + i] = acc;
        }
        for i in 0..n {
            r[i] = s[i];
            r[Tip5RoundAir::SB + i] = sb[i];
        }
        r[Tip5RoundAir::IS_PERM] = Val::ONE;
        rows.extend(r);
    }
    let h = (rows.len() / w).next_power_of_two();
    rows.resize(h * w, Val::ZERO);
    RowMajorMatrix::new(rows, w)
}

/// **W4 (Tip5 in-circuit) — the SPREAD round (feasibility de-risk of the full permutation).** The round-on-one-row
/// packs 32 byte-lookups ⇒ log_nqc 6 and does NOT verify (`tip5_round_degree_needs_spreading`). This SPREADS them:
/// each split-lane S-box goes on its OWN row (8 byte-lookups/row = the proven `Tip5SboxAir` level, ch0), and a
/// per-round "round row" does the `x⁷` power lanes (witnessed x², degree 4) + circulant MDS + round constants. The
/// two are connected by ONE ordered bus (ch1): the round row PROVIDES its `s[lane]` (key `lane`) + READS the
/// S-box output `sb[lane]` (key `16+lane`); each S-box row READS the `s[lane]` it decomposes + PROVIDES its `sb`.
/// Balance ⇒ each S-box row decomposes the round's real `s[lane]` and feeds back the real `sb[lane]`. This measures
/// that the SPREAD design composes at `log_nqc ≤ LOG_BLOWUP` — the feasibility the round-on-one-row could not reach
/// (the caps/openings "compose de-risk before assembly" pattern; the full 5-round permutation threads these rows +
/// the state chain, the remaining multi-brick assembly). `x⁷`/MDS reuse [`Tip5RoundAir`]; the S-box reuses [`Tip5SboxAir`].
#[cfg(feature = "tip5")]
pub struct Tip5SpreadRoundAir;

#[cfg(feature = "tip5")]
impl Tip5SpreadRoundAir {
    pub const N: usize = crate::tip5::WIDTH; // 16
    pub const NS: usize = crate::tip5::NUM_SPLIT_LANES; // 4
    pub const NB: usize = 8;
    pub const S: usize = 0; // round input state
    pub const SB: usize = Self::S + Self::N; // sbox-layer output
    pub const SO: usize = Self::SB + Self::N; // round output
    pub const K: usize = Self::SO + Self::N; // sbox row: 8 input bytes
    pub const O: usize = Self::K + Self::NB; // sbox row: 8 L-image bytes
    pub const X2: usize = Self::O + Self::NB; // round row: power-lane squares (N−NS)
    pub const LANE: usize = Self::X2 + (Self::N - Self::NS); // sbox row: which split lane
    pub const SVAL: usize = Self::LANE + 1; // sbox row: the decomposed value (= s[lane])
    pub const OVAL: usize = Self::SVAL + 1; // sbox row: the recomposed value (= sb[lane])
    pub const IS_SBOX: usize = Self::OVAL + 1;
    pub const IS_ROUND: usize = Self::IS_SBOX + 1;
    pub const TM: usize = Self::IS_ROUND + 1; // byte-table mult
    pub const W: usize = Self::TM + 1;
}

#[cfg(feature = "tip5")]
impl<F: p3_field::Field> BaseAir<F> for Tip5SpreadRoundAir {
    fn width(&self) -> usize {
        Self::W
    }
}

#[cfg(feature = "tip5")]
impl<AB: AirBuilder<F = Val> + InteractionBuilder> Air<AB> for Tip5SpreadRoundAir {
    fn eval(&self, builder: &mut AB) {
        use crate::tip5::{MDS_FIRST_COLUMN, ROUND_CONSTANTS};
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let (n, ns, nb) = (Tip5SpreadRoundAir::N, Tip5SpreadRoundAir::NS, Tip5SpreadRoundAir::NB);
        let c = |x: usize| cur[x].clone();
        let (is_sbox, is_round, tm) =
            (c(Tip5SpreadRoundAir::IS_SBOX), c(Tip5SpreadRoundAir::IS_ROUND), c(Tip5SpreadRoundAir::TM));
        let one = AB::Expr::ONE;
        builder.assert_zero(is_sbox.clone() * (is_sbox.clone() - one.clone()));
        builder.assert_zero(is_round.clone() * (is_round.clone() - one.clone()));
        let b256 = AB::Expr::from(Val::from_u64(256));
        // S-box row: sval = Σ kⱼ·256ʲ, oval = Σ oⱼ·256ʲ (the LogUp ch0 binds oⱼ = L(kⱼ)).
        let (mut kr, mut or_, mut base) = (AB::Expr::ZERO, AB::Expr::ZERO, AB::Expr::ONE);
        for j in 0..nb {
            kr = kr + c(Tip5SpreadRoundAir::K + j) * base.clone();
            or_ = or_ + c(Tip5SpreadRoundAir::O + j) * base.clone();
            base = base * b256.clone();
        }
        builder.assert_zero(is_sbox.clone() * (c(Tip5SpreadRoundAir::SVAL) - kr));
        builder.assert_zero(is_sbox.clone() * (c(Tip5SpreadRoundAir::OVAL) - or_));
        // Round row: power lanes sb[i] = s[i]⁷ (via witnessed x2, degree 4), MDS + round constants.
        for i in ns..n {
            let s = c(Tip5SpreadRoundAir::S + i);
            let x2 = c(Tip5SpreadRoundAir::X2 + (i - ns));
            builder.assert_zero(x2.clone() - s.clone() * s.clone());
            builder.assert_zero(c(Tip5SpreadRoundAir::SB + i) - x2.clone() * x2.clone() * x2.clone() * s);
        }
        for i in 0..n {
            let mut acc = AB::Expr::ZERO;
            for j in 0..n {
                acc = acc + AB::Expr::from(Val::from_u64(MDS_FIRST_COLUMN[(i + n - j) % n])) * c(Tip5SpreadRoundAir::SB + j);
            }
            acc = acc + AB::Expr::from(ROUND_CONSTANTS[i]);
            builder.assert_zero(is_round.clone() * (c(Tip5SpreadRoundAir::SO + i) - acc));
        }
        // Channel 0 — the byte-table (8 lookups/row = the proven S-box level). Table PROVIDES (byte, L(byte)) on slot 0.
        let mut ch0: Vec<(Vec<AB::Expr>, AB::Expr)> = Vec::with_capacity(nb);
        for j in 0..nb {
            let mult = if j == 0 { is_sbox.clone() + tm.clone() } else { is_sbox.clone() };
            ch0.push((vec![c(Tip5SpreadRoundAir::K + j), c(Tip5SpreadRoundAir::O + j)], mult));
        }
        builder.push_local_interaction(ch0);
        // Channel 1 — the s/sb CONNECTION bus. Round row: PROVIDE (lane, s[lane]) −is_round + READ (16+lane, sb[lane])
        // +is_round for each split lane. S-box row: READ (lane, sval) +is_sbox + PROVIDE (16+lane, oval) −is_sbox.
        let mut ch1: Vec<(Vec<AB::Expr>, AB::Expr)> = Vec::with_capacity(2 * ns + 2);
        for l in 0..ns {
            ch1.push((vec![AB::Expr::from(Val::from_u64(l as u64)), c(Tip5SpreadRoundAir::S + l)], AB::Expr::ZERO - is_round.clone()));
        }
        for l in 0..ns {
            ch1.push((vec![AB::Expr::from(Val::from_u64((n + l) as u64)), c(Tip5SpreadRoundAir::SB + l)], is_round.clone()));
        }
        ch1.push((vec![c(Tip5SpreadRoundAir::LANE), c(Tip5SpreadRoundAir::SVAL)], is_sbox.clone()));
        ch1.push((
            vec![c(Tip5SpreadRoundAir::LANE) + AB::Expr::from(Val::from_u64(n as u64)), c(Tip5SpreadRoundAir::OVAL)],
            AB::Expr::ZERO - is_sbox.clone(),
        ));
        builder.push_local_interaction(ch1);
    }
}

/// **AA5 — the in-circuit ORDERED SPONGE-CAP BUS** (feasibility, real data). The FS-anchor AA5 needs binds the
/// narrow-tall cap region to the caps the transcript sponge ACTUALLY absorbed (so removing the pw cap columns in
/// cw=true keeps inner-auth non-vacuous, and closes the pre-existing FS⟂auth cap decoupling). This proves that
/// binding through the W1 lookup prover on the REAL join-split absorb stream. ONE LogUp channel keyed by the
/// enumeration index `gi` (0..n_cap_felts, the [`crate::recursion::monolith::tests::sim_cap_positions`] order):
///  - SPONGE rows carry the real sponge block-input rate lanes `[0..RATE)`; for each lane `l` a witnessed
///    `(gi_l, sel_l)` PROVIDES `(gi_l, lane_l)` with mult `−sel_l` — the ordered PER-LANE provide (up to RATE per
///    row; the trace cap's straddle means one row's lanes can belong to different cap entries, so tags are
///    per-lane, not per-row).
///  - REGION rows are the narrow-tall cap entries flattened one felt/row: `(gi, val)` READS `(gi, val)` mult
///    `+is_region`, `val` sourced from the COMMITTED cap (`roots()[entry][k]`).
/// Balance on `(gi, value)` ⇒ every committed region felt == the FS-absorbed felt at its stream position: the
/// FS-anchor. Degree ~2, width `3·RATE + 3` (constant). Tags are WITNESSED here (a MECHANISM brick — the
/// assembly PINS them to periodic, the FT_BIND pattern, so the prover can't shuffle the order);
/// `cap_absorb_stream_matches_committed_caps` already validated the `(block,lane)→(cap_id,entry,k)` map
/// bit-for-bit, so this isolates that the LogUp binding COMPOSES + PROVES.
pub struct SpongeCapBusAir;

/// Rate = the sponge absorbs `RATE` felts/block; each cap ENTRY is a `DIGEST`(4)-felt run, so `RATE == DIGEST`.
const SCB_RATE: usize = 4;
/// Column layout: `[lane_0..RATE, gi_0..RATE, sel_0..RATE, rgi, rval, is_region]`.
const SCB_WIDTH: usize = 3 * SCB_RATE + 3;

impl<F: p3_field::Field> BaseAir<F> for SpongeCapBusAir {
    fn width(&self) -> usize {
        SCB_WIDTH
    }
}

impl<AB: AirBuilder<F = Val> + InteractionBuilder> Air<AB> for SpongeCapBusAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let is_region = cur[3 * SCB_RATE + 2].clone();
        builder.assert_zero(is_region.clone() * (is_region.clone() - one.clone())); // boolean
        let mut tuples: Vec<(Vec<AB::Expr>, AB::Expr)> = Vec::with_capacity(SCB_RATE + 1);
        // SPONGE side: per lane, PROVIDE (gi_l, lane_l) with mult −sel_l (sel_l boolean).
        for l in 0..SCB_RATE {
            let sel = cur[2 * SCB_RATE + l].clone();
            builder.assert_zero(sel.clone() * (sel.clone() - one.clone())); // boolean
            tuples.push((vec![cur[SCB_RATE + l].clone(), cur[l].clone()], AB::Expr::ZERO - sel));
        }
        // REGION side: READ (rgi, rval) with mult +is_region.
        tuples.push((vec![cur[3 * SCB_RATE].clone(), cur[3 * SCB_RATE + 1].clone()], is_region));
        builder.push_local_interaction(tuples);
    }
}

/// Build the ordered sponge-cap bus trace from a REAL absorb stream: SPONGE rows (one per distinct sponge block
/// that holds ≥1 cap felt — rate lanes from `block_inputs[block]`, per-lane `gi`/`sel` marking the absorbed cap
/// felts) followed by REGION rows (one per cap felt, `(gi = its index, committed[gi])`). `positions` and
/// `committed` are index-aligned (`positions[gi]` ↔ `committed[gi]` = that felt's committed cap value). Padded
/// (mult 0) to a power-of-two height.
pub fn sponge_cap_bus_trace(
    block_inputs: &[[Val; crate::poseidon2_air::W]],
    positions: &[(usize, usize, usize, usize, usize)], // (cap_id, entry, k, block, lane)
    committed: &[Val],
) -> RowMajorMatrix<Val> {
    assert_eq!(positions.len(), committed.len(), "positions and committed values must be index-aligned");
    use std::collections::BTreeMap;
    // block → per-lane (present, gi).
    let mut by_block: BTreeMap<usize, [(bool, usize); SCB_RATE]> = BTreeMap::new();
    for (gi, &(_c, _e, _k, block, lane)) in positions.iter().enumerate() {
        assert!(lane < SCB_RATE, "cap felt must land in a rate lane");
        by_block.entry(block).or_insert([(false, 0); SCB_RATE])[lane] = (true, gi);
    }
    let mut rows: Vec<[Val; SCB_WIDTH]> = Vec::new();
    for (&block, lanes) in &by_block {
        let mut row = [Val::ZERO; SCB_WIDTH];
        for (l, &(present, gi)) in lanes.iter().enumerate() {
            row[l] = block_inputs[block][l]; // the actual FS-absorbed rate lane
            if present {
                row[SCB_RATE + l] = Val::from_u64(gi as u64);
                row[2 * SCB_RATE + l] = Val::ONE; // sel
            }
        }
        rows.push(row);
    }
    for (gi, &val) in committed.iter().enumerate() {
        let mut row = [Val::ZERO; SCB_WIDTH];
        row[3 * SCB_RATE] = Val::from_u64(gi as u64); // rgi
        row[3 * SCB_RATE + 1] = val; // rval = committed cap felt
        row[3 * SCB_RATE + 2] = Val::ONE; // is_region
        rows.push(row);
    }
    rows.resize(rows.len().next_power_of_two(), [Val::ZERO; SCB_WIDTH]);
    RowMajorMatrix::new(rows.into_iter().flatten().collect(), SCB_WIDTH)
}

/// **W2-C (size)** — the size-efficient form of C: evaluate a product DOWN THE ROWS as a running product
/// (constant width) instead of across `2·degree − 1` columns (`DagFoldAir` witnessed). Boundary `prod = x` on
/// the first row; transition `prod' = prod · x'` (degree 2). Width 3 (`[x, prod, mult]`, constant regardless of
/// the product length — height carries the length), so a degree-`d` constraint costs `d` ROWS not `2d` columns
/// ("never re-evaluate the tree" as a running eval). Carries a trivially-balanced range-check lookup so it
/// proves + verifies through the W1 lookup prover — which also **exercises the prover's transition support**
/// (every earlier lookup AIR is local-only; the wrap's real inner has transition constraints).
pub struct ChainEvalAir;

impl<F: p3_field::Field> BaseAir<F> for ChainEvalAir {
    fn width(&self) -> usize {
        3
    }
}

impl<AB: AirBuilder<F = Val> + InteractionBuilder> Air<AB> for ChainEvalAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur = main.current_slice().to_vec();
        let nxt = main.next_slice().to_vec();
        let (x, prod, mult) = (cur[0], cur[1], cur[2]);
        builder.when_first_row().assert_zero(prod.into() - x.into()); // boundary: prod = x
        builder.when_transition().assert_zero(nxt[1].into() - prod.into() * nxt[0].into()); // prod' = prod·x'
        // A trivially-balanced (query x, provide x) range-check lookup to commit a terminal.
        builder.push_local_interaction(vec![
            (vec![x.into()], AB::Expr::ONE),
            (vec![x.into()], -(mult.into())),
        ]);
    }
}

/// A valid running-product trace: `x = 1` everywhere ⇒ `prod = 1`; `mult = 1` (the lookup self-cancels).
pub fn chain_eval_trace(height: usize) -> RowMajorMatrix<Val> {
    let mut flat = Vec::with_capacity(height * 3);
    for _ in 0..height {
        flat.push(Val::ONE); // x
        flat.push(Val::ONE); // prod (running product of 1s)
        flat.push(Val::ONE); // mult
    }
    RowMajorMatrix::new(flat, 3)
}

/// **Arith-tile narrow-tall (the W5 fixed-point's biggest remaining lever).** After W3 the wrap's dominant
/// inner-scaling term is the super-tile ARITH TILE — the DEEP reduced-opening fold
/// `ro = Σ_k α^k·(pz_k − px_k)/(z_k − x)` — which lays its `n_terms` terms in COLUMNS (`9·n_terms` cols, ≈ 62%
/// of `fused_w`, so B ≈ 42; `recursion/monolith/air.rs:1283-1296`). `DeepFoldAir` models it NARROW-TALL: each
/// term is a ROW, with the running product `α^k` and running sum `ro` carried DOWN the rows (transitions), at
/// CONSTANT width — the SAME columns→rows contraction the op-table did for `c_k`, now for the reduced-opening
/// fold. Feasibility brick (like [`DagFoldAir`]); the full arith-tile swap + its opening binding (reusing the
/// `OpTableF2Air` + 2c machinery, since `pz`/`px` are the same committed openings) is the next big effort.
///
/// Columns (F_p², 2 felts each, 18 total): `[α, x, apow, z, pz, px, inv, t, ro]`. Per row (term k):
/// `apow' = apow·α`; `inv·(z − x) = 1`; `t = apow·(pz − px)·inv`; `ro' = ro + t'`. Boundary `apow = 1`, `ro = t`.
pub struct DeepFoldAir;

impl<F: p3_field::Field> BaseAir<F> for DeepFoldAir {
    fn width(&self) -> usize {
        18 // constant, INDEPENDENT of n_terms (vs the monolith's 9·n_terms columns)
    }
}

impl<AB: AirBuilder<F = Val>> Air<AB> for DeepFoldAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let we = AB::Expr::from(Val::from_u64(7)); // F_p² : X² = 7
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (a.0.clone() * b.0.clone() + we.clone() * a.1.clone() * b.1.clone(), a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone())
        };
        let gg = |r: &[AB::Expr], o: usize| (r[o].clone(), r[o + 1].clone());
        let (alpha, x) = (gg(&cur, 0), gg(&cur, 2));
        let (apow, z, pz, px, inv, t, ro) =
            (gg(&cur, 4), gg(&cur, 6), gg(&cur, 8), gg(&cur, 10), gg(&cur, 12), gg(&cur, 14), gg(&cur, 16));
        let one = AB::Expr::ONE;

        // α and x are constant across the fold (same FRI batch challenge + query point).
        for i in 0..4 {
            builder.when_transition().assert_zero(nxt[i].clone() - cur[i].clone());
        }
        // apow = α^k (running product), boundary α^0 = 1.
        builder.when_first_row().assert_zero(apow.0.clone() - one.clone());
        builder.when_first_row().assert_zero(apow.1.clone());
        let ap = emul(apow.clone(), alpha);
        builder.when_transition().assert_zero(gg(&nxt, 4).0 - ap.0);
        builder.when_transition().assert_zero(gg(&nxt, 4).1 - ap.1);
        // inv = 1/(z − x): inv·(z − x) == 1.
        let chk = emul(inv.clone(), (z.0 - x.0, z.1 - x.1));
        builder.assert_zero(chk.0 - one);
        builder.assert_zero(chk.1);
        // t = apow · (pz − px) · inv (the term's DEEP contribution).
        let tv = emul(emul(apow, (pz.0 - px.0, pz.1 - px.1)), inv);
        builder.assert_zero(t.0.clone() - tv.0);
        builder.assert_zero(t.1.clone() - tv.1);
        // ro = running sum of t; boundary ro_0 = t_0; transition ro' = ro + t'.
        builder.when_first_row().assert_zero(ro.0.clone() - t.0.clone());
        builder.when_first_row().assert_zero(ro.1.clone() - t.1.clone());
        builder.when_transition().assert_zero(gg(&nxt, 16).0 - (ro.0.clone() + gg(&nxt, 14).0));
        builder.when_transition().assert_zero(gg(&nxt, 16).1 - (ro.1 + gg(&nxt, 14).1));
    }
}

/// A valid [`DeepFoldAir`] trace over explicit `(z, pz, px)` terms with `α`, `x` fixed — the general seed that
/// grounds the narrow-tall fold in a REAL inner's openings (the monolith arith tile at `air.rs:1278-1296`).
/// `inv = 1/(z − x)`, `t = α^k·(pz − px)·inv`, `ro` the running sum. Rows past `terms.len()` are synthetic
/// padding whose `z` carries a nonzero imaginary part (so `z − x` is invertible for ANY base-field `x`); every
/// row — real or pad — satisfies the AIR, and `ro` at row `k` is `Σ_{j≤k} t_j` (so row `terms.len()−1` holds
/// the full reduced opening, matching the monolith's committed `QT_E`).
pub fn deep_fold_trace_from(
    alpha: crate::config::Challenge,
    x: crate::config::Challenge,
    terms: &[(crate::config::Challenge, crate::config::Challenge, crate::config::Challenge)],
    min_rows: usize,
) -> RowMajorMatrix<Val> {
    use crate::config::Challenge;
    use p3_field::{BasedVectorSpace, Field};
    let cc = |v: Challenge| -> [Val; 2] { v.as_basis_coefficients_slice().try_into().unwrap() };
    let h = terms.len().max(min_rows).max(1).next_power_of_two().max(1 << 4);
    let mut flat = vec![Val::ZERO; h * 18];
    let (mut apow, mut ro) = (Challenge::ONE, Challenge::ZERO);
    for k in 0..h {
        let (z, pz, px) = terms.get(k).copied().unwrap_or_else(|| {
            // padding: z has imaginary 1 ⇒ z − x invertible for any base-field x; pz/px arbitrary.
            (
                Challenge::from_basis_coefficients_fn(|i| Val::from_u64(if i == 0 { 100 + k as u64 } else { 1 })),
                Challenge::ZERO,
                Challenge::ZERO,
            )
        });
        let inv = (z - x).inverse();
        let t = apow * (pz - px) * inv;
        ro += t;
        let b = k * 18;
        for (o, v) in [(0, alpha), (2, x), (4, apow), (6, z), (8, pz), (10, px), (12, inv), (14, t), (16, ro)] {
            flat[b + o..b + o + 2].copy_from_slice(&cc(v));
        }
        apow *= alpha;
    }
    RowMajorMatrix::new(flat, 18)
}

/// A valid [`DeepFoldAir`] trace of `n_terms` synthetic terms (padded) — the self-contained seed for the
/// standalone prove test. Delegates to [`deep_fold_trace_from`] with `α`, `x` and per-term `z/pz/px` chosen so
/// every `z − x` is invertible (`z` base-field, `x` imaginary 7 ⇒ `z − x` imaginary −7 ≠ 0).
pub fn deep_fold_trace(n_terms: usize) -> RowMajorMatrix<Val> {
    use crate::config::Challenge;
    use p3_field::BasedVectorSpace;
    let alpha = Challenge::from_basis_coefficients_fn(|k| Val::from_u64(if k == 0 { 3 } else { 2 }));
    let x = Challenge::from_basis_coefficients_fn(|k| Val::from_u64(if k == 0 { 5 } else { 7 }));
    let terms: Vec<(Challenge, Challenge, Challenge)> = (0..n_terms)
        .map(|k| {
            (
                Challenge::from(Val::from_u64(100 + k as u64 * 13)),
                Challenge::from(Val::from_u64(200 + k as u64 * 7)),
                Challenge::from(Val::from_u64(50 + k as u64 * 11)),
            )
        })
        .collect();
    deep_fold_trace_from(alpha, x, &terms, 0)
}

/// **W3 (size) — the FLATTEN op-table: a narrow-tall arithmetic-circuit evaluator with a LogUp wiring bus.**
/// The W2 witnessed epilogue pays `2·n_mul` dedicated COLUMNS (each F_p² `Mul` → a degree-1 column pair,
/// filled only at the `n_queries` arith heads, wasted on every other row). W3 replaces them with this
/// op-table: each DAG operation (mul / add / sub) is ONE trace ROW at CONSTANT width, and its two operands are
/// routed from their producing rows *by address* through a single LogUp "wiring bus" `(addr, value)`. Leaves
/// (opening values) are seeded as provide-only bus entries; each producer defines its wire with multiplicity
/// `−fanout`, each consumer reads `+1`, so the multiset balances iff every operand read equals the value its
/// producer wrote at that address — the standard offline-memory / permutation argument. `joinsplit_epilogue_
/// dag_shape` chose this FLATTEN form (fan-in exactly 2 per row) over a one-row-per-`Mul` hybrid (operands
/// fan-in ≤ 15). The DAG size becomes ROWS (cheap slack) instead of the witnessed COLUMNS.
///
/// Columns (width 10, scalar `Val`): `[is_mul, is_add, is_sub, out_addr, out_val, a_addr, a_val, b_addr, b_val,
/// out_mult]`. A row is either a leaf-seed (`is_*` all 0, defines `(out_addr, out_val)`) or an op (`out_val =
/// a_val ∘ b_val`, defines its output AND reads both operands). Degree 3 (`is_mul·a·b`); the bus is degree ≤ 3.
/// **Brick 1 validates the WIRING mechanism over scalar `Val`** — the F_p² lift (2-felt values + `emul`), the
/// real-ζ-opening leaf seed, and the fold/output-check integration are the later W3 bricks; the novel/risky
/// part here is the DAG operand routing (the F_p² `emul` is already proven by the W2 `Witnesser`).
pub struct OpTableAir;

impl<F: p3_field::Field> BaseAir<F> for OpTableAir {
    fn width(&self) -> usize {
        10
    }
}

impl<AB: AirBuilder<F = Val> + InteractionBuilder> Air<AB> for OpTableAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let r = main.current_slice().to_vec();
        let (is_mul, is_add, is_sub) = (r[0], r[1], r[2]);
        let (out_addr, out_val) = (r[3], r[4]);
        let (a_addr, a_val) = (r[5], r[6]);
        let (b_addr, b_val) = (r[7], r[8]);
        let out_mult = r[9];

        // Each opcode selector is boolean, and at most one fires (their sum `is_op` is boolean too) — so `is_op`
        // is exactly the operand-read count: 0 on leaf/pad rows, 1 on op rows.
        for s in [is_mul, is_add, is_sub] {
            builder.assert_zero(s.into() * (s.into() - AB::Expr::ONE));
        }
        let is_op: AB::Expr = is_mul.into() + is_add.into() + is_sub.into();
        builder.assert_zero(is_op.clone() * (is_op.clone() - AB::Expr::ONE));

        // The gated op relation: out = a·b (mul) / a+b (add) / a−b (sub). Leaf/pad rows (all selectors 0) leave
        // `out_val` unconstrained here — a leaf's value is an input, bound only by the bus (not computed).
        builder.assert_zero(is_mul.into() * (out_val.into() - a_val.into() * b_val.into()));
        builder.assert_zero(is_add.into() * (out_val.into() - (a_val.into() + b_val.into())));
        builder.assert_zero(is_sub.into() * (out_val.into() - (a_val.into() - b_val.into())));

        // The wiring bus (one LogUp channel): DEFINE this row's output `(out_addr, out_val)` with signed
        // multiplicity `out_mult` (= −fanout for a producer, 0 for pad), and READ both operands with `+is_op`
        // (leaf/pad rows read nothing). Balance ⇒ every read value equals the value its producer wrote there.
        builder.push_local_interaction(vec![
            (vec![a_addr.into(), a_val.into()], is_op.clone()),
            (vec![b_addr.into(), b_val.into()], is_op.clone()),
            (vec![out_addr.into(), out_val.into()], out_mult.into()),
        ]);
    }
}

/// Build an [`OpTableAir`] trace evaluating a constraint DAG (structure from `get_symbolic_constraints`). Each
/// unique node (Arc identity) becomes one wire: leaves get a deterministic pseudo-value (constants keep their
/// actual value), ops compute `out = a ∘ b` over `Val`. Emits a leaf-seed row per leaf and an op row per
/// operation in definition order, sets each producer's `out_mult = −fanout` (fanout = how many operand-reads
/// reference it), and pads to a power-of-two height (pad rows contribute nothing: all selectors 0, `out_mult`
/// 0). The 81 owned constraint ROOTS are processed directly; sub-expression sharing lives in their Arc
/// children (deduped by the memo, matching the `joinsplit_epilogue_dag_shape` census).
pub fn op_table_trace(constraints: &[p3_air::symbolic::SymbolicExpression<Val>]) -> RowMajorMatrix<Val> {
    use p3_air::symbolic::SymbolicExpr;
    use p3_uni_stark::BaseLeaf;
    use std::collections::HashMap;
    use std::sync::Arc;

    #[derive(Clone, Copy)]
    struct Row {
        op: u8, // 0 = leaf, 1 = mul, 2 = add, 3 = sub
        out_addr: u64,
        out_val: Val,
        a_addr: u64,
        a_val: Val,
        b_addr: u64,
        b_val: Val,
    }
    struct B {
        rows: Vec<Row>,
        memo: HashMap<usize, (u64, Val)>,
        next: u64,
        ctr: u64,
        zero: Option<(u64, Val)>,
    }
    impl B {
        fn pseudo(&mut self) -> Val {
            self.ctr += 1;
            Val::from_u64(0x9E37_79B9_7F4A_7C15u64.wrapping_mul(self.ctr))
        }
        fn leaf(&mut self, val: Val) -> (u64, Val) {
            let addr = self.next;
            self.next += 1;
            self.rows.push(Row { op: 0, out_addr: addr, out_val: val, a_addr: 0, a_val: Val::ZERO, b_addr: 0, b_val: Val::ZERO });
            (addr, val)
        }
        fn emit(&mut self, op: u8, a: (u64, Val), b: (u64, Val)) -> (u64, Val) {
            let val = match op {
                1 => a.1 * b.1,
                2 => a.1 + b.1,
                3 => a.1 - b.1,
                _ => unreachable!("op ∈ {{mul, add, sub}}"),
            };
            let addr = self.next;
            self.next += 1;
            self.rows.push(Row { op, out_addr: addr, out_val: val, a_addr: a.0, a_val: a.1, b_addr: b.0, b_val: b.1 });
            (addr, val)
        }
        fn zero_wire(&mut self) -> (u64, Val) {
            match self.zero {
                Some(z) => z,
                None => {
                    let z = self.leaf(Val::ZERO);
                    self.zero = Some(z);
                    z
                }
            }
        }
    }
    fn go_arc(arc: &Arc<p3_air::symbolic::SymbolicExpression<Val>>, b: &mut B) -> (u64, Val) {
        let k = Arc::as_ptr(arc) as usize;
        if let Some(v) = b.memo.get(&k) {
            return *v;
        }
        let v = go(arc.as_ref(), b);
        b.memo.insert(k, v);
        v
    }
    fn go(node: &p3_air::symbolic::SymbolicExpression<Val>, b: &mut B) -> (u64, Val) {
        match node {
            SymbolicExpr::Leaf(l) => {
                let v = match l {
                    BaseLeaf::Constant(c) => *c,
                    _ => b.pseudo(), // Variable / is_first / is_last / is_trans — an opening value (pseudo here)
                };
                b.leaf(v)
            }
            SymbolicExpr::Add { x, y, .. } => {
                let (a, c) = (go_arc(x, b), go_arc(y, b));
                b.emit(2, a, c)
            }
            SymbolicExpr::Sub { x, y, .. } => {
                let (a, c) = (go_arc(x, b), go_arc(y, b));
                b.emit(3, a, c)
            }
            SymbolicExpr::Mul { x, y, .. } => {
                let (a, c) = (go_arc(x, b), go_arc(y, b));
                b.emit(1, a, c)
            }
            SymbolicExpr::Neg { x, .. } => {
                let z = b.zero_wire(); // 0 − x (0 negs in join-split; keeps the builder total for any DAG)
                let a = go_arc(x, b);
                b.emit(3, z, a)
            }
        }
    }

    let mut b = B { rows: Vec::new(), memo: HashMap::new(), next: 0, ctr: 0, zero: None };
    for root in constraints {
        let _ = go(root, &mut b); // the root's wire (fanout 0 in brick 1 — read by the fold in a later brick)
    }

    // Fanout: how many operand-reads reference each address (only op rows read). Each producer's `out_mult` is
    // −fanout, so the bus balances (def −fanout, read +1 × fanout).
    let mut fanout: HashMap<u64, u64> = HashMap::new();
    for row in &b.rows {
        if row.op != 0 {
            *fanout.entry(row.a_addr).or_default() += 1;
            *fanout.entry(row.b_addr).or_default() += 1;
        }
    }

    let w = 10;
    let h = b.rows.len().next_power_of_two().max(1 << 4);
    let mut flat = vec![Val::ZERO; h * w];
    for (i, row) in b.rows.iter().enumerate() {
        let base = i * w;
        let one_if = |c: bool| if c { Val::ONE } else { Val::ZERO };
        flat[base] = one_if(row.op == 1);
        flat[base + 1] = one_if(row.op == 2);
        flat[base + 2] = one_if(row.op == 3);
        flat[base + 3] = Val::from_u64(row.out_addr);
        flat[base + 4] = row.out_val;
        flat[base + 5] = Val::from_u64(row.a_addr);
        flat[base + 6] = row.a_val;
        flat[base + 7] = Val::from_u64(row.b_addr);
        flat[base + 8] = row.b_val;
        flat[base + 9] = -Val::from_u64(*fanout.get(&row.out_addr).unwrap_or(&0));
    }
    RowMajorMatrix::new(flat, w)
}

/// **W3 op-table brick 2 — the F_p² lift.** The real epilogue evaluates each `c_k` over F_p² (the OOD point ζ
/// and every opening live in the degree-2 extension), so the faithful op-table carries **2-felt** values and
/// multiplies via `emul` (`X² = 7`, the monolith's `MRO_W_EXT`) instead of scalar `Val`. Same FLATTEN shape as
/// [`OpTableAir`] (one op per row, operands routed by a LogUp wiring bus), but the bus tuple is `(addr, v0,
/// v1)` and the `mul` relation is the two-component `emul`. Native `Challenge` multiplication equals `emul(7)`
/// (this is what the W2 `Witnesser`'s native mirror relies on), so a `Challenge`-valued trace satisfies the
/// AIR by construction.
///
/// Columns (width 13): `[is_mul, is_add, is_sub, out_addr, out0, out1, a_addr, a0, a1, b_addr, b0, b1,
/// out_mult]`. Degree 3 (`is_mul · a0 · b0`). The leaf-seed is a closure, so the SAME builder serves both the
/// pseudo-value validation here and the real-ζ-opening seed (brick 3) — only the closure changes.
pub struct OpTableF2Air;

impl<F: p3_field::Field> BaseAir<F> for OpTableF2Air {
    fn width(&self) -> usize {
        13
    }
}

impl<AB: AirBuilder<F = Val> + InteractionBuilder> Air<AB> for OpTableF2Air {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let r = main.current_slice().to_vec();
        let (is_mul, is_add, is_sub) = (r[0], r[1], r[2]);
        let (out_addr, o0, o1) = (r[3], r[4], r[5]);
        let (a_addr, a0, a1) = (r[6], r[7], r[8]);
        let (b_addr, b0, b1) = (r[9], r[10], r[11]);
        let out_mult = r[12];
        let w = AB::Expr::from(Val::from_u64(7)); // F_p² : X² = 7 (= MRO_W_EXT)

        for s in [is_mul, is_add, is_sub] {
            builder.assert_zero(s.into() * (s.into() - AB::Expr::ONE));
        }
        let is_op: AB::Expr = is_mul.into() + is_add.into() + is_sub.into();
        builder.assert_zero(is_op.clone() * (is_op.clone() - AB::Expr::ONE));

        // The gated op relation over F_p²: mul = emul (X²=7), add/sub componentwise.
        builder.assert_zero(is_mul.into() * (o0.into() - (a0.into() * b0.into() + w * a1.into() * b1.into())));
        builder.assert_zero(is_mul.into() * (o1.into() - (a0.into() * b1.into() + a1.into() * b0.into())));
        builder.assert_zero(is_add.into() * (o0.into() - (a0.into() + b0.into())));
        builder.assert_zero(is_add.into() * (o1.into() - (a1.into() + b1.into())));
        builder.assert_zero(is_sub.into() * (o0.into() - (a0.into() - b0.into())));
        builder.assert_zero(is_sub.into() * (o1.into() - (a1.into() - b1.into())));

        // The wiring bus (one LogUp channel) — the 3-felt tuple `(addr, v0, v1)`.
        builder.push_local_interaction(vec![
            (vec![a_addr.into(), a0.into(), a1.into()], is_op.clone()),
            (vec![b_addr.into(), b0.into(), b1.into()], is_op.clone()),
            (vec![out_addr.into(), o0.into(), o1.into()], out_mult.into()),
        ]);
    }
}

/// Build an [`OpTableF2Air`] trace evaluating a constraint DAG over F_p² (`Challenge`). `leaf_val` supplies
/// each leaf's `Challenge` value (constants keep their actual value; the closure maps Variables/selectors —
/// pseudo values here, real ζ-openings in brick 3). Ops compute `out = a ∘ b` in `Challenge` (native mul =
/// `emul(7)`). Returns the trace and the constraint ROOT values (each the native `c_k` — the hook the fold /
/// faithfulness check reads). Same wiring/fanout/padding as [`op_table_trace`].
/// When `alpha` is `Some`, the builder appends the epilogue's **α-Horner fold (B)** as more op rows — reading
/// the constraint ROOT wires (the `c_k`) and an α leaf: `folded = ((c_0·α + c_1)·α + …)·α + c_{n−1}`, each step
/// a mul + an add. This makes the op-table a COMPLETE B+C epilogue (it computes `folded`, not just the `c_k`),
/// still at constant width and needing no AIR change (the fold is ordinary mul/add rows). The final `folded`
/// value is returned so the caller can check the epilogue identity `folded·inv_van == quot(ζ)` (the arith head
/// does this O(1) check in the eventual integration; the fold itself no longer costs `2·n_mul` columns).
/// `preseed` (for the assembly's soundness binding, 2c) pre-creates a leaf wire for each `(opening_key, value,
/// open_id)` BEFORE the DAG walk, so EVERY opening the arith head will provide on the bus has a leaf that reads
/// it — even openings the DAG doesn't use (they become fanout-0 leaves). The DAG walk then REUSES these
/// (by `opening_key`). The 4th return value maps each such opening-leaf's ROW to its `open_id` (so the assembly
/// can set the `is_leaf`/`open_id` columns). Standalone callers pass `&[]` (no preseed, empty bindings).
/// **Brick 5d.3** — one quotient chunk's recompose inputs: the two sub-openings `d0`/`d1` (values + their opening
/// ids = `trm_quot(i,0/1)`, bound as TRACE leaves to the FS opening-rows) and the weight `zps` (value + its
/// `open_id((7,i))`, a NON-trace leaf off the window). `op_table_f2_trace` appends rows computing
/// `quot(ζ) = Σ_i zps_i·(d0_i + X·d1_i)` (`X·d1 = emul((0,1),d1)`) and returns quot's `(value, wiring addr)`.
#[derive(Clone, Copy)]
pub struct QuotChunk {
    pub d0: crate::config::Challenge,
    pub d0_oid: u64,
    pub d1: crate::config::Challenge,
    pub d1_oid: u64,
    pub zps: crate::config::Challenge,
    pub zps_oid: u64,
}

pub fn op_table_f2_trace(
    constraints: &[p3_air::symbolic::SymbolicExpression<Val>],
    leaf_val: impl FnMut(&p3_uni_stark::BaseLeaf<Val>) -> crate::config::Challenge,
    alpha: Option<crate::config::Challenge>,
    preseed: &[((u8, u64), crate::config::Challenge, u64)],
    quot: Option<&[QuotChunk]>,
) -> (
    RowMajorMatrix<Val>,
    Vec<crate::config::Challenge>,
    Option<(crate::config::Challenge, u64)>,
    Vec<(usize, u64)>,
    Option<(crate::config::Challenge, u64)>,
) {
    use crate::config::Challenge;
    use p3_air::symbolic::SymbolicExpr;
    use p3_field::{BasedVectorSpace, PrimeField64};
    use p3_uni_stark::{BaseEntry, BaseLeaf};
    use std::collections::HashMap;
    use std::sync::Arc;

    // A leaf's OPENING identity — so leaves are deduped by which ζ-opening they are (`(entry, index/value)`),
    // NOT per-Arc. Each distinct opening ⇒ ONE wire (read by the ops), so the assembly's soundness binding can
    // provide each opening on the bus with a CONSTANT multiplicity (see the 2c design). Tags: 0/1 = Main{0/1}
    // (local/next), 2 = Public, 3 = Periodic, 4/5/6 = is_first/last/trans, 7 = Constant (deduped by value).
    fn opening_key(l: &BaseLeaf<Val>) -> (u8, u64) {
        match l {
            BaseLeaf::Variable(v) => match v.entry {
                BaseEntry::Main { offset } => (offset as u8, v.index as u64),
                BaseEntry::Public => (2, v.index as u64),
                BaseEntry::Periodic => (3, v.index as u64),
                BaseEntry::Preprocessed { .. } => panic!("preprocessed columns unsupported"),
            },
            BaseLeaf::IsFirstRow => (4, 0),
            BaseLeaf::IsLastRow => (5, 0),
            BaseLeaf::IsTransition => (6, 0),
            BaseLeaf::Constant(c) => (7, c.as_canonical_u64()),
        }
    }

    #[derive(Clone, Copy)]
    struct Row {
        op: u8, // 0 = leaf, 1 = mul, 2 = add, 3 = sub
        out_addr: u64,
        out: Challenge,
        a_addr: u64,
        a: Challenge,
        b_addr: u64,
        b: Challenge,
    }
    struct B<G> {
        rows: Vec<Row>,
        memo: HashMap<usize, (u64, Challenge)>,
        leaf_memo: HashMap<(u8, u64), (u64, Challenge)>, // dedupe leaves by opening identity
        next: u64,
        zero: Option<(u64, Challenge)>,
        leaf_val: G,
    }
    impl<G: FnMut(&p3_uni_stark::BaseLeaf<Val>) -> Challenge> B<G> {
        fn leaf(&mut self, val: Challenge) -> (u64, Challenge) {
            let addr = self.next;
            self.next += 1;
            self.rows.push(Row { op: 0, out_addr: addr, out: val, a_addr: 0, a: Challenge::ZERO, b_addr: 0, b: Challenge::ZERO });
            (addr, val)
        }
        fn emit(&mut self, op: u8, a: (u64, Challenge), b: (u64, Challenge)) -> (u64, Challenge) {
            let val = match op {
                1 => a.1 * b.1, // native Challenge mul = emul(7)
                2 => a.1 + b.1,
                3 => a.1 - b.1,
                _ => unreachable!("op ∈ {{mul, add, sub}}"),
            };
            let addr = self.next;
            self.next += 1;
            self.rows.push(Row { op, out_addr: addr, out: val, a_addr: a.0, a: a.1, b_addr: b.0, b: b.1 });
            (addr, val)
        }
        fn zero_wire(&mut self) -> (u64, Challenge) {
            match self.zero {
                Some(z) => z,
                None => {
                    let z = self.leaf(Challenge::ZERO);
                    self.zero = Some(z);
                    z
                }
            }
        }
        fn go_arc(&mut self, arc: &Arc<p3_air::symbolic::SymbolicExpression<Val>>) -> (u64, Challenge) {
            let k = Arc::as_ptr(arc) as usize;
            if let Some(v) = self.memo.get(&k) {
                return *v;
            }
            let v = self.go(arc.as_ref());
            self.memo.insert(k, v);
            v
        }
        fn go(&mut self, node: &p3_air::symbolic::SymbolicExpression<Val>) -> (u64, Challenge) {
            match node {
                SymbolicExpr::Leaf(l) => {
                    let key = opening_key(l);
                    if let Some(&wire) = self.leaf_memo.get(&key) {
                        return wire; // same opening (across different Arcs) ⇒ one shared leaf wire
                    }
                    let v = (self.leaf_val)(l);
                    let wire = self.leaf(v);
                    self.leaf_memo.insert(key, wire);
                    wire
                }
                SymbolicExpr::Add { x, y, .. } => {
                    let (a, c) = (self.go_arc(x), self.go_arc(y));
                    self.emit(2, a, c)
                }
                SymbolicExpr::Sub { x, y, .. } => {
                    let (a, c) = (self.go_arc(x), self.go_arc(y));
                    self.emit(3, a, c)
                }
                SymbolicExpr::Mul { x, y, .. } => {
                    let (a, c) = (self.go_arc(x), self.go_arc(y));
                    self.emit(1, a, c)
                }
                SymbolicExpr::Neg { x, .. } => {
                    let z = self.zero_wire();
                    let a = self.go_arc(x);
                    self.emit(3, z, a)
                }
            }
        }
    }

    let mut b = B { rows: Vec::new(), memo: HashMap::new(), leaf_memo: HashMap::new(), next: 0, zero: None, leaf_val };
    // 2c preseed: pre-create an opening-leaf per `(key, value, open_id)` so EVERY opening the arith head provides
    // has a reader (the DAG walk below reuses these via `leaf_memo`; unused openings become fanout-0 leaves).
    let mut leaf_bindings: Vec<(usize, u64)> = Vec::with_capacity(preseed.len());
    for &(key, val, open_id) in preseed {
        let row_index = b.rows.len();
        let wire = b.leaf(val);
        b.leaf_memo.insert(key, wire);
        leaf_bindings.push((row_index, open_id));
    }
    let mut root_wires: Vec<(u64, Challenge)> = Vec::with_capacity(constraints.len());
    for root in constraints {
        root_wires.push(b.go(root));
    }
    let roots: Vec<Challenge> = root_wires.iter().map(|&(_, v)| v).collect();

    // B — the α-Horner fold over the constraint roots (only op rows; reads roots + an α leaf).
    let folded = match alpha {
        Some(alpha) if !root_wires.is_empty() => {
            let a_wire = b.leaf(alpha);
            let mut f = root_wires[0];
            for &rw in &root_wires[1..] {
                let t = b.emit(1, f, a_wire); // t = f · α
                f = b.emit(2, t, rw); // f = t + c_k
            }
            Some((f.1, f.0)) // (folded value, its wiring-bus address)
        }
        _ => None,
    };

    // Brick 5d.3 — the quotient recompose quot(ζ) = Σ_i zps_i·(d0_i + X·d1_i), appended as op rows. X·d1 =
    // emul((0,1), d1) (mul by the F_p² generator). The sub-openings d0/d1 (bound to the FS opening-rows at
    // term_idx = trm_quot(i,j)) + the weights zps (bound to the window) are op-table LEAVES — their opening ids
    // join `leaf_bindings` alongside the preseed leaves, so the assembly marks them is_tr_leaf / op_is_ch.
    let quot_out = match quot {
        Some(chunks) if !chunks.is_empty() => {
            let x_gen = Challenge::from_basis_coefficients_fn(|k| if k == 1 { Val::ONE } else { Val::ZERO }); // (0,1)
            let x_wire = b.leaf(x_gen); // constant leaf (pinned by the epilogue identity, no bus binding)
            let mut acc: Option<(u64, Challenge)> = None;
            for ch in chunks {
                let d0_row = b.rows.len();
                let d0w = b.leaf(ch.d0);
                leaf_bindings.push((d0_row, ch.d0_oid));
                let d1_row = b.rows.len();
                let d1w = b.leaf(ch.d1);
                leaf_bindings.push((d1_row, ch.d1_oid));
                let zps_row = b.rows.len();
                let zpsw = b.leaf(ch.zps);
                leaf_bindings.push((zps_row, ch.zps_oid));
                let xd1 = b.emit(1, x_wire, d1w); // X·d1
                let chunk = b.emit(2, xd1, d0w); // + d0
                let wv = b.emit(1, zpsw, chunk); // zps·chunk
                acc = Some(match acc {
                    None => wv,
                    Some(a) => b.emit(2, a, wv),
                });
            }
            acc.map(|(addr, val)| (val, addr))
        }
        _ => None,
    };

    let mut fanout: HashMap<u64, u64> = HashMap::new();
    for row in &b.rows {
        if row.op != 0 {
            *fanout.entry(row.a_addr).or_default() += 1;
            *fanout.entry(row.b_addr).or_default() += 1;
        }
    }

    let (w, cc) = (13usize, |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() });
    let h = b.rows.len().next_power_of_two().max(1 << 4);
    let mut flat = vec![Val::ZERO; h * w];
    for (i, row) in b.rows.iter().enumerate() {
        let base = i * w;
        let one_if = |c: bool| if c { Val::ONE } else { Val::ZERO };
        flat[base] = one_if(row.op == 1);
        flat[base + 1] = one_if(row.op == 2);
        flat[base + 2] = one_if(row.op == 3);
        flat[base + 3] = Val::from_u64(row.out_addr);
        flat[base + 4..base + 6].copy_from_slice(&cc(row.out));
        flat[base + 6] = Val::from_u64(row.a_addr);
        flat[base + 7..base + 9].copy_from_slice(&cc(row.a));
        flat[base + 9] = Val::from_u64(row.b_addr);
        flat[base + 10..base + 12].copy_from_slice(&cc(row.b));
        flat[base + 12] = -Val::from_u64(*fanout.get(&row.out_addr).unwrap_or(&0));
    }
    (RowMajorMatrix::new(flat, w), roots, folded, leaf_bindings, quot_out)
}

/// A deterministic F_p² pseudo leaf-value closure (constants keep their value; Variables/selectors get
/// distinct non-base `Challenge`s — both coefficients nonzero, so `emul`'s cross terms are exercised).
#[cfg(test)]
fn pseudo_leaf_f2() -> impl FnMut(&p3_uni_stark::BaseLeaf<Val>) -> crate::config::Challenge {
    use crate::config::Challenge;
    use p3_field::BasedVectorSpace;
    use p3_uni_stark::BaseLeaf;
    let mut ctr = 0u64;
    move |l: &BaseLeaf<Val>| match l {
        BaseLeaf::Constant(c) => Challenge::from(*c),
        _ => {
            ctr += 1;
            let m = 0x9E37_79B9_7F4A_7C15u64.wrapping_mul(ctr);
            Challenge::from_basis_coefficients_fn(|k| Val::from_u64(m.wrapping_add(0x1234_5678 * k as u64 + 1)))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{Challenge, LOG_BLOWUP};
    use crate::joinsplit_air::JoinSplitAir;
    use crate::lookup::prover::{combined_constraint_layout, prove_lookup, verify_lookup, LookupVerifyError};
    use crate::poseidon2_air::Poseidon2RowsAir;
    use p3_air::symbolic::{get_symbolic_constraints, SymbolicExpr, SymbolicExpression};
    use p3_lookup::Lookups;
    use std::collections::HashSet;
    use std::sync::Arc;

    /// Count the **unique** Mul nodes reachable from a constraint DAG (memoized by `Arc` identity via `seen`),
    /// i.e. the witnessed intermediate columns the size-efficient C would need WITH sub-expression sharing
    /// ("never re-evaluate the tree"). Add/Sub/Neg don't raise degree, so only Mul nodes are witnessed.
    fn count_mul_nodes(expr: &SymbolicExpression<Val>, seen: &mut HashSet<usize>) -> usize {
        match expr {
            SymbolicExpr::Leaf(_) => 0,
            SymbolicExpr::Neg { x, .. } => count_mul_arc(x, seen),
            SymbolicExpr::Add { x, y, .. } | SymbolicExpr::Sub { x, y, .. } => {
                count_mul_arc(x, seen) + count_mul_arc(y, seen)
            }
            SymbolicExpr::Mul { x, y, .. } => 1 + count_mul_arc(x, seen) + count_mul_arc(y, seen),
        }
    }
    fn count_mul_arc(arc: &Arc<SymbolicExpression<Val>>, seen: &mut HashSet<usize>) -> usize {
        if !seen.insert(Arc::as_ptr(arc) as usize) {
            return 0; // already counted this shared sub-expression
        }
        count_mul_nodes(arc, seen)
    }

    /// The **B degree fix**: with WITNESSED inner-constraint values (degree-1 columns) and the chunked fold,
    /// the α_stark fold stays within the degree-16 / `log_blowup` cliff — even for a realistic 384-constraint
    /// inner (the join-split `MonolithAir` scale).
    #[test]
    fn witnessed_chunked_fold_stays_within_blowup() {
        let air = FoldAir { n_constraints: 384, chunk: 7, c_cols_per_constraint: 1 };
        let log_nqc = fold_log_nqc(&air);
        println!("WITNESSED chunked fold (N=384, chunk=7): log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        assert!(log_nqc <= LOG_BLOWUP, "witnessed + chunked fold must stay ≤ log_blowup (got {log_nqc})");
    }

    /// The explosion source the monolith actually hits: INLINE degree-16 constraint evaluation
    /// (`eval_symbolic_circuit`), even chunked, exceeds the cliff. Witnessing the `c_k` (above) is the fix.
    #[test]
    fn inline_high_degree_fold_exceeds_blowup() {
        let air = FoldAir { n_constraints: 384, chunk: 7, c_cols_per_constraint: 16 };
        let log_nqc = fold_log_nqc(&air);
        println!("INLINE deg-16 chunked fold (N=384, chunk=7): log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        assert!(log_nqc > LOG_BLOWUP, "inline degree-16 fold must exceed log_blowup (got {log_nqc})");
    }

    /// The second lever — chunking. Without it (chunk = N), the α-Horner accumulates α-degree across all N
    /// constraints and explodes even for WITNESSED (degree-1) `c_k`. Both witnessing and chunking are needed.
    #[test]
    fn unchunked_fold_exceeds_blowup() {
        let air = FoldAir { n_constraints: 384, chunk: 384, c_cols_per_constraint: 1 };
        let log_nqc = fold_log_nqc(&air);
        println!("UNCHUNKED witnessed fold (N=384): log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        assert!(log_nqc > LOG_BLOWUP, "an unchunked α-Horner fold explodes even for witnessed c_k (got {log_nqc})");
    }

    /// **W2-C** — the combined epilogue: evaluating each `c_k` via WITNESSED degree-2 steps (C) and folding the
    /// resulting degree-1 `c_k` (B) keeps the FULL fold within the degree-16 / log_blowup cliff, for a
    /// realistic 384-constraint × degree-16 inner.
    #[test]
    fn witnessed_dag_fold_stays_within_blowup() {
        let air = DagFoldAir { n_constraints: 384, chunk: 7, degree: 16, witnessed: true };
        let log_nqc = wrap_log_nqc(&air);
        println!("C+B WITNESSED (N=384, deg=16, chunk=7): log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        assert!(log_nqc <= LOG_BLOWUP, "witnessed c_k evaluation + fold must stay ≤ log_blowup (got {log_nqc})");
    }

    /// The monolith's inline path, for contrast: evaluating each `c_k` as one degree-16 expression and folding
    /// it inline exceeds the cliff. Witnessing the `c_k` (above) is the fix.
    #[test]
    fn inline_dag_fold_exceeds_blowup() {
        let air = DagFoldAir { n_constraints: 384, chunk: 7, degree: 16, witnessed: false };
        let log_nqc = wrap_log_nqc(&air);
        println!("C+B INLINE (N=384, deg=16, chunk=7): log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        assert!(log_nqc > LOG_BLOWUP, "inline degree-16 c_k evaluation + fold must exceed log_blowup (got {log_nqc})");
    }

    /// **W2-I** — the cap-mux, as a lookup, proves + verifies end to end through the W1 lookup prover: queries
    /// selecting the real `cap[index]` balance the multiset.
    #[test]
    fn cap_mux_round_trips() {
        let cap: Vec<Val> = (0..(1u64 << 6)).map(|j| Val::from_u64(0x1000 + j)).collect();
        let queries = vec![3usize, 3, 17, 40, 63, 0];
        let air = CapMuxAir;
        let proof = prove_lookup(&air, cap_mux_trace(&cap, &queries), &[]);
        assert!(verify_lookup(&air, &proof, &[]).is_ok(), "valid cap selections must verify");
    }

    /// A query selecting a WRONG value (≠ `cap[index]`) unbalances the multiset ⇒ non-zero terminal ⇒
    /// rejected — the mux soundness, at degree 3 (the product-mux would need a degree-`cap_height` selector).
    #[test]
    fn cap_mux_rejects_wrong_selection() {
        let cap: Vec<Val> = (0..(1u64 << 6)).map(|j| Val::from_u64(0x1000 + j)).collect();
        let queries = vec![3usize, 17, 40];
        let mut trace = cap_mux_trace(&cap, &queries);
        // The first query row follows the cap.len() table rows; corrupt its value column (col 1).
        let qrow = cap.len();
        trace.values[qrow * 3 + 1] = Val::from_u64(0xDEAD); // index 3 now selects a non-cap value
        let air = CapMuxAir;
        let proof = prove_lookup(&air, trace, &[]);
        assert!(
            matches!(verify_lookup(&air, &proof, &[]), Err(LookupVerifyError::NonZeroTerminal)),
            "a query selecting value ≠ cap[index] must be rejected"
        );
    }

    /// The degree + size win: the cap-mux lookup is **width 3 (constant)** and within the degree budget —
    /// versus the product-mux's `2^cap_height` width and `cap_height` degree.
    #[test]
    fn cap_mux_is_low_degree_and_narrow() {
        let air = CapMuxAir;
        assert_eq!(BaseAir::<Val>::width(&air), 3, "cap-mux width is constant (not 2^cap_height)");
        let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        println!("cap-mux lookup: width = 3, log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        assert!(log_nqc <= LOG_BLOWUP, "cap-mux lookup must be within the degree budget (got {log_nqc})");
    }

    /// **W4 (Tip5 in-circuit) — the split-and-lookup S-box proves + verifies** through the W1 lookup prover: for
    /// a set of field elements, every S-box row's 8 byte-lookups balance against the 256-row `(byte, L(byte))`
    /// table ⇒ each `y = split_and_lookup(x)`. The foundational gadget of the in-circuit Tip5 hash (Step 4).
    #[cfg(feature = "tip5")]
    #[test]
    fn tip5_sbox_lookup_round_trips() {
        let inputs = vec![0u64, 1, 255, 256, 0xDEAD_BEEF, 0x0123_4567_89AB_CDEF, 0xFFFF_FFFF_0000_0000];
        let air = Tip5SboxAir;
        let proof = prove_lookup(&air, tip5_sbox_trace(&inputs), &[]);
        assert!(verify_lookup(&air, &proof, &[]).is_ok(), "valid Tip5 S-box instances must verify");
    }

    /// A corrupted S-box output byte (`oᵢ ≠ L(bᵢ)`, kept recomposition-consistent) reads a `(byte, non-L)` tuple
    /// ABSENT from the table ⇒ the multiset does not balance ⇒ `NonZeroTerminal` — the S-box soundness (the
    /// lookup FORCES `oᵢ = L(bᵢ)`, i.e. the byte map is exactly the real Tip5 offset-Fermat-cube map).
    #[cfg(feature = "tip5")]
    #[test]
    fn tip5_sbox_rejects_wrong_output() {
        let inputs = vec![0xDEAD_BEEFu64, 42, 255];
        let mut trace = tip5_sbox_trace(&inputs);
        let (w, nb) = (Tip5SboxAir::W, Tip5SboxAir::NB);
        // the first sbox row follows the 256 table rows; bump o_0 AND y by the same amount so the recomposition
        // constraint still holds (256⁰·1) but the lookup reads (b_0, L(b_0)+1) — no such table entry.
        let srow = 256;
        trace.values[srow * w + nb] += Val::ONE; // o_0 ≠ L(b_0)
        trace.values[srow * w + 2 * nb + 1] += Val::ONE; // y += 1 (keep y == Σ oᵢ·256ⁱ)
        let air = Tip5SboxAir;
        let proof = prove_lookup(&air, trace, &[]);
        assert!(
            matches!(verify_lookup(&air, &proof, &[]), Err(LookupVerifyError::NonZeroTerminal)),
            "a Tip5 S-box output ≠ L(byte) must be rejected"
        );
    }

    /// **The Tip5 recursion win, PROVEN:** the split-and-lookup S-box is a LOW-DEGREE lookup (`log_nqc ≤` budget)
    /// — validating `cost_estimate`'s "split lanes → ~degree-1 lookups" (vs the x⁷ lanes' degree 7). This is the
    /// whole point of Tip5 for recursion, now an actual measured degree rather than an asserted cost number.
    #[cfg(feature = "tip5")]
    #[test]
    fn tip5_sbox_is_low_degree() {
        let air = Tip5SboxAir;
        let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        println!(
            "Tip5 S-box lookup: width {}, log_nqc {log_nqc} (budget {LOG_BLOWUP}) — the split lanes are a cheap lookup",
            Tip5SboxAir::W
        );
        assert!(log_nqc <= LOG_BLOWUP, "the Tip5 split-and-lookup S-box must be within the degree budget (got {log_nqc})");
    }

    /// **W4 (Tip5 in-circuit) — the round AIR's arithmetic MATCHES the native Tip5 round** (`--features tip5,lookup`,
    /// cheap; NO prove — a NON-circular correctness check). Builds the round trace and confirms each permutation
    /// row's output `so` equals `Tip5::round(s, 0)` (the native S-box layer + MDS + round-0 constants) bit-for-bit —
    /// so the in-circuit round (LogUp split-and-lookup S-box + `x⁷` power lanes + real circulant MDS + real round
    /// constants) computes the EXACT Tip5 round transformation. The composed round is arithmetically correct; the
    /// remaining work is purely its in-circuit COST (see `tip5_round_degree_needs_spreading`).
    #[cfg(feature = "tip5")]
    #[test]
    fn tip5_round_matches_native() {
        use crate::tip5::{Tip5, WIDTH as TW};
        use p3_field::PrimeField64;
        let states: Vec<[u64; 16]> = vec![
            core::array::from_fn(|i| i as u64),
            core::array::from_fn(|i| 0x1234_5678_9ABC_DEF0u64.wrapping_mul(i as u64 + 1)),
            [7u64; 16],
        ];
        let trace = tip5_round_trace(&states);
        let w = Tip5RoundAir::W;
        for (k, st) in states.iter().enumerate() {
            let mut ref_s: [p3_goldilocks::Goldilocks; TW] =
                core::array::from_fn(|i| p3_goldilocks::Goldilocks::from_u64(st[i]));
            Tip5::round(&mut ref_s, 0); // the native single round
            let row = 256 + k; // perm rows follow the 256 table rows
            for i in 0..TW {
                assert_eq!(
                    trace.values[row * w + Tip5RoundAir::SO + i].as_canonical_u64(),
                    ref_s[i].as_canonical_u64(),
                    "state {k} lane {i}: in-circuit round output must equal the native Tip5 round"
                );
            }
        }
        println!(
            "W4 Tip5 round: the in-circuit round (LogUp S-box + x⁷ + circulant MDS + RC₀) matches Tip5::round \
             bit-for-bit on {} states — the composed round arithmetic is correct.",
            states.len()
        );
    }

    /// **W4 (Tip5 in-circuit) — the whole-round-on-one-row exceeds the ≤4 budget ⇒ the full permutation needs
    /// tuple-SPREADING** (`--features tip5,lookup`, cheap). The S-box alone (8 byte-lookups/row) is log_nqc 4
    /// (`tip5_sbox_is_low_degree`, and it PROVES); a full round packs 4 split lanes × 8 bytes = 32 lookups/row,
    /// pushing log_nqc to ~6 — the SAME many-interactions-per-row wall the caps/op-table tracks hit. ⇒ the full
    /// 5-round permutation AIR must SPREAD the S-box lookups across rows (one lane/round per row, state threaded),
    /// exactly the narrow-tall/spread construction those tracks used — a real multi-brick effort, NOT a one-row
    /// extension. (The round ARITHMETIC is already native-exact per `tip5_round_matches_native`; this is the cost.)
    #[cfg(feature = "tip5")]
    #[test]
    fn tip5_round_degree_needs_spreading() {
        let air = Tip5RoundAir;
        let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        assert!(log_nqc > LOG_BLOWUP, "the whole-round-on-one-row exceeds ≤4 (documents the spreading need); got {log_nqc}");
        assert!(log_nqc <= 8, "…and it's the moderate 2c-wall level, not a runaway blow-up (got {log_nqc})");
        // DEFINITIVE: the 32-lookups/row round does NOT verify (the many-tuples-per-row LogUp quotient is
        // mis-sized ⇒ OodMismatch) — whereas the 8-lookups/row S-box PROVES (tip5_sbox_lookup_round_trips). So the
        // full permutation MUST spread the S-box lookups to ≤8/row (the multi-brick narrow-tall construction).
        let proof = prove_lookup(&air, tip5_round_trace(&[core::array::from_fn(|i| (i as u64) * 5 + 1)]), &[]);
        assert!(
            verify_lookup(&air, &proof, &[]).is_err(),
            "the whole-round-on-one-row (32 lookups) must NOT verify — proving the spreading need"
        );
        println!(
            "Tip5 ROUND (32 lookups/row): width {}, log_nqc {log_nqc} > {LOG_BLOWUP}, AND the prove does NOT verify \
             (OodMismatch) ⇒ the full permutation MUST SPREAD the S-box lookups to ≤8/row (the proven S-box level) — \
             a real multi-brick construction, not a one-row extension.",
            Tip5RoundAir::W
        );
    }

    /// **W4 (Tip5 in-circuit) — the SPREAD round COMPOSES at ≤4** (`--features tip5,lookup`, cheap; the feasibility
    /// de-risk the round-on-one-row could NOT reach). By moving each split-lane S-box to its own row (8 byte-lookups/
    /// row = the proven `Tip5SboxAir` level, ch0) and connecting the round arithmetic via one ordered bus (ch1), the
    /// SPREAD round composes at `log_nqc ≤ LOG_BLOWUP` — vs the whole-round-on-one-row's log_nqc 6 (which does not
    /// verify). ⇒ the SPREAD design is degree-FEASIBLE: the full 5-round permutation (threading these rows + the
    /// state chain, the remaining multi-brick assembly) has a provable path. (The caps/openings "compose de-risk
    /// before the full assembly" step, now for the Tip5 permutation.)
    #[cfg(feature = "tip5")]
    #[test]
    fn tip5_spread_round_composes() {
        let air = Tip5SpreadRoundAir;
        let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        println!(
            "Tip5 SPREAD round: width {}, {} channels (byte-table 8/row + s/sb connection), log_nqc {log_nqc} ≤ \
             {LOG_BLOWUP} — spreading the S-box lookups to ≤8/row makes the round degree-FEASIBLE (the one-row form \
             was log_nqc 6 + un-provable). The full permutation threads these rows + the state chain.",
            Tip5SpreadRoundAir::W,
            lookups.len()
        );
        assert_eq!(lookups.len(), 2, "the byte-table + the s/sb connection channels");
        assert!(
            log_nqc <= LOG_BLOWUP,
            "spreading to ≤8 lookups/row must reach log_nqc ≤ {LOG_BLOWUP} (got {log_nqc}) — the round-on-one-row was 6"
        );
    }

    /// **W2-C (size)** — the narrow-tall running eval proves + verifies through the W1 lookup prover, which
    /// also validates the prover's TRANSITION support end to end (every earlier lookup AIR is local-only).
    #[test]
    fn chain_eval_round_trips() {
        let air = ChainEvalAir;
        let proof = prove_lookup(&air, chain_eval_trace(1 << 5), &[]);
        assert!(verify_lookup(&air, &proof, &[]).is_ok(), "a valid running-product trace must verify");
    }

    /// Breaking the running product violates the `prod' = prod·x'` transition ⇒ OOD mismatch — confirming
    /// transition constraints are folded correctly in both the prover's quotient and the ζ-check.
    #[test]
    fn chain_eval_rejects_broken_product() {
        let air = ChainEvalAir;
        let mut trace = chain_eval_trace(1 << 5);
        trace.values[5 * 3 + 1] = Val::from_u64(2); // row 5's prod ≠ prod_4 · x_5
        let proof = prove_lookup(&air, trace, &[]);
        assert!(
            matches!(verify_lookup(&air, &proof, &[]), Err(LookupVerifyError::OodMismatch)),
            "a broken running product must fail the OOD identity"
        );
    }

    /// The size win: the running eval is WIDTH 3 (constant) and within the degree budget — a degree-`d`
    /// constraint costs `d` ROWS, not the wide layout's `2·d` columns.
    #[test]
    fn chain_eval_is_narrow_and_low_degree() {
        let air = ChainEvalAir;
        assert_eq!(BaseAir::<Val>::width(&air), 3, "running-eval width is constant (independent of length)");
        let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(&air);
        let (_layout, log_nqc) = combined_constraint_layout(&air, &lookups, 1);
        println!("ChainEval: width = 3 (wide would be 2·degree), log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        assert!(log_nqc <= LOG_BLOWUP, "narrow-tall running eval must stay within the degree budget (got {log_nqc})");
    }

    /// **Arith-tile narrow-tall feasibility (W5).** The DEEP reduced-opening fold (the wrap's dominant
    /// inner-scaling term post-W3, `9·n_terms` COLUMNS ≈ 62% of `fused_w`) is CONSTANT width 18 as a narrow-tall
    /// `DeepFoldAir` (each term a ROW, `α^k`/`ro` carried down) and stays within the degree budget — so the same
    /// columns→rows contraction the op-table did for `c_k` applies to the arith tile (`9·n_terms` cols → 18).
    #[test]
    fn deep_fold_is_narrow_and_low_degree() {
        let air = DeepFoldAir;
        assert_eq!(BaseAir::<Val>::width(&air), 18, "the DEEP fold is constant width (independent of n_terms)");
        let log_nqc = wrap_log_nqc(&air);
        // A real join-split inner has n_terms = 2·W + 2·nqc = 2·19 + 2·8 = 54 ⇒ the monolith arith tile is
        // 9·54 = 486 COLUMNS; the narrow-tall form is 54 ROWS at constant width 18.
        println!(
            "DeepFoldAir (arith-tile narrow-tall): width 18 (const, vs monolith 9·n_terms), log_nqc = {log_nqc} \
             (budget {LOG_BLOWUP}) — replaces the 486-COLUMN arith tile (join-split n_terms=54) with 54 slack ROWS"
        );
        assert!(log_nqc <= LOG_BLOWUP, "the narrow-tall DEEP fold must stay within the degree budget (got {log_nqc})");
    }

    /// **Arith-tile narrow-tall brick 2 — PROVE the recurrence is correct.** The measure test shows constant
    /// width + low degree; this proves the DEEP-fold *constraints* are right. A synthetic 54-term fold (the real
    /// join-split `n_terms`) proves + verifies through the PRODUCTION prover, and corrupting a single
    /// running-sum cell is rejected (prove can't close the quotient, or verify catches it) — so the narrow-tall
    /// `ro = Σ α^k·(pz − px)/(z − x)` recurrence is sound, ready to swap for the monolith's `9·n_terms` columns.
    #[test]
    fn deep_fold_proves() {
        use crate::config::make_config;
        use p3_uni_stark::{prove, verify};
        let config = make_config();
        let proof = prove(&config, &DeepFoldAir, deep_fold_trace(54), &[]);
        assert!(verify(&config, &DeepFoldAir, &proof, &[]).is_ok(), "the narrow-tall DEEP fold must verify");

        // Corrupt one running-sum (ro.0, row 0) ⇒ the fold recurrence breaks. A broken trace must NOT yield a
        // valid proof: prove either fails to form the quotient (panics in debug) or verify rejects it.
        let mut bad = deep_fold_trace(54);
        bad.values[16] += Val::ONE;
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {})); // a broken-trace prove panic is expected — keep test output clean
        let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let p = prove(&config, &DeepFoldAir, bad, &[]);
            verify(&config, &DeepFoldAir, &p, &[]).is_err()
        }))
        .unwrap_or(true);
        std::panic::set_hook(hook);
        assert!(rejected, "a corrupted DEEP fold must not produce a valid proof");
    }

    /// **The synthetic result, grounded in the REAL inner.** Extract the actual `JoinSplitAir` constraints,
    /// report the real profile, and confirm the OOD epilogue — folding its `N` witnessed (degree-1) `c_k` via
    /// the chunked Horner (B) — stays within the degree-16 / log_blowup cliff, versus the monolith's inline
    /// evaluation at the real max degree.
    #[test]
    fn real_joinsplit_inner_epilogue_within_budget() {
        let layout = AirLayout::from_air::<Val>(&JoinSplitAir);
        let constraints = get_symbolic_constraints::<Val, _>(&JoinSplitAir, layout);
        let n = constraints.len();
        let max_deg = constraints.iter().map(|c| c.degree_multiple()).max().unwrap_or(0);
        let mut seen = HashSet::new();
        let muls: usize = constraints.iter().map(|c| count_mul_nodes(c, &mut seen)).sum();
        println!(
            "REAL JoinSplitAir inner: {n} constraints, max degree {max_deg}, {muls} unique Mul nodes \
             (= witnessed C columns, shared)"
        );

        // The OOD epilogue folds the N witnessed degree-1 c_k via the chunked Horner (B).
        let witnessed = FoldAir { n_constraints: n, chunk: 7, c_cols_per_constraint: 1 };
        let log_nqc = wrap_log_nqc(&witnessed);
        println!("REAL epilogue (witnessed C + fold B): log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        assert!(log_nqc <= LOG_BLOWUP, "the real-inner witnessed epilogue must stay ≤ log_blowup (got {log_nqc})");

        // Contrast: the monolith's inline evaluation folds each c_k at the real max degree (reported, not
        // asserted — the explosion's magnitude depends on the inner's exact max degree).
        let inline = FoldAir { n_constraints: n, chunk: 7, c_cols_per_constraint: max_deg.max(1) };
        println!("REAL epilogue INLINE (monolith, deg {max_deg}): log_nqc = {}", wrap_log_nqc(&inline));
    }

    /// **W3 (size) — profile the epilogue DAG to choose the op-table canonicalization.** The witnessed epilogue
    /// (W2) pays `2·n_mul` COLUMNS (each F_p² `Mul` → a degree-1 column pair, filled only at the `n_queries`
    /// arith heads, wasted on every other row); W3 trades those for narrow-tall op-table ROWS at constant width
    /// (overlaid on slack rows). Two canonical forms are possible, and the REAL DAG shape decides between them:
    /// - **(A) FLATTEN** every op (Add/Sub/Neg/Mul) to its own row, wired by a permutation/LogUp bus — each row
    ///   reads exactly **2** operands by address and writes 1 output, so the width is a small CONSTANT and the
    ///   fan-in is trivially bounded; the cost is `n_ops` rows (all node types, not just `Mul`).
    /// - **(B) HYBRID** — keep the linear folding of Add/Sub/Neg and put one row per `Mul` (`n_mul` rows), but
    ///   then each `Mul` operand is a linear combination of terminals (opening leaves + child-`Mul` outputs)
    ///   needing **bounded bus fan-in** — viable only if the max operand fan-in is small.
    ///
    /// This measures the deciding data on the real inner: the node-type census over the shared DAG (Arc-dedup)
    /// and the per-`Mul` operand linear fan-in (distinct terminals reachable through Add/Sub/Neg without
    /// crossing another `Mul`). Reported, not asserted — it documents the op-table design input (like W2-real's
    /// "81 constraints, 214 Muls"), so the next brick builds the right canonical form.
    #[test]
    fn joinsplit_epilogue_dag_shape() {
        use p3_uni_stark::BaseLeaf;
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));

        // (1) Node-type census over the shared DAG (dedup at Arc boundaries, like `count_mul_nodes`; the 81
        // constraint ROOTS are owned, counted directly — sharing lives in their Arc children).
        #[derive(Default)]
        struct Census {
            leaf_var: usize,  // opening values (Main/Public/Periodic) — bus terminals
            leaf_sel: usize,  // is_first/is_last/is_trans selectors — witnessed at ζ, also terminals
            leaf_const: usize, // pure constants — affine constant term, not a bus read
            add: usize,
            sub: usize,
            neg: usize,
            mul: usize,
        }
        // Collect each unique Mul's operand arcs (for the fan-in pass) alongside the census.
        type Arcs = Vec<(Arc<SymbolicExpression<Val>>, Arc<SymbolicExpression<Val>>)>;
        fn census_node(e: &SymbolicExpression<Val>, seen: &mut HashSet<usize>, c: &mut Census, ops: &mut Arcs) {
            match e {
                SymbolicExpr::Leaf(l) => match l {
                    BaseLeaf::Constant(_) => c.leaf_const += 1,
                    BaseLeaf::Variable(_) => c.leaf_var += 1,
                    _ => c.leaf_sel += 1,
                },
                SymbolicExpr::Add { x, y, .. } => {
                    c.add += 1;
                    census_arc(x, seen, c, ops);
                    census_arc(y, seen, c, ops);
                }
                SymbolicExpr::Sub { x, y, .. } => {
                    c.sub += 1;
                    census_arc(x, seen, c, ops);
                    census_arc(y, seen, c, ops);
                }
                SymbolicExpr::Neg { x, .. } => {
                    c.neg += 1;
                    census_arc(x, seen, c, ops);
                }
                SymbolicExpr::Mul { x, y, .. } => {
                    c.mul += 1;
                    ops.push((x.clone(), y.clone()));
                    census_arc(x, seen, c, ops);
                    census_arc(y, seen, c, ops);
                }
            }
        }
        fn census_arc(arc: &Arc<SymbolicExpression<Val>>, seen: &mut HashSet<usize>, c: &mut Census, ops: &mut Arcs) {
            if seen.insert(Arc::as_ptr(arc) as usize) {
                census_node(arc.as_ref(), seen, c, ops);
            }
        }
        let (mut seen, mut cen, mut mul_ops) = (HashSet::new(), Census::default(), Arcs::new());
        for root in &constraints {
            census_node(root, &mut seen, &mut cen, &mut mul_ops);
        }
        let n_ops = cen.add + cen.sub + cen.neg + cen.mul;
        assert_eq!(cen.mul, mul_ops.len(), "one operand pair recorded per unique Mul node");

        // (2) Per-Mul operand linear fan-in: distinct terminals (non-constant leaf OR child-Mul cut point)
        // reachable through Add/Sub/Neg. This is the bus-read count a HYBRID (one-row-per-Mul) design needs
        // per operand — the number that decides whether B is viable vs. the always-2 FLATTEN form.
        fn terminals(arc: &Arc<SymbolicExpression<Val>>, set: &mut HashSet<usize>) {
            match arc.as_ref() {
                SymbolicExpr::Leaf(BaseLeaf::Constant(_)) => {} // constant term, not a bus read
                SymbolicExpr::Leaf(_) | SymbolicExpr::Mul { .. } => {
                    set.insert(Arc::as_ptr(arc) as usize); // opening terminal / Mul cut point
                }
                SymbolicExpr::Neg { x, .. } => terminals(x, set),
                SymbolicExpr::Add { x, y, .. } | SymbolicExpr::Sub { x, y, .. } => {
                    terminals(x, set);
                    terminals(y, set);
                }
            }
        }
        let mut fanins: Vec<usize> = Vec::with_capacity(2 * mul_ops.len());
        for (x, y) in &mul_ops {
            for operand in [x, y] {
                let mut set = HashSet::new();
                terminals(operand, &mut set);
                fanins.push(set.len());
            }
        }
        let max_fanin = fanins.iter().copied().max().unwrap_or(0);
        let sum_fanin: usize = fanins.iter().sum();
        let mean_fanin = sum_fanin as f64 / fanins.len().max(1) as f64;
        // Histogram over the fan-in buckets that matter for a fixed-width hybrid row.
        let buckets = [(1usize, 2usize), (3, 4), (5, 8), (9, 16), (17, usize::MAX)];
        let hist: Vec<(String, usize)> = buckets
            .iter()
            .map(|&(lo, hi)| {
                let label = if hi == usize::MAX { format!("{lo}+") } else { format!("{lo}-{hi}") };
                (label, fanins.iter().filter(|&&f| f >= lo && f <= hi).count())
            })
            .collect();

        println!(
            "W3 DAG shape (real JoinSplitAir epilogue): {} constraints ⇒ unique nodes: {} leaf-var (openings), \
             {} leaf-sel, {} const, {} add, {} sub, {} neg, {} MUL",
            constraints.len(), cen.leaf_var, cen.leaf_sel, cen.leaf_const, cen.add, cen.sub, cen.neg, cen.mul,
        );
        println!(
            "  op count n_ops = {n_ops} (add+sub+neg+mul); Mul operand fan-in: max {max_fanin}, mean {mean_fanin:.2}, \
             histogram {hist:?}",
        );
        // The size trade-off the number decides. Witnessed (W2) = 2·n_mul dedicated COLUMNS (all rows).
        // FLATTEN op-table = a small const width W_op over n_ops slack ROWS (fan-in exactly 2). HYBRID =
        // const width over n_mul ROWS but only if max_fanin is small enough to bound the per-row bus reads.
        println!(
            "  ⇒ witnessed W2 = {} COLUMNS; FLATTEN op-table = const-width × {n_ops} ROWS (fan-in 2); \
             HYBRID = const-width × {} ROWS (needs fan-in ≤ K, max here {max_fanin})",
            2 * cen.mul, cen.mul,
        );
    }

    /// **Wrap degree-budget rollup (W2-super).** `log_nqc` composes as the MAX over regions (it is monotonic
    /// in the max constraint degree), so the whole wrap's budget is the max of its regions' log_nqc. Roll up
    /// the real regions and confirm they compose within budget: the OOD epilogue (B, over the real inner's 81
    /// witnessed c_k), the real Poseidon2 hash rows (A), the cap-mux (I), and the narrow-tall C eval — plus,
    /// under `--features recursion`, the reused super-tile verifier tiles D (FRI β-fold), E (Merkle-opening +
    /// SUM-form not_term), F (transcript sponge). This turns the plan's "every other gadget is already ≤16"
    /// premise into a measurement. (G/H/J — DEEP α_fri / OOD selectors / tx-root fold — are `monolith/air.rs`
    /// regions, measured when the wrap AIR is assembled, W2-assemble.)
    #[test]
    fn wrap_degree_budget_rollup() {
        let n_inner =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir)).len();
        let l_epilogue = wrap_log_nqc(&FoldAir { n_constraints: n_inner, chunk: 7, c_cols_per_constraint: 1 });
        let l_hash = wrap_log_nqc(&Poseidon2RowsAir);
        let l_capmux =
            combined_constraint_layout(&CapMuxAir, &Lookups::from_air::<Challenge, _>(&CapMuxAir), 1).1;
        let l_chain =
            combined_constraint_layout(&ChainEvalAir, &Lookups::from_air::<Challenge, _>(&ChainEvalAir), 1).1;

        // Accessible without `--features recursion`: the OOD epilogue fold (B) over the real inner, the real
        // Poseidon2 hash rows (A), the cap-mux lookup (I), the narrow-tall C eval.
        let base = [
            ("epilogue(B)", l_epilogue),
            ("hash(Poseidon2,A)", l_hash),
            ("cap-mux(I)", l_capmux),
            ("chain-eval(C)", l_chain),
        ];

        // W2-super — the reused super-tile verifier tiles (standalone AIRs faithful to the monolith's fused
        // fold/Merkle/transcript regions). D (FRI β-fold) is F_p² arithmetic; E (Merkle-opening) and F
        // (transcript sponge) reuse the degree-7 Poseidon2 S-box. Each must land within the budget.
        #[cfg(feature = "recursion")]
        let extra: Vec<(&str, usize)> = {
            use crate::recursion::fri_fold::FriFoldAir;
            use crate::recursion::fri_merkle::FriMerkleAir;
            use crate::recursion::transcript::SpongeAir;
            vec![
                ("fri-fold(D)", wrap_log_nqc(&FriFoldAir)),
                ("fri-merkle(E)", wrap_log_nqc(&FriMerkleAir)),
                ("transcript(F)", wrap_log_nqc(&SpongeAir { blocks: 2 })),
            ]
        };
        #[cfg(not(feature = "recursion"))]
        let extra: Vec<(&str, usize)> = Vec::new();

        let regions: Vec<(&str, usize)> = base.iter().copied().chain(extra).collect();
        let composed = regions.iter().map(|&(_, l)| l).max().unwrap();
        let detail = regions.iter().map(|(n, l)| format!("{n}={l}")).collect::<Vec<_>>().join(", ");
        println!("WRAP budget rollup: {detail} ⇒ composed log_nqc = {composed} (budget {LOG_BLOWUP})");

        for (name, l) in &regions {
            assert!(*l <= LOG_BLOWUP, "wrap region {name} exceeds the degree budget: log_nqc {l} > {LOG_BLOWUP}");
        }
        assert!(composed <= LOG_BLOWUP, "the wrap regions must compose within the degree budget");

        #[cfg(not(feature = "recursion"))]
        println!(
            "  (super-tile FRI β-fold (D) / Merkle-path (E) / transcript (F) live behind --features \
             recursion — run `--features lookup,recursion` to fold them in)"
        );
        #[cfg(feature = "recursion")]
        println!(
            "  remaining: DEEP α_fri (G) / OOD selectors (H) / tx-root fold (J) — monolith/air.rs regions, \
             measured when the wrap AIR is assembled (W2-assemble)"
        );
    }

    /// **W2-assemble prerequisite — the full wrap feature-combination in ONE AIR.** The composed wrap AIR
    /// exercises transitions, periodic selectors, public values, AND multiple lookups simultaneously; each was
    /// validated in isolation (`ChainEvalAir` transitions here; `PeriodicAir`/`PinnedAir`/`TwoLookupAir` in
    /// the lookup prover) but never COMBINED. `CompositeAir` combines all four so the W1 lookup prover's
    /// combined layout + quotient sizing is proven ready for the composed wrap before the coupled W2-assemble
    /// build (a cheap gate on a genuine prover-integration risk).
    ///
    /// Cols `[x, prod, y, table, m1, m2]`: `x` is the running-product input, range-checked by two lookups;
    /// `prod` is the running product (transition `prod' = prod·x'`, boundary `prod = x`) — kept OUTSIDE the
    /// lookups so a broken product is isolable; `y` is pinned to `public[0]` (first row) and periodic-gated
    /// (`sel·(y−1) = 0` on even rows) — also outside the lookups; `table` provides both range-checks.
    struct CompositeAir;

    impl<F: p3_field::Field> BaseAir<F> for CompositeAir {
        fn width(&self) -> usize {
            6
        }
        fn num_public_values(&self) -> usize {
            1
        }
        fn num_periodic_columns(&self) -> usize {
            1
        }
        fn periodic_columns(&self) -> Vec<Vec<F>> {
            vec![vec![F::ONE, F::ZERO]] // period-2 selector: 1 on even rows
        }
    }

    impl<AB: AirBuilder<F = Val> + InteractionBuilder> Air<AB> for CompositeAir {
        fn eval(&self, builder: &mut AB) {
            let main = builder.main();
            let cur = main.current_slice().to_vec();
            let nxt = main.next_slice().to_vec();
            let (x, prod, y, table, m1, m2) = (cur[0], cur[1], cur[2], cur[3], cur[4], cur[5]);
            let sel: AB::Expr = builder.periodic_values()[0].into();
            let pin: AB::Expr = builder.public_values()[0].into();

            // base constraints over columns NOT carried in any lookup, so each is independently tamperable.
            builder.when_first_row().assert_zero(prod.into() - x.into()); // boundary: prod = x
            builder.when_transition().assert_zero(nxt[1].into() - prod.into() * nxt[0].into()); // prod' = prod·x'
            builder.when_first_row().assert_eq(y, pin); // y(row 0) == public[0]
            builder.assert_zero(sel * (y.into() - AB::Expr::ONE)); // even rows (sel = 1): y == 1

            // two LogUp range-checks of x against the shared table (multi-lookup ⇒ aux width 3).
            builder
                .push_local_interaction(vec![(vec![x.into()], AB::Expr::ONE), (vec![table.into()], -(m1.into()))]);
            builder
                .push_local_interaction(vec![(vec![x.into()], AB::Expr::ONE), (vec![table.into()], -(m2.into()))]);
        }
    }

    /// A valid trace: everything `1` (both range-checks self-cancel; running product of ones; even-row
    /// `y == 1`; first-row `y == public[0] = 1`).
    fn composite_trace(height: usize) -> RowMajorMatrix<Val> {
        let mut flat = Vec::with_capacity(height * 6);
        for _ in 0..height {
            flat.extend_from_slice(&[Val::ONE; 6]);
        }
        RowMajorMatrix::new(flat, 6)
    }

    /// The combination proves + verifies end to end (aux width 3 = 1 accumulator + 2 fractions) — the W1
    /// lookup prover threads transitions + periodic + public values + multi-lookup together, the composed
    /// wrap AIR's prover requirements, validated before the coupled assembly.
    #[test]
    fn composite_air_round_trips() {
        let air = CompositeAir;
        let proof = prove_lookup(&air, composite_trace(1 << 5), &[Val::ONE]);
        assert_eq!(proof.aux_width, 3, "two lookups ⇒ aux width = 1 accumulator + 2 fractions");
        assert!(verify_lookup(&air, &proof, &[Val::ONE]).is_ok(), "the combined-feature AIR must verify end to end");
    }

    /// Breaking the running product (a column outside the lookups) violates the transition ⇒ OOD mismatch —
    /// transitions fold correctly amid the periodic + multi-lookup constraints.
    #[test]
    fn composite_air_rejects_broken_product() {
        let air = CompositeAir;
        let mut trace = composite_trace(1 << 5);
        trace.values[5 * 6 + 1] = Val::from_u64(2); // row 5's prod ≠ prod_4 · x_5
        let proof = prove_lookup(&air, trace, &[Val::ONE]);
        assert!(
            matches!(verify_lookup(&air, &proof, &[Val::ONE]), Err(LookupVerifyError::OodMismatch)),
            "a broken running product must fail the OOD identity"
        );
    }

    /// Violating an even row's periodic-gated bind (`y ≠ 1`, kept lookup-balanced since `y` is outside the
    /// lookups) ⇒ OOD mismatch — periodic columns fold consistently alongside the lookups.
    #[test]
    fn composite_air_rejects_violated_periodic() {
        let air = CompositeAir;
        let mut trace = composite_trace(1 << 5);
        trace.values[2 * 6 + 2] = Val::from_u64(5); // row 2 (even, sel = 1): y = 5 ≠ 1
        let proof = prove_lookup(&air, trace, &[Val::ONE]);
        assert!(
            matches!(verify_lookup(&air, &proof, &[Val::ONE]), Err(LookupVerifyError::OodMismatch)),
            "a violated even-row periodic constraint must fail the OOD identity"
        );
    }

    /// Unbalancing one lookup (bump a multiplicity) leaves the base constraints satisfied but breaks that
    /// lookup's LogUp terminal ⇒ rejected — the two lookups are checked independently in the combined layout.
    #[test]
    fn composite_air_rejects_unbalanced_lookup() {
        let air = CompositeAir;
        let mut trace = composite_trace(1 << 5);
        trace.values[7 * 6 + 4] = Val::from_u64(2); // row 7's m1 = 2 ⇒ lookup 1 no longer cancels
        let proof = prove_lookup(&air, trace, &[Val::ONE]);
        assert!(
            matches!(verify_lookup(&air, &proof, &[Val::ONE]), Err(LookupVerifyError::NonZeroTerminal)),
            "an unbalanced lookup must be rejected by the terminal check"
        );
    }

    /// **W3 op-table brick 1 — the FLATTEN op-table evaluates the REAL join-split DAG and proves + verifies.**
    /// Build the op-table over the actual `JoinSplitAir` constraint DAG (501 ops + 372 leaf seeds ⇒ ~873 rows at
    /// constant width 10) and run it through the W1 lookup prover: the local op relations (out = a ∘ b) hold and
    /// the wiring bus balances (every operand read = its producer's write). This validates the narrow-tall
    /// mechanism the size fix rests on, on real structure at real scale — the analog of `chain_eval_round_trips`
    /// for a full DAG (with the operand-routing bus, not just a running product).
    #[test]
    fn op_table_round_trips() {
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let trace = op_table_trace(&constraints);
        let proof = prove_lookup(&OpTableAir, trace, &[]);
        assert!(
            verify_lookup(&OpTableAir, &proof, &[]).is_ok(),
            "the op-table must evaluate the real DAG and balance the wiring bus"
        );
    }

    /// Corrupting a LEAF's provided value (a wire read by ≥1 op) unbalances the bus — the consumers still read
    /// the old value, so the `(addr, value)` multiset no longer cancels ⇒ non-zero LogUp terminal. This is the
    /// WIRING half: the bus binds each read to its producer's write.
    #[test]
    fn op_table_rejects_broken_wire() {
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let mut trace = op_table_trace(&constraints);
        let w = 10;
        // A leaf row has all selectors 0 and (if read) `out_mult` (col 9) ≠ 0 (= −fanout). Corrupt its value.
        let h = trace.values.len() / w;
        let leaf = (0..h)
            .find(|&r| {
                let base = r * w;
                trace.values[base] == Val::ZERO
                    && trace.values[base + 1] == Val::ZERO
                    && trace.values[base + 2] == Val::ZERO
                    && trace.values[base + 9] != Val::ZERO
            })
            .expect("a leaf wire with fanout ≥ 1 exists");
        trace.values[leaf * w + 4] += Val::ONE; // provided value ≠ what consumers read
        let proof = prove_lookup(&OpTableAir, trace, &[]);
        assert!(
            matches!(verify_lookup(&OpTableAir, &proof, &[]), Err(LookupVerifyError::NonZeroTerminal)),
            "a corrupted wire value must unbalance the wiring bus"
        );
    }

    /// Corrupting a ROOT op's output (a constraint value, fanout 0 ⇒ `out_mult` 0, so the bus is unaffected)
    /// violates its local relation `out = a ∘ b` ⇒ OOD mismatch. This is the EVALUATION half: each op row is
    /// checked to compute its operation correctly.
    #[test]
    fn op_table_rejects_broken_op() {
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let mut trace = op_table_trace(&constraints);
        let w = 10;
        // A root op row: some selector set (is_op = 1) and `out_mult` (col 9) == 0 (nothing reads it).
        let h = trace.values.len() / w;
        let root = (0..h)
            .find(|&r| {
                let base = r * w;
                let is_op = trace.values[base] != Val::ZERO
                    || trace.values[base + 1] != Val::ZERO
                    || trace.values[base + 2] != Val::ZERO;
                is_op && trace.values[base + 9] == Val::ZERO
            })
            .expect("a root op (fanout 0) exists");
        trace.values[root * w + 4] += Val::ONE; // out ≠ a ∘ b now
        let proof = prove_lookup(&OpTableAir, trace, &[]);
        assert!(
            matches!(verify_lookup(&OpTableAir, &proof, &[]), Err(LookupVerifyError::OodMismatch)),
            "a corrupted op output must fail its local op relation"
        );
    }

    /// **The SIZE win, measured.** The op-table width is a CONSTANT 10 — independent of the DAG size — because
    /// the DAG becomes ROWS, not columns. So the epilogue's `2·n_mul` witnessed COLUMNS (428 for the real
    /// join-split inner; 2088 for the R5 monolith-as-inner) collapse to a fixed narrow tile plus slack rows,
    /// and it stays within the degree budget (`log_nqc ≤ 4`).
    #[test]
    fn op_table_is_narrow_and_low_degree() {
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let trace = op_table_trace(&constraints);
        let (rows, w) = (trace.values.len() / 10, 10);
        assert_eq!(BaseAir::<Val>::width(&OpTableAir), w, "op-table width is constant (independent of DAG size)");
        let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(&OpTableAir);
        let (_layout, log_nqc) = combined_constraint_layout(&OpTableAir, &lookups, 1);
        let mut seen = HashSet::new();
        let n_mul: usize = constraints.iter().map(|c| count_mul_nodes(c, &mut seen)).sum();
        println!(
            "OpTable (real join-split DAG): width {w} (const), {rows} padded rows, log_nqc = {log_nqc} (budget \
             {LOG_BLOWUP}) — replaces the witnessed {} COLUMNS (2·{n_mul} Muls) with slack ROWS at constant width",
            2 * n_mul,
        );
        assert!(log_nqc <= LOG_BLOWUP, "the op-table must stay within the degree budget (got {log_nqc})");
    }

    /// **W3 op-table brick 2 — the F_p² op-table evaluates the real DAG via `emul` and proves + verifies.** The
    /// faithful op-table carries 2-felt `Challenge` values (both coefficients nonzero here, so `emul`'s cross
    /// terms are exercised) and routes them through the 3-felt wiring bus `(addr, v0, v1)`. Same real
    /// `JoinSplitAir` DAG as brick 1, now over the extension field the real epilogue uses.
    #[test]
    fn op_table_f2_round_trips() {
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let (trace, _roots, _folded, _lb, _quot) = op_table_f2_trace(&constraints, pseudo_leaf_f2(), None, &[], None);
        let proof = prove_lookup(&OpTableF2Air, trace, &[]);
        assert!(
            verify_lookup(&OpTableF2Air, &proof, &[]).is_ok(),
            "the F_p² op-table must evaluate the real DAG (emul) and balance the wiring bus"
        );
    }

    /// Corrupting one felt of a LEAF's F_p² value (a wire read by ≥1 op) unbalances the `(addr, v0, v1)` bus ⇒
    /// non-zero terminal — the wiring binds the full 2-felt value.
    #[test]
    fn op_table_f2_rejects_broken_wire() {
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let (mut trace, _roots, _folded, _lb, _quot) = op_table_f2_trace(&constraints, pseudo_leaf_f2(), None, &[], None);
        let w = 13;
        let h = trace.values.len() / w;
        let leaf = (0..h)
            .find(|&r| {
                let base = r * w;
                trace.values[base] == Val::ZERO
                    && trace.values[base + 1] == Val::ZERO
                    && trace.values[base + 2] == Val::ZERO
                    && trace.values[base + 12] != Val::ZERO
            })
            .expect("a leaf wire with fanout ≥ 1 exists");
        trace.values[leaf * w + 4] += Val::ONE; // corrupt out0 (v0) of the leaf
        let proof = prove_lookup(&OpTableF2Air, trace, &[]);
        assert!(
            matches!(verify_lookup(&OpTableF2Air, &proof, &[]), Err(LookupVerifyError::NonZeroTerminal)),
            "a corrupted F_p² wire value must unbalance the wiring bus"
        );
    }

    /// Corrupting a ROOT op's F_p² output (fanout 0 ⇒ bus unaffected) violates its local `emul`/add/sub
    /// relation ⇒ OOD mismatch — the two-component evaluation is checked.
    #[test]
    fn op_table_f2_rejects_broken_op() {
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let (mut trace, _roots, _folded, _lb, _quot) = op_table_f2_trace(&constraints, pseudo_leaf_f2(), None, &[], None);
        let w = 13;
        let h = trace.values.len() / w;
        let root = (0..h)
            .find(|&r| {
                let base = r * w;
                let is_op = trace.values[base] != Val::ZERO
                    || trace.values[base + 1] != Val::ZERO
                    || trace.values[base + 2] != Val::ZERO;
                is_op && trace.values[base + 12] == Val::ZERO
            })
            .expect("a root op (fanout 0) exists");
        trace.values[root * w + 4] += Val::ONE; // out0 ≠ (a ∘ b).0 now
        let proof = prove_lookup(&OpTableF2Air, trace, &[]);
        assert!(
            matches!(verify_lookup(&OpTableF2Air, &proof, &[]), Err(LookupVerifyError::OodMismatch)),
            "a corrupted F_p² op output must fail its local relation"
        );
    }

    /// The F_p² op-table is width 13 (constant, independent of DAG size) and within the degree budget — the
    /// extension lift costs only a fixed 3 value felts more per wire than the scalar demonstrator (still ROWS,
    /// not columns; the DAG's `2·n_mul` witnessed columns still collapse to slack rows).
    #[test]
    fn op_table_f2_is_narrow_and_low_degree() {
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let (trace, _roots, _folded, _lb, _quot) = op_table_f2_trace(&constraints, pseudo_leaf_f2(), None, &[], None);
        let (rows, w) = (trace.values.len() / 13, 13);
        assert_eq!(BaseAir::<Val>::width(&OpTableF2Air), w, "F_p² op-table width is constant");
        let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(&OpTableF2Air);
        let (_layout, log_nqc) = combined_constraint_layout(&OpTableF2Air, &lookups, 1);
        let mut seen = HashSet::new();
        let n_mul: usize = constraints.iter().map(|c| count_mul_nodes(c, &mut seen)).sum();
        println!(
            "OpTableF2 (real join-split DAG, F_p²): width {w} (const), {rows} padded rows, log_nqc = {log_nqc} \
             (budget {LOG_BLOWUP}) — the witnessed {} COLUMNS (2·{n_mul} Muls) collapse to slack ROWS",
            2 * n_mul,
        );
        assert!(log_nqc <= LOG_BLOWUP, "the F_p² op-table must stay within the degree budget (got {log_nqc})");
    }

    /// **W3 op-table brick 3 — the op-table faithfully computes the REAL epilogue** (`--features recursion`).
    /// Seed the F_p² op-table's leaves with a real join-split inner's actual ζ-openings (the exact mapping the
    /// W2 `Witnesser` uses: `Main{0}`→local, `Main{≠0}`→next, `Public`→pubs, `Periodic`→periodic, the three
    /// selectors, constants) and confirm each constraint ROOT the op-table computes equals the native
    /// `eval_symbolic_native` `c_k`. So the FLATTEN op-table is a faithful re-encoding of the epilogue's
    /// constraint evaluation — not just "a" DAG — and then it proves + verifies through the W1 lookup prover.
    /// This is the op-table's W2-real analog: the narrow-tall mechanism now stands on the actual openings the
    /// wrap must bind, so the remaining W3 work is the fold/output check (α-Horner → `folded·inv_van == quot`)
    /// and the monolith arith-tile integration (where the size contraction is finally measured on the wrap).
    #[cfg(feature = "recursion")]
    #[test]
    fn op_table_f2_matches_native_epilogue() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::{epilogue_openings, eval_symbolic_native, make_config};
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout, BaseEntry, BaseLeaf};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (eo_local, eo_next, is_first, is_last, is_trans, _inv_van, _eo_quot, _eo_alpha, _z, eo_periodic) =
            epilogue_openings(&config, &JoinSplitAir, &proof, &pvs);
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let pubs: Vec<Challenge> = pvs.iter().map(|&p| Challenge::from(p)).collect();

        // The real leaf seed: map each leaf to its ζ-opening exactly as the epilogue does.
        let seed = |l: &BaseLeaf<Val>| -> Challenge {
            match l {
                BaseLeaf::Constant(c) => Challenge::from(*c),
                BaseLeaf::Variable(v) => match v.entry {
                    BaseEntry::Main { offset } => {
                        if offset == 0 {
                            eo_local[v.index]
                        } else {
                            eo_next[v.index]
                        }
                    }
                    BaseEntry::Public => pubs[v.index],
                    BaseEntry::Periodic => eo_periodic[v.index],
                    BaseEntry::Preprocessed { .. } => panic!("preprocessed columns unsupported"),
                },
                BaseLeaf::IsFirstRow => is_first,
                BaseLeaf::IsLastRow => is_last,
                BaseLeaf::IsTransition => is_trans,
            }
        };
        let (trace, roots, _folded, _lb, _quot) = op_table_f2_trace(&constraints, seed, None, &[], None);

        // FAITHFULNESS: each op-table root equals the native epilogue `c_k`.
        for (k, c) in constraints.iter().enumerate() {
            let native =
                eval_symbolic_native(c, &eo_local, &eo_next, &pubs, &eo_periodic, is_first, is_last, is_trans);
            assert_eq!(roots[k], native, "op-table root {k} must equal the native epilogue c_k");
        }

        // The real-seeded op-table proves + verifies through the W1 lookup prover.
        let lproof = prove_lookup(&OpTableF2Air, trace, &[]);
        assert!(
            verify_lookup(&OpTableF2Air, &lproof, &[]).is_ok(),
            "the op-table seeded with real ζ-openings must verify"
        );
    }

    /// **W3 op-table brick 4 — the COMPLETE B+C epilogue in the op-table** (`--features recursion`). With the
    /// α-Horner fold appended (`alpha = Some`), the op-table computes not just each `c_k` but the folded value,
    /// and it reproduces the epilogue's whole identity `folded·inv_van == quotient(ζ)` on a real join-split
    /// inner's ζ-openings — B (the fold) and C (the `c_k` evaluation) both as narrow-tall op rows, no
    /// `2·n_mul` witnessed columns. The fold needs no AIR change (ordinary mul/add rows reading the root wires
    /// + an α leaf), and the final `folded·inv_van == quot` check is the O(1) binding the arith head does in
    /// the eventual integration (brick 5). The op-table is now a full epilogue replacement, proven end-to-end.
    #[cfg(feature = "recursion")]
    #[test]
    fn op_table_f2_folds_to_quotient() {
        use crate::joinsplit_air::{build_trace, demo_witness, public_values, JoinSplitAir};
        use crate::recursion::native_fri::{epilogue_openings, make_config};
        use p3_uni_stark::{get_symbolic_constraints, prove, AirLayout, BaseEntry, BaseLeaf};

        let config = make_config(1, 4);
        let w = demo_witness();
        let pvs = public_values(&w);
        let proof = prove(&config, &JoinSplitAir, build_trace(&w), &pvs);
        let (eo_local, eo_next, is_first, is_last, is_trans, inv_van, eo_quot, eo_alpha, _z, eo_periodic) =
            epilogue_openings(&config, &JoinSplitAir, &proof, &pvs);
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let pubs: Vec<Challenge> = pvs.iter().map(|&p| Challenge::from(p)).collect();
        let seed = |l: &BaseLeaf<Val>| -> Challenge {
            match l {
                BaseLeaf::Constant(c) => Challenge::from(*c),
                BaseLeaf::Variable(v) => match v.entry {
                    BaseEntry::Main { offset } => {
                        if offset == 0 {
                            eo_local[v.index]
                        } else {
                            eo_next[v.index]
                        }
                    }
                    BaseEntry::Public => pubs[v.index],
                    BaseEntry::Periodic => eo_periodic[v.index],
                    BaseEntry::Preprocessed { .. } => panic!("preprocessed columns unsupported"),
                },
                BaseLeaf::IsFirstRow => is_first,
                BaseLeaf::IsLastRow => is_last,
                BaseLeaf::IsTransition => is_trans,
            }
        };
        // Append the α-Horner fold (B) in the op-table and read out `folded`.
        let (trace, _roots, folded, _lb, _quot) = op_table_f2_trace(&constraints, seed, Some(eo_alpha), &[], None);
        let folded = folded.expect("the fold produces a value for a non-empty constraint set").0;

        // The op-table's in-table fold reproduces the epilogue's COMPLETE identity.
        assert_eq!(folded * inv_van, eo_quot, "op-table α-Horner fold ⇒ folded·inv_van == quotient(ζ)");

        // And the whole op-table (c_k evaluation + fold) proves + verifies through the W1 lookup prover.
        let lproof = prove_lookup(&OpTableF2Air, trace, &[]);
        assert!(verify_lookup(&OpTableF2Air, &lproof, &[]).is_ok(), "the folded op-table must verify");
    }

    /// **W3 brick 5 prototype (is_zk=1) — region-gated op-table + a high-degree region, one AIR, one prover.**
    /// The full integration wires the op-table into the wrap: the op rows live in the trace SLACK (a subset of
    /// rows), the monolith's A–J tiles occupy the rest, and both compose in ONE lookup-carrying AIR through the
    /// W1 lookup prover. This de-risks the core GLUE at the production hiding config: a **witnessed selector
    /// `sel`** marks the op rows (the slack-tail marking, since op rows are not a periodic tile), so the
    /// op-table's constraints AND its wiring bus fire ONLY where `sel = 1`; a **degree-7 region** (`y = x⁷`, a
    /// Poseidon2 S-box degree stand-in for a real monolith tile) fires where `sel = 0`, **OVERLAYING** the
    /// op-table's value columns (`a0`/`a1` are the op operand on op rows, `x`/`x⁷` on region rows). Both regions
    /// coexist and prove through `prove_lookup` (is_zk=1) — the gating + column-overlay the integration rests on.
    /// (The larger brick-5 work remains: binding the op-table leaves to the monolith's committed ζ-openings, the
    /// full A–J regions, and — for production — porting to the non-hiding config.)
    struct GatedWrapProtoAir;

    impl BaseAir<Val> for GatedWrapProtoAir {
        fn width(&self) -> usize {
            14 // the 13 OpTableF2Air columns + a witnessed `sel` (op-row marker)
        }
    }

    impl<AB: AirBuilder<F = Val> + InteractionBuilder> Air<AB> for GatedWrapProtoAir {
        fn eval(&self, builder: &mut AB) {
            let main = builder.main();
            let r = main.current_slice().to_vec();
            let (is_mul, is_add, is_sub) = (r[0], r[1], r[2]);
            let (out_addr, o0, o1) = (r[3], r[4], r[5]);
            let (a_addr, a0, a1) = (r[6], r[7], r[8]);
            let (b_addr, b0, b1) = (r[9], r[10], r[11]);
            let out_mult = r[12];
            let sel: AB::Expr = r[13].into();
            let w = AB::Expr::from(Val::from_u64(7));

            builder.assert_zero(sel.clone() * (sel.clone() - AB::Expr::ONE)); // sel boolean

            // Op-table region (sel = 1): all op-table constraints GATED by sel, so they are inert on sel = 0.
            for s in [is_mul, is_add, is_sub] {
                builder.assert_zero(sel.clone() * s.into() * (s.into() - AB::Expr::ONE));
            }
            let is_op: AB::Expr = is_mul.into() + is_add.into() + is_sub.into();
            builder.assert_zero(sel.clone() * is_op.clone() * (is_op.clone() - AB::Expr::ONE));
            builder.assert_zero(sel.clone() * is_mul.into() * (o0.into() - (a0.into() * b0.into() + w.clone() * a1.into() * b1.into())));
            builder.assert_zero(sel.clone() * is_mul.into() * (o1.into() - (a0.into() * b1.into() + a1.into() * b0.into())));
            builder.assert_zero(sel.clone() * is_add.into() * (o0.into() - (a0.into() + b0.into())));
            builder.assert_zero(sel.clone() * is_add.into() * (o1.into() - (a1.into() + b1.into())));
            builder.assert_zero(sel.clone() * is_sub.into() * (o0.into() - (a0.into() - b0.into())));
            builder.assert_zero(sel.clone() * is_sub.into() * (o1.into() - (a1.into() - b1.into())));

            // Monolith-tile stand-in (sel = 0): a degree-7 identity y = x⁷ OVERLAYING the op operand columns.
            let one_minus: AB::Expr = AB::Expr::ONE - sel.clone();
            let x: AB::Expr = a0.into();
            let x7 = x.clone() * x.clone() * x.clone() * x.clone() * x.clone() * x.clone() * x.clone();
            builder.assert_zero(one_minus * (a1.into() - x7));

            // The wiring bus, GATED by sel (op rows only): reads +sel·is_op, define sel·out_mult (0 on sel = 0).
            let read_mult = sel.clone() * is_op.clone();
            let def_mult = sel * out_mult.into();
            builder.push_local_interaction(vec![
                (vec![a_addr.into(), a0.into(), a1.into()], read_mult.clone()),
                (vec![b_addr.into(), b0.into(), b1.into()], read_mult),
                (vec![out_addr.into(), o0.into(), o1.into()], def_mult),
            ]);
        }
    }

    /// Build a [`GatedWrapProtoAir`] trace: the real join-split op-table on the first rows (`sel = 1`, widened
    /// to 14 cols) followed by `n_region` degree-7 region rows (`sel = 0`, `x`/`x⁷` overlaying `a0`/`a1`), padded
    /// (pad rows `sel = 0`, all-zero — the region identity `0 = 0⁷` holds and the bus is inert).
    fn gated_proto_trace(n_region: usize) -> RowMajorMatrix<Val> {
        let constraints =
            get_symbolic_constraints::<Val, _>(&JoinSplitAir, AirLayout::from_air::<Val>(&JoinSplitAir));
        let (op, _r, _f, _lb, _quot) = op_table_f2_trace(&constraints, pseudo_leaf_f2(), None, &[], None);
        let h_op = op.values.len() / 13;
        let (w, total) = (14, (h_op + n_region).next_power_of_two());
        let mut flat = vec![Val::ZERO; total * w];
        for row in 0..h_op {
            flat[row * w..row * w + 13].copy_from_slice(&op.values[row * 13..row * 13 + 13]);
            flat[row * w + 13] = Val::ONE; // sel = 1 (op rows)
        }
        for i in 0..n_region {
            let row = h_op + i;
            let x = Val::from_u64(3 + i as u64);
            let mut x7 = Val::ONE;
            for _ in 0..7 {
                x7 *= x;
            }
            flat[row * w + 7] = x; // a0 = x
            flat[row * w + 8] = x7; // a1 = x⁷ (sel = 0 ⇒ the region identity fires here)
        }
        RowMajorMatrix::new(flat, w)
    }

    /// The prototype proves + verifies through `prove_lookup` (is_zk=1): the op-table's wiring bus and the
    /// degree-7 region compose in ONE AIR, region-gated, at the production hiding config.
    #[test]
    fn gated_wrap_proto_proves() {
        let lookups: Lookups<Val> = Lookups::from_air::<Challenge, _>(&GatedWrapProtoAir);
        let (_layout, log_nqc) = combined_constraint_layout(&GatedWrapProtoAir, &lookups, 1);
        println!("GatedWrapProto (op-table + deg-7 region, gated): log_nqc = {log_nqc} (budget {LOG_BLOWUP})");
        let proof = prove_lookup(&GatedWrapProtoAir, gated_proto_trace(16), &[]);
        assert!(
            verify_lookup(&GatedWrapProtoAir, &proof, &[]).is_ok(),
            "the region-gated op-table + degree-7 region must prove through prove_lookup at is_zk=1"
        );
    }

    /// Breaking a REGION row's `x⁷` violates the gated degree-7 identity ⇒ OOD mismatch — the region constraint
    /// is checked on `sel = 0` rows (and is correctly inert on the op rows).
    #[test]
    fn gated_wrap_proto_rejects_broken_region() {
        let mut trace = gated_proto_trace(16);
        let (w, h) = (14, trace.values.len() / 14);
        let region0 = (0..h).find(|&row| trace.values[row * w + 13] == Val::ZERO && trace.values[row * w + 7] != Val::ZERO)
            .expect("a region row (sel = 0, x ≠ 0) exists");
        trace.values[region0 * w + 8] += Val::ONE; // a1 ≠ x⁷ now
        let proof = prove_lookup(&GatedWrapProtoAir, trace, &[]);
        assert!(
            matches!(verify_lookup(&GatedWrapProtoAir, &proof, &[]), Err(LookupVerifyError::OodMismatch)),
            "a broken region identity must fail the OOD check"
        );
    }

    /// Breaking an op-table LEAF value (on a `sel = 1` row) unbalances the wiring bus ⇒ non-zero terminal — the
    /// op-table region is checked amid the gated degree-7 region.
    #[test]
    fn gated_wrap_proto_rejects_broken_optable() {
        let mut trace = gated_proto_trace(16);
        let (w, h) = (14, trace.values.len() / 14);
        // A sel = 1 leaf row: op-selectors 0 and out_mult (col 12) ≠ 0 (a wire read ≥ 1 time).
        let leaf = (0..h)
            .find(|&row| {
                let base = row * w;
                trace.values[base + 13] == Val::ONE
                    && trace.values[base] == Val::ZERO
                    && trace.values[base + 1] == Val::ZERO
                    && trace.values[base + 2] == Val::ZERO
                    && trace.values[base + 12] != Val::ZERO
            })
            .expect("a sel = 1 leaf wire with fanout ≥ 1 exists");
        trace.values[leaf * w + 4] += Val::ONE; // corrupt its provided value
        let proof = prove_lookup(&GatedWrapProtoAir, trace, &[]);
        assert!(
            matches!(verify_lookup(&GatedWrapProtoAir, &proof, &[]), Err(LookupVerifyError::NonZeroTerminal)),
            "a corrupted op-table wire must unbalance the bus even amid the gated region"
        );
    }

    /// **W3 brick 5 prototype (is_zk=1) — the openings→bus SEAM: one gated region PROVIDES a value that another
    /// gated region CONSUMES and uses in a constraint.** This is the exact integration seam — in the full wrap
    /// the arith head (an A–J tile) provides each committed ζ-opening on the bus and the op-table leaves consume
    /// them by address. Neither the op-table (provider+consumer, but NOT gated into separate regions) nor the
    /// gated prototype (two regions, but sharing NO data) shows this alone. `SeamProtoAir` (F_p², width 9): a
    /// **provider** region (`sel = 1`) provides `(addr, v0, v1)` on the wiring bus; a **consumer** region
    /// (`sel = 0`) reads `(addr, r0, r1)` — so the bus BINDS `recv = v` (same addr) across the region boundary —
    /// and asserts `recv² = sq` (emul), proving the consumer actually received and used the provided value.
    struct SeamProtoAir;

    impl BaseAir<Val> for SeamProtoAir {
        fn width(&self) -> usize {
            9 // [is_cons, addr, v0, v1, r0, r1, s0, s1, mult]
        }
    }

    impl<AB: AirBuilder<F = Val> + InteractionBuilder> Air<AB> for SeamProtoAir {
        fn eval(&self, builder: &mut AB) {
            let main = builder.main();
            let r = main.current_slice().to_vec();
            let is_cons: AB::Expr = r[0].into(); // 1 on consumer rows, 0 on provider AND pad rows
            let (addr, v0, v1) = (r[1], r[2], r[3]);
            let (r0, r1) = (r[4], r[5]);
            let (s0, s1) = (r[6], r[7]);
            let mult = r[8]; // define multiplicity: −n_consumers on the provider, 0 elsewhere
            let w = AB::Expr::from(Val::from_u64(7));

            builder.assert_zero(is_cons.clone() * (is_cons.clone() - AB::Expr::ONE)); // is_cons boolean

            // Consumer (is_cons = 1): the received value (bound to the provider's by the bus) squares to `sq`.
            builder.assert_zero(is_cons.clone() * (s0.into() - (r0.into() * r0.into() + w * r1.into() * r1.into())));
            builder.assert_zero(is_cons.clone() * (s1.into() - (r0.into() * r1.into() + r1.into() * r0.into())));

            // One wiring bus: the DEFINE term `(addr, v)` carries `mult` (nonzero only on the provider), the
            // READ term `(addr, recv)` fires only on consumers (`is_cons`) — so PAD rows (both 0) are inert.
            // Balance ⇒ every consumed `(addr, recv)` matches the provided `(addr, v)` — the cross-region
            // binding `recv = v`.
            builder.push_local_interaction(vec![
                (vec![addr.into(), v0.into(), v1.into()], mult.into()),
                (vec![addr.into(), r0.into(), r1.into()], is_cons),
            ]);
        }
    }

    /// Build a [`SeamProtoAir`] trace: one provider row `(is_cons = 0, addr, v, mult = −n_consumers)` and
    /// `n_consumers` consumer rows `(is_cons = 1, addr, recv = v, sq = v²)`, padded (pad rows all-zero: `is_cons
    /// = 0` ⇒ the square is vacuous and both bus terms are 0). `v` has both F_p² coefficients nonzero so `emul`
    /// is exercised.
    fn seam_proto_trace(n_consumers: usize) -> RowMajorMatrix<Val> {
        use p3_field::BasedVectorSpace;
        let v = Challenge::from_basis_coefficients_fn(|k| Val::from_u64(if k == 0 { 3 } else { 5 }));
        let vsq = v * v;
        let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
        let (addr, w) = (Val::from_u64(7), 9);
        let total = (1 + n_consumers).next_power_of_two().max(1 << 4);
        let mut flat = vec![Val::ZERO; total * w];
        // Provider row 0: is_cons = 0, addr, v, mult = −n_consumers (nothing read yet).
        flat[1] = addr;
        flat[2..4].copy_from_slice(&cc(v));
        flat[8] = -Val::from_u64(n_consumers as u64);
        // Consumer rows: is_cons = 1, addr, recv = v, sq = v².
        for i in 0..n_consumers {
            let base = (1 + i) * w;
            flat[base] = Val::ONE; // is_cons
            flat[base + 1] = addr;
            flat[base + 4..base + 6].copy_from_slice(&cc(v)); // recv = v
            flat[base + 6..base + 8].copy_from_slice(&cc(vsq)); // sq = v²
        }
        RowMajorMatrix::new(flat, w)
    }

    /// The seam proves + verifies through `prove_lookup` (is_zk=1): a value crosses the region boundary via the
    /// bus and is used in the consumer's constraint.
    #[test]
    fn seam_proto_proves() {
        let proof = prove_lookup(&SeamProtoAir, seam_proto_trace(3), &[]);
        assert!(
            verify_lookup(&SeamProtoAir, &proof, &[]).is_ok(),
            "the cross-region openings→bus seam must prove through prove_lookup at is_zk=1"
        );
    }

    /// A consumer that received a value NOT provided (`recv ≠ v`, but squared correctly so its local constraint
    /// still holds) breaks the bus balance ⇒ non-zero terminal — the bus binds the consumer's received value to
    /// the provider's, independently of the local use.
    #[test]
    fn seam_proto_rejects_wrong_recv() {
        use p3_field::BasedVectorSpace;
        let mut trace = seam_proto_trace(3);
        let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
        let bad = Challenge::from(Val::from_u64(999)); // ≠ v, and never provided
        trace.values[9 + 4..9 + 6].copy_from_slice(&cc(bad)); // consumer 0 recv = bad
        trace.values[9 + 6..9 + 8].copy_from_slice(&cc(bad * bad)); // sq = bad² (local square still holds)
        let proof = prove_lookup(&SeamProtoAir, trace, &[]);
        assert!(
            matches!(verify_lookup(&SeamProtoAir, &proof, &[]), Err(LookupVerifyError::NonZeroTerminal)),
            "a consumer that received an unprovided value must unbalance the bus"
        );
    }

    /// A consumer that received the right value but mis-squares it (`sq ≠ recv²`) fails its local constraint ⇒
    /// OOD mismatch — the consumer's USE of the seam value is checked.
    #[test]
    fn seam_proto_rejects_wrong_square() {
        let mut trace = seam_proto_trace(3);
        trace.values[1 * 9 + 6] += Val::ONE; // consumer 0's s0 ≠ recv²
        let proof = prove_lookup(&SeamProtoAir, trace, &[]);
        assert!(
            matches!(verify_lookup(&SeamProtoAir, &proof, &[]), Err(LookupVerifyError::OodMismatch)),
            "a consumer that misuses the received value must fail its local constraint"
        );
    }
}
