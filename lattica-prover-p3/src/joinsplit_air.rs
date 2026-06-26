//! Join-split (N-in / M-out) spend circuit — the audit-target shape, with the soundness fixes baked
//! in (A1 position-consistency, A2 domain separation, A3 fee range-check). Built fresh; the 1-in/1-out
//! `full_spend_air` is kept intact as the simpler reference.
//!
//! This file (so far) is the **native oracle** + design — the statement computed in plain Rust, which
//! pins the hash layouts, the nullifier/position binding, the multi-input membership to a shared
//! anchor, and the value balance. The AIR is built on top of it next, and is differential-tested
//! against this oracle.
//!
//! ## Hashes (A2 — domain separation)
//! Every data hash carries a distinct **domain tag in lane 0** of the Poseidon2 input, so a digest
//! produced in one context can't be reinterpreted in another:
//!   * ownership  `recipient = H(DOM_OWN ‖ nk)`
//!   * commitment `cm        = H(DOM_CM  ‖ recipient(4) ‖ value ‖ rho ‖ rcm)`   (input & output notes)
//!   * nullifier  `nf        = H(DOM_NF  ‖ nk ‖ rho ‖ pos)`
//! The Merkle **merge** `H(l(4) ‖ r(4))` fills all 8 lanes (no tag); it is structurally separated —
//! it only ever appears as an internal node over two 4-element digests, and the leaf entering the
//! tree is constrained to be a `DOM_CM`-tagged commitment, so a node can't be presented as a leaf.
//! (Documented for the auditor; see docs A4.)
//!
//! ## Nullifier / position (A1)
//! `pos = Σ_d bits_d · 2^d` — the integer position implied by the membership path bits — is fed into
//! the nullifier. So a note at tree position p has exactly one nullifier; it cannot be nullified
//! "as if" at a different position (which would otherwise allow a second, undetected spend).

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{FriParameters, HidingFriPcs};
use p3_goldilocks::{default_goldilocks_poseidon2_8, Goldilocks, Poseidon2Goldilocks};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeHidingMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{prove, verify, StarkConfig};
use rand::rngs::SmallRng;
use rand::SeedableRng;

use crate::poseidon2_air::{ext_linear, int_linear, native_permute, native_steps, periodic_table, pow7, BLOCK};

pub const N_IN: usize = 2; // inputs per transaction
pub const M_OUT: usize = 2; // outputs per transaction
pub const DEPTH: usize = 32; // production Merkle depth
pub const BITS: usize = 52; // value range bound (2·2^BITS < p ⇒ no wraparound)
pub const DIGEST: usize = 4;
const W: usize = 8;

// A2 domain-separation tags (lane 0 of each data hash). Distinct, nonzero.
pub const DOM_OWN: u64 = 1;
pub const DOM_CM: u64 = 2;
pub const DOM_NF: u64 = 3;

type Val = Goldilocks;

/// Domain-tagged fixed-input hash: `H(domain ‖ elems)`, digest = first `DIGEST` lanes of the
/// permutation output. `elems.len()` must be ≤ 7 (lane 0 holds the domain).
fn h(domain: u64, elems: &[Val]) -> [Val; DIGEST] {
    debug_assert!(elems.len() <= W - 1);
    let mut s = [Val::ZERO; W];
    s[0] = Val::from_u64(domain);
    s[1..1 + elems.len()].copy_from_slice(elems);
    native_permute(s)[..DIGEST].try_into().unwrap()
}

pub fn recipient_of(nk: Val) -> [Val; DIGEST] {
    h(DOM_OWN, &[nk])
}

pub fn commit(recipient: [Val; DIGEST], value: Val, rho: Val, rcm: Val) -> [Val; DIGEST] {
    let mut e = [Val::ZERO; 7];
    e[..DIGEST].copy_from_slice(&recipient);
    e[DIGEST] = value;
    e[DIGEST + 1] = rho;
    e[DIGEST + 2] = rcm;
    h(DOM_CM, &e)
}

pub fn nullifier(nk: Val, rho: Val, pos: Val) -> [Val; DIGEST] {
    h(DOM_NF, &[nk, rho, pos])
}

/// Untagged 2-to-1 Merkle compression `H(l ‖ r)` (fills all 8 lanes).
pub fn merge(l: [Val; DIGEST], r: [Val; DIGEST]) -> [Val; DIGEST] {
    let mut s = [Val::ZERO; W];
    s[..DIGEST].copy_from_slice(&l);
    s[DIGEST..].copy_from_slice(&r);
    native_permute(s)[..DIGEST].try_into().unwrap()
}

/// `pos = Σ_d bits[d]·2^d` (A1): the integer tree position implied by the path bits.
pub fn pos_of(bits: &[bool; DEPTH]) -> Val {
    let mut p: u64 = 0;
    for d in (0..DEPTH).rev() {
        p = (p << 1) | bits[d] as u64;
    }
    Val::from_u64(p)
}

/// Fold a leaf up a general-position path to the root.
pub fn fold(leaf: [Val; DIGEST], sib: &[[Val; DIGEST]; DEPTH], bits: &[bool; DEPTH]) -> [Val; DIGEST] {
    let mut node = leaf;
    for d in 0..DEPTH {
        node = if bits[d] { merge(sib[d], node) } else { merge(node, sib[d]) };
    }
    node
}

#[derive(Clone)]
pub struct Input {
    pub nk: u64,
    pub value: u64,
    pub rho: Val,
    pub rcm: Val,
    pub sib: [[Val; DIGEST]; DEPTH],
    pub bits: [bool; DEPTH],
}

#[derive(Clone, Copy)]
pub struct Output {
    pub recipient: [Val; DIGEST],
    pub value: u64,
    pub rho: Val,
    pub rcm: Val,
}

#[derive(Clone)]
pub struct Witness {
    pub inputs: [Input; N_IN],
    pub outputs: [Output; M_OUT],
    pub fee: u64,
    pub tx_binding: [Val; DIGEST],
}

pub struct PublicOutputs {
    pub anchor: [Val; DIGEST],
    pub nullifiers: [[Val; DIGEST]; N_IN],
    pub out_cms: [[Val; DIGEST]; M_OUT],
}

/// Compute the public outputs from a witness, and assert the relation holds (all inputs under one
/// anchor; value balance). Panics on an inconsistent witness — the prover-side oracle.
pub fn native_outputs(w: &Witness) -> PublicOutputs {
    // per-input commitment, membership (shared anchor), nullifier
    let mut anchor: Option<[Val; DIGEST]> = None;
    let mut nullifiers = [[Val::ZERO; DIGEST]; N_IN];
    let mut in_sum: u128 = 0;
    for (i, inp) in w.inputs.iter().enumerate() {
        let nk = Val::from_u64(inp.nk);
        let recipient = recipient_of(nk);
        let cm = commit(recipient, Val::from_u64(inp.value), inp.rho, inp.rcm);
        let root = fold(cm, &inp.sib, &inp.bits);
        match anchor {
            None => anchor = Some(root),
            Some(a) => assert_eq!(a, root, "input {i} folds to a different anchor"),
        }
        nullifiers[i] = nullifier(nk, inp.rho, pos_of(&inp.bits));
        in_sum += inp.value as u128;
    }
    // per-output commitment
    let mut out_cms = [[Val::ZERO; DIGEST]; M_OUT];
    let mut out_sum: u128 = 0;
    for (j, out) in w.outputs.iter().enumerate() {
        out_cms[j] = commit(out.recipient, Val::from_u64(out.value), out.rho, out.rcm);
        out_sum += out.value as u128;
    }
    // value balance (A3: all values range-bounded ⇒ no wraparound)
    assert_eq!(in_sum, out_sum + w.fee as u128, "value balance Σin = Σout + fee");
    PublicOutputs { anchor: anchor.unwrap(), nullifiers, out_cms }
}

// ==============================================================================================
// AIR — stage 1: multi-input membership to a shared anchor (domain-tagged ownership + commitment).
// Later stages add nullifiers (A1 pos-binding), accumulator balance + range (A3), outputs, and the
// per-instance public bindings. Built incrementally; each stage differential-tested vs the oracle.
// ==============================================================================================

const SPAN_BLOCKS: usize = 3 + DEPTH; // ownership, commitment, DEPTH merges, nullifier
const OUT_BLOCKS: usize = 2; // out_cm perm + range overflow (BITS > 32 ⇒ 2 blocks)
const FEE_BLOCKS: usize = 2; // fee binding + range
const USED_BLOCKS: usize = N_IN * SPAN_BLOCKS + M_OUT * OUT_BLOCKS + FEE_BLOCKS;
const NUM_BLOCKS: usize = USED_BLOCKS.next_power_of_two();
const HEIGHT: usize = NUM_BLOCKS * BLOCK;

// columns
const BIT: usize = 8; // membership position bit
const NK: usize = 9; // local-persistent within an input span
const RHO: usize = 10;
const VAL: usize = 11; // value within input / output / fee region
const POSACC: usize = 12; // Σ bit_d·2^d within an input's membership (A1)
const VALACC: usize = 13; // global balance accumulator: +in, −out, −fee ⇒ 0
const REM: usize = 14; // range running remainder
const RBIT: usize = 15;
const WIDTH: usize = 16;

// periodic-column indices: 0..11 round schedule (period 32), then fixed (length HEIGHT) selectors
const P_OWN_IN: usize = 11;
const P_RECIP_LINK: usize = 12;
const P_COMMIT_IN: usize = 13;
const P_MEM_LINK: usize = 14;
const P_POS_COEFF: usize = 15; // 2^d at each membership link
const P_ROOT: usize = 16;
const P_NULL_IN: usize = 17;
const P_OUT_IN: usize = 18;
const P_FEE_IN: usize = 19;
const P_REGION_LAST: usize = 20; // last row of each region (gates local-persistent columns)
const P_RANGE_SEED: usize = 21; // rem = VAL (each value's first range row)
const P_RANGE_ACTIVE: usize = 22; // decomposition rows
const P_RANGE_CLOSE: usize = 23; // rem = 0 (value < 2^BITS)
const P_ROW0: usize = 24; // VALACC = 0
const P_FINAL: usize = 25; // VALACC = 0 (balance)
const P_NULLOUT: usize = 26; // N_IN one-hots: nf_i binding
const P_OUTOUT: usize = 26 + N_IN; // M_OUT one-hots: out_cm_j binding
const N_PERIODIC: usize = 26 + N_IN + M_OUT;

// public inputs: anchor(4) ‖ nf_i(4·N) ‖ out_cm_j(4·M) ‖ fee(1) ‖ tx_binding(4)
const PI_ANCHOR: usize = 0;
const PI_NF: usize = 4;
const PI_OUTCM: usize = 4 + N_IN * DIGEST;
const PI_FEE: usize = 4 + N_IN * DIGEST + M_OUT * DIGEST;
const PI_TXBIND: usize = PI_FEE + 1;
const N_PUBLIC: usize = PI_TXBIND + DIGEST;

const fn input_base(i: usize) -> usize {
    i * SPAN_BLOCKS
}
const fn own_in_row(i: usize) -> usize {
    input_base(i) * BLOCK
}
const fn own_out_row(i: usize) -> usize {
    input_base(i) * BLOCK + BLOCK - 1
}
const fn commit_in_row(i: usize) -> usize {
    (input_base(i) + 1) * BLOCK
}
const fn root_row(i: usize) -> usize {
    (input_base(i) + 1 + DEPTH) * BLOCK + BLOCK - 1
}
const fn null_block(i: usize) -> usize {
    input_base(i) + 2 + DEPTH
}
const fn null_in_row(i: usize) -> usize {
    null_block(i) * BLOCK
}
const fn null_out_row(i: usize) -> usize {
    null_block(i) * BLOCK + BLOCK - 1
}
const fn out_base(j: usize) -> usize {
    N_IN * SPAN_BLOCKS + j * OUT_BLOCKS
}
const fn out_in_row(j: usize) -> usize {
    out_base(j) * BLOCK
}
const fn out_out_row(j: usize) -> usize {
    out_base(j) * BLOCK + BLOCK - 1
}
const fn fee_base() -> usize {
    N_IN * SPAN_BLOCKS + M_OUT * OUT_BLOCKS
}
const fn fee_in_row() -> usize {
    fee_base() * BLOCK
}

fn one_hot(rows: &[usize]) -> Vec<Val> {
    let mut c = vec![Val::ZERO; HEIGHT];
    for &r in rows {
        c[r] = Val::ONE;
    }
    c
}

fn periodic() -> Vec<Vec<Val>> {
    let mut cols = periodic_table(); // 11 round-schedule columns, period 32
    let own_in: Vec<usize> = (0..N_IN).map(own_in_row).collect();
    let recip: Vec<usize> = (0..N_IN).map(own_out_row).collect(); // own output → commit input
    let commit_in: Vec<usize> = (0..N_IN).map(commit_in_row).collect();
    // membership links + the 2^d position coefficient at each link (A1).
    let mut mem: Vec<usize> = Vec::new();
    let mut pos_coeff = vec![Val::ZERO; HEIGHT];
    for i in 0..N_IN {
        for d in 0..DEPTH {
            let row = (input_base(i) + 1 + d) * BLOCK + BLOCK - 1;
            mem.push(row);
            pos_coeff[row] = Val::from_u64(1u64 << d);
        }
    }
    let root: Vec<usize> = (0..N_IN).map(root_row).collect();
    let null_in: Vec<usize> = (0..N_IN).map(null_in_row).collect();
    let out_in: Vec<usize> = (0..M_OUT).map(out_in_row).collect();
    // region-last rows (gate local-persistent columns at region boundaries)
    let mut region_last: Vec<usize> = (0..N_IN).map(null_out_row).collect();
    region_last.extend((0..M_OUT).map(|j| out_in_row(j) + OUT_BLOCKS * BLOCK - 1));
    region_last.push(fee_in_row() + FEE_BLOCKS * BLOCK - 1);
    // range windows: one per value (each input value, output value, and the fee)
    let mut seeds: Vec<usize> = (0..N_IN).map(commit_in_row).collect();
    seeds.extend((0..M_OUT).map(out_in_row));
    seeds.push(fee_in_row());
    let mut range_active: Vec<usize> = Vec::new();
    let mut range_close: Vec<usize> = Vec::new();
    for &s in &seeds {
        range_active.extend(s..s + BITS);
        range_close.push(s + BITS);
    }

    cols.push(one_hot(&own_in)); // P_OWN_IN
    cols.push(one_hot(&recip)); // P_RECIP_LINK
    cols.push(one_hot(&commit_in)); // P_COMMIT_IN
    cols.push(one_hot(&mem)); // P_MEM_LINK
    cols.push(pos_coeff); // P_POS_COEFF
    cols.push(one_hot(&root)); // P_ROOT
    cols.push(one_hot(&null_in)); // P_NULL_IN
    cols.push(one_hot(&out_in)); // P_OUT_IN
    cols.push(one_hot(&[fee_in_row()])); // P_FEE_IN
    cols.push(one_hot(&region_last)); // P_REGION_LAST
    cols.push(one_hot(&seeds)); // P_RANGE_SEED
    cols.push(one_hot(&range_active)); // P_RANGE_ACTIVE
    cols.push(one_hot(&range_close)); // P_RANGE_CLOSE
    cols.push(one_hot(&[0])); // P_ROW0
    cols.push(one_hot(&[fee_in_row() + FEE_BLOCKS * BLOCK - 1])); // P_FINAL
    for i in 0..N_IN {
        cols.push(one_hot(&[null_out_row(i)])); // P_NULLOUT + i
    }
    for j in 0..M_OUT {
        cols.push(one_hot(&[out_out_row(j)])); // P_OUTOUT + j
    }
    cols
}

pub struct JoinSplitAir;

impl BaseAir<Goldilocks> for JoinSplitAir {
    fn width(&self) -> usize {
        WIDTH
    }
    fn num_public_values(&self) -> usize {
        N_PUBLIC // anchor ‖ N nullifiers ‖ M out_cms ‖ fee ‖ tx_binding
    }
    fn num_periodic_columns(&self) -> usize {
        N_PERIODIC
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        periodic()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for JoinSplitAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let two = AB::Expr::TWO;
        let dom_own = AB::Expr::from(Goldilocks::from_u64(DOM_OWN));
        let dom_cm = AB::Expr::from(Goldilocks::from_u64(DOM_CM));
        let dom_nf = AB::Expr::from(Goldilocks::from_u64(DOM_NF));

        let is_init = p[0].clone();
        let is_full = p[1].clone();
        let is_partial = p[2].clone();
        let rc: Vec<AB::Expr> = (0..8).map(|i| p[3 + i].clone()).collect();

        // ---- Poseidon2 round constraints on the state columns (period-32 schedule) ----
        let mut init_s: [AB::Expr; 8] = core::array::from_fn(|i| cur[i].clone());
        ext_linear(&mut init_s);
        let mut full_s: [AB::Expr; 8] = core::array::from_fn(|i| pow7(cur[i].clone() + rc[i].clone()));
        ext_linear(&mut full_s);
        let mut part_s: [AB::Expr; 8] =
            core::array::from_fn(|i| if i == 0 { pow7(cur[0].clone() + rc[0].clone()) } else { cur[i].clone() });
        int_linear(&mut part_s);
        for i in 0..8 {
            let round = is_init.clone() * (nxt[i].clone() - init_s[i].clone())
                + is_full.clone() * (nxt[i].clone() - full_s[i].clone())
                + is_partial.clone() * (nxt[i].clone() - part_s[i].clone());
            builder.when_transition().assert_zero(round);
        }

        // ---- local-persistent columns: constant within a region, free at region boundaries ----
        let not_last = one.clone() - p[P_REGION_LAST].clone();
        for &c in &[NK, RHO, VAL] {
            builder.when_transition().assert_zero(not_last.clone() * (nxt[c].clone() - cur[c].clone()));
        }
        // pos_acc: += bit·2^d at membership links, else constant within the span (A1)
        let bit = nxt[BIT].clone();
        builder.when_transition().assert_zero(
            not_last.clone()
                * (nxt[POSACC].clone() - cur[POSACC].clone() - p[P_MEM_LINK].clone() * (bit.clone() * p[P_POS_COEFF].clone())),
        );
        builder.assert_zero(p[P_OWN_IN].clone() * cur[POSACC].clone()); // reset to 0 at span start

        // ---- global value accumulator: +in (commit), −out, −fee ⇒ 0 ----
        builder.assert_zero(p[P_ROW0].clone() * cur[VALACC].clone());
        let acc_delta = (p[P_COMMIT_IN].clone() - p[P_OUT_IN].clone() - p[P_FEE_IN].clone()) * cur[VAL].clone();
        builder.when_transition().assert_zero(nxt[VALACC].clone() - cur[VALACC].clone() - acc_delta);
        builder.assert_zero(p[P_FINAL].clone() * cur[VALACC].clone()); // balance: Σin = Σout + fee

        // ---- range: rem=VAL at seed, rem=2·rem'+rbit (rbit boolean), rem=0 at close (A3) ----
        builder.assert_zero(p[P_RANGE_SEED].clone() * (cur[REM].clone() - cur[VAL].clone()));
        let ra = p[P_RANGE_ACTIVE].clone();
        builder
            .when_transition()
            .assert_zero(ra.clone() * (cur[REM].clone() - (two.clone() * nxt[REM].clone() + cur[RBIT].clone())));
        builder.when_transition().assert_zero(ra.clone() * (cur[RBIT].clone() * (one.clone() - cur[RBIT].clone())));
        builder.assert_zero(p[P_RANGE_CLOSE].clone() * cur[REM].clone());

        // ---- ownership input: [DOM_OWN, nk, 0,..] ----
        let own = p[P_OWN_IN].clone();
        builder.assert_zero(own.clone() * (cur[0].clone() - dom_own.clone()));
        builder.assert_zero(own.clone() * (cur[1].clone() - cur[NK].clone()));
        for i in 2..8 {
            builder.assert_zero(own.clone() * cur[i].clone());
        }

        // ---- recipient link: commit.in[1..5] = own.out[0..4] ----
        let rl = p[P_RECIP_LINK].clone();
        for k in 0..DIGEST {
            builder.when_transition().assert_zero(rl.clone() * (nxt[1 + k].clone() - cur[k].clone()));
        }

        // ---- commitment input: [DOM_CM, recipient(link), value, rho, rcm(free)] ----
        let ci = p[P_COMMIT_IN].clone();
        builder.assert_zero(ci.clone() * (cur[0].clone() - dom_cm.clone()));
        builder.assert_zero(ci.clone() * (cur[1 + DIGEST].clone() - cur[VAL].clone())); // value (lane 5)
        builder.assert_zero(ci.clone() * (cur[2 + DIGEST].clone() - cur[RHO].clone())); // rho   (lane 6)

        // ---- membership links: place running digest by the bit (general position) ----
        let ml = p[P_MEM_LINK].clone();
        for k in 0..DIGEST {
            let placed = (one.clone() - bit.clone()) * (nxt[k].clone() - cur[k].clone())
                + bit.clone() * (nxt[DIGEST + k].clone() - cur[k].clone());
            builder.when_transition().assert_zero(ml.clone() * placed);
        }
        builder.when_transition().assert_zero(ml.clone() * (bit.clone() * (one.clone() - bit.clone())));

        // ---- root: every input folds to the shared public anchor ----
        let pr = p[P_ROOT].clone();
        for k in 0..DIGEST {
            builder.assert_zero(pr.clone() * (cur[k].clone() - pis[PI_ANCHOR + k].clone()));
        }

        // ---- nullifier input: [DOM_NF, nk, rho, pos_acc, 0,0,0,0] (A1: pos = pos_acc) ----
        let ni = p[P_NULL_IN].clone();
        builder.assert_zero(ni.clone() * (cur[0].clone() - dom_nf.clone()));
        builder.assert_zero(ni.clone() * (cur[1].clone() - cur[NK].clone()));
        builder.assert_zero(ni.clone() * (cur[2].clone() - cur[RHO].clone()));
        builder.assert_zero(ni.clone() * (cur[3].clone() - cur[POSACC].clone()));
        for i in 4..8 {
            builder.assert_zero(ni.clone() * cur[i].clone());
        }
        // ---- nullifier output: per-input public nf_i ----
        for i in 0..N_IN {
            let sel = p[P_NULLOUT + i].clone();
            for k in 0..DIGEST {
                builder.assert_zero(sel.clone() * (cur[k].clone() - pis[PI_NF + i * DIGEST + k].clone()));
            }
        }

        // ---- output-commitment input: [DOM_CM, out_recipient(free), out_value, out_rho/rcm(free)] ----
        let oi = p[P_OUT_IN].clone();
        builder.assert_zero(oi.clone() * (cur[0].clone() - dom_cm.clone()));
        builder.assert_zero(oi.clone() * (cur[1 + DIGEST].clone() - cur[VAL].clone())); // out_value (lane 5)
        // ---- output-commitment output: per-output public out_cm_j ----
        for j in 0..M_OUT {
            let sel = p[P_OUTOUT + j].clone();
            for k in 0..DIGEST {
                builder.assert_zero(sel.clone() * (cur[k].clone() - pis[PI_OUTCM + j * DIGEST + k].clone()));
            }
        }

        // ---- fee region: VAL = public fee (range-checked like any value; A3) ----
        builder.assert_zero(p[P_FEE_IN].clone() * (cur[VAL].clone() - pis[PI_FEE].clone()));

        // tx_binding (pis[PI_TXBIND..]) is bound to the proof by Fiat–Shamir (observed public input).
    }
}

// --- trace + ZK config (stage 1) --------------------------------------------------------------

type Perm = Poseidon2Goldilocks<8>;
type MyHash = PaddingFreeSponge<Perm, 8, 4, 4>;
type MyCompress = TruncatedPermutation<Perm, 2, 4, 8>;
type ValMmcs =
    MerkleTreeHidingMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, SmallRng, 2, 4, 4>;
type Challenge = BinomialExtensionField<Val, 2>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Challenger = DuplexChallenger<Val, Perm, 8, 4>;
type Dft = Radix2DitParallel<Val>;
type Pcs = HidingFriPcs<Val, Dft, ValMmcs, ChallengeMmcs, SmallRng>;
type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;

fn make_config(seed: u64) -> MyConfig {
    let perm = default_goldilocks_poseidon2_8();
    // production FRI parameters (C-04): ≈103-bit proven / ~127-bit conjectured, smallest-encoding.
    let val_mmcs = ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), 6, SmallRng::seed_from_u64(seed));
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let fri = FriParameters {
        log_blowup: 4,
        log_final_poly_len: 0,
        max_log_arity: 4,
        num_queries: 96,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 16,
        mmcs: challenge_mmcs,
    };
    let pcs = Pcs::new(Dft::default(), val_mmcs, fri, 4, SmallRng::seed_from_u64(seed));
    MyConfig::new(pcs, Challenger::new(perm))
}

fn set_block(t: &mut [Val], block: usize, input: [Val; 8]) {
    let rows = native_steps(input);
    for (r, row) in rows.iter().enumerate() {
        let base = (block * BLOCK + r) * WIDTH;
        t[base..base + 8].copy_from_slice(row);
    }
}

/// Range-decompose `value` into the running-remainder columns starting at row `seed`.
fn fill_range(t: &mut [Val], seed: usize, value: u64) {
    let mut rem = value;
    for k in 0..=BITS {
        t[(seed + k) * WIDTH + REM] = Val::from_u64(rem);
        if k < BITS {
            t[(seed + k) * WIDTH + RBIT] = Val::from_u64(rem & 1);
            rem >>= 1;
        }
    }
}

/// Set a local-persistent column to `v` across `[lo, hi]`.
fn fill_col(t: &mut [Val], lo: usize, hi: usize, col: usize, v: Val) {
    for r in lo..=hi {
        t[r * WIDTH + col] = v;
    }
}

fn build_trace(w: &Witness) -> RowMajorMatrix<Val> {
    let mut t = vec![Val::ZERO; HEIGHT * WIDTH];

    // --- inputs: ownership, commitment, membership, nullifier (+ local-persistent + pos_acc) ---
    for (i, inp) in w.inputs.iter().enumerate() {
        let nk = Val::from_u64(inp.nk);
        let value = Val::from_u64(inp.value);
        let base = input_base(i);
        let mut own = [Val::ZERO; 8];
        own[0] = Val::from_u64(DOM_OWN);
        own[1] = nk;
        set_block(&mut t, base, own);
        let recipient = recipient_of(nk);
        let mut cin = [Val::ZERO; 8];
        cin[0] = Val::from_u64(DOM_CM);
        cin[1..1 + DIGEST].copy_from_slice(&recipient);
        cin[1 + DIGEST] = value;
        cin[1 + DIGEST + 1] = inp.rho;
        cin[1 + DIGEST + 2] = inp.rcm;
        set_block(&mut t, base + 1, cin);
        let mut node = commit(recipient, value, inp.rho, inp.rcm);
        for d in 0..DEPTH {
            let (l, r) = if inp.bits[d] { (inp.sib[d], node) } else { (node, inp.sib[d]) };
            let mut min = [Val::ZERO; 8];
            min[..DIGEST].copy_from_slice(&l);
            min[DIGEST..].copy_from_slice(&r);
            set_block(&mut t, base + 2 + d, min);
            t[((base + 2 + d) * BLOCK) * WIDTH + BIT] = if inp.bits[d] { Val::ONE } else { Val::ZERO };
            node = merge(l, r);
        }
        // nullifier block: [DOM_NF, nk, rho, pos, 0,0,0,0]
        let pos = pos_of(&inp.bits);
        let mut nin = [Val::ZERO; 8];
        nin[0] = Val::from_u64(DOM_NF);
        nin[1] = nk;
        nin[2] = inp.rho;
        nin[3] = pos;
        set_block(&mut t, null_block(i), nin);
        // local-persistent nk/rho/value across the span
        let (lo, hi) = (own_in_row(i), null_out_row(i));
        fill_col(&mut t, lo, hi, NK, nk);
        fill_col(&mut t, lo, hi, RHO, inp.rho);
        fill_col(&mut t, lo, hi, VAL, value);
        // pos_acc: cumulative Σ bit_d·2^d (jumps after each link row)
        let mut acc = 0u64;
        let mut links: Vec<(usize, u64)> = Vec::new();
        for d in 0..DEPTH {
            links.push(((base + 1 + d) * BLOCK + BLOCK - 1, if inp.bits[d] { 1u64 << d } else { 0 }));
        }
        for r in lo..=hi {
            t[r * WIDTH + POSACC] = Val::from_u64(acc);
            for (lr, add) in &links {
                if *lr == r {
                    acc += add;
                }
            }
        }
        // range-check the input value (window starts at the commit input row)
        fill_range(&mut t, commit_in_row(i), inp.value);
    }

    // --- outputs: commitment block + value range ---
    for (j, out) in w.outputs.iter().enumerate() {
        let mut oin = [Val::ZERO; 8];
        oin[0] = Val::from_u64(DOM_CM);
        oin[1..1 + DIGEST].copy_from_slice(&out.recipient);
        oin[1 + DIGEST] = Val::from_u64(out.value);
        oin[1 + DIGEST + 1] = out.rho;
        oin[1 + DIGEST + 2] = out.rcm;
        set_block(&mut t, out_base(j), oin);
        set_block(&mut t, out_base(j) + 1, [Val::ZERO; 8]); // range-overflow block (dummy perm)
        let (lo, hi) = (out_in_row(j), out_in_row(j) + OUT_BLOCKS * BLOCK - 1);
        fill_col(&mut t, lo, hi, VAL, Val::from_u64(out.value));
        fill_range(&mut t, out_in_row(j), out.value);
    }

    // --- fee region: VAL = fee, range-checked (A3) ---
    set_block(&mut t, fee_base(), [Val::ZERO; 8]);
    set_block(&mut t, fee_base() + 1, [Val::ZERO; 8]);
    let (flo, fhi) = (fee_in_row(), fee_in_row() + FEE_BLOCKS * BLOCK - 1);
    fill_col(&mut t, flo, fhi, VAL, Val::from_u64(w.fee));
    fill_range(&mut t, fee_in_row(), w.fee);

    // --- padding blocks: valid permutations of zero ---
    for b in USED_BLOCKS..NUM_BLOCKS {
        set_block(&mut t, b, [Val::ZERO; 8]);
    }

    // --- global value accumulator: +in at each commit, −out at each output, −fee ⇒ 0 ---
    let mut delta = vec![0i128; HEIGHT];
    for (i, inp) in w.inputs.iter().enumerate() {
        delta[commit_in_row(i)] += inp.value as i128;
    }
    for (j, out) in w.outputs.iter().enumerate() {
        delta[out_in_row(j)] -= out.value as i128;
    }
    delta[fee_in_row()] -= w.fee as i128;
    let mut acc: i128 = 0;
    for r in 0..HEIGHT {
        t[r * WIDTH + VALACC] = if acc >= 0 {
            Val::from_u64(acc as u64)
        } else {
            -Val::from_u64((-acc) as u64)
        };
        acc += delta[r];
    }
    RowMajorMatrix::new(t, WIDTH)
}

/// The circuit's public inputs: `anchor ‖ nf_i ‖ out_cm_j ‖ fee ‖ tx_binding`.
pub fn public_values(w: &Witness) -> Vec<Val> {
    let o = native_outputs(w);
    let mut pis = vec![Val::ZERO; N_PUBLIC];
    pis[PI_ANCHOR..PI_ANCHOR + DIGEST].copy_from_slice(&o.anchor);
    for i in 0..N_IN {
        pis[PI_NF + i * DIGEST..PI_NF + (i + 1) * DIGEST].copy_from_slice(&o.nullifiers[i]);
    }
    for j in 0..M_OUT {
        pis[PI_OUTCM + j * DIGEST..PI_OUTCM + (j + 1) * DIGEST].copy_from_slice(&o.out_cms[j]);
    }
    pis[PI_FEE] = Val::from_u64(w.fee);
    pis[PI_TXBIND..PI_TXBIND + DIGEST].copy_from_slice(&w.tx_binding);
    pis
}

pub fn prove_verify_with(w: &Witness, pis: &[Val]) -> Result<(), String> {
    let config = make_config(1);
    let air = JoinSplitAir;
    let trace = build_trace(w);
    let proof = prove(&config, &air, trace, pis);
    verify(&config, &air, &proof, pis).map_err(|e| format!("{e:?}"))
}

pub fn prove_verify(w: &Witness) -> Result<(), String> {
    prove_verify_with(w, &public_values(w))
}

/// Prove with the witness's real public inputs, verify against `verify_pis` (tests FS binding).
#[allow(dead_code)]
pub fn prove_real_verify_with(w: &Witness, verify_pis: &[Val]) -> Result<(), String> {
    let config = make_config(1);
    let air = JoinSplitAir;
    let trace = build_trace(w);
    let proof = prove(&config, &air, trace, &public_values(w));
    verify(&config, &air, &proof, verify_pis).map_err(|e| format!("{e:?}"))
}

// --- sparse Merkle test helper: N leaves at positions 0..N (leftmost), shared anchor -----------

#[cfg(test)]
pub(crate) fn empty_hashes() -> [[Val; DIGEST]; DEPTH] {
    let mut e = [[Val::ZERO; DIGEST]; DEPTH];
    for d in 1..DEPTH {
        e[d] = merge(e[d - 1], e[d - 1]);
    }
    e
}

/// Build a tree holding `leaves` at positions 0..leaves.len() (a power of two) in the leftmost
/// subtree, the rest empty. Returns the anchor and each leaf's (sib, bits) authentication path.
#[cfg(test)]
pub(crate) fn build_paths(
    leaves: &[[Val; DIGEST]],
) -> ([Val; DIGEST], Vec<([[Val; DIGEST]; DEPTH], [bool; DEPTH])>) {
    let n = leaves.len();
    assert!(n.is_power_of_two());
    let k = n.trailing_zeros() as usize; // explicit subtree depth
    let e = empty_hashes();

    // explicit levels 0..=k over the n leaves
    let mut levels: Vec<Vec<[Val; DIGEST]>> = vec![leaves.to_vec()];
    for d in 0..k {
        let cur = &levels[d];
        let next: Vec<[Val; DIGEST]> = (0..cur.len() / 2).map(|i| merge(cur[2 * i], cur[2 * i + 1])).collect();
        levels.push(next);
    }
    let subtree_root = levels[k][0];

    // anchor: fold subtree_root with empty siblings up to DEPTH (subtree is the left child all the way)
    let mut node = subtree_root;
    for d in k..DEPTH {
        node = merge(node, e[d]);
    }
    let anchor = node;

    // per-leaf path
    let mut paths = Vec::with_capacity(n);
    for p in 0..n {
        let mut sib = [[Val::ZERO; DIGEST]; DEPTH];
        let mut bits = [false; DEPTH];
        for d in 0..k {
            let idx = p >> d;
            sib[d] = levels[d][idx ^ 1];
            bits[d] = (idx & 1) == 1;
        }
        for d in k..DEPTH {
            sib[d] = e[d];
            bits[d] = false; // subtree is the left child above level k
        }
        paths.push((sib, bits));
    }
    (anchor, paths)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A valid 2-in/2-out witness whose two input commitments sit at positions 0 and 1 of a shared
    /// tree, balanced so Σin = Σout + fee.
    pub(crate) fn sample() -> Witness {
        let in0 = (1000u64, 7u64, 11u64, 100u64); // value, nk, rho, rcm
        let in1 = (500u64, 9u64, 13u64, 101u64);
        let cm0 = commit(recipient_of(Val::from_u64(in0.1)), Val::from_u64(in0.0), Val::from_u64(in0.2), Val::from_u64(in0.3));
        let cm1 = commit(recipient_of(Val::from_u64(in1.1)), Val::from_u64(in1.0), Val::from_u64(in1.2), Val::from_u64(in1.3));
        let (_, paths) = build_paths(&[cm0, cm1]);
        let mk_in = |v: (u64, u64, u64, u64), pth: &([[Val; DIGEST]; DEPTH], [bool; DEPTH])| Input {
            nk: v.1,
            value: v.0,
            rho: Val::from_u64(v.2),
            rcm: Val::from_u64(v.3),
            sib: pth.0,
            bits: pth.1,
        };
        let inputs = [mk_in(in0, &paths[0]), mk_in(in1, &paths[1])];
        let outputs = [
            Output { recipient: recipient_of(Val::from_u64(77)), value: 900, rho: Val::from_u64(21), rcm: Val::from_u64(22) },
            Output { recipient: recipient_of(Val::from_u64(88)), value: 500, rho: Val::from_u64(23), rcm: Val::from_u64(24) },
        ];
        // Σin = 1500, Σout = 1400, fee = 100
        Witness { inputs, outputs, fee: 100, tx_binding: core::array::from_fn(|i| Val::from_u64(0xABCD + i as u64)) }
    }

    #[test]
    fn native_relation_holds() {
        let o = native_outputs(&sample());
        // both inputs fold to the same anchor (assert inside native_outputs); nullifiers distinct
        assert_ne!(o.nullifiers[0], o.nullifiers[1]);
        assert_ne!(o.out_cms[0], o.out_cms[1]);
    }

    #[test]
    fn domain_separation_distinguishes_hashes() {
        // same field inputs, different domains ⇒ different digests (A2)
        let x = Val::from_u64(42);
        assert_ne!(h(DOM_OWN, &[x]), h(DOM_NF, &[x]));
        assert_ne!(h(DOM_CM, &[x]), h(DOM_NF, &[x]));
        assert_ne!(h(DOM_OWN, &[x]), h(DOM_CM, &[x]));
    }

    #[test]
    fn pos_matches_path_bits() {
        // pos = Σ bits·2^d (A1)
        let mut bits = [false; DEPTH];
        bits[0] = true;
        bits[3] = true; // pos = 1 + 8 = 9
        assert_eq!(pos_of(&bits), Val::from_u64(9));
    }

    #[test]
    #[should_panic(expected = "value balance")]
    fn unbalanced_witness_panics() {
        let mut w = sample();
        w.fee = 101; // 1500 != 1400 + 101
        native_outputs(&w);
    }

    /// Build a balanced witness with the given input/output values + fee (computes Merkle paths).
    fn witness_with(in_values: [u64; N_IN], out_values: [u64; M_OUT], fee: u64) -> Witness {
        let cms: Vec<[Val; DIGEST]> = (0..N_IN)
            .map(|i| {
                commit(
                    recipient_of(Val::from_u64(7 + i as u64)),
                    Val::from_u64(in_values[i]),
                    Val::from_u64(11 + i as u64),
                    Val::from_u64(100 + i as u64),
                )
            })
            .collect();
        let (_, paths) = build_paths(&cms);
        let inputs = core::array::from_fn(|i| Input {
            nk: 7 + i as u64,
            value: in_values[i],
            rho: Val::from_u64(11 + i as u64),
            rcm: Val::from_u64(100 + i as u64),
            sib: paths[i].0,
            bits: paths[i].1,
        });
        let outputs = core::array::from_fn(|j| Output {
            recipient: recipient_of(Val::from_u64(77 + j as u64)),
            value: out_values[j],
            rho: Val::from_u64(21 + j as u64),
            rcm: Val::from_u64(22 + j as u64),
        });
        Witness { inputs, outputs, fee, tx_binding: core::array::from_fn(|i| Val::from_u64(0xABCD + i as u64)) }
    }

    #[test]
    fn joinsplit_verifies() {
        prove_verify(&witness_with([1000, 500], [900, 500], 100)).expect("valid join-split should verify");
    }

    #[test]
    fn wrong_anchor_rejected() {
        let w = witness_with([1000, 500], [900, 500], 100);
        let mut pis = public_values(&w);
        pis[PI_ANCHOR] += Val::ONE;
        assert!(prove_verify_with(&w, &pis).is_err());
    }

    #[test]
    fn wrong_nullifier_rejected() {
        let w = witness_with([1000, 500], [900, 500], 100);
        let mut pis = public_values(&w);
        pis[PI_NF + DIGEST] += Val::ONE; // tamper input 1's nullifier
        assert!(prove_verify_with(&w, &pis).is_err());
    }

    #[test]
    fn wrong_out_cm_rejected() {
        let w = witness_with([1000, 500], [900, 500], 100);
        let mut pis = public_values(&w);
        pis[PI_OUTCM] += Val::ONE;
        assert!(prove_verify_with(&w, &pis).is_err());
    }

    #[test]
    fn wrong_fee_rejected() {
        let w = witness_with([1000, 500], [900, 500], 100);
        let mut pis = public_values(&w);
        pis[PI_FEE] += Val::ONE; // fee region binds VAL == public fee
        assert!(prove_verify_with(&w, &pis).is_err());
    }

    #[test]
    fn out_of_range_value_rejected() {
        // input 0 value ≥ 2^BITS; fee chosen so the balance still holds ⇒ only range fails.
        let big = 1u64 << 53;
        let w = witness_with([big, 500], [900, 500], big + 500 - 1400);
        assert!(prove_verify(&w).is_err());
    }

    #[test]
    fn wrong_tx_binding_rejected() {
        let w = witness_with([1000, 500], [900, 500], 100);
        let mut pis = public_values(&w);
        pis[PI_TXBIND] += Val::ONE; // Fiat–Shamir binds the proof to the tx
        assert!(prove_real_verify_with(&w, &pis).is_err());
    }

    #[test]
    fn distinct_positions_give_distinct_nullifiers() {
        // same note key/rho at different positions ⇒ different nullifiers (A1 prevents replay)
        let nk = Val::from_u64(5);
        let rho = Val::from_u64(6);
        let mut b0 = [false; DEPTH];
        let mut b1 = [false; DEPTH];
        b1[0] = true;
        assert_ne!(nullifier(nk, rho, pos_of(&b0)), nullifier(nk, rho, pos_of(&b1)));
        let _ = &mut b0;
    }
}
