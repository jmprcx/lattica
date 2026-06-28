//! Join-split (N-in / M-out) spend circuit — the single production circuit (the audit target), with
//! the soundness fixes baked in (A1 position-consistency, A2 domain separation, A3 value/fee/mint
//! range-checks; 128-bit spend authority).
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
use p3_air::symbolic::AirLayout;
use p3_uni_stark::{prove, verify, Proof, ProvenSecurity, StarkConfig, StarkSecurityParams};
use rand_chacha::ChaCha20Rng;
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

/// Diversified ownership tag: `recipient = H(DOM_OWN ‖ nk0 ‖ nk1 ‖ d)`. The 128-bit key `nk` is the
/// single spend authority; the diversifier `d` makes per-address tags unlinkable while remaining
/// spendable by the same `nk`. (`d = 0` is a non-diversified address.)
pub fn recipient_of(nk0: Val, nk1: Val, d: Val) -> [Val; DIGEST] {
    h(DOM_OWN, &[nk0, nk1, d])
}

/// Two-permutation (128-bit-randomness) commitment:
///   H1 = perm([DOM_CM, recipient(4), value, rho0, rho1])     (8 lanes, full)
///   cm = perm([H1(4), rcm0, rcm1, 0, 0])                      (Merkle-Damgård chain)
/// rho/rcm are each two field elements ⇒ 128-bit note randomness + hiding (vs 64-bit before). The
/// second block is merge-shaped; the chaining value (256-bit) gives 128-bit collision resistance.
pub fn commit(recipient: [Val; DIGEST], value: Val, rho: [Val; 2], rcm: [Val; 2], asset: Val) -> [Val; DIGEST] {
    let mut a = [Val::ZERO; W];
    a[0] = Val::from_u64(DOM_CM);
    a[1..1 + DIGEST].copy_from_slice(&recipient);
    a[1 + DIGEST] = value;
    a[1 + DIGEST + 1] = rho[0];
    a[1 + DIGEST + 2] = rho[1];
    let chain = native_permute(a);
    let mut b = [Val::ZERO; W];
    b[..DIGEST].copy_from_slice(&chain[..DIGEST]);
    b[DIGEST] = rcm[0];
    b[DIGEST + 1] = rcm[1];
    b[DIGEST + 2] = asset; // lane 6: hidden asset id (lane 7 stays 0, reserved for note_type)
    native_permute(b)[..DIGEST].try_into().unwrap()
}

pub fn nullifier(nk0: Val, nk1: Val, rho: [Val; 2], pos: Val) -> [Val; DIGEST] {
    h(DOM_NF, &[nk0, nk1, rho[0], rho[1], pos])
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
    pub nk: [u64; 2], // 128-bit nullifier key / spend authority
    pub div: Val, // diversifier of the address this note was sent to (recipient = H(nk ‖ div))
    pub asset: Val, // hidden asset id (all notes in a tx share one asset)
    pub value: u64,
    pub rho: [Val; 2], // 128-bit note randomness
    pub rcm: [Val; 2], // 128-bit commitment trapdoor
    pub sib: [[Val; DIGEST]; DEPTH],
    pub bits: [bool; DEPTH],
}

#[derive(Clone, Copy)]
pub struct Output {
    pub recipient: [Val; DIGEST],
    pub asset: Val, // hidden asset id (must equal the inputs' asset)
    pub value: u64,
    pub rho: [Val; 2],
    pub rcm: [Val; 2],
}

#[derive(Clone)]
pub struct Witness {
    pub inputs: [Input; N_IN],
    pub outputs: [Output; M_OUT],
    pub fee: u64,
    pub mint: u64, // public issuance (0 for a normal tx; > 0 for coinbase)
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
    let asset = w.inputs[0].asset; // the single (hidden) asset of this tx
    for (i, inp) in w.inputs.iter().enumerate() {
        assert_eq!(inp.asset, asset, "input {i} uses a different asset (single-asset tx)");
        let (nk0, nk1) = (Val::from_u64(inp.nk[0]), Val::from_u64(inp.nk[1]));
        let recipient = recipient_of(nk0, nk1, inp.div);
        let cm = commit(recipient, Val::from_u64(inp.value), inp.rho, inp.rcm, inp.asset);
        let root = fold(cm, &inp.sib, &inp.bits);
        match anchor {
            None => anchor = Some(root),
            Some(a) => assert_eq!(a, root, "input {i} folds to a different anchor"),
        }
        nullifiers[i] = nullifier(nk0, nk1, inp.rho, pos_of(&inp.bits));
        in_sum += inp.value as u128;
    }
    // per-output commitment
    let mut out_cms = [[Val::ZERO; DIGEST]; M_OUT];
    let mut out_sum: u128 = 0;
    for (j, out) in w.outputs.iter().enumerate() {
        assert_eq!(out.asset, asset, "output {j} uses a different asset (single-asset tx)");
        out_cms[j] = commit(out.recipient, Val::from_u64(out.value), out.rho, out.rcm, out.asset);
        out_sum += out.value as u128;
    }
    // value balance (A3: all values range-bounded ⇒ no wraparound)
    assert_eq!(in_sum + w.mint as u128, out_sum + w.fee as u128, "value balance Σin + mint = Σout + fee");
    PublicOutputs { anchor: anchor.unwrap(), nullifiers, out_cms }
}

// ==============================================================================================
// AIR — stage 1: multi-input membership to a shared anchor (domain-tagged ownership + commitment).
// Later stages add nullifiers (A1 pos-binding), accumulator balance + range (A3), outputs, and the
// per-instance public bindings. Built incrementally; each stage differential-tested vs the oracle.
// ==============================================================================================

const SPAN_BLOCKS: usize = 4 + DEPTH; // ownership, commit_a, commit_b, DEPTH merges, nullifier
const OUT_BLOCKS: usize = 2; // out_cm perm_a + perm_b (2-permutation commitment; also 64 rows for the value range)
const FEE_BLOCKS: usize = 2; // fee binding + range
const MINT_BLOCKS: usize = 2; // mint (issuance) binding + range
const USED_BLOCKS: usize = N_IN * SPAN_BLOCKS + M_OUT * OUT_BLOCKS + FEE_BLOCKS + MINT_BLOCKS;
const NUM_BLOCKS: usize = USED_BLOCKS.next_power_of_two();
const HEIGHT: usize = NUM_BLOCKS * BLOCK;

// columns
const BIT: usize = 8; // membership position bit
const NK: usize = 9; // local-persistent within an input span
const RHO: usize = 10; // rho limb 0 (local-persistent)
const VAL: usize = 11; // value within input / output / fee / mint region
const POSACC: usize = 12; // Σ bit_d·2^d within an input's membership (A1)
const VALACC: usize = 13; // global balance accumulator: +in +mint −out −fee ⇒ 0
const REM: usize = 14; // range running remainder
const RBIT: usize = 15;
const NK1: usize = 16; // second limb of the 128-bit nullifier key (NK = limb 0)
const RHO1: usize = 17; // rho limb 1 (local-persistent; 128-bit note randomness)
const ASSET: usize = 18; // hidden asset id — GLOBAL-persistent (constant across the whole tx)
const WIDTH: usize = 19;

// periodic-column indices: 0..11 round schedule (period 32), then fixed (length HEIGHT) selectors.
// The commitment is two permutations (commit_a -> chain -> commit_b -> cm); outputs likewise.
const P_OWN_IN: usize = 11;
const P_RECIP_LINK: usize = 12; // own.out -> commit_a.in recipient lanes
const P_COMMIT_A_IN: usize = 13; // input commit_a: DOM_CM, value, rho0, rho1
const P_CHAIN_LINK: usize = 14; // commit_a.out -> commit_b.in[0..4] (input & output commitments)
const P_COMMIT_B: usize = 15; // commit_b.in pad lanes = 0 (input & output commitments)
const P_MEM_LINK: usize = 16;
const P_POS_COEFF: usize = 17; // 2^d at each membership link
const P_ROOT: usize = 18;
const P_NULL_IN: usize = 19;
const P_OUT_A_IN: usize = 20; // output out_a: DOM_CM, out_value
const P_FEE_IN: usize = 21;
const P_MINT_IN: usize = 22; // issuance amount binding row
const P_REGION_LAST: usize = 23; // last row of each region (gates local-persistent columns)
const P_RANGE_SEED: usize = 24; // rem = VAL (each value's first range row)
const P_RANGE_ACTIVE: usize = 25; // decomposition rows
const P_RANGE_CLOSE: usize = 26; // rem = 0 (value < 2^BITS)
const P_ROW0: usize = 27; // VALACC = 0
const P_FINAL: usize = 28; // VALACC = 0 (balance)
const P_NULLOUT: usize = 29; // N_IN one-hots: nf_i binding
const P_OUTOUT: usize = 29 + N_IN; // M_OUT one-hots: out_cm_j binding
const N_PERIODIC: usize = 29 + N_IN + M_OUT;

// public inputs: anchor(4) ‖ nf_i(4·N) ‖ out_cm_j(4·M) ‖ fee(1) ‖ mint(1) ‖ tx_binding(4)
const PI_ANCHOR: usize = 0;
const PI_NF: usize = 4;
const PI_OUTCM: usize = 4 + N_IN * DIGEST;
const PI_FEE: usize = 4 + N_IN * DIGEST + M_OUT * DIGEST;
const PI_MINT: usize = PI_FEE + 1;
const PI_TXBIND: usize = PI_MINT + 1;
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
const fn commit_a_in_row(i: usize) -> usize {
    (input_base(i) + 1) * BLOCK
}
const fn commit_a_out_row(i: usize) -> usize {
    (input_base(i) + 1) * BLOCK + BLOCK - 1
}
const fn commit_b_in_row(i: usize) -> usize {
    (input_base(i) + 2) * BLOCK
}
const fn root_row(i: usize) -> usize {
    (input_base(i) + 2 + DEPTH) * BLOCK + BLOCK - 1
}
const fn null_block(i: usize) -> usize {
    input_base(i) + 3 + DEPTH
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
    out_base(j) * BLOCK // out_a input (DOM_CM, recipient, value, rho0, rho1); value-range seed
}
const fn out_a_out_row(j: usize) -> usize {
    out_base(j) * BLOCK + BLOCK - 1
}
const fn out_b_in_row(j: usize) -> usize {
    (out_base(j) + 1) * BLOCK
}
const fn out_out_row(j: usize) -> usize {
    (out_base(j) + 1) * BLOCK + BLOCK - 1 // out_b output = public out_cm_j
}
const fn fee_base() -> usize {
    N_IN * SPAN_BLOCKS + M_OUT * OUT_BLOCKS
}
const fn fee_in_row() -> usize {
    fee_base() * BLOCK
}
const fn mint_base() -> usize {
    fee_base() + FEE_BLOCKS
}
const fn mint_in_row() -> usize {
    mint_base() * BLOCK
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
    let recip: Vec<usize> = (0..N_IN).map(own_out_row).collect(); // own output → commit_a recipient
    let commit_a_in: Vec<usize> = (0..N_IN).map(commit_a_in_row).collect();
    // chain links: commit_a.out → commit_b.in (inputs) and out_a.out → out_b.in (outputs)
    let mut chain_link: Vec<usize> = (0..N_IN).map(commit_a_out_row).collect();
    chain_link.extend((0..M_OUT).map(out_a_out_row));
    // commit_b input rows (inputs & outputs): the pad lanes (6,7) are constrained to 0
    let mut commit_b: Vec<usize> = (0..N_IN).map(commit_b_in_row).collect();
    commit_b.extend((0..M_OUT).map(out_b_in_row));
    // membership links + the 2^d position coefficient at each link (A1). Leaf = commit_b output.
    let mut mem: Vec<usize> = Vec::new();
    let mut pos_coeff = vec![Val::ZERO; HEIGHT];
    for i in 0..N_IN {
        for d in 0..DEPTH {
            let row = (input_base(i) + 2 + d) * BLOCK + BLOCK - 1;
            mem.push(row);
            pos_coeff[row] = Val::from_u64(1u64 << d);
        }
    }
    let root: Vec<usize> = (0..N_IN).map(root_row).collect();
    let null_in: Vec<usize> = (0..N_IN).map(null_in_row).collect();
    let out_a_in: Vec<usize> = (0..M_OUT).map(out_in_row).collect();
    // region-last rows (gate local-persistent columns at region boundaries)
    let mut region_last: Vec<usize> = (0..N_IN).map(null_out_row).collect();
    region_last.extend((0..M_OUT).map(|j| out_in_row(j) + OUT_BLOCKS * BLOCK - 1));
    region_last.push(fee_in_row() + FEE_BLOCKS * BLOCK - 1);
    region_last.push(mint_in_row() + MINT_BLOCKS * BLOCK - 1);
    // range windows: one per value (each input value at commit_a, output value at out_a, fee, mint)
    let mut seeds: Vec<usize> = (0..N_IN).map(commit_a_in_row).collect();
    seeds.extend((0..M_OUT).map(out_in_row));
    seeds.push(fee_in_row());
    seeds.push(mint_in_row());
    let mut range_active: Vec<usize> = Vec::new();
    let mut range_close: Vec<usize> = Vec::new();
    for &s in &seeds {
        range_active.extend(s..s + BITS);
        range_close.push(s + BITS);
    }

    cols.push(one_hot(&own_in)); // P_OWN_IN
    cols.push(one_hot(&recip)); // P_RECIP_LINK
    cols.push(one_hot(&commit_a_in)); // P_COMMIT_A_IN
    cols.push(one_hot(&chain_link)); // P_CHAIN_LINK
    cols.push(one_hot(&commit_b)); // P_COMMIT_B
    cols.push(one_hot(&mem)); // P_MEM_LINK
    cols.push(pos_coeff); // P_POS_COEFF
    cols.push(one_hot(&root)); // P_ROOT
    cols.push(one_hot(&null_in)); // P_NULL_IN
    cols.push(one_hot(&out_a_in)); // P_OUT_A_IN
    cols.push(one_hot(&[fee_in_row()])); // P_FEE_IN
    cols.push(one_hot(&[mint_in_row()])); // P_MINT_IN
    cols.push(one_hot(&region_last)); // P_REGION_LAST
    cols.push(one_hot(&seeds)); // P_RANGE_SEED
    cols.push(one_hot(&range_active)); // P_RANGE_ACTIVE
    cols.push(one_hot(&range_close)); // P_RANGE_CLOSE
    cols.push(one_hot(&[0])); // P_ROW0
    cols.push(one_hot(&[mint_in_row() + MINT_BLOCKS * BLOCK - 1])); // P_FINAL (after mint contribution)
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
        // RHO1 MUST be here: it is read at both commit_a (lane 7) and the nullifier (lane 4); without
        // persistence a prover could use one rho1 in the commitment and another in the nullifier,
        // minting a fresh nullifier for a real note ⇒ double-spend.
        let not_last = one.clone() - p[P_REGION_LAST].clone();
        for &c in &[NK, NK1, RHO, RHO1, VAL] {
            builder.when_transition().assert_zero(not_last.clone() * (nxt[c].clone() - cur[c].clone()));
        }
        // ASSET is GLOBAL-persistent: constant across the whole trace (one hidden asset per tx), so
        // every note's committed asset (bound at commit_b below) equals this single value.
        builder.when_transition().assert_zero(nxt[ASSET].clone() - cur[ASSET].clone());
        // pos_acc: += bit·2^d at membership links, else constant within the span (A1)
        let bit = nxt[BIT].clone();
        builder.when_transition().assert_zero(
            not_last.clone()
                * (nxt[POSACC].clone() - cur[POSACC].clone() - p[P_MEM_LINK].clone() * (bit.clone() * p[P_POS_COEFF].clone())),
        );
        builder.assert_zero(p[P_OWN_IN].clone() * cur[POSACC].clone()); // reset to 0 at span start

        // ---- global value accumulator: +in (commit), −out, −fee ⇒ 0 ----
        builder.assert_zero(p[P_ROW0].clone() * cur[VALACC].clone());
        let acc_delta = (p[P_COMMIT_A_IN].clone() + p[P_MINT_IN].clone() - p[P_OUT_A_IN].clone() - p[P_FEE_IN].clone())
            * cur[VAL].clone();
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

        // ---- ownership input: [DOM_OWN, nk0, nk1, d, 0,0,0,0] ----
        // `d` (lane 3) is the diversifier — a FREE input: the spender uses the note's actual
        // diversifier (else the recomputed recipient → cm won't be in the tree), so no extra
        // constraint is needed (matching someone else's tag is a 2^128 preimage). recipient = H(DOM_OWN
        // ‖ nk0 ‖ nk1 ‖ d).
        let own = p[P_OWN_IN].clone();
        builder.assert_zero(own.clone() * (cur[0].clone() - dom_own.clone()));
        builder.assert_zero(own.clone() * (cur[1].clone() - cur[NK].clone()));
        builder.assert_zero(own.clone() * (cur[2].clone() - cur[NK1].clone()));
        for i in 4..8 {
            builder.assert_zero(own.clone() * cur[i].clone());
        }

        // ---- recipient link: commit.in[1..5] = own.out[0..4] ----
        let rl = p[P_RECIP_LINK].clone();
        for k in 0..DIGEST {
            builder.when_transition().assert_zero(rl.clone() * (nxt[1 + k].clone() - cur[k].clone()));
        }

        // ---- commit_a input: [DOM_CM, recipient(link), value, rho0, rho1] ----
        let ca = p[P_COMMIT_A_IN].clone();
        builder.assert_zero(ca.clone() * (cur[0].clone() - dom_cm.clone()));
        builder.assert_zero(ca.clone() * (cur[1 + DIGEST].clone() - cur[VAL].clone())); // value (lane 5)
        builder.assert_zero(ca.clone() * (cur[2 + DIGEST].clone() - cur[RHO].clone())); // rho0  (lane 6)
        builder.assert_zero(ca.clone() * (cur[3 + DIGEST].clone() - cur[RHO1].clone())); // rho1 (lane 7)

        // ---- chain link: commit_b.in[0..4] = commit_a.out[0..4] (also out_b ← out_a) ----
        let cl = p[P_CHAIN_LINK].clone();
        for k in 0..DIGEST {
            builder.when_transition().assert_zero(cl.clone() * (nxt[k].clone() - cur[k].clone()));
        }

        // ---- commit_b input: [chain(4), rcm0, rcm1, 0, 0] — pad lanes 6,7 pinned to 0 (rcm free) ----
        let cb = p[P_COMMIT_B].clone();
        builder.assert_zero(cb.clone() * (cur[DIGEST + 2].clone() - cur[ASSET].clone())); // lane 6 = hidden asset id
        builder.assert_zero(cb.clone() * cur[DIGEST + 3].clone()); // lane 7 = 0 (reserved)

        // ---- membership links: place running digest (= commit_b output) by the bit ----
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

        // ---- nullifier input: [DOM_NF, nk0, nk1, rho0, rho1, pos_acc, 0, 0] (A1: pos = pos_acc) ----
        let ni = p[P_NULL_IN].clone();
        builder.assert_zero(ni.clone() * (cur[0].clone() - dom_nf.clone()));
        builder.assert_zero(ni.clone() * (cur[1].clone() - cur[NK].clone()));
        builder.assert_zero(ni.clone() * (cur[2].clone() - cur[NK1].clone()));
        builder.assert_zero(ni.clone() * (cur[3].clone() - cur[RHO].clone()));
        builder.assert_zero(ni.clone() * (cur[4].clone() - cur[RHO1].clone()));
        builder.assert_zero(ni.clone() * (cur[5].clone() - cur[POSACC].clone()));
        for i in 6..8 {
            builder.assert_zero(ni.clone() * cur[i].clone());
        }
        // ---- nullifier output: per-input public nf_i ----
        for i in 0..N_IN {
            let sel = p[P_NULLOUT + i].clone();
            for k in 0..DIGEST {
                builder.assert_zero(sel.clone() * (cur[k].clone() - pis[PI_NF + i * DIGEST + k].clone()));
            }
        }

        // ---- output commit_a: [DOM_CM, out_recipient(free), out_value, out_rho0/1(free)] ----
        // (out_b chain-link + pad lanes are covered by P_CHAIN_LINK / P_COMMIT_B above.)
        let oa = p[P_OUT_A_IN].clone();
        builder.assert_zero(oa.clone() * (cur[0].clone() - dom_cm.clone()));
        builder.assert_zero(oa.clone() * (cur[1 + DIGEST].clone() - cur[VAL].clone())); // out_value (lane 5)
        // ---- output-commitment output (out_b): per-output public out_cm_j ----
        for j in 0..M_OUT {
            let sel = p[P_OUTOUT + j].clone();
            for k in 0..DIGEST {
                builder.assert_zero(sel.clone() * (cur[k].clone() - pis[PI_OUTCM + j * DIGEST + k].clone()));
            }
        }

        // ---- fee region: VAL = public fee (range-checked like any value; A3) ----
        builder.assert_zero(p[P_FEE_IN].clone() * (cur[VAL].clone() - pis[PI_FEE].clone()));

        // ---- mint region: VAL = public mint (issuance; range-checked; added to the balance) ----
        builder.assert_zero(p[P_MINT_IN].clone() * (cur[VAL].clone() - pis[PI_MINT].clone()));

        // tx_binding (pis[PI_TXBIND..]) is bound to the proof by Fiat–Shamir (observed public input).
    }
}

// --- trace + ZK config (stage 1) --------------------------------------------------------------

type Perm = Poseidon2Goldilocks<8>;
type MyHash = PaddingFreeSponge<Perm, 8, 4, 4>;
type MyCompress = TruncatedPermutation<Perm, 2, 4, 8>;
type ValMmcs =
    MerkleTreeHidingMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, ChaCha20Rng, 2, 4, 4>;
type Challenge = BinomialExtensionField<Val, 2>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Challenger = DuplexChallenger<Val, Perm, 8, 4>;
type Dft = Radix2DitParallel<Val>;
type Pcs = HidingFriPcs<Val, Dft, ValMmcs, ChallengeMmcs, ChaCha20Rng>;
type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;

fn make_config() -> MyConfig {
    let perm = default_goldilocks_poseidon2_8();
    // The hiding-PCS / Merkle-salt RNG must be a CSPRNG seeded from fresh OS entropy **per proof** —
    // otherwise the zero-knowledge blinding is predictable/identical across proofs and the witness is
    // not actually hidden. ChaCha20Rng is ChaCha-based; `from_os_rng` reseeds each call.
    let val_mmcs = ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), 6, ChaCha20Rng::from_rng(&mut rand::rng()));
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    // production FRI parameters (C-04): ≈103-bit proven / ~127-bit conjectured, smallest-encoding.
    let fri = FriParameters {
        log_blowup: 4,
        log_final_poly_len: 0,
        max_log_arity: 4,
        num_queries: 96,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 16,
        mmcs: challenge_mmcs,
    };
    let pcs = Pcs::new(Dft::default(), val_mmcs, fri, 4, ChaCha20Rng::from_rng(&mut rand::rng()));
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

    // ASSET is global-persistent (one hidden asset id for the whole tx); fill it on every row.
    fill_col(&mut t, 0, HEIGHT - 1, ASSET, w.inputs[0].asset);

    // --- inputs: ownership, commitment, membership, nullifier (+ local-persistent + pos_acc) ---
    for (i, inp) in w.inputs.iter().enumerate() {
        let (nk0, nk1) = (Val::from_u64(inp.nk[0]), Val::from_u64(inp.nk[1]));
        let value = Val::from_u64(inp.value);
        let base = input_base(i);
        let mut own = [Val::ZERO; 8];
        own[0] = Val::from_u64(DOM_OWN);
        own[1] = nk0;
        own[2] = nk1;
        own[3] = inp.div; // diversifier (free input)
        set_block(&mut t, base, own);
        let recipient = recipient_of(nk0, nk1, inp.div);
        // commit_a: H1 = perm([DOM_CM, recipient(4), value, rho0, rho1]); its digest is the chain.
        let mut a = [Val::ZERO; 8];
        a[0] = Val::from_u64(DOM_CM);
        a[1..1 + DIGEST].copy_from_slice(&recipient);
        a[1 + DIGEST] = value;
        a[1 + DIGEST + 1] = inp.rho[0];
        a[1 + DIGEST + 2] = inp.rho[1];
        set_block(&mut t, base + 1, a);
        let chain = native_permute(a);
        // commit_b: cm = perm([chain(4), rcm0, rcm1, asset, 0]).
        let mut b = [Val::ZERO; 8];
        b[..DIGEST].copy_from_slice(&chain[..DIGEST]);
        b[DIGEST] = inp.rcm[0];
        b[DIGEST + 1] = inp.rcm[1];
        b[DIGEST + 2] = inp.asset;
        set_block(&mut t, base + 2, b);
        let mut node = commit(recipient, value, inp.rho, inp.rcm, inp.asset); // = perm(b)[..DIGEST]
        for d in 0..DEPTH {
            let (l, r) = if inp.bits[d] { (inp.sib[d], node) } else { (node, inp.sib[d]) };
            let mut min = [Val::ZERO; 8];
            min[..DIGEST].copy_from_slice(&l);
            min[DIGEST..].copy_from_slice(&r);
            set_block(&mut t, base + 3 + d, min);
            t[((base + 3 + d) * BLOCK) * WIDTH + BIT] = if inp.bits[d] { Val::ONE } else { Val::ZERO };
            node = merge(l, r);
        }
        // nullifier block: [DOM_NF, nk0, nk1, rho0, rho1, pos, 0, 0]
        let pos = pos_of(&inp.bits);
        let mut nin = [Val::ZERO; 8];
        nin[0] = Val::from_u64(DOM_NF);
        nin[1] = nk0;
        nin[2] = nk1;
        nin[3] = inp.rho[0];
        nin[4] = inp.rho[1];
        nin[5] = pos;
        set_block(&mut t, null_block(i), nin);
        // local-persistent nk/rho/value across the span
        let (lo, hi) = (own_in_row(i), null_out_row(i));
        fill_col(&mut t, lo, hi, NK, nk0);
        fill_col(&mut t, lo, hi, NK1, nk1);
        fill_col(&mut t, lo, hi, RHO, inp.rho[0]);
        fill_col(&mut t, lo, hi, RHO1, inp.rho[1]);
        fill_col(&mut t, lo, hi, VAL, value);
        // pos_acc: cumulative Σ bit_d·2^d (jumps after each membership link; leaf = commit_b output)
        let mut acc = 0u64;
        let mut links: Vec<(usize, u64)> = Vec::new();
        for d in 0..DEPTH {
            links.push(((base + 2 + d) * BLOCK + BLOCK - 1, if inp.bits[d] { 1u64 << d } else { 0 }));
        }
        for r in lo..=hi {
            t[r * WIDTH + POSACC] = Val::from_u64(acc);
            for (lr, add) in &links {
                if *lr == r {
                    acc += add;
                }
            }
        }
        // range-check the input value (window starts at commit_a; spans commit_a+commit_b = 64 rows)
        fill_range(&mut t, commit_a_in_row(i), inp.value);
    }

    // --- outputs: 2-permutation commitment (out_a, out_b) + value range ---
    for (j, out) in w.outputs.iter().enumerate() {
        let mut oa = [Val::ZERO; 8];
        oa[0] = Val::from_u64(DOM_CM);
        oa[1..1 + DIGEST].copy_from_slice(&out.recipient);
        oa[1 + DIGEST] = Val::from_u64(out.value);
        oa[1 + DIGEST + 1] = out.rho[0];
        oa[1 + DIGEST + 2] = out.rho[1];
        set_block(&mut t, out_base(j), oa);
        let chain = native_permute(oa);
        let mut ob = [Val::ZERO; 8];
        ob[..DIGEST].copy_from_slice(&chain[..DIGEST]);
        ob[DIGEST] = out.rcm[0];
        ob[DIGEST + 1] = out.rcm[1];
        ob[DIGEST + 2] = out.asset;
        set_block(&mut t, out_base(j) + 1, ob); // out_b: cm = perm(ob)[..DIGEST]
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

    // --- mint region: VAL = mint (issuance), range-checked ---
    set_block(&mut t, mint_base(), [Val::ZERO; 8]);
    set_block(&mut t, mint_base() + 1, [Val::ZERO; 8]);
    let (mlo, mhi) = (mint_in_row(), mint_in_row() + MINT_BLOCKS * BLOCK - 1);
    fill_col(&mut t, mlo, mhi, VAL, Val::from_u64(w.mint));
    fill_range(&mut t, mint_in_row(), w.mint);

    // --- padding blocks: valid permutations of zero ---
    for b in USED_BLOCKS..NUM_BLOCKS {
        set_block(&mut t, b, [Val::ZERO; 8]);
    }

    // --- global value accumulator: +in (commit) +mint −out −fee ⇒ 0 ---
    let mut delta = vec![0i128; HEIGHT];
    for (i, inp) in w.inputs.iter().enumerate() {
        delta[commit_a_in_row(i)] += inp.value as i128;
    }
    for (j, out) in w.outputs.iter().enumerate() {
        delta[out_in_row(j)] -= out.value as i128;
    }
    delta[fee_in_row()] -= w.fee as i128;
    delta[mint_in_row()] += w.mint as i128;
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
    pis[PI_MINT] = Val::from_u64(w.mint);
    pis[PI_TXBIND..PI_TXBIND + DIGEST].copy_from_slice(&w.tx_binding);
    pis
}

pub fn prove_verify_with(w: &Witness, pis: &[Val]) -> Result<(), String> {
    let config = make_config();
    let air = JoinSplitAir;
    let trace = build_trace(w);
    let proof = prove(&config, &air, trace, pis);
    verify(&config, &air, &proof, pis).map_err(|e| format!("{e:?}"))
}

pub fn prove_verify(w: &Witness) -> Result<(), String> {
    prove_verify_with(w, &public_values(w))
}

/// Number of public-input field elements: `anchor ‖ N·nf ‖ M·out_cm ‖ fee ‖ tx_binding`.
pub const NUM_PUBLIC_INPUTS: usize = N_PUBLIC;

/// Prove a join-split and return canonical (postcard) proof bytes.
pub fn prove_to_bytes(w: &Witness) -> Vec<u8> {
    let config = make_config();
    let trace = build_trace(w);
    let proof = prove(&config, &JoinSplitAir, trace, &public_values(w));
    postcard::to_allocvec(&proof).expect("proof serialization is infallible")
}

/// Verify canonical proof bytes against public inputs. **Fail-closed** on any error.
pub fn verify_bytes(proof_bytes: &[u8], pis: &[Val]) -> bool {
    if pis.len() != N_PUBLIC {
        return false;
    }
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), &JoinSplitAir, &proof, pis).is_ok()
}

/// A representative valid join-split witness (2 inputs at tree positions 0,1; balanced).
pub fn demo_witness() -> Witness {
    let in_values = [1000u64, 500];
    let nks: [[u64; 2]; N_IN] = core::array::from_fn(|i| [7 + i as u64, 700 + i as u64]);
    let in_rho = |i: usize| [Val::from_u64(11 + i as u64), Val::from_u64(211 + i as u64)];
    let in_rcm = |i: usize| [Val::from_u64(100 + i as u64), Val::from_u64(300 + i as u64)];
    let in_div = |i: usize| Val::from_u64(500 + i as u64); // per-input diversifier
    let asset = Val::from_u64(42); // single (hidden) asset for the whole tx
    let cms: Vec<[Val; DIGEST]> = (0..N_IN)
        .map(|i| {
            commit(
                recipient_of(Val::from_u64(nks[i][0]), Val::from_u64(nks[i][1]), in_div(i)),
                Val::from_u64(in_values[i]),
                in_rho(i),
                in_rcm(i),
                asset,
            )
        })
        .collect();
    let (_, paths) = build_paths(&cms);
    let inputs = core::array::from_fn(|i| Input {
        nk: nks[i],
        div: in_div(i),
        asset,
        value: in_values[i],
        rho: in_rho(i),
        rcm: in_rcm(i),
        sib: paths[i].0,
        bits: paths[i].1,
    });
    let outputs = core::array::from_fn(|j| Output {
        recipient: recipient_of(Val::from_u64(77 + j as u64), Val::from_u64(j as u64), Val::from_u64(600 + j as u64)),
        asset,
        value: [900u64, 500][j],
        rho: [Val::from_u64(21 + j as u64), Val::from_u64(221 + j as u64)],
        rcm: [Val::from_u64(22 + j as u64), Val::from_u64(222 + j as u64)],
    });
    Witness { inputs, outputs, fee: 100, mint: 0, tx_binding: core::array::from_fn(|i| Val::from_u64(0xABCD + i as u64)) }
}

/// (proof bytes, prove ms, verify ms, proven security bits) for a representative join-split.
pub fn measure(w: &Witness) -> (usize, u128, u128, usize) {
    let config = make_config();
    let trace = build_trace(w);
    let pis = public_values(w);
    let t0 = std::time::Instant::now();
    let proof = prove(&config, &JoinSplitAir, trace, &pis);
    let prove_ms = t0.elapsed().as_millis();
    let bytes = postcard::to_allocvec(&proof).unwrap();
    let t1 = std::time::Instant::now();
    assert!(verify(&config, &JoinSplitAir, &proof, &pis).is_ok());
    let verify_ms = t1.elapsed().as_millis();
    // proven security at this trace height
    let perm = default_goldilocks_poseidon2_8();
    let vm = ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm), 6, ChaCha20Rng::seed_from_u64(1));
    let fri = FriParameters {
        log_blowup: 4,
        log_final_poly_len: 0,
        max_log_arity: 4,
        num_queries: 96,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 16,
        mmcs: ChallengeMmcs::new(vm),
    };
    let layout = AirLayout::from_air::<Goldilocks>(&JoinSplitAir);
    let params = StarkSecurityParams::from_air::<Val, Challenge, JoinSplitAir, ChallengeMmcs>(&fri, &JoinSplitAir, layout, 127, 128, 2);
    let proven = ProvenSecurity::compute(&params, 1usize << (HEIGHT.trailing_zeros() as usize + 1)).security_bits();
    (bytes.len(), prove_ms, verify_ms, proven)
}

/// Prove with the witness's real public inputs, verify against `verify_pis` (tests FS binding).
#[allow(dead_code)]
pub fn prove_real_verify_with(w: &Witness, verify_pis: &[Val]) -> Result<(), String> {
    let config = make_config();
    let air = JoinSplitAir;
    let trace = build_trace(w);
    let proof = prove(&config, &air, trace, &public_values(w));
    verify(&config, &air, &proof, verify_pis).map_err(|e| format!("{e:?}"))
}

// --- sparse Merkle test helper: N leaves at positions 0..N (leftmost), shared anchor -----------

pub(crate) fn empty_hashes() -> [[Val; DIGEST]; DEPTH] {
    let mut e = [[Val::ZERO; DIGEST]; DEPTH];
    for d in 1..DEPTH {
        e[d] = merge(e[d - 1], e[d - 1]);
    }
    e
}

/// Build a tree holding `leaves` at positions 0..leaves.len() (a power of two) in the leftmost
/// subtree, the rest empty. Returns the anchor and each leaf's (sib, bits) authentication path.
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
        let in0 = (1000u64, [7u64, 70u64], 11u64, 100u64, 501u64); // value, nk(2), rho, rcm, div
        let in1 = (500u64, [9u64, 90u64], 13u64, 101u64, 502u64);
        let rho2 = |x: u64| [Val::from_u64(x), Val::from_u64(x + 200)];
        let rcm2 = |x: u64| [Val::from_u64(x), Val::from_u64(x + 300)];
        let asset = Val::from_u64(42); // single hidden asset for the tx
        let cmf = |v: &(u64, [u64; 2], u64, u64, u64)| {
            commit(recipient_of(Val::from_u64(v.1[0]), Val::from_u64(v.1[1]), Val::from_u64(v.4)), Val::from_u64(v.0), rho2(v.2), rcm2(v.3), asset)
        };
        let (_, paths) = build_paths(&[cmf(&in0), cmf(&in1)]);
        let mk_in = |v: (u64, [u64; 2], u64, u64, u64), pth: &([[Val; DIGEST]; DEPTH], [bool; DEPTH])| Input {
            nk: v.1,
            div: Val::from_u64(v.4),
            asset,
            value: v.0,
            rho: rho2(v.2),
            rcm: rcm2(v.3),
            sib: pth.0,
            bits: pth.1,
        };
        let inputs = [mk_in(in0, &paths[0]), mk_in(in1, &paths[1])];
        let outputs = [
            Output { recipient: recipient_of(Val::from_u64(77), Val::from_u64(7), Val::from_u64(601)), asset, value: 900, rho: rho2(21), rcm: rcm2(22) },
            Output { recipient: recipient_of(Val::from_u64(88), Val::from_u64(8), Val::from_u64(602)), asset, value: 500, rho: rho2(23), rcm: rcm2(24) },
        ];
        // Σin = 1500, Σout = 1400, fee = 100
        Witness { inputs, outputs, fee: 100, mint: 0, tx_binding: core::array::from_fn(|i| Val::from_u64(0xABCD + i as u64)) }
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
        let nk = |i: usize| [7 + i as u64, 700 + i as u64];
        let in_rho = |i: usize| [Val::from_u64(11 + i as u64), Val::from_u64(211 + i as u64)];
        let in_rcm = |i: usize| [Val::from_u64(100 + i as u64), Val::from_u64(300 + i as u64)];
        let in_div = |i: usize| Val::from_u64(500 + i as u64);
        let asset = Val::from_u64(42); // single hidden asset for the tx
        let cms: Vec<[Val; DIGEST]> = (0..N_IN)
            .map(|i| {
                commit(
                    recipient_of(Val::from_u64(nk(i)[0]), Val::from_u64(nk(i)[1]), in_div(i)),
                    Val::from_u64(in_values[i]),
                    in_rho(i),
                    in_rcm(i),
                    asset,
                )
            })
            .collect();
        let (_, paths) = build_paths(&cms);
        let inputs = core::array::from_fn(|i| Input {
            nk: nk(i),
            div: in_div(i),
            asset,
            value: in_values[i],
            rho: in_rho(i),
            rcm: in_rcm(i),
            sib: paths[i].0,
            bits: paths[i].1,
        });
        let outputs = core::array::from_fn(|j| Output {
            recipient: recipient_of(Val::from_u64(77 + j as u64), Val::from_u64(j as u64), Val::from_u64(600 + j as u64)),
            asset,
            value: out_values[j],
            rho: [Val::from_u64(21 + j as u64), Val::from_u64(221 + j as u64)],
            rcm: [Val::from_u64(22 + j as u64), Val::from_u64(222 + j as u64)],
        });
        Witness { inputs, outputs, fee, mint: 0, tx_binding: core::array::from_fn(|i| Val::from_u64(0xABCD + i as u64)) }
    }

    #[test]
    fn joinsplit_verifies() {
        prove_verify(&witness_with([1000, 500], [900, 500], 100)).expect("valid join-split should verify");
    }

    #[test]
    fn zk_blinding_is_fresh_per_proof() {
        // Two proofs of the *same* witness must differ — the hiding-PCS blinding is fresh CSPRNG
        // randomness per proof (would fail with the old fixed-seed RNG).
        let w = witness_with([1000, 500], [900, 500], 100);
        let a = prove_to_bytes(&w);
        let b = prove_to_bytes(&w);
        assert_ne!(a, b, "ZK proofs of the same statement must be re-randomized");
        // both still verify
        assert!(verify_bytes(&a, &public_values(&w)));
        assert!(verify_bytes(&b, &public_values(&w)));
    }

    #[test]
    fn mint_issuance_verifies() {
        // coinbase: dummy (zero-value) inputs, one output funded by issuance, no fee.
        let mut w = witness_with([0, 0], [1000, 0], 0);
        w.mint = 1000; // Σin(0) + mint(1000) = Σout(1000) + fee(0)
        prove_verify(&w).expect("coinbase mint should verify");
    }

    #[test]
    fn wrong_mint_rejected() {
        let mut w = witness_with([0, 0], [1000, 0], 0);
        w.mint = 1000;
        let mut pis = public_values(&w);
        pis[PI_MINT] += Val::ONE; // claim a different issuance ⇒ mint binding fails
        assert!(prove_verify_with(&w, &pis).is_err());
    }

    #[test]
    fn dummy_notes_pad_smaller_transactions() {
        // A 1-real-in / 1-real-out transaction, padded to the fixed 2-in/2-out shape with
        // zero-value dummy notes (Σin = 1000 = 900 + 100 = Σout + fee). This is how variable
        // (N, M) is supported without a variable-shape circuit.
        prove_verify(&witness_with([1000, 0], [900, 0], 100)).expect("dummy-padded tx should verify");
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
        let (nk0, nk1) = (Val::from_u64(5), Val::from_u64(50));
        let rho = [Val::from_u64(6), Val::from_u64(66)];
        let b0 = [false; DEPTH];
        let mut b1 = [false; DEPTH];
        b1[0] = true;
        assert_ne!(nullifier(nk0, nk1, rho, pos_of(&b0)), nullifier(nk0, nk1, rho, pos_of(&b1)));
    }

    /// Robust "this corrupted trace must not yield a verifying proof" (debug: prove's constraint
    /// check panics; release: verify rejects).
    fn corrupt_trace_rejected(trace: RowMajorMatrix<Val>, pis: Vec<Val>) -> bool {
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let proof = prove(&make_config(), &JoinSplitAir, trace, &pis);
            verify_bytes(&postcard::to_allocvec(&proof).unwrap(), &pis)
        }));
        matches!(outcome, Ok(false) | Err(_))
    }

    /// For each persistent key/randomness limb fed to BOTH the commitment/ownership AND the nullifier,
    /// forge a trace that uses a different value in the nullifier (publishing the matching forged nf),
    /// so ONLY that limb's persistence constraint is violated. Each must be unprovable — this is the
    /// corrupted-trace coverage whose absence hid the original rho1 double-spend gap. Covers
    /// nk0(NK), nk1(NK1), rho0(RHO), rho1(RHO1).
    #[test]
    fn forged_nullifier_limbs_are_rejected() {
        let cols = [NK, NK1, RHO, RHO1];
        for limb in 0..4usize {
            let w = sample();
            let mut trace = build_trace(&w);
            let (nk0, nk1) = (Val::from_u64(w.inputs[0].nk[0]), Val::from_u64(w.inputs[0].nk[1]));
            let mut vals = [nk0, nk1, w.inputs[0].rho[0], w.inputs[0].rho[1]];
            let pos = pos_of(&w.inputs[0].bits);
            vals[limb] += Val::ONE; // bump the limb the nullifier consumes
            // rewrite input 0's nullifier block to bind the bumped limb (commitment/ownership keep the
            // real value, so cm/anchor still verify); make the local nullifier binding hold.
            let nin = [Val::from_u64(DOM_NF), vals[0], vals[1], vals[2], vals[3], pos, Val::ZERO, Val::ZERO];
            set_block(&mut trace.values, null_block(0), nin);
            for r in null_in_row(0)..=null_out_row(0) {
                trace.values[r * WIDTH + cols[limb]] = vals[limb];
            }
            let mut pis = public_values(&w);
            let nfp = nullifier(vals[0], vals[1], [vals[2], vals[3]], pos);
            pis[PI_NF..PI_NF + DIGEST].copy_from_slice(&nfp);
            assert!(corrupt_trace_rejected(trace, pis), "forged nullifier limb {limb} must not verify");
        }
    }

    /// The commitment chain link (`commit_b.in[0..4] = commit_a.out[0..4]`) must be non-vacuous: a
    /// trace that feeds an arbitrary chain value into commit_b would forge the commitment.
    #[test]
    fn forged_commitment_chain_is_rejected() {
        let w = sample();
        let mut trace = build_trace(&w);
        // Corrupt input 0's commit_b input lane 0 (the chaining value) — no longer = commit_a output.
        let row = commit_b_in_row(0);
        trace.values[row * WIDTH + 0] += Val::ONE;
        // public inputs unchanged: the forged chain breaks the chain-link (and downstream cm), which
        // must make the proof unverifiable regardless of the published statement.
        let pis = public_values(&w);
        assert!(corrupt_trace_rejected(trace, pis), "a forged commitment chaining value must not verify");
    }

    /// The hidden-asset binding must be non-vacuous: a prover must not turn the inputs' asset into a
    /// different output asset. Forge output 0's committed asset (≠ the global ASSET) and publish the
    /// matching out_cm, so ONLY the `lane6 == ASSET` binding is violated.
    #[test]
    fn output_with_mismatched_asset_is_rejected() {
        let w = sample(); // asset = 42 on every note
        let mut trace = build_trace(&w);
        let out0 = w.outputs[0];
        let alt = out0.asset + Val::ONE; // a different asset for the output
        // recompute output 0's commit_b (out_a output = chain; lane6 = forged asset).
        let mut oa = [Val::ZERO; 8];
        oa[0] = Val::from_u64(DOM_CM);
        oa[1..1 + DIGEST].copy_from_slice(&out0.recipient);
        oa[1 + DIGEST] = Val::from_u64(out0.value);
        oa[1 + DIGEST + 1] = out0.rho[0];
        oa[1 + DIGEST + 2] = out0.rho[1];
        let chain = native_permute(oa);
        let mut ob = [Val::ZERO; 8];
        ob[..DIGEST].copy_from_slice(&chain[..DIGEST]);
        ob[DIGEST] = out0.rcm[0];
        ob[DIGEST + 1] = out0.rcm[1];
        ob[DIGEST + 2] = alt;
        set_block(&mut trace.values, out_base(0) + 1, ob);
        let new_cm: [Val; DIGEST] = native_permute(ob)[..DIGEST].try_into().unwrap();
        let mut pis = public_values(&w);
        pis[PI_OUTCM..PI_OUTCM + DIGEST].copy_from_slice(&new_cm);
        assert!(corrupt_trace_rejected(trace, pis), "a mismatched output asset must not verify");
    }
}
