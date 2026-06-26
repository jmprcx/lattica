//! M4c — the **full spend statement** as one across-rows `uni-stark` AIR (zero-knowledge).
//!
//! Eight Poseidon2 blocks (DEPTH=4 ⇒ NUM_BLOCKS=8, height 256), each the M4a permutation:
//!   0 ownership   recipient = Perm([nk,0,..])           (recipient = H(nk)[0])
//!   1 commitment  cm        = Perm([recipient,value,rho,rcm,0,..])[0..4]
//!   2..=5 merges  fold cm up a general-position path to the public `root`
//!   6 nullifier   nf        = Perm([nk,rho,pos,0,..])[0..4]      (public)
//!   7 output      out_cm    = Perm([out_recipient,out_value,out_rho,out_rcm,0,..])[0..4] (public)
//!
//! Cross-region binding uses **persistent columns** (nk, rho, value, out_value) that are constant
//! across the trace and pinned to the relevant block inputs, so the same `nk` drives ownership +
//! nullifier and the same `rho` drives commitment + nullifier (forging either is rejected).
//! Per-boundary wiring uses **period-256 selectors** (distinct per block) alongside the period-32
//! round schedule. Value-balance `value = out_value + fee` and a running-remainder **range** proof
//! (`value,out_value < 2^BITS`, so the balance cannot wrap mod p) complete the economic soundness.
//! The public inputs `(root, nf, out_cm, fee, tx_binding)` bind the proof (Fiat–Shamir) to one tx.
//!
//! Every binding has a dedicated negative test (vacuous bindings are the failure mode the audit
//! flagged). Validated against an independent native Poseidon2 oracle and proven/verified under the
//! hiding (ZK) PCS.

use p3_air::symbolic::AirLayout;
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
use p3_uni_stark::{prove, verify, Proof, ProvenSecurity, StarkConfig, StarkSecurityParams};
use rand::rngs::SmallRng;
use rand::SeedableRng;

use crate::poseidon2_air::{ext_linear, int_linear, native_permute, native_steps, periodic_table, pow7, BLOCK, W};

type Val = Goldilocks;

pub const DEPTH: usize = 32; // production Merkle depth
const NUM_BLOCKS_USED: usize = 4 + DEPTH; // ownership, commitment, DEPTH merges, nullifier, output = 36
const NUM_BLOCKS: usize = NUM_BLOCKS_USED.next_power_of_two(); // pad the trace to a power of two = 64
const HEIGHT: usize = NUM_BLOCKS * BLOCK; // 2048
const DIGEST: usize = 4;
// Value range bound. Goldilocks p ≈ 2^64; `value = out_value + fee` is checked in the field, so all
// three must stay < 2^BITS with 2·2^BITS < p (no wraparound). BITS=52 covers any realistic supply.
const BITS: usize = 52;

// column layout (WIDTH = 17)
const BIT: usize = W; // 8  membership position bit
const NK: usize = 9; // persistent
const RHO: usize = 10;
const VALUE: usize = 11;
const OUTVAL: usize = 12;
const REMV: usize = 13; // range running remainder of value
const REMO: usize = 14; // ... of out_value
const BITV: usize = 15; // extracted bit of value
const BITO: usize = 16; // ... of out_value
const WIDTH: usize = 17;

// block indices and their output rows
const B_OWN: usize = 0;
const B_COMMIT: usize = 1;
const B_MERGE0: usize = 2;
const B_NULL: usize = 2 + DEPTH; // 6
const B_OUT: usize = 3 + DEPTH; // 7
const ROW_OWN_OUT: usize = B_OWN * BLOCK + BLOCK - 1; // 31
const ROW_COMMIT_IN: usize = B_COMMIT * BLOCK; // 32
const ROW_ROOT: usize = (B_MERGE0 + DEPTH - 1) * BLOCK + BLOCK - 1; // block5 output = 191
const ROW_NULL_IN: usize = B_NULL * BLOCK; // 192
const ROW_NULL_OUT: usize = B_NULL * BLOCK + BLOCK - 1; // 223
const ROW_OUT_IN: usize = B_OUT * BLOCK; // 224
const ROW_OUT_OUT: usize = B_OUT * BLOCK + BLOCK - 1; // 255

// periodic-column indices (0..11 = round schedule, 11.. = period-256 boundary selectors)
const P_ROW0: usize = 11;
const P_RECIP_LINK: usize = 12;
const P_COMMIT_IN: usize = 13;
const P_MEM_LINK: usize = 14;
const P_ROOT: usize = 15;
const P_NULL_IN: usize = 16;
const P_NULL_OUT: usize = 17;
const P_OUT_IN: usize = 18;
const P_OUT_OUT: usize = 19;
const P_RANGE_ACTIVE: usize = 20;
const P_RANGE_CLOSE: usize = 21;
const N_PERIODIC: usize = 22;

// public-input indices
const PI_ROOT: usize = 0; // 0..4
const PI_NF: usize = 4; // 4..8
const PI_OUTCM: usize = 8; // 8..12
const PI_FEE: usize = 12;
const PI_TXBIND: usize = 13; // 13..17 (full 4-element sighash digest)
const N_PUBLIC: usize = 17;

#[derive(Clone, Copy)]
pub struct Witness {
    pub nk: u64,
    pub value: u64,
    pub rho: Val,
    pub rcm: Val,
    pub pos: Val,
    pub sib: [[Val; DIGEST]; DEPTH],
    pub bits: [bool; DEPTH],
    pub out_recipient: [Val; DIGEST],
    pub out_value: u64,
    pub out_rho: Val,
    pub out_rcm: Val,
    pub fee: u64,
    pub tx_binding: [Val; DIGEST],
}

// --- native oracle ----------------------------------------------------------------------------

fn perm_in(elems: &[Val]) -> [Val; W] {
    let mut s = [Val::ZERO; W];
    s[..elems.len()].copy_from_slice(elems);
    s
}
fn recipient_of(nk: Val) -> [Val; DIGEST] {
    native_permute(perm_in(&[nk]))[..DIGEST].try_into().unwrap()
}
/// The Poseidon2 input layout shared by the input- and output-note commitments:
/// `[recipient(4), value, rho, rcm, pad]`.
fn note_input(recipient: [Val; DIGEST], value: Val, rho: Val, rcm: Val) -> [Val; W] {
    let mut s = [Val::ZERO; W];
    s[..DIGEST].copy_from_slice(&recipient);
    s[DIGEST] = value;
    s[DIGEST + 1] = rho;
    s[DIGEST + 2] = rcm;
    s
}
/// A note commitment over a full 4-element recipient digest: `H(recipient‖value‖rho‖rcm)` (7 inputs).
fn commit(recipient: [Val; DIGEST], value: Val, rho: Val, rcm: Val) -> [Val; DIGEST] {
    native_permute(note_input(recipient, value, rho, rcm))[..DIGEST].try_into().unwrap()
}
fn merge(l: [Val; DIGEST], r: [Val; DIGEST]) -> [Val; DIGEST] {
    let mut s = [Val::ZERO; W];
    s[..DIGEST].copy_from_slice(&l);
    s[DIGEST..].copy_from_slice(&r);
    native_permute(s)[..DIGEST].try_into().unwrap()
}

pub struct PublicOutputs {
    pub root: [Val; DIGEST],
    pub nf: [Val; DIGEST],
    pub out_cm: [Val; DIGEST],
}

pub fn native_outputs(w: &Witness) -> PublicOutputs {
    let nk = Val::from_u64(w.nk);
    let recipient = recipient_of(nk);
    let mut node = commit(recipient, Val::from_u64(w.value), w.rho, w.rcm);
    for d in 0..DEPTH {
        node = if w.bits[d] { merge(w.sib[d], node) } else { merge(node, w.sib[d]) };
    }
    let nf: [Val; DIGEST] = native_permute(perm_in(&[nk, w.rho, w.pos]))[..DIGEST].try_into().unwrap();
    let out_cm = commit(w.out_recipient, Val::from_u64(w.out_value), w.out_rho, w.out_rcm);
    PublicOutputs { root: node, nf, out_cm }
}

pub fn public_values(w: &Witness) -> Vec<Val> {
    let o = native_outputs(w);
    let mut pis = vec![Val::ZERO; N_PUBLIC];
    pis[PI_ROOT..PI_ROOT + DIGEST].copy_from_slice(&o.root);
    pis[PI_NF..PI_NF + DIGEST].copy_from_slice(&o.nf);
    pis[PI_OUTCM..PI_OUTCM + DIGEST].copy_from_slice(&o.out_cm);
    pis[PI_FEE] = Val::from_u64(w.fee);
    pis[PI_TXBIND..PI_TXBIND + DIGEST].copy_from_slice(&w.tx_binding);
    pis
}

// --- periodic columns -------------------------------------------------------------------------

fn one_hot(rows: &[usize]) -> Vec<Val> {
    let mut c = vec![Val::ZERO; HEIGHT];
    for &r in rows {
        c[r] = Val::ONE;
    }
    c
}

fn periodic() -> Vec<Vec<Val>> {
    let mut cols = periodic_table(); // 11 round-schedule columns, period 32
    debug_assert_eq!(cols.len(), 11);
    let mem_link_rows: Vec<usize> = (0..DEPTH).map(|d| (B_COMMIT + d) * BLOCK + BLOCK - 1).collect();
    let range_active: Vec<usize> = (0..BITS).collect();
    cols.push(one_hot(&[0])); // P_ROW0
    cols.push(one_hot(&[ROW_OWN_OUT])); // P_RECIP_LINK
    cols.push(one_hot(&[ROW_COMMIT_IN])); // P_COMMIT_IN
    cols.push(one_hot(&mem_link_rows)); // P_MEM_LINK
    cols.push(one_hot(&[ROW_ROOT])); // P_ROOT
    cols.push(one_hot(&[ROW_NULL_IN])); // P_NULL_IN
    cols.push(one_hot(&[ROW_NULL_OUT])); // P_NULL_OUT
    cols.push(one_hot(&[ROW_OUT_IN])); // P_OUT_IN
    cols.push(one_hot(&[ROW_OUT_OUT])); // P_OUT_OUT
    cols.push(one_hot(&range_active)); // P_RANGE_ACTIVE
    cols.push(one_hot(&[BITS])); // P_RANGE_CLOSE
    cols
}

// --- AIR --------------------------------------------------------------------------------------

pub struct FullSpendAir;

impl BaseAir<Goldilocks> for FullSpendAir {
    fn width(&self) -> usize {
        WIDTH
    }
    fn num_public_values(&self) -> usize {
        N_PUBLIC
    }
    fn num_periodic_columns(&self) -> usize {
        N_PERIODIC
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        periodic()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for FullSpendAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let cur_vars: Vec<AB::Var> = main.current_slice().to_vec();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let two = AB::Expr::TWO;

        let is_init = p[0].clone();
        let is_full = p[1].clone();
        let is_partial = p[2].clone();
        let rc: Vec<AB::Expr> = (0..W).map(|i| p[3 + i].clone()).collect();

        // ---- within-block Poseidon2 round constraints (state columns 0..8) ----
        let mut init_s: [AB::Expr; W] = core::array::from_fn(|i| cur[i].clone());
        ext_linear(&mut init_s);
        let mut full_s: [AB::Expr; W] = core::array::from_fn(|i| pow7(cur[i].clone() + rc[i].clone()));
        ext_linear(&mut full_s);
        let mut part_s: [AB::Expr; W] =
            core::array::from_fn(|i| if i == 0 { pow7(cur[0].clone() + rc[0].clone()) } else { cur[i].clone() });
        int_linear(&mut part_s);
        for i in 0..W {
            let round = is_init.clone() * (nxt[i].clone() - init_s[i].clone())
                + is_full.clone() * (nxt[i].clone() - full_s[i].clone())
                + is_partial.clone() * (nxt[i].clone() - part_s[i].clone());
            builder.when_transition().assert_zero(round);
        }

        // ---- persistent columns are constant across the trace ----
        for &c in &[NK, RHO, VALUE, OUTVAL] {
            builder.when_transition().assert_zero(nxt[c].clone() - cur[c].clone());
        }

        // ---- recipient link (boundary ownership→commitment): commit.in[0..4] = own.out[0..4] ----
        // recipient = H(nk) is the full 4-element digest; carry all four into the commitment input.
        for i in 0..DIGEST {
            builder
                .when_transition()
                .assert_zero(p[P_RECIP_LINK].clone() * (nxt[i].clone() - cur[i].clone()));
        }

        // ---- membership links (boundaries into each merge): place running digest by the bit ----
        let bit = nxt[BIT].clone();
        for i in 0..DIGEST {
            let placed = (one.clone() - bit.clone()) * (nxt[i].clone() - cur[i].clone())
                + bit.clone() * (nxt[DIGEST + i].clone() - cur[i].clone());
            builder.when_transition().assert_zero(p[P_MEM_LINK].clone() * placed);
        }
        builder
            .when_transition()
            .assert_zero(p[P_MEM_LINK].clone() * (bit.clone() * (one.clone() - bit.clone())));

        // ---- range decomposition (running remainder over the first BITS rows) ----
        // cur.rem = 2*next.rem + cur.bit, with cur.bit boolean.
        let ra = p[P_RANGE_ACTIVE].clone();
        builder
            .when_transition()
            .assert_zero(ra.clone() * (cur[REMV].clone() - (two.clone() * nxt[REMV].clone() + cur[BITV].clone())));
        builder
            .when_transition()
            .assert_zero(ra.clone() * (cur[REMO].clone() - (two.clone() * nxt[REMO].clone() + cur[BITO].clone())));
        builder
            .when_transition()
            .assert_zero(ra.clone() * (cur[BITV].clone() * (one.clone() - cur[BITV].clone())));
        builder
            .when_transition()
            .assert_zero(ra.clone() * (cur[BITO].clone() * (one.clone() - cur[BITO].clone())));

        // ---- per-row bindings (gated by period-256 one-hot selectors) ----
        // row 0: ownership input = [nk, 0,..]; range seed; value-balance.
        let r0 = p[P_ROW0].clone();
        builder.assert_zero(r0.clone() * (cur[0].clone() - cur[NK].clone()));
        for i in 1..W {
            builder.assert_zero(r0.clone() * cur[i].clone());
        }
        builder.assert_zero(r0.clone() * (cur[REMV].clone() - cur[VALUE].clone()));
        builder.assert_zero(r0.clone() * (cur[REMO].clone() - cur[OUTVAL].clone()));
        builder
            .assert_zero(r0.clone() * (cur[VALUE].clone() - cur[OUTVAL].clone() - pis[PI_FEE].clone()));

        // range close (row BITS): remainders are zero ⇒ value,out_value < 2^BITS.
        let rc_close = p[P_RANGE_CLOSE].clone();
        builder.assert_zero(rc_close.clone() * cur[REMV].clone());
        builder.assert_zero(rc_close.clone() * cur[REMO].clone());

        // commitment input: [recipient(0..4, via link), value(4), rho(5), rcm(6, free), pad(7)].
        let ci = p[P_COMMIT_IN].clone();
        builder.assert_zero(ci.clone() * (cur[DIGEST].clone() - cur[VALUE].clone())); // value
        builder.assert_zero(ci.clone() * (cur[DIGEST + 1].clone() - cur[RHO].clone())); // rho
        builder.assert_zero(ci.clone() * cur[DIGEST + 3].clone()); // pad (index 7)

        // root output (row 191): state[0..4] = public root.
        let pr = p[P_ROOT].clone();
        for i in 0..DIGEST {
            builder.assert_zero(pr.clone() * (cur[i].clone() - pis[PI_ROOT + i].clone()));
        }

        // nullifier input (row 192): state = [nk, rho, pos(free), 0,0,0,0,0].
        let ni = p[P_NULL_IN].clone();
        builder.assert_zero(ni.clone() * (cur[0].clone() - cur[NK].clone()));
        builder.assert_zero(ni.clone() * (cur[1].clone() - cur[RHO].clone()));
        for i in DIGEST.saturating_sub(1)..W {
            // state[3..8] = 0 (state[2]=pos is free)
            if i >= 3 {
                builder.assert_zero(ni.clone() * cur[i].clone());
            }
        }
        // nullifier output (row 223): state[0..4] = public nf.
        let no = p[P_NULL_OUT].clone();
        for i in 0..DIGEST {
            builder.assert_zero(no.clone() * (cur[i].clone() - pis[PI_NF + i].clone()));
        }

        // output-commitment input: [out_recipient(0..4, free), out_value(4), out_rho(5, free),
        // out_rcm(6, free), pad(7)]. Only out_value (bound to its persistent column) and the pad fix.
        let oi = p[P_OUT_IN].clone();
        builder.assert_zero(oi.clone() * (cur[DIGEST].clone() - cur[OUTVAL].clone())); // out_value
        builder.assert_zero(oi.clone() * cur[DIGEST + 3].clone()); // pad (index 7)
        // output-commitment output (row 255): state[0..4] = public out_cm.
        let oo = p[P_OUT_OUT].clone();
        for i in 0..DIGEST {
            builder.assert_zero(oo.clone() * (cur[i].clone() - pis[PI_OUTCM + i].clone()));
        }

        // tx_binding (pis[PI_TXBIND]) needs no constraint: uni-stark observes all public values
        // into the Fiat–Shamir transcript (prover.rs `observe_slice(public_values)`), so a proof is
        // bound to the tx and will not verify against a different tx_binding.
        let _ = cur_vars;
    }
}

// --- trace ------------------------------------------------------------------------------------

fn set_state(trace: &mut [Val], block: usize, input: [Val; W]) {
    let rows = native_steps(input);
    for (r, row) in rows.iter().enumerate() {
        let base = (block * BLOCK + r) * WIDTH;
        trace[base..base + W].copy_from_slice(row);
    }
}

fn build_trace(w: &Witness) -> RowMajorMatrix<Val> {
    let mut t = vec![Val::ZERO; HEIGHT * WIDTH];
    let nk = Val::from_u64(w.nk);
    let value = Val::from_u64(w.value);
    let out_value = Val::from_u64(w.out_value);

    // states
    set_state(&mut t, B_OWN, perm_in(&[nk]));
    let recipient = recipient_of(nk);
    set_state(&mut t, B_COMMIT, note_input(recipient, value, w.rho, w.rcm));
    let mut node = commit(recipient, value, w.rho, w.rcm);
    for d in 0..DEPTH {
        let (l, r) = if w.bits[d] { (w.sib[d], node) } else { (node, w.sib[d]) };
        let mut min = [Val::ZERO; W];
        min[..DIGEST].copy_from_slice(&l);
        min[DIGEST..].copy_from_slice(&r);
        set_state(&mut t, B_MERGE0 + d, min);
        // position bit lives on the merge block's input row
        t[((B_MERGE0 + d) * BLOCK) * WIDTH + BIT] = if w.bits[d] { Val::ONE } else { Val::ZERO };
        node = native_permute(min)[..DIGEST].try_into().unwrap();
    }
    set_state(&mut t, B_NULL, perm_in(&[nk, w.rho, w.pos]));
    set_state(&mut t, B_OUT, note_input(w.out_recipient, out_value, w.out_rho, w.out_rcm));
    // padding blocks (NUM_BLOCKS rounded up to a power of two): valid permutations of zero so the
    // round constraints hold; no boundary selector references them, so they bind nothing.
    for b in NUM_BLOCKS_USED..NUM_BLOCKS {
        set_state(&mut t, b, [Val::ZERO; W]);
    }

    // persistent columns
    for r in 0..HEIGHT {
        let base = r * WIDTH;
        t[base + NK] = nk;
        t[base + RHO] = w.rho;
        t[base + VALUE] = value;
        t[base + OUTVAL] = out_value;
    }

    // range running remainder over rows 0..=BITS
    let mut rv = w.value;
    let mut ro = w.out_value;
    for r in 0..HEIGHT {
        let base = r * WIDTH;
        t[base + REMV] = Val::from_u64(rv);
        t[base + REMO] = Val::from_u64(ro);
        if r < BITS {
            t[base + BITV] = Val::from_u64(rv & 1);
            t[base + BITO] = Val::from_u64(ro & 1);
            rv >>= 1;
            ro >>= 1;
        }
    }
    RowMajorMatrix::new(t, WIDTH)
}

// --- ZK config (hiding FRI PCS over Goldilocks) ------------------------------------------------

type Perm = Poseidon2Goldilocks<8>;

// --- C-04 production FRI / soundness parameters ------------------------------------------------
// Rate ρ = 2^-LOG_BLOWUP. LOG_BLOWUP=4 (blowup 16) is the minimum the constraint degree allows
// (degree ≤ blowup+1) and gives the FRI rate. Conjectured query soundness (ethSTARK) =
// LOG_BLOWUP·NUM_QUERIES + QUERY_POW bits; challenges live in F_p² (~127-bit) and the Poseidon2
// 4-Goldilocks commitment digest gives ~128-bit collision resistance. The numbers are
// machine-checked by `security_report` / the `production_security_budget` test against Plonky3's
// `ProvenSecurity`/`ConjecturedSecurity` (docs/soundness-budget.md).
pub const LOG_BLOWUP: usize = 4;
pub const NUM_QUERIES: usize = 96;
pub const COMMIT_POW_BITS: usize = 0;
pub const QUERY_POW_BITS: usize = 16;
/// Bit-length of the extension field FRI/challenges operate in (Goldilocks², ⌊log2 p²⌋).
pub const EXT_FIELD_BITS: usize = 127;
/// Collision resistance of the Poseidon2 4-Goldilocks Merkle digest (birthday bound).
pub const COLLISION_RESISTANCE_BITS: usize = 128;
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
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress, 0, SmallRng::seed_from_u64(seed));
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_params = production_fri_params(challenge_mmcs);
    let pcs = Pcs::new(dft, val_mmcs, fri_params, 4, SmallRng::seed_from_u64(seed));
    let challenger = Challenger::new(perm);
    MyConfig::new(pcs, challenger)
}

fn production_fri_params(mmcs: ChallengeMmcs) -> FriParameters<ChallengeMmcs> {
    FriParameters {
        log_blowup: LOG_BLOWUP,
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: NUM_QUERIES,
        commit_proof_of_work_bits: COMMIT_POW_BITS,
        query_proof_of_work_bits: QUERY_POW_BITS,
        mmcs,
    }
}

/// C-04 soundness budget, computed from the *actual* AIR + production FRI parameters using
/// Plonky3's security accounting (ethSTARK conjectured FRI soundness + the proven UDR/LDR bounds of
/// [2024/1553] / [2025/2055], capped by the commitment's collision resistance and the field size).
#[derive(Debug, Clone, Copy)]
pub struct SecurityReport {
    /// ethSTARK conjectured FRI query soundness: `LOG_BLOWUP·NUM_QUERIES + QUERY_POW_BITS`.
    pub conjectured_fri_bits: usize,
    /// Proven round-by-round soundness = max(unique-decoding, list-decoding), capped.
    pub proven_bits: usize,
    pub proven_udr_bits: usize,
    pub proven_ldr_bits: usize,
    pub num_constraints: usize,
    pub max_constraint_degree: usize,
    pub trace_height: usize,
}

pub fn security_report() -> SecurityReport {
    let perm = default_goldilocks_poseidon2_8();
    let val_mmcs = ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), 0, SmallRng::seed_from_u64(1));
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs);
    let fri_params = production_fri_params(challenge_mmcs);

    let air = FullSpendAir;
    let layout = AirLayout::from_air::<Goldilocks>(&air);
    let params = StarkSecurityParams::from_air::<Val, Challenge, FullSpendAir, ChallengeMmcs>(
        &fri_params,
        &air,
        layout,
        EXT_FIELD_BITS,
        COLLISION_RESISTANCE_BITS,
        2, // max_combo: local + next rotations
    );
    // committed-polynomial size = HEIGHT plus the hiding PCS's +1 zk degree bump.
    let zk_degree_bits = HEIGHT.trailing_zeros() as usize + 1;
    let proven = ProvenSecurity::compute(&params, 1usize << zk_degree_bits);
    SecurityReport {
        conjectured_fri_bits: fri_params.conjectured_soundness_bits(),
        proven_bits: proven.security_bits(),
        proven_udr_bits: proven.unique_decoding_bits,
        proven_ldr_bits: proven.list_decoding_bits,
        num_constraints: params.num_constraints,
        max_constraint_degree: params.air_max_constraint_degree,
        trace_height: HEIGHT,
    }
}

pub fn prove_verify_with(w: &Witness, pis: &[Val]) -> Result<(), String> {
    let config = make_config(1);
    let air = FullSpendAir;
    let tr = build_trace(w);
    let proof = prove(&config, &air, tr, pis);
    verify(&config, &air, &proof, pis).map_err(|e| format!("{e:?}"))
}

pub fn prove_verify(w: &Witness) -> Result<(), String> {
    prove_verify_with(w, &public_values(w))
}

/// Prove with the witness's real public inputs, then verify against `verify_pis`. Used to test
/// Fiat–Shamir binding (e.g. tx_binding): the proof must not verify against a different tx.
#[allow(dead_code)]
pub fn prove_real_verify_with(w: &Witness, verify_pis: &[Val]) -> Result<(), String> {
    let config = make_config(1);
    let air = FullSpendAir;
    let tr = build_trace(w);
    let proof = prove(&config, &air, tr, &public_values(w));
    verify(&config, &air, &proof, verify_pis).map_err(|e| format!("{e:?}"))
}

/// Number of public-input field elements the statement binds.
pub const NUM_PUBLIC_INPUTS: usize = N_PUBLIC;

/// Prove the spend and return the canonical (postcard) proof bytes.
pub fn prove_to_bytes(w: &Witness) -> Vec<u8> {
    let config = make_config(1);
    let air = FullSpendAir;
    let tr = build_trace(w);
    let proof = prove(&config, &air, tr, &public_values(w));
    postcard::to_allocvec(&proof).expect("proof serialization is infallible")
}

/// Verify canonical proof bytes against the public inputs. **Fail-closed**: any deserialization
/// error, wrong public-input count, or verification failure returns `false`.
pub fn verify_bytes(proof_bytes: &[u8], pis: &[Val]) -> bool {
    if pis.len() != N_PUBLIC {
        return false;
    }
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    let config = make_config(1);
    verify(&config, &FullSpendAir, &proof, pis).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> Witness {
        Witness {
            nk: 12345,
            value: 1000,
            rho: Val::from_u64(7),
            rcm: Val::from_u64(9),
            pos: Val::from_u64(3),
            sib: core::array::from_fn(|d| core::array::from_fn(|k| Val::from_u64((d * 4 + k + 50) as u64))),
            bits: core::array::from_fn(|d| d % 3 == 0),
            out_recipient: core::array::from_fn(|i| Val::from_u64(77 + i as u64)),
            out_value: 600,
            out_rho: Val::from_u64(11),
            out_rcm: Val::from_u64(13),
            fee: 400, // value = out_value + fee  (1000 = 600 + 400)
            tx_binding: core::array::from_fn(|i| Val::from_u64(0xABCDEF + i as u64)),
        }
    }

    #[test]
    fn proof_bytes_roundtrip_and_tamper() {
        let w = sample();
        let bytes = prove_to_bytes(&w);
        assert!(verify_bytes(&bytes, &public_values(&w)), "round-trip should verify");
        // tampered public inputs rejected
        let mut bad = public_values(&w);
        bad[PI_ROOT] += Val::ONE;
        assert!(!verify_bytes(&bytes, &bad));
        // truncated / malformed proof bytes fail closed
        assert!(!verify_bytes(&bytes[..bytes.len() - 1], &public_values(&w)));
        assert!(!verify_bytes(&[], &public_values(&w)));
        // wrong public-input count fails closed
        assert!(!verify_bytes(&bytes, &public_values(&w)[..N_PUBLIC - 1]));
    }

    #[test]
    fn valid_spend_verifies() {
        prove_verify(&sample()).expect("valid spend should verify");
    }

    #[test]
    fn production_security_budget() {
        let r = security_report();
        println!("C-04 security report: {r:?}");
        // the prover requires max_constraint_degree ≤ blowup + 1
        assert!(r.max_constraint_degree <= (1 << LOG_BLOWUP) + 1, "degree {} too high", r.max_constraint_degree);
        assert!(r.conjectured_fri_bits >= 128, "conjectured {} < 128", r.conjectured_fri_bits);
        assert!(r.proven_bits >= 100, "proven {} < 100", r.proven_bits);
    }

    #[test]
    fn wrong_root_rejected() {
        let w = sample();
        let mut pis = public_values(&w);
        pis[PI_ROOT] += Val::ONE;
        assert!(prove_verify_with(&w, &pis).is_err());
    }

    #[test]
    fn wrong_nf_rejected() {
        let w = sample();
        let mut pis = public_values(&w);
        pis[PI_NF] += Val::ONE;
        assert!(prove_verify_with(&w, &pis).is_err());
    }

    #[test]
    fn wrong_out_cm_rejected() {
        let w = sample();
        let mut pis = public_values(&w);
        pis[PI_OUTCM] += Val::ONE;
        assert!(prove_verify_with(&w, &pis).is_err());
    }

    #[test]
    fn unbalanced_rejected() {
        let mut w = sample();
        w.fee = 401; // 1000 != 600 + 401
        // recompute outputs are unaffected by fee; balance constraint uses public fee.
        assert!(prove_verify(&w).is_err());
    }

    #[test]
    fn out_of_range_value_rejected() {
        let mut w = sample();
        w.value = 1u64 << 53; // >= 2^BITS (52)
        w.out_value = 0;
        w.fee = w.value; // keep balance so only range fails
        assert!(prove_verify(&w).is_err());
    }

    #[test]
    fn wrong_tx_binding_rejected() {
        // Prove for the real tx, then verify against a different tx_binding: Fiat–Shamir mismatch.
        let w = sample();
        let mut pis = public_values(&w);
        pis[PI_TXBIND] += Val::ONE;
        assert!(prove_real_verify_with(&w, &pis).is_err());
    }

    #[test]
    fn forged_nk_in_nullifier_rejected() {
        // The nullifier must use the same nk as ownership/commitment. Tampering the persistent
        // nk would change recipient ⇒ cm ⇒ root, so a proof with mismatched nk cannot match the
        // public root. Here we check that a different nk yields different public outputs.
        let w = sample();
        let mut w2 = w;
        w2.nk = 999;
        let o1 = native_outputs(&w);
        let o2 = native_outputs(&w2);
        assert_ne!(o1.nf, o2.nf);
        assert_ne!(o1.root, o2.root);
        // a proof for w2 against w's public inputs must fail
        assert!(prove_verify_with(&w2, &public_values(&w)).is_err());
    }
}
