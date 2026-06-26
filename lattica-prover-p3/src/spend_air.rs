//! M4b — commitment + Merkle membership as one across-rows `uni-stark` AIR (ZK).
//!
//! Composes `NUM_BLOCKS = 1 + DEPTH` Poseidon2 permutations (M4a's block) into one trace:
//!   * block 0 = commitment: `cm = Perm([recipient, value, rho, rcm, 0,0,0,0])[0..4]`;
//!   * blocks 1..=DEPTH = Merkle merges: `node' = Perm(ordered(node, sibling))[0..4]`, general
//!     position (a per-merge bit picks left/right).
//! The running digest folds up to the public `root`. Each block's 31 within-block transitions are
//! the M4a Poseidon2 round constraints (reused, vetted constants/layers); the block boundaries
//! (`is_link`, `t≡31`) carry the running digest into the next merge's input (the other half is the
//! free sibling), with the position bit constrained boolean. Validated against the native fold and
//! proven/verified under the hiding (ZK) PCS.

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

use crate::poseidon2_air::{ext_linear, int_linear, native_permute, native_steps, periodic_table, pow7, BLOCK, W};

pub const DEPTH: usize = 3; // membership levels (NUM_BLOCKS must stay a power of two)
const NUM_BLOCKS: usize = 1 + DEPTH; // commitment + DEPTH merges = 4
const HEIGHT: usize = NUM_BLOCKS * BLOCK; // 128
const DIGEST: usize = 4;
const WIDTH: usize = W + 1; // 8 state + 1 position bit
const BIT: usize = W; // col 8
const N_PERIODIC: usize = (3 + W) + 1; // round schedule (11) + is_link
const LINK_T: usize = BLOCK - 1; // t within a block where the boundary link applies

type Val = Goldilocks;

// --- native oracle ----------------------------------------------------------------------------

fn commit(opening: [Val; DIGEST]) -> [Val; DIGEST] {
    let mut s = [Val::ZERO; W];
    s[..DIGEST].copy_from_slice(&opening);
    native_permute(s)[..DIGEST].try_into().unwrap()
}
fn merge(left: [Val; DIGEST], right: [Val; DIGEST]) -> [Val; DIGEST] {
    let mut s = [Val::ZERO; W];
    s[..DIGEST].copy_from_slice(&left);
    s[DIGEST..].copy_from_slice(&right);
    native_permute(s)[..DIGEST].try_into().unwrap()
}
pub fn native_root(opening: [Val; DIGEST], sib: &[[Val; DIGEST]; DEPTH], bits: &[bool; DEPTH]) -> [Val; DIGEST] {
    let mut node = commit(opening);
    for d in 0..DEPTH {
        node = if bits[d] { merge(sib[d], node) } else { merge(node, sib[d]) };
    }
    node
}

// --- periodic columns: round schedule (period 32) + is_link (1 at t=LINK_T) --------------------

fn periodic() -> Vec<Vec<Val>> {
    let mut cols = periodic_table(); // 11 round-schedule columns, length BLOCK
    let mut is_link = vec![Val::ZERO; BLOCK];
    is_link[LINK_T] = Val::ONE;
    cols.push(is_link);
    cols
}

// --- AIR --------------------------------------------------------------------------------------

pub struct SpendAir;

impl BaseAir<Goldilocks> for SpendAir {
    fn width(&self) -> usize {
        WIDTH
    }
    fn num_public_values(&self) -> usize {
        DIGEST // the root
    }
    fn num_periodic_columns(&self) -> usize {
        N_PERIODIC
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        periodic()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for SpendAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let cur_vars: Vec<AB::Var> = main.current_slice().to_vec();
        let p = builder.periodic_values();
        let is_init: AB::Expr = p[0].into();
        let is_full: AB::Expr = p[1].into();
        let is_partial: AB::Expr = p[2].into();
        let rc: Vec<AB::Expr> = (0..W).map(|i| p[3 + i].into()).collect();
        let is_link: AB::Expr = p[3 + W].into();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;

        // --- within-block Poseidon2 round constraints (on the 8 state columns) ---
        let st: [AB::Expr; W] = core::array::from_fn(|i| cur[i].clone());
        let mut init_s = st.clone();
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

        // --- block-boundary link: running digest cur[0..4] is placed (by the bit) into the next
        //     merge's input; the other half is the free sibling; the bit is boolean ---
        let bit = nxt[BIT].clone();
        for i in 0..DIGEST {
            let placed = (one.clone() - bit.clone()) * (nxt[i].clone() - cur[i].clone())
                + bit.clone() * (nxt[DIGEST + i].clone() - cur[i].clone());
            builder.when_transition().assert_zero(is_link.clone() * placed);
        }
        builder
            .when_transition()
            .assert_zero(is_link.clone() * (bit.clone() * (one.clone() - bit.clone())));

        // --- boundaries: commitment pad (row 0, state[4..8]=0) and root (last row, state[0..4]) ---
        let mut when_first = builder.when_first_row();
        for i in DIGEST..W {
            when_first.assert_zero(cur_vars[i]);
        }
        let mut when_last = builder.when_last_row();
        for i in 0..DIGEST {
            when_last.assert_eq(cur_vars[i], pis[i].clone());
        }
    }
}

// --- trace ------------------------------------------------------------------------------------

fn fill_block(trace: &mut [Val], block: usize, input: [Val; W], bit: Option<bool>) {
    let rows = native_steps(input);
    for (r, row) in rows.iter().enumerate() {
        let base = (block * BLOCK + r) * WIDTH;
        trace[base..base + W].copy_from_slice(row);
        trace[base + BIT] = Val::ZERO;
    }
    // the position bit lives on this block's input row (read by the link from the previous block)
    if let Some(b) = bit {
        let base = (block * BLOCK) * WIDTH;
        trace[base + BIT] = if b { Val::ONE } else { Val::ZERO };
    }
}

fn build_trace(opening: [Val; DIGEST], sib: &[[Val; DIGEST]; DEPTH], bits: &[bool; DEPTH]) -> RowMajorMatrix<Val> {
    let mut trace = vec![Val::ZERO; HEIGHT * WIDTH];
    // block 0: commitment input [opening, 0,0,0,0]
    let mut cin = [Val::ZERO; W];
    cin[..DIGEST].copy_from_slice(&opening);
    fill_block(&mut trace, 0, cin, None);
    // blocks 1..=DEPTH: merges
    let mut node = commit(opening);
    for d in 0..DEPTH {
        let (l, r) = if bits[d] { (sib[d], node) } else { (node, sib[d]) };
        let mut min = [Val::ZERO; W];
        min[..DIGEST].copy_from_slice(&l);
        min[DIGEST..].copy_from_slice(&r);
        fill_block(&mut trace, d + 1, min, Some(bits[d]));
        node = native_permute(min)[..DIGEST].try_into().unwrap();
    }
    RowMajorMatrix::new(trace, WIDTH)
}

// --- ZK config (hiding FRI PCS over Goldilocks) ------------------------------------------------

type Perm = Poseidon2Goldilocks<8>;
const LOG_BLOWUP: usize = 3;
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
    let fri_params = FriParameters {
        log_blowup: LOG_BLOWUP,
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 24,
        commit_proof_of_work_bits: 1,
        query_proof_of_work_bits: 1,
        mmcs: challenge_mmcs,
    };
    let pcs = Pcs::new(dft, val_mmcs, fri_params, 4, SmallRng::seed_from_u64(seed));
    let challenger = Challenger::new(perm);
    MyConfig::new(pcs, challenger)
}

pub fn prove_verify(
    opening: [Val; DIGEST],
    sib: [[Val; DIGEST]; DEPTH],
    bits: [bool; DEPTH],
    claimed_root: [Val; DIGEST],
) -> Result<(), String> {
    let config = make_config(1);
    let air = SpendAir;
    let tr = build_trace(opening, &sib, &bits);
    let pis = claimed_root.to_vec();
    let proof = prove(&config, &air, tr, &pis);
    verify(&config, &air, &proof, &pis).map_err(|e| format!("{e:?}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> ([Val; DIGEST], [[Val; DIGEST]; DEPTH], [bool; DEPTH]) {
        let opening = core::array::from_fn(|i| Val::from_u64(i as u64 + 1));
        let mut sib = [[Val::ZERO; DIGEST]; DEPTH];
        let mut bits = [false; DEPTH];
        for d in 0..DEPTH {
            sib[d] = core::array::from_fn(|k| Val::from_u64((d * 10 + k + 100) as u64));
            bits[d] = d % 2 == 1;
        }
        (opening, sib, bits)
    }

    #[test]
    fn trace_root_matches_native() {
        let (opening, sib, bits) = sample();
        let tr = build_trace(opening, &sib, &bits);
        let last = (HEIGHT - 1) * WIDTH;
        let air_root: [Val; DIGEST] = tr.values[last..last + DIGEST].try_into().unwrap();
        assert_eq!(air_root, native_root(opening, &sib, &bits));
    }

    #[test]
    fn valid_membership_verifies() {
        let (opening, sib, bits) = sample();
        let root = native_root(opening, &sib, &bits);
        prove_verify(opening, sib, bits, root).expect("should verify");
    }

    #[test]
    fn wrong_root_rejected() {
        let (opening, sib, bits) = sample();
        let mut root = native_root(opening, &sib, &bits);
        root[0] += Val::ONE;
        assert!(prove_verify(opening, sib, bits, root).is_err());
    }

    #[test]
    fn tampered_opening_changes_root() {
        let (opening, sib, bits) = sample();
        let real = native_root(opening, &sib, &bits);
        let mut bad = opening;
        bad[1] += Val::ONE; // different value ⇒ different cm ⇒ different root
        assert_ne!(native_root(bad, &sib, &bits), real);
        assert!(prove_verify(bad, sib, bits, real).is_err());
    }
}
