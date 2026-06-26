//! M4a — the Poseidon2-Goldilocks permutation as an **across-rows** custom `uni-stark` AIR.
//!
//! This is the foundational building block of the single-AIR spend statement (option B). One
//! permutation occupies `BLOCK = 32` rows: row 0 = input, then 31 transition steps matching the
//! native `Poseidon2` sequence — initial external linear layer, 4 initial full rounds, 22 partial
//! rounds, 4 terminal full rounds — and row 31 = output. The **vetted** linear layers
//! (`GenericPoseidon2LinearLayersGoldilocks`) and **vetted** round constants
//! (`GOLDILOCKS_POSEIDON2_RC_8_*`) are reused; only the S-box (`x⁷`), the round-constant add, and
//! the round sequencing are written here. The round type + constants per row come from periodic
//! columns. Validated against the native `Poseidon2Goldilocks` permutation, and proven/verified
//! under the hiding (ZK) PCS.
//!
//! Linking many permutations (membership chain, etc.) happens at the free `t=31` block boundary —
//! that is M4b.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{FriParameters, HidingFriPcs};
use p3_goldilocks::{
    default_goldilocks_poseidon2_8, GenericPoseidon2LinearLayersGoldilocks, Goldilocks,
    Poseidon2Goldilocks, GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_FINAL,
    GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_INITIAL, GOLDILOCKS_POSEIDON2_RC_8_INTERNAL,
};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeHidingMmcs;
use p3_poseidon2::GenericPoseidon2LinearLayers;
use p3_symmetric::{PaddingFreeSponge, Permutation, TruncatedPermutation};
use p3_uni_stark::{prove, verify, StarkConfig};
use rand::rngs::SmallRng;
use rand::SeedableRng;

const W: usize = 8; // state width
const BLOCK: usize = 32; // rows per permutation (31 transitions + output row)
const FULL_HALF: usize = 4; // initial / terminal full rounds
const PARTIAL: usize = 22; // partial rounds

type Val = Goldilocks;
type LL = GenericPoseidon2LinearLayersGoldilocks;

fn pow7<R: PrimeCharacteristicRing>(x: R) -> R {
    let x2 = x.clone() * x.clone();
    let x4 = x2.clone() * x2.clone();
    x4 * x2 * x
}

fn ext_linear<R: PrimeCharacteristicRing>(s: &mut [R; W]) {
    LL::external_linear_layer(s);
}
fn int_linear<R: PrimeCharacteristicRing>(s: &mut [R; W]) {
    LL::internal_linear_layer(s);
}

/// The native permutation, computed step-by-step with the vetted constants/layers (so it can fill
/// the trace). Equals `Poseidon2Goldilocks::permute` (checked in tests).
fn native_steps(input: [Val; W]) -> [[Val; W]; BLOCK] {
    let mut rows = [[Val::ZERO; W]; BLOCK];
    let mut s = input;
    rows[0] = s;
    // t=0: initial external linear layer
    ext_linear(&mut s);
    rows[1] = s;
    // t=1..=4: initial full rounds
    for r in 0..FULL_HALF {
        for i in 0..W {
            s[i] = pow7(s[i] + GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_INITIAL[r][i]);
        }
        ext_linear(&mut s);
        rows[2 + r] = s;
    }
    // t=5..=26: partial rounds
    for r in 0..PARTIAL {
        s[0] = pow7(s[0] + GOLDILOCKS_POSEIDON2_RC_8_INTERNAL[r]);
        int_linear(&mut s);
        rows[2 + FULL_HALF + r] = s;
    }
    // t=27..=30: terminal full rounds
    for r in 0..FULL_HALF {
        for i in 0..W {
            s[i] = pow7(s[i] + GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_FINAL[r][i]);
        }
        ext_linear(&mut s);
        rows[2 + FULL_HALF + PARTIAL + r] = s;
    }
    rows
}

pub fn native_permute(input: [Val; W]) -> [Val; W] {
    let mut s = input;
    default_goldilocks_poseidon2_8().permute_mut(&mut s);
    s
}

// --- periodic columns: [is_init, is_full, is_partial, rc0..rc8] (length BLOCK) -----------------

const N_PERIODIC: usize = 3 + W; // 11

fn periodic_table() -> Vec<Vec<Val>> {
    let mut is_init = vec![Val::ZERO; BLOCK];
    let mut is_full = vec![Val::ZERO; BLOCK];
    let mut is_partial = vec![Val::ZERO; BLOCK];
    let mut rc: Vec<Vec<Val>> = (0..W).map(|_| vec![Val::ZERO; BLOCK]).collect();

    is_init[0] = Val::ONE;
    // t=1..=4 initial full
    for r in 0..FULL_HALF {
        let t = 1 + r;
        is_full[t] = Val::ONE;
        for i in 0..W {
            rc[i][t] = GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_INITIAL[r][i];
        }
    }
    // t=5..=26 partial
    for r in 0..PARTIAL {
        let t = 1 + FULL_HALF + r;
        is_partial[t] = Val::ONE;
        rc[0][t] = GOLDILOCKS_POSEIDON2_RC_8_INTERNAL[r];
    }
    // t=27..=30 terminal full
    for r in 0..FULL_HALF {
        let t = 1 + FULL_HALF + PARTIAL + r;
        is_full[t] = Val::ONE;
        for i in 0..W {
            rc[i][t] = GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_FINAL[r][i];
        }
    }
    let mut cols = vec![is_init, is_full, is_partial];
    cols.extend(rc);
    cols
}

// --- AIR --------------------------------------------------------------------------------------

pub struct Poseidon2RowsAir;

impl BaseAir<Goldilocks> for Poseidon2RowsAir {
    fn width(&self) -> usize {
        W
    }
    fn num_public_values(&self) -> usize {
        W // the permutation output
    }
    fn num_periodic_columns(&self) -> usize {
        N_PERIODIC
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        periodic_table()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for Poseidon2RowsAir {
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
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();

        // init external linear layer: next = M_ext(cur)
        let mut init_s: [AB::Expr; W] = core::array::from_fn(|i| cur[i].clone());
        ext_linear(&mut init_s);

        // full round: next = M_ext(sbox(cur + rc))
        let mut full_s: [AB::Expr; W] = core::array::from_fn(|i| pow7(cur[i].clone() + rc[i].clone()));
        ext_linear(&mut full_s);

        // partial round: next = M_int( [sbox(cur0 + rc0), cur1, .., cur7] )
        let mut part_s: [AB::Expr; W] =
            core::array::from_fn(|i| if i == 0 { pow7(cur[0].clone() + rc[0].clone()) } else { cur[i].clone() });
        int_linear(&mut part_s);

        for i in 0..W {
            let c = is_init.clone() * (nxt[i].clone() - init_s[i].clone())
                + is_full.clone() * (nxt[i].clone() - full_s[i].clone())
                + is_partial.clone() * (nxt[i].clone() - part_s[i].clone());
            builder.when_transition().assert_zero(c);
        }

        // boundary: the last row is the permutation output (public).
        let mut when_last = builder.when_last_row();
        for i in 0..W {
            when_last.assert_eq(cur_vars[i], pis[i].clone());
        }
    }
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

fn trace(input: [Val; W]) -> RowMajorMatrix<Val> {
    let rows = native_steps(input);
    let mut vals = Vec::with_capacity(BLOCK * W);
    for r in rows.iter() {
        vals.extend_from_slice(r);
    }
    RowMajorMatrix::new(vals, W)
}

pub fn prove_verify(input: [Val; W]) -> Result<(), String> {
    let config = make_config(1);
    let air = Poseidon2RowsAir;
    let out = native_permute(input);
    let tr = trace(input);
    let pis = out.to_vec();
    let proof = prove(&config, &air, tr, &pis);
    verify(&config, &air, &proof, &pis).map_err(|e| format!("{e:?}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_steps_match_poseidon2_goldilocks() {
        let input: [Val; W] = core::array::from_fn(|i| Val::from_u64(i as u64 + 1));
        let rows = native_steps(input);
        assert_eq!(rows[BLOCK - 1], native_permute(input), "across-rows trace must match native");
    }

    #[test]
    fn air_proves_and_verifies() {
        let input: [Val; W] = core::array::from_fn(|i| Val::from_u64(i as u64 * 7 + 3));
        prove_verify(input).expect("prove/verify should succeed");
    }

    #[test]
    fn wrong_output_rejected() {
        let input: [Val; W] = core::array::from_fn(|i| Val::from_u64(i as u64 + 1));
        let config = make_config(1);
        let air = Poseidon2RowsAir;
        let mut out = native_permute(input);
        out[0] += Val::ONE; // claim a wrong output
        let tr = trace(input);
        let pis = out.to_vec();
        let proof = prove(&config, &air, tr, &pis);
        assert!(verify(&config, &air, &proof, &pis).is_err());
    }
}
