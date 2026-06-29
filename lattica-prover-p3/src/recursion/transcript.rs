//! B2 spike — the in-circuit **Fiat-Shamir transcript** (Plonky3 `DuplexChallenger` over Poseidon2).
//!
//! The recursive verifier must replay the prover↔verifier transcript in-circuit: absorb the
//! commitments + public values, squeeze the challenges (α, ζ, the FRI round challenges β_i, query
//! indices). The challenger is a Poseidon2 **duplex sponge** (width 8, rate 4, capacity 4): `observe`
//! buffers field elements and, every `RATE`, runs one permutation (overwriting the rate lanes, keeping
//! the capacity, and folding the prefix-free count `+= num_absorbed` into the first capacity lane);
//! `sample` squeezes from the rate lanes of the last permutation.
//!
//! This spike (a) pins the EXACT native semantics with a fast fidelity check against the real
//! `DuplexChallenger`, and (b) builds an AIR that reproduces the squeeze in-circuit (chained
//! `poseidon2_air` blocks, capacity carried + prefix-free count linked across blocks), validated
//! against the native sponge. Scope: the absorb-a-multiple-of-RATE-then-sample case (the core mechanic);
//! variable-length buffering + `sample_bits` are follow-ons. Base-field only.

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
use p3_uni_stark::{prove, verify, Proof, StarkConfig};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use crate::poseidon2_air::{ext_linear, int_linear, native_permute, native_steps, periodic_table, pow7, BLOCK, W};

type Val = Goldilocks;
const RATE: usize = 4;
const CAP_LANE: usize = RATE; // first capacity lane = state[4], holds the prefix-free count

const P_BLOCK_LAST: usize = 11; // appended after poseidon2's 11 round columns
const N_PERIODIC: usize = P_BLOCK_LAST + 1;

/// Native duplex sponge over `native_permute`, modeling `DuplexChallenger` for the
/// observe-(RATE·m)-then-sample case: each block overwrites the rate lanes with the next RATE absorbed
/// elements, keeps the capacity, folds `+= RATE` into `state[CAP_LANE]`, permutes. Returns the final
/// rate lanes (the squeeze source). Pinned equal to the real challenger by `fidelity_*` tests.
pub fn native_sponge(blocks: &[[Val; RATE]]) -> [Val; RATE] {
    let mut state_out = [Val::ZERO; W];
    let mut cap = [Val::ZERO; W - RATE];
    for blk in blocks {
        let mut input = [Val::ZERO; W];
        input[..RATE].copy_from_slice(blk);
        input[RATE..].copy_from_slice(&cap);
        input[CAP_LANE] += Val::from_u64(RATE as u64); // prefix-free num_absorbed
        state_out = native_permute(input);
        cap.copy_from_slice(&state_out[RATE..]);
    }
    state_out[..RATE].try_into().unwrap()
}

fn periodic() -> Vec<Vec<Val>> {
    let mut cols = periodic_table();
    let mut block_last = vec![Val::ZERO; BLOCK];
    block_last[BLOCK - 1] = Val::ONE;
    cols.push(block_last);
    cols
}

/// AIR: an `m`-block Poseidon2 duplex sponge. The rate lanes of each block's input are free witness (the
/// absorbed transcript); the capacity is carried from the previous block with `state[CAP_LANE] += RATE`;
/// the first block starts from the zero capacity (so `state[CAP_LANE] == RATE`). The final block's rate
/// output is bound to the public squeeze.
pub struct SpongeAir {
    pub blocks: usize,
}

impl BaseAir<Goldilocks> for SpongeAir {
    fn width(&self) -> usize {
        W
    }
    fn num_public_values(&self) -> usize {
        RATE // the squeezed rate lanes
    }
    fn num_periodic_columns(&self) -> usize {
        N_PERIODIC
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        periodic()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for SpongeAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let rate = AB::Expr::from(Goldilocks::from_u64(RATE as u64));

        // ---- Poseidon2 round constraints per block (reused from poseidon2_air) ----
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

        // ---- block 0 starts from the zero capacity: state[CAP_LANE] == RATE, other capacity lanes == 0
        //      (the rate lanes 0..RATE are free = the first absorbed block). ----
        {
            let mut fr = builder.when_first_row();
            fr.assert_zero(cur[CAP_LANE].clone() - rate.clone());
            for i in (CAP_LANE + 1)..W {
                fr.assert_zero(cur[i].clone());
            }
        }

        // ---- link: block i output (row 31) carries the capacity into block i+1's input (row 0), with
        //      the prefix-free count folded in: nxt.cap[CAP_LANE] = cur.out[CAP_LANE] + RATE, other
        //      capacity lanes copied; the rate lanes of nxt are free (the next absorbed block). ----
        {
            let bl = p[P_BLOCK_LAST].clone();
            builder
                .when_transition()
                .assert_zero(bl.clone() * (nxt[CAP_LANE].clone() - (cur[CAP_LANE].clone() + rate.clone())));
            for i in (CAP_LANE + 1)..W {
                builder.when_transition().assert_zero(bl.clone() * (nxt[i].clone() - cur[i].clone()));
            }
        }

        // ---- squeeze: the final block's rate lanes == public output ----
        {
            let mut lr = builder.when_last_row();
            for k in 0..RATE {
                lr.assert_zero(cur[k].clone() - pis[k].clone());
            }
        }
    }
}

fn build_trace(blocks: &[[Val; RATE]]) -> RowMajorMatrix<Val> {
    let m = blocks.len();
    let mut t = vec![Val::ZERO; m * BLOCK * W];
    let mut cap = [Val::ZERO; W - RATE];
    for (j, blk) in blocks.iter().enumerate() {
        let mut input = [Val::ZERO; W];
        input[..RATE].copy_from_slice(blk);
        input[RATE..].copy_from_slice(&cap);
        input[CAP_LANE] += Val::from_u64(RATE as u64);
        let rows = native_steps(input);
        for r in 0..BLOCK {
            let base = (j * BLOCK + r) * W;
            t[base..base + W].copy_from_slice(&rows[r]);
        }
        let out = native_permute(input);
        cap.copy_from_slice(&out[RATE..]);
    }
    RowMajorMatrix::new(t, W)
}

// --- FRI config (same as the spike's) ----------------------------------------------------------
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
    let val_mmcs = ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), 6, ChaCha20Rng::from_rng(&mut rand::rng()));
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
    let pcs = Pcs::new(Dft::default(), val_mmcs, fri, 4, ChaCha20Rng::from_rng(&mut rand::rng()));
    MyConfig::new(pcs, Challenger::new(perm))
}

/// Prove that absorbing `blocks` squeezes `out` (the final rate lanes).
pub fn prove_squeeze(blocks: &[[Val; RATE]], out: [Val; RATE]) -> Vec<u8> {
    let proof = prove(&make_config(), &SpongeAir { blocks: blocks.len() }, build_trace(blocks), &out.to_vec());
    postcard::to_allocvec(&proof).expect("serialize")
}

pub fn verify_squeeze(proof_bytes: &[u8], out: [Val; RATE], blocks: usize) -> bool {
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), &SpongeAir { blocks }, &proof, &out.to_vec()).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_challenger::{CanObserve, FieldChallenger};
    use p3_field::BasedVectorSpace;

    fn blocks_of(m: usize) -> Vec<[Val; RATE]> {
        (0..m).map(|j| core::array::from_fn(|k| Val::from_u64(1 + (j * RATE + k) as u64))).collect()
    }

    #[test]
    fn fidelity_native_sponge_matches_duplex_challenger() {
        // The real DuplexChallenger, observing RATE·m elements then sampling an F_p² challenge, must
        // squeeze from the same rate lanes our native_sponge computes. This pins the model.
        for m in [1usize, 2, 3] {
            let blocks = blocks_of(m);
            let sq = native_sponge(&blocks);
            let mut ch = Challenger::new(default_goldilocks_poseidon2_8());
            for blk in &blocks {
                for &x in blk {
                    ch.observe(x);
                }
            }
            let c: Challenge = ch.sample_algebra_element();
            let coeffs = <Challenge as BasedVectorSpace<Val>>::as_basis_coefficients_slice(&c);
            // sample pops DIMENSION=2 base elements from the squeezed rate lanes; assert they come from
            // our squeeze (the exact lane/order is asserted here, fixing the model).
            // `sample` pops the squeezed rate lanes from the BACK of the output buffer, so the F_p²
            // challenge coefficients are (rate[3], rate[2]). This pins the model exactly.
            assert_eq!(coeffs.len(), 2);
            assert_eq!(coeffs[0], sq[3], "m={m}: challenge coeff0 != squeeze[3]");
            assert_eq!(coeffs[1], sq[2], "m={m}: challenge coeff1 != squeeze[2]");
        }
    }

    #[test]
    #[ignore = "slow: real prover (in-circuit transcript squeeze)"]
    fn in_circuit_squeeze_matches_native() {
        let blocks = blocks_of(2); // 8 absorbed elements
        let sq = native_sponge(&blocks);
        let proof = prove_squeeze(&blocks, sq);
        assert!(verify_squeeze(&proof, sq, blocks.len()));
        // wrong squeeze ⇒ reject
        let mut bad = sq;
        bad[0] += Val::ONE;
        assert!(!verify_squeeze(&proof, bad, blocks.len()));
    }

    #[test]
    #[ignore = "slow: corrupted-trace transcript"]
    fn tampered_absorb_changes_squeeze() {
        let blocks = blocks_of(2);
        let sq = native_sponge(&blocks);
        // a different absorbed transcript must not authenticate to the original squeeze.
        let mut tampered = blocks.clone();
        tampered[0][0] += Val::ONE;
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let p = prove_squeeze(&tampered, sq); // squeeze no longer matches the tampered absorb
            verify_squeeze(&p, sq, tampered.len())
        }));
        assert!(matches!(outcome, Ok(false) | Err(_)));
    }
}
