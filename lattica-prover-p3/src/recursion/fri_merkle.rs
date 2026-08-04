//! B1 spike — an in-circuit **FRI-query Merkle-opening verifier**.
//!
//! A FRI verifier's dominant, most-repeated work is verifying Merkle authentication paths of the
//! committed polynomials at the sampled query indices (96 queries × several openings each × path
//! depth). The internal-node compression of that Merkle tree is `TruncatedPermutation<Perm,2,4,8>`,
//! which is **bit-identical to lattica's `merge`** (`native_permute(l‖r)[0..4]`) — the same compression
//! the `joinsplit_air` membership fold already verifies in-circuit at depth 32. This spike builds a
//! standalone AIR that, given a leaf digest + a sibling/bit path, recomputes the Merkle root by
//! bit-controlled `merge` up the path (each level = one Poseidon2 permutation block, reusing
//! `poseidon2_air`'s round constraints) and binds it to a public root. It exists to (a) prove the reuse
//! is correct (differential vs the native `merge`-tree opening), (b) reject tampered paths
//! (corrupted-trace), and (c) benchmark the per-path in-circuit cost for the go/no-go.
//!
//! Scope: base-field only. The F_p² FRI *folding* arithmetic, the transcript (B2), and the
//! OOD/quotient check (B3) are NOT in this spike — this is the hashing skeleton, the size-dominant part.

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

use crate::poseidon2_air::{
    ext_linear, int_linear, native_permute, native_steps, periodic_table, pow7, BLOCK, W,
};

type Val = Goldilocks;
const DIGEST: usize = 4;

// --- column layout (width 13): 8 Poseidon2 state lanes ‖ 4 sibling lanes ‖ 1 index bit -----------
const SIB: usize = W; // 8..12
const BIT: usize = SIB + DIGEST; // 12
const WIDTH: usize = BIT + 1; // 13

// periodic: poseidon2's 11 round columns (is_init,is_full,is_partial,rc0..7) + P_BLOCK_LAST (row 31)
const P_BLOCK_LAST: usize = 11;
const N_PERIODIC: usize = P_BLOCK_LAST + 1; // 12

/// The FRI internal-node compression — identical to `joinsplit_air::merge` and to the MMCS's
/// `TruncatedPermutation<Perm,2,4,8>`. Kept local so the spike is self-contained.
fn merge(l: [Val; DIGEST], r: [Val; DIGEST]) -> [Val; DIGEST] {
    let mut s = [Val::ZERO; W];
    s[..DIGEST].copy_from_slice(&l);
    s[DIGEST..].copy_from_slice(&r);
    native_permute(s)[..DIGEST].try_into().unwrap()
}

fn periodic() -> Vec<Vec<Val>> {
    let mut cols = periodic_table(); // 11 round columns, length BLOCK
    let mut block_last = vec![Val::ZERO; BLOCK];
    block_last[BLOCK - 1] = Val::ONE; // row 31 of every block
    cols.push(block_last);
    cols
}

/// Height-agnostic: the path depth is implied by the trace height (the proof carries it).
pub struct FriMerkleAir;

impl BaseAir<Goldilocks> for FriMerkleAir {
    fn width(&self) -> usize {
        WIDTH
    }
    fn num_public_values(&self) -> usize {
        2 * DIGEST // leaf ‖ root
    }
    fn num_periodic_columns(&self) -> usize {
        N_PERIODIC
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        periodic()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for FriMerkleAir {
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

        // ---- Poseidon2 round constraints per block (period-32 schedule; reused verbatim from
        //      poseidon2_air). At row 31 all three selectors are 0, so the block→block transition is
        //      free for the link constraint below. ----
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
            let c = is_init.clone() * (nxt[i].clone() - init_s[i].clone())
                + is_full.clone() * (nxt[i].clone() - full_s[i].clone())
                + is_partial.clone() * (nxt[i].clone() - part_s[i].clone());
            builder.when_transition().assert_zero(c);
        }

        // ---- BIT is boolean (read at each block's row 0; held constant per block in the trace) ----
        let bit = cur[BIT].clone();
        builder.assert_zero(bit.clone() * (one.clone() - bit.clone()));

        // ---- block 0 input = bit-ordered(leaf, sibling_0): node=leaf on the left if bit=0, else right.
        let leaf: Vec<AB::Expr> = (0..DIGEST).map(|k| pis[k].clone()).collect();
        {
            let b = cur[BIT].clone();
            let mut fr = builder.when_first_row();
            for k in 0..DIGEST {
                // input[k]   = (1-b)·leaf[k] + b·sib[k]
                fr.assert_zero(
                    cur[k].clone()
                        - ((one.clone() - b.clone()) * leaf[k].clone()
                            + b.clone() * cur[SIB + k].clone()),
                );
                // input[4+k] = (1-b)·sib[k]  + b·leaf[k]
                fr.assert_zero(
                    cur[DIGEST + k].clone()
                        - ((one.clone() - b.clone()) * cur[SIB + k].clone()
                            + b.clone() * leaf[k].clone()),
                );
            }
        }

        // ---- link: block i output (row 31) folds into block i+1 input (row 0), ordered by block i+1's
        //      bit. cur = row 31 (cur[0..4] = node_{i+1} = merge result), nxt = next block's row 0. ----
        {
            let bl = p[P_BLOCK_LAST].clone();
            let nb = nxt[BIT].clone();
            for k in 0..DIGEST {
                // nxt.input[k]   = (1-nb)·node[k] + nb·nxt.sib[k]
                builder.when_transition().assert_zero(
                    bl.clone()
                        * (nxt[k].clone()
                            - ((one.clone() - nb.clone()) * cur[k].clone()
                                + nb.clone() * nxt[SIB + k].clone())),
                );
                // nxt.input[4+k] = (1-nb)·nxt.sib[k] + nb·node[k]
                builder.when_transition().assert_zero(
                    bl.clone()
                        * (nxt[DIGEST + k].clone()
                            - ((one.clone() - nb.clone()) * nxt[SIB + k].clone()
                                + nb.clone() * cur[k].clone())),
                );
            }
        }

        // ---- root binding: the final block's output (last row, lanes 0..4) == public root ----
        {
            let mut lr = builder.when_last_row();
            for k in 0..DIGEST {
                lr.assert_zero(cur[k].clone() - pis[DIGEST + k].clone());
            }
        }
    }
}

// --- FRI config (production-like: blowup 4, 96 queries, arity 4 — matches the batch circuits) -----
type Perm = Poseidon2Goldilocks<8>;
type MyHash = PaddingFreeSponge<Perm, 8, 4, 4>;
type MyCompress = TruncatedPermutation<Perm, 2, 4, 8>;
type ValMmcs = MerkleTreeHidingMmcs<
    <Val as Field>::Packing,
    <Val as Field>::Packing,
    MyHash,
    MyCompress,
    ChaCha20Rng,
    2,
    4,
    4,
>;
type Challenge = BinomialExtensionField<Val, 2>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Challenger = DuplexChallenger<Val, Perm, 8, 4>;
type Dft = Radix2DitParallel<Val>;
type Pcs = HidingFriPcs<Val, Dft, ValMmcs, ChallengeMmcs, ChaCha20Rng>;
type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;

fn make_config() -> MyConfig {
    let perm = default_goldilocks_poseidon2_8();
    let val_mmcs = ValMmcs::new(
        MyHash::new(perm.clone()),
        MyCompress::new(perm.clone()),
        6,
        ChaCha20Rng::from_rng(&mut rand::rng()),
    );
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
    let pcs = Pcs::new(
        Dft::default(),
        val_mmcs,
        fri,
        4,
        ChaCha20Rng::from_rng(&mut rand::rng()),
    );
    MyConfig::new(pcs, Challenger::new(perm))
}

/// Build a Merkle tree (level 0 = leaves) using `merge` for every internal node. Requires a
/// power-of-two leaf count.
pub fn build_tree(leaves: &[[Val; DIGEST]]) -> Vec<Vec<[Val; DIGEST]>> {
    assert!(leaves.len().is_power_of_two() && !leaves.is_empty());
    let mut levels = vec![leaves.to_vec()];
    while levels.last().unwrap().len() > 1 {
        let cur = levels.last().unwrap();
        let next: Vec<[Val; DIGEST]> = cur.chunks(2).map(|pair| merge(pair[0], pair[1])).collect();
        levels.push(next);
    }
    levels
}

/// An authentication path for leaf `idx`: (leaf, [(sibling, node_is_right_child)], root).
pub fn opening(
    levels: &[Vec<[Val; DIGEST]>],
    idx: usize,
) -> ([Val; DIGEST], Vec<([Val; DIGEST], bool)>, [Val; DIGEST]) {
    let leaf = levels[0][idx];
    let mut path = Vec::with_capacity(levels.len() - 1);
    let mut i = idx;
    for level in &levels[..levels.len() - 1] {
        let sib = level[i ^ 1];
        path.push((sib, i & 1 == 1));
        i >>= 1;
    }
    (leaf, path, levels.last().unwrap()[0])
}

/// Fill the trace: one Poseidon2 permutation block per path level, folding the running node with the
/// level's sibling in the bit-selected order.
pub fn build_trace(leaf: [Val; DIGEST], path: &[([Val; DIGEST], bool)]) -> RowMajorMatrix<Val> {
    let d = path.len();
    let mut t = vec![Val::ZERO; d * BLOCK * WIDTH];
    let mut node = leaf;
    for (lvl, (sib, bit)) in path.iter().enumerate() {
        let mut input = [Val::ZERO; W];
        if *bit {
            input[..DIGEST].copy_from_slice(sib);
            input[DIGEST..].copy_from_slice(&node);
        } else {
            input[..DIGEST].copy_from_slice(&node);
            input[DIGEST..].copy_from_slice(sib);
        }
        let rows = native_steps(input);
        for r in 0..BLOCK {
            let base = (lvl * BLOCK + r) * WIDTH;
            t[base..base + W].copy_from_slice(&rows[r]);
            t[base + SIB..base + SIB + DIGEST].copy_from_slice(sib);
            t[base + BIT] = if *bit { Val::ONE } else { Val::ZERO };
        }
        node = native_permute(input)[..DIGEST].try_into().unwrap();
    }
    RowMajorMatrix::new(t, WIDTH)
}

/// Prove that the opening (leaf, path) authenticates to `root`; returns the serialized proof.
pub fn prove_opening(
    leaf: [Val; DIGEST],
    path: &[([Val; DIGEST], bool)],
    root: [Val; DIGEST],
) -> Vec<u8> {
    let mut pis = leaf.to_vec();
    pis.extend_from_slice(&root);
    let proof = prove(&make_config(), &FriMerkleAir, build_trace(leaf, path), &pis);
    postcard::to_allocvec(&proof).expect("serialize")
}

/// Verify a Merkle-opening proof against (leaf, root). Fail-closed on a bad proof.
pub fn verify_opening(proof_bytes: &[u8], leaf: [Val; DIGEST], root: [Val; DIGEST]) -> bool {
    let mut pis = leaf.to_vec();
    pis.extend_from_slice(&root);
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), &FriMerkleAir, &proof, &pis).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf_of(i: u64) -> [Val; DIGEST] {
        core::array::from_fn(|k| Val::from_u64(1 + i * 7 + k as u64))
    }

    #[test]
    fn merge_matches_native_compression() {
        // merge is exactly native_permute(l‖r)[0..4] = the FRI MMCS TruncatedPermutation<2,4,8>.
        let l = leaf_of(3);
        let r = leaf_of(9);
        let mut s = [Val::ZERO; W];
        s[..DIGEST].copy_from_slice(&l);
        s[DIGEST..].copy_from_slice(&r);
        assert_eq!(
            merge(l, r),
            <[Val; DIGEST]>::try_from(&native_permute(s)[..DIGEST]).unwrap()
        );
    }

    #[test]
    #[ignore = "slow: real prover (Merkle-opening verify)"]
    fn opening_verifies_against_native_root() {
        // depth-16 tree (2^16 leaves) — a realistic FRI input-opening depth.
        let leaves: Vec<[Val; DIGEST]> = (0..(1u64 << 16)).map(leaf_of).collect();
        let levels = build_tree(&leaves);
        let (leaf, path, root) = opening(&levels, 0xBEEF);
        assert_eq!(path.len(), 16);
        // differential: the in-circuit recomputed root (bound to pis) == the native merge-tree root.
        let proof = prove_opening(leaf, &path, root);
        assert!(verify_opening(&proof, leaf, root));
    }

    #[test]
    #[ignore = "slow: real prover (negative cases)"]
    fn rejects_wrong_root_and_tampered_sibling() {
        let leaves: Vec<[Val; DIGEST]> = (0..(1u64 << 8)).map(leaf_of).collect();
        let levels = build_tree(&leaves);
        let (leaf, path, root) = opening(&levels, 42);
        let proof = prove_opening(leaf, &path, root);
        assert!(verify_opening(&proof, leaf, root));
        // wrong root ⇒ reject
        let mut bad = root;
        bad[0] += Val::ONE;
        assert!(!verify_opening(&proof, leaf, bad));
        // a tampered sibling in the trace ⇒ unsatisfiable / different root ⇒ reject
        let mut tpath = path.clone();
        tpath[0].0[0] += Val::ONE;
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let p = prove_opening(leaf, &tpath, root); // root no longer matches the tampered path
            verify_opening(&p, leaf, root)
        }));
        assert!(matches!(outcome, Ok(false) | Err(_)));
    }

    #[test]
    #[ignore = "slow: real prover (B3-wire §9.1 proof-structure groundwork)"]
    fn proof_structure_introspection() {
        // B3-wire §9.1: pin the real Proof structure the integration must parse into trace columns.
        // opening_proof = (OpenedValues, FriProof); FriProof carries the FRI commit-phase commitments,
        // the per-query proofs, and the final polynomial. Validated against a real proof under lattica's
        // config (num_queries = 96, log_final_poly_len = 0 ⇒ final_poly length 1).
        let leaves: Vec<[Val; DIGEST]> = (0..(1u64 << 8)).map(leaf_of).collect();
        let levels = build_tree(&leaves);
        let (leaf, path, root) = opening(&levels, 5);
        let bytes = prove_opening(leaf, &path, root);
        let proof: Proof<MyConfig> = postcard::from_bytes(&bytes).unwrap();
        let fri = &proof.opening_proof.1;
        assert_eq!(fri.query_proofs.len(), 96, "one query proof per FRI query");
        assert_eq!(
            fri.final_poly.len(),
            1,
            "log_final_poly_len = 0 ⇒ constant final poly"
        );
        assert!(!fri.commit_phase_commits.is_empty());
        let rounds = fri.commit_phase_commits.len();
        for q in &fri.query_proofs {
            // each query opens once per commit-phase round
            assert_eq!(
                q.commit_phase_openings.len(),
                rounds,
                "openings per query == commit rounds"
            );
        }
        println!(
            "B3-wire proof structure: {} queries, {} commit rounds, final_poly len {}",
            fri.query_proofs.len(),
            rounds,
            fri.final_poly.len(),
        );
    }

    #[test]
    #[ignore = "slow: benchmark — per-path proving cost for the go/no-go"]
    fn benchmark_one_path() {
        use p3_field::PrimeField64;
        let leaves: Vec<[Val; DIGEST]> = (0..(1u64 << 16)).map(leaf_of).collect();
        let levels = build_tree(&leaves);
        let (leaf, path, root) = opening(&levels, 1);
        let rows = path.len() * BLOCK;
        let proof = prove_opening(leaf, &path, root);
        assert!(verify_opening(&proof, leaf, root));
        // report: rows for ONE depth-16 path + proof size. (Extrapolation to a full verifier is in
        // docs/recursion-verifier-audit.md §5: ~288 such openings ⇒ ~2^18 rows, batch-circuit scale.)
        println!(
            "fri_merkle spike: depth={} rows={} (=2^{:.1}) proof_bytes={} root0={}",
            path.len(),
            rows,
            (rows as f64).log2(),
            proof.len(),
            root[0].as_canonical_u64(),
        );
    }
}
