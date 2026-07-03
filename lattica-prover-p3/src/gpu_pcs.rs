//! `GpuHidingPcs` — the production hiding PCS with the **quotient-chunk randomization pipeline on the
//! GPU** (`--features gpu`).
//!
//! p3's `HidingFriPcs::get_quotient_ldes` randomizes each quotient chunk (Section 4.2 of
//! <https://eprint.iacr.org/2024/1037.pdf>): per chunk it runs a coset-LDE, evaluates the vanishing-poly
//! randomizer `v_H(X)·r(X)` with a **full-size `dft_batch` whose input is ~94% zero rows**, materializes
//! both results natural-order on the host (two bit-reversal permutation passes over the LDE), adds them
//! elementwise on the CPU, and bit-reverses AGAIN for storage. Per proof that is 16 full-size DFTs of
//! mostly zeros, ~48 host permutation passes, and two 6+ MiB downloads per chunk.
//!
//! `get_quotient_ldes` is a `Pcs` **trait** method, so this wrapper delegates every other method to the
//! inner `HidingFriPcs` (associated types are literally the inner's, so `Proof` serialization — the wire
//! format — is untouched) and overrides just that one: the randomization *math* (which values are drawn
//! and what the chunks become) is replicated exactly, but per chunk the coset-LDE, the zero-padded
//! vanishing-poly NTT (only the `2h`-row nonzero coefficient prefix is uploaded), the elementwise add,
//! and the bit-reversed store all happen device-side (`gpu::gpu_quotient_chunk_lde`) with ONE download.
//!
//! Correctness gates: `gpu_quotient_ldes_match_p3` (same-seed byte-identity of the returned LDEs vs
//! p3's `HidingFriPcs`) and the killer tests `gpu_{joinsplit,htlc}_proof_verifies_hiding` (a proof made
//! with this PCS verifies under the standard production verifier, unchanged).

use crate::config::{Challenge, Challenger};
use crate::gpu::{gpu_quotient_chunk_lde, GpuDft, GpuHidingMerkleMmcs};
use p3_commit::{BuildPeriodicLdeTableFast, ExtensionMmcs, OpenedValues, Pcs, PeriodicLdeTable, PolynomialSpace};
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::{batch_multiplicative_inverse, Field, PrimeCharacteristicRing, PrimeField64};
use p3_fri::{FriParameters, HidingFriPcs};
use p3_goldilocks::Goldilocks;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use rand::RngExt;
use rand_chacha::ChaCha20Rng;

type Val = Goldilocks;
pub type ChallengeMmcsGpuHiding = ExtensionMmcs<Val, Challenge, GpuHidingMerkleMmcs>;
type Inner = HidingFriPcs<Val, GpuDft, GpuHidingMerkleMmcs, ChallengeMmcsGpuHiding, ChaCha20Rng>;

/// The production GPU-hiding PCS: `HidingFriPcs` (GPU LDE + GPU Merkle) with the quotient-chunk
/// randomization pipeline overridden to run device-side. Prove-only + wire-compatible — every
/// associated type is the inner PCS's, and `verify` delegates untouched.
pub struct GpuHidingPcs {
    inner: Inner,
    num_random_codewords: usize,
    log_blowup: usize,
    /// Drives the quotient randomization draws (p3 uses the PCS rng for these; a separate stream is
    /// equally sound — the values are fresh CSPRNG output either way and never leave the prover).
    rng: std::sync::Mutex<ChaCha20Rng>,
}

impl Clone for GpuHidingPcs {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            num_random_codewords: self.num_random_codewords,
            log_blowup: self.log_blowup,
            rng: std::sync::Mutex::new(self.rng.lock().unwrap().clone()),
        }
    }
}

impl GpuHidingPcs {
    /// Mirror of `HidingFriPcs::new` with one extra argument: the RNG stream for the quotient
    /// randomization (kept separate so tests can pin it against p3's independently of the inner
    /// PCS's trace-randomization draws).
    pub fn new(
        dft: GpuDft,
        mmcs: GpuHidingMerkleMmcs,
        fri: FriParameters<ChallengeMmcsGpuHiding>,
        num_random_codewords: usize,
        inner_rng: ChaCha20Rng,
        quotient_rng: ChaCha20Rng,
    ) -> Self {
        let log_blowup = fri.log_blowup;
        Self {
            inner: Inner::new(dft, mmcs, fri, num_random_codewords, inner_rng),
            num_random_codewords,
            log_blowup,
            rng: std::sync::Mutex::new(quotient_rng),
        }
    }
}

/// The Lagrange-selector normalization constants for the chunk domains — replica of p3's private
/// `hiding_pcs::get_zp_cis` (same math, same order).
fn get_zp_cis(qc_domains: &[TwoAdicMultiplicativeCoset<Val>]) -> Vec<Val> {
    batch_multiplicative_inverse(
        &qc_domains
            .iter()
            .enumerate()
            .map(|(i, domain)| {
                qc_domains
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, other_domain)| other_domain.vanishing_poly_at_point(domain.first_point()))
                    .product()
            })
            .collect::<Vec<_>>(),
    )
}

impl BuildPeriodicLdeTableFast for GpuHidingPcs {
    type PeriodicDomain = TwoAdicMultiplicativeCoset<Val>;

    fn maybe_build_periodic_lde_table_fast(
        &self,
        periodic_cols: &[Vec<Val>],
        trace_domain: Self::PeriodicDomain,
        quotient_domain: Self::PeriodicDomain,
    ) -> Option<PeriodicLdeTable<Val>> {
        self.inner.maybe_build_periodic_lde_table_fast(periodic_cols, trace_domain, quotient_domain)
    }
}

impl Pcs<Challenge, Challenger> for GpuHidingPcs {
    type Domain = <Inner as Pcs<Challenge, Challenger>>::Domain;
    type Commitment = <Inner as Pcs<Challenge, Challenger>>::Commitment;
    type ProverData = <Inner as Pcs<Challenge, Challenger>>::ProverData;
    type EvaluationsOnDomain<'a> = <Inner as Pcs<Challenge, Challenger>>::EvaluationsOnDomain<'a>;
    type Proof = <Inner as Pcs<Challenge, Challenger>>::Proof;
    type Error = <Inner as Pcs<Challenge, Challenger>>::Error;

    const ZK: bool = true;

    fn natural_domain_for_degree(&self, degree: usize) -> Self::Domain {
        <Inner as Pcs<Challenge, Challenger>>::natural_domain_for_degree(&self.inner, degree)
    }

    fn log_max_lde_height(&self) -> usize {
        <Inner as Pcs<Challenge, Challenger>>::log_max_lde_height(&self.inner)
    }

    fn commit(
        &self,
        evaluations: impl IntoIterator<Item = (Self::Domain, RowMajorMatrix<Val>)>,
    ) -> (Self::Commitment, Self::ProverData) {
        <Inner as Pcs<Challenge, Challenger>>::commit(&self.inner, evaluations)
    }

    fn commit_preprocessing(
        &self,
        evaluations: impl IntoIterator<Item = (Self::Domain, RowMajorMatrix<Val>)>,
    ) -> (Self::Commitment, Self::ProverData) {
        <Inner as Pcs<Challenge, Challenger>>::commit_preprocessing(&self.inner, evaluations)
    }

    /// The GPU override. The randomization math is p3's `HidingFriPcs::get_quotient_ldes` verbatim
    /// (same draws, same order — see the module doc); the per-chunk pipeline (coset-LDE + zero-padded
    /// vanishing NTT + add + bit-reversed store) runs on the GPU with a single download per chunk.
    fn get_quotient_ldes(
        &self,
        evaluations: impl IntoIterator<Item = (Self::Domain, RowMajorMatrix<Val>)>,
        num_chunks: usize,
    ) -> Vec<RowMajorMatrix<Val>> {
        assert!(num_chunks > 1, "num_chunks must be > 1 to preserve hiding (got {num_chunks})");
        let (domains, evaluations): (Vec<_>, Vec<_>) = evaluations.into_iter().unzip();
        let cis = get_zp_cis(&domains);
        let last_chunk = num_chunks - 1;
        let last_chunk_ci_inv = cis[last_chunk].inverse();
        let mul_coeffs: Vec<Val> = (0..last_chunk).map(|i| cis[i] * last_chunk_ci_inv).collect();

        let randomized_evaluations: Vec<RowMajorMatrix<Val>>;
        let mut all_random_values: Vec<Val>;
        {
            let mut rng = self.rng.lock().unwrap();
            randomized_evaluations = evaluations
                .into_iter()
                .map(|mat| mat.with_random_cols(self.num_random_codewords, &mut *rng))
                .collect();
            let h = randomized_evaluations[0].height();
            let w = randomized_evaluations[0].width();
            all_random_values = (0..(randomized_evaluations.len() - 1) * h * w)
                .map(|_| rng.random())
                .chain(core::iter::repeat_n(Val::ZERO, h * w))
                .collect();
        }
        let h = randomized_evaluations[0].height();
        let w = randomized_evaluations[0].width();
        // Fix the last chunk's randomizer so the chunks still recompose to the quotient.
        for j in 0..last_chunk {
            let mul_coeff = mul_coeffs[j];
            for k in 0..h * w {
                let t = all_random_values[j * h * w + k] * mul_coeff;
                all_random_values[last_chunk * h * w + k] -= t;
            }
        }

        domains
            .into_iter()
            .zip(randomized_evaluations)
            .enumerate()
            .map(|(i, (domain, evals))| {
                assert_eq!(domain.size(), evals.height());
                let shift = Val::GENERATOR / domain.shift();
                let random_values = &all_random_values[i * h * w..(i + 1) * h * w];
                // v_H(X)·r(X) in coefficient form is nonzero only in the first 2h rows
                // (v_H = (shift·X)^h − 1 in p3's coset normalization): row r gets −c_r, row h+r gets
                // p·c_r with p = shift^h and c_r = GENERATOR^r · random_values[r]. Only this prefix is
                // built/uploaded; the GPU zero-pads and NTTs it.
                let p = shift.exp_u64(h as u64);
                let mut van_prefix = vec![0u64; 2 * h * w];
                Val::GENERATOR.powers().take(h).enumerate().for_each(|(r, p_r)| {
                    for j in 0..w {
                        let mul_coeff = p_r * random_values[r * w + j];
                        van_prefix[r * w + j] = (-mul_coeff).as_canonical_u64();
                        van_prefix[(h + r) * w + j] = (p * mul_coeff).as_canonical_u64();
                    }
                });
                let evals_u64: Vec<u64> = evals.values.iter().map(|f| f.as_canonical_u64()).collect();
                let stored =
                    gpu_quotient_chunk_lde(&evals_u64, &van_prefix, h, w, self.log_blowup + 1, shift.as_canonical_u64());
                RowMajorMatrix::new(stored.into_iter().map(Goldilocks::new).collect(), w)
            })
            .collect()
    }

    fn commit_ldes(&self, ldes: Vec<RowMajorMatrix<Val>>) -> (Self::Commitment, Self::ProverData) {
        <Inner as Pcs<Challenge, Challenger>>::commit_ldes(&self.inner, ldes)
    }

    fn get_evaluations_on_domain<'a>(
        &self,
        prover_data: &'a Self::ProverData,
        idx: usize,
        domain: Self::Domain,
    ) -> Self::EvaluationsOnDomain<'a> {
        <Inner as Pcs<Challenge, Challenger>>::get_evaluations_on_domain(&self.inner, prover_data, idx, domain)
    }

    fn get_evaluations_on_domain_no_random<'a>(
        &self,
        prover_data: &'a Self::ProverData,
        idx: usize,
        domain: Self::Domain,
    ) -> Self::EvaluationsOnDomain<'a> {
        <Inner as Pcs<Challenge, Challenger>>::get_evaluations_on_domain_no_random(&self.inner, prover_data, idx, domain)
    }

    fn open(
        &self,
        commitment_data_with_opening_points: Vec<(&Self::ProverData, Vec<Vec<Challenge>>)>,
        fiat_shamir_challenger: &mut Challenger,
    ) -> (OpenedValues<Challenge>, Self::Proof) {
        <Inner as Pcs<Challenge, Challenger>>::open(&self.inner, commitment_data_with_opening_points, fiat_shamir_challenger)
    }

    fn open_with_preprocessing(
        &self,
        commitment_data_with_opening_points: Vec<(&Self::ProverData, Vec<Vec<Challenge>>)>,
        fiat_shamir_challenger: &mut Challenger,
        is_preprocessing: bool,
    ) -> (OpenedValues<Challenge>, Self::Proof) {
        <Inner as Pcs<Challenge, Challenger>>::open_with_preprocessing(
            &self.inner,
            commitment_data_with_opening_points,
            fiat_shamir_challenger,
            is_preprocessing,
        )
    }

    #[allow(clippy::type_complexity)]
    fn verify(
        &self,
        commitments_with_opening_points: Vec<(
            Self::Commitment,
            Vec<(Self::Domain, Vec<(Challenge, Vec<Challenge>)>)>,
        )>,
        proof: &Self::Proof,
        fiat_shamir_challenger: &mut Challenger,
    ) -> Result<(), Self::Error> {
        <Inner as Pcs<Challenge, Challenger>>::verify(&self.inner, commitments_with_opening_points, proof, fiat_shamir_challenger)
    }

    fn get_opt_randomization_poly_commitment(
        &self,
        domain: impl IntoIterator<Item = Self::Domain>,
    ) -> Option<(Self::Commitment, Self::ProverData)> {
        <Inner as Pcs<Challenge, Challenger>>::get_opt_randomization_poly_commitment(&self.inner, domain)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{production_fri, ChallengeMmcs, MyCompress, MyHash, ValMmcs, CAP_HEIGHT, NUM_RANDOM_CODEWORDS};
    use p3_dft::Radix2DitParallel;
    use p3_goldilocks::default_goldilocks_poseidon2_8;
    use rand::SeedableRng;

    /// GOLD GATE: seeded with the same quotient RNG, `GpuHidingPcs::get_quotient_ldes` returns LDE
    /// matrices **byte-identical** to p3's `HidingFriPcs` (production CPU PCS) — the randomization
    /// draws, the vanishing-poly randomizer, the coset-LDE, the add, and the bit-reversed storage
    /// order all reproduced exactly. Production chunk shape is h=4096 w=6 ×16; this covers that and
    /// smaller/odder shapes.
    #[test]
    #[ignore = "requires an OpenCL runtime + GPU"]
    fn gpu_quotient_ldes_match_p3() {
        let perm = default_goldilocks_poseidon2_8();
        let seed = 20260703u64;
        for &(log_chunk, w2, num_chunks) in &[(4usize, 2usize, 4usize), (8, 2, 16), (12, 2, 16)] {
            // Reference: the production CPU PCS (Radix2DitParallel + MerkleTreeHidingMmcs), seeded.
            let cpu_valmmcs = ValMmcs::new(
                MyHash::new(perm.clone()),
                MyCompress::new(perm.clone()),
                CAP_HEIGHT,
                ChaCha20Rng::seed_from_u64(1),
            );
            let cpu: crate::config::MyPcs = HidingFriPcs::new(
                Radix2DitParallel::default(),
                cpu_valmmcs.clone(),
                production_fri(ChallengeMmcs::new(cpu_valmmcs)),
                NUM_RANDOM_CODEWORDS,
                ChaCha20Rng::seed_from_u64(seed),
            );
            // GPU wrapper: quotient rng seeded identically (inner rng irrelevant here).
            let gpu_valmmcs = GpuHidingMerkleMmcs::new(
                MyHash::new(perm.clone()),
                MyCompress::new(perm.clone()),
                CAP_HEIGHT,
                ChaCha20Rng::seed_from_u64(2),
            );
            let fri = FriParameters {
                log_blowup: crate::config::LOG_BLOWUP,
                log_final_poly_len: 0,
                max_log_arity: 4,
                num_queries: crate::config::NUM_QUERIES,
                commit_proof_of_work_bits: 0,
                query_proof_of_work_bits: crate::config::QUERY_POW_BITS,
                mmcs: ChallengeMmcsGpuHiding::new(gpu_valmmcs.clone()),
            };
            let gpu = GpuHidingPcs::new(
                GpuDft,
                gpu_valmmcs,
                fri,
                NUM_RANDOM_CODEWORDS,
                ChaCha20Rng::seed_from_u64(3),
                ChaCha20Rng::seed_from_u64(seed),
            );
            // A quotient domain split into chunks, with random "quotient evaluations".
            let log_q = log_chunk + num_chunks.trailing_zeros() as usize;
            let trace_domain =
                <crate::config::MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(&cpu, 1 << log_chunk);
            let quotient_domain = trace_domain.create_disjoint_domain(1 << log_q);
            let sub_domains = quotient_domain.split_domains(num_chunks);
            let mut rng = ChaCha20Rng::seed_from_u64(99);
            let flat = RowMajorMatrix::new(
                (0..(1usize << log_q) * w2).map(|_| Goldilocks::new(rng.random::<u64>() % 0xFFFF_FFFF_0000_0001)).collect(),
                w2,
            );
            let sub_evals = quotient_domain.split_evals(num_chunks, flat);
            let cpu_ldes = <crate::config::MyPcs as Pcs<Challenge, Challenger>>::get_quotient_ldes(
                &cpu,
                sub_domains.clone().into_iter().zip(sub_evals.clone()),
                num_chunks,
            );
            let gpu_ldes = <GpuHidingPcs as Pcs<Challenge, Challenger>>::get_quotient_ldes(
                &gpu,
                sub_domains.into_iter().zip(sub_evals),
                num_chunks,
            );
            assert_eq!(cpu_ldes.len(), gpu_ldes.len());
            for (i, (c, g)) in cpu_ldes.iter().zip(&gpu_ldes).enumerate() {
                assert_eq!(c.width(), g.width(), "chunk {i} width, h=2^{log_chunk}");
                assert_eq!(c.values, g.values, "chunk {i} LDE mismatch, h=2^{log_chunk}");
            }
        }
    }
}
