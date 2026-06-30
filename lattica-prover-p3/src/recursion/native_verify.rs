//! B3-wire — a native re-verifier that re-implements `p3_uni_stark::verify`'s orchestration explicitly,
//! validated to agree with the real `verify` (accept valid, reject tampered). This is the porting
//! blueprint for the in-circuit verifier: it spells out the transcript replay (observe → sample α →
//! observe → sample ζ), the opening-rounds construction, and the quotient/constraint check, with the FRI
//! low-degree test delegated to `pcs.verify` (whose internals are covered by the separately-validated
//! primitives `fri_merkle`/`transcript`/`fri_fold`).
//!
//! Built against a minimal `ConstAir` (one column, constant) to keep the AIR-specific quotient logic
//! small, under the **production hiding (ZK) FRI config** — so the orchestration is validated against the
//! real ZK path (random commitment + the hiding opening structure + the `is_zk`-adjusted quotient-chunk
//! count). Transcript, openings, quotient, constraints are all exercised end-to-end.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_challenger::{CanObserve, DuplexChallenger, FieldChallenger};
use p3_commit::{ExtensionMmcs, Pcs, PolynomialSpace};
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::HidingFriPcs;
use p3_goldilocks::{Goldilocks, Poseidon2Goldilocks};
use p3_merkle_tree::MerkleTreeHidingMmcs;
use rand_chacha::ChaCha20Rng;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{
    get_log_num_quotient_chunks, recompose_quotient_from_chunks, validate_degree_bits, verify_constraints,
    AirLayout, Proof, StarkConfig, StarkGenericConfig,
};

type Val = Goldilocks;
type Challenge = BinomialExtensionField<Val, 2>;

/// Minimal AIR: a single column constrained to a public constant on every row.
pub struct ConstAir;

impl BaseAir<Goldilocks> for ConstAir {
    fn width(&self) -> usize {
        1
    }
    fn num_public_values(&self) -> usize {
        1
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for ConstAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        builder.when_first_row().assert_zero(cur[0].clone() - pis[0].clone());
        builder.when_transition().assert_zero(nxt[0].clone() - cur[0].clone());
    }
}

// --- hiding (ZK) FRI config — the PRODUCTION config family lattica uses (so the re-verifier is
//     validated against the real ZK path: random commitment + hiding opening structure).
type Perm = Poseidon2Goldilocks<8>;
type MyHash = PaddingFreeSponge<Perm, 8, 4, 4>;
type MyCompress = TruncatedPermutation<Perm, 2, 4, 8>;
type ValMmcs =
    MerkleTreeHidingMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, ChaCha20Rng, 2, 4, 4>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Challenger = DuplexChallenger<Val, Perm, 8, 4>;
type Dft = Radix2DitParallel<Val>;
type MyPcs = HidingFriPcs<Val, Dft, ValMmcs, ChallengeMmcs, ChaCha20Rng>;
type MyConfig = StarkConfig<MyPcs, Challenge, Challenger>;

/// Native re-verifier: re-implements `verify`'s orchestration step-by-step (production hiding/ZK config;
/// the `is_zk=1` path — random commitment observed, `init_trace_domain = degree >> is_zk`, quotient-chunk
/// count `1 << (log + is_zk)`), delegating only the FRI low-degree test to `pcs.verify`.
pub fn reverify(config: &MyConfig, proof: &Proof<MyConfig>, public_values: &[Val]) -> Result<(), String> {
    let air = ConstAir;
    let Proof { commitments, opened_values, opening_proof, degree_bits } = proof;
    let degree_bits = *degree_bits;
    let pcs = config.pcs();
    let is_zk = config.is_zk();

    let (base_degree_bits, degree) =
        validate_degree_bits(None, degree_bits, is_zk, <MyPcs as Pcs<Challenge, Challenger>>::log_max_lde_height(pcs)).map_err(|e| format!("degree bits: {e:?}"))?;
    let trace_domain = <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, degree);
    let preprocessed_width = 0usize; // ConstAir has no preprocessed trace

    let layout = AirLayout::from_air::<Val>(&air);
    let log_num_quotient_chunks = get_log_num_quotient_chunks::<Val, ConstAir>(&air, layout, is_zk);
    let num_quotient_chunks = 1usize << (log_num_quotient_chunks + is_zk); // checked_log_size_sum(log, is_zk)

    let mut challenger = config.initialise_challenger();
    let init_trace_domain = <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, degree >> is_zk);

    let quotient_domain_size = 1usize << (degree_bits + log_num_quotient_chunks);
    let quotient_domain = trace_domain.create_disjoint_domain(quotient_domain_size);
    let quotient_chunks_domains = quotient_domain.split_domains(num_quotient_chunks);
    let randomized_quotient_chunks_domains: Vec<_> = quotient_chunks_domains
        .iter()
        .map(|d| <MyPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(pcs, d.size() << is_zk))
        .collect();

    // ---- observe the instance ----
    challenger.observe(Val::from_usize(degree_bits));
    challenger.observe(Val::from_usize(base_degree_bits));
    challenger.observe(Val::from_usize(preprocessed_width));
    challenger.observe(commitments.trace.clone());
    challenger.observe_slice(public_values);

    // ---- α (constraint combination) ----
    let alpha: Challenge = challenger.sample_algebra_element();
    challenger.observe(commitments.quotient_chunks.clone());
    if let Some(r) = commitments.random.clone() {
        challenger.observe(r);
    }

    // ---- ζ (out-of-domain point) ----
    let zeta: Challenge = challenger.sample_algebra_element();
    if init_trace_domain.vanishing_poly_at_point(zeta).is_zero() {
        return Err("zeta in trace domain".into());
    }

    let periodic_columns = air.periodic_columns();
    let periodic_values: Vec<Challenge> = periodic_columns
        .iter()
        .map(|c| init_trace_domain.evaluate_periodic_column_at(c, zeta))
        .collect();
    let zeta_next = init_trace_domain.next_point(zeta).ok_or("no next point")?;

    // ---- opening rounds (random, trace, quotient) ----
    let main_next = !air.main_next_row_columns().is_empty();
    let mut coms_to_verify = if let Some(random_commit) = &commitments.random {
        let random_values = opened_values.random.as_ref().ok_or("missing random opened values")?;
        vec![(random_commit.clone(), vec![(trace_domain, vec![(zeta, random_values.clone())])])]
    } else {
        vec![]
    };
    let trace_round = {
        let mut pts = vec![(zeta, opened_values.trace_local.clone())];
        if main_next {
            pts.push((zeta_next, opened_values.trace_next.clone().ok_or("missing trace_next")?));
        }
        (commitments.trace.clone(), vec![(trace_domain, pts)])
    };
    coms_to_verify.push(trace_round);
    coms_to_verify.push((
        commitments.quotient_chunks.clone(),
        randomized_quotient_chunks_domains
            .iter()
            .zip(&opened_values.quotient_chunks)
            .map(|(d, v)| (*d, vec![(zeta, v.clone())]))
            .collect(),
    ));

    // ---- FRI low-degree test (delegated; internals = the validated primitives) ----
    <MyPcs as Pcs<Challenge, Challenger>>::verify(pcs, coms_to_verify, opening_proof, &mut challenger).map_err(|e| format!("pcs.verify: {e:?}"))?;

    // ---- recompose the quotient + check the constraint relation at ζ ----
    let quotient = recompose_quotient_from_chunks::<MyConfig>(&quotient_chunks_domains, &opened_values.quotient_chunks, zeta);
    let zeros;
    let trace_next_slice: &[Challenge] = match &opened_values.trace_next {
        Some(v) => v.as_slice(),
        None => {
            zeros = Challenge::zero_vec(air.width());
            &zeros
        }
    };
    verify_constraints::<MyConfig, ConstAir, <MyPcs as Pcs<Challenge, Challenger>>::Error>(
        &air,
        &opened_values.trace_local,
        trace_next_slice,
        None,
        None,
        &periodic_values,
        public_values,
        init_trace_domain,
        zeta,
        alpha,
        quotient,
    )
    .map_err(|e| format!("constraints: {e:?}"))?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_fri::FriParameters;
    use p3_goldilocks::default_goldilocks_poseidon2_8;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_uni_stark::{prove, verify};
    use rand::SeedableRng;

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
        let pcs = MyPcs::new(Dft::default(), val_mmcs, fri, 4, ChaCha20Rng::from_rng(&mut rand::rng()));
        MyConfig::new(pcs, Challenger::new(perm))
    }

    fn gen_proof(config: &MyConfig, value: u64, log_height: usize) -> (Proof<MyConfig>, Vec<Val>) {
        let v = Val::from_u64(value);
        let trace = RowMajorMatrix::new(vec![v; 1 << log_height], 1);
        let pvs = vec![v];
        (prove(config, &ConstAir, trace, &pvs), pvs)
    }

    #[test]
    #[ignore = "slow: native re-verifier vs p3::verify"]
    fn reverify_agrees_with_p3() {
        let config = make_config();
        let (proof, pvs) = gen_proof(&config, 42, 6);

        // sanity: p3 accepts the proof.
        assert!(verify(&config, &ConstAir, &proof, &pvs).is_ok(), "p3::verify should accept");
        // the native re-verifier accepts the same valid proof.
        if let Err(e) = reverify(&config, &proof, &pvs) {
            panic!("reverify rejected a valid proof: {e}");
        }

        // tampered public value ⇒ both reject (the constraint check fails the OOD relation).
        let bad_pvs = vec![Val::from_u64(43)];
        assert!(verify(&config, &ConstAir, &proof, &bad_pvs).is_err());
        assert!(reverify(&config, &proof, &bad_pvs).is_err(), "reverify should reject wrong public value");
    }
}
