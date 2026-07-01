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

/// Minimal NON-DEGENERATE AIR (Phase 6): a single column counting up — `cur = pub` on the first row,
/// `next = cur + 1` on every transition. Unlike `ConstAir`, its trace is NON-constant, so the committed
/// Merkle leaves (hence the cap entries) differ per query and the quotient at ζ is non-zero — this is what
/// exercises the cap-mux and the OOD epilogue that `ConstAir`'s degeneracy masks.
pub struct CounterAir;

impl BaseAir<Goldilocks> for CounterAir {
    fn width(&self) -> usize {
        1
    }
    fn num_public_values(&self) -> usize {
        1
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for CounterAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        builder.when_first_row().assert_zero(cur[0].clone() - pis[0].clone());
        builder.when_transition().assert_zero(nxt[0].clone() - cur[0].clone() - AB::Expr::ONE);
    }
}

/// A MULTI-COLUMN inner (Phase 7): the classic Fibonacci recurrence over 2 columns `[a, b]`. First row seeds
/// `a=pub[0]`, `b=pub[1]`; transition `a'=b`, `b'=a+b`; last row `b=pub[2]`. Unlike the 1-column ConstAir/
/// CounterAir, it exercises the GENERAL OOD epilogue: multi-column openings, CROSS-column constraints, and
/// all three Lagrange selectors (first, transition, last) in the α-fold — the first bounded step toward the
/// arbitrary-inner-AIR epilogue (the blocker for B5 recursion depth + folding real join-split statements).
/// Constraint EMISSION ORDER (the α-fold is Horner, first-emitted gets the highest power): C0 first-row a,
/// C1 first-row b, C2 transition a', C3 transition b', C4 last-row b.
pub struct FibonacciAir;

impl BaseAir<Goldilocks> for FibonacciAir {
    fn width(&self) -> usize {
        2
    }
    fn num_public_values(&self) -> usize {
        3
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for FibonacciAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        builder.when_first_row().assert_zero(cur[0].clone() - pis[0].clone()); // C0
        builder.when_first_row().assert_zero(cur[1].clone() - pis[1].clone()); // C1
        builder.when_transition().assert_zero(nxt[0].clone() - cur[1].clone()); // C2: a' = b
        builder.when_transition().assert_zero(nxt[1].clone() - cur[0].clone() - cur[1].clone()); // C3: b' = a + b
        builder.when_last_row().assert_zero(cur[1].clone() - pis[2].clone()); // C4
    }
}

/// A DEGREE-2 multi-column inner (Phase 7.5): 3 columns `[a, b, c]` with two counters (a'=a+1, b'=b+1) and a
/// NON-AFFINE product constraint `c = a·b` (every row). Unlike Fibonacci (whose constraints are all affine —
/// Add/Sub + a selector multiply), this has a Mul of two TRACE VARIABLES, so it exercises the symbolic
/// evaluator's variable·variable path — the constraint shape real high-degree AIRs (Poseidon, range checks)
/// use. Emission order: C0 first-row a, C1 first-row b, C2 product c−a·b (unconditional), C3 a'−a−1, C4 b'−b−1.
pub struct MulAir;

impl BaseAir<Goldilocks> for MulAir {
    fn width(&self) -> usize {
        3
    }
    fn num_public_values(&self) -> usize {
        2 // seed a, seed b
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for MulAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        builder.when_first_row().assert_zero(cur[0].clone() - pis[0].clone()); // C0
        builder.when_first_row().assert_zero(cur[1].clone() - pis[1].clone()); // C1
        builder.assert_zero(cur[2].clone() - cur[0].clone() * cur[1].clone()); // C2: c = a·b (degree 2, every row)
        builder.when_transition().assert_zero(nxt[0].clone() - cur[0].clone() - AB::Expr::ONE); // C3: a' = a + 1
        builder.when_transition().assert_zero(nxt[1].clone() - cur[1].clone() - AB::Expr::ONE); // C4: b' = b + 1
    }
}

/// An inner with a PERIODIC column (Phase 7.7): 1 trace column `a` accumulating a repeating pattern
/// `p = [3, 7]` (a periodic column, e.g. round constants in real AIRs): first row `a = pub[0]`, transition
/// `a' = a + p`. The transition constraint references the periodic value `p` (BaseEntry::Periodic in the
/// symbolic tree) — the last leaf kind the evaluator needs for real high-degree AIRs. Emission order: C0
/// first-row seed, C1 transition accumulate.
pub struct PeriodicAir;

/// The periodic pattern `[3, 7]` (period 2), shared by the AIR and the proof/oracle.
pub const PERIODIC_PATTERN: [u64; 2] = [3, 7];

impl BaseAir<Goldilocks> for PeriodicAir {
    fn width(&self) -> usize {
        1
    }
    fn num_public_values(&self) -> usize {
        1 // seed
    }
    fn num_periodic_columns(&self) -> usize {
        1 // (the default is 0; must be overridden alongside periodic_columns)
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        vec![PERIODIC_PATTERN.iter().map(|&v| Goldilocks::from_u64(v)).collect()]
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for PeriodicAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        builder.when_first_row().assert_zero(cur[0].clone() - pis[0].clone()); // C0
        builder.when_transition().assert_zero(nxt[0].clone() - cur[0].clone() - p[0].clone()); // C1: a' = a + p
    }
}

/// A WIDE inner (Phase 7 "wire it"): `WIDE_W`=8 independent counter columns (`col_i' = col_i + 1`, first row
/// `col_i = pub_i`). W=8 > RATE=4, so the trace-commitment leaf at a query row spans `ceil(8/4)=2` Poseidon
/// blocks — the smallest inner that exercises the MONOLITH'S MULTI-BLOCK input-leaf hashing (the real
/// join-split needs W=19 ⇒ 5 blocks). Still degree-1 (nqc=1), so ONLY the leaf-block dimension is new (the
/// quotient stays single-block). Emission order: C0..C7 first-row seeds, then C8..C15 transitions.
pub struct WideAir;

/// Trace width of `WideAir` (chosen > RATE=4 to force a 2-block Merkle leaf).
pub const WIDE_W: usize = 8;

impl BaseAir<Goldilocks> for WideAir {
    fn width(&self) -> usize {
        WIDE_W
    }
    fn num_public_values(&self) -> usize {
        WIDE_W // one seed per column
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for WideAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        for i in 0..WIDE_W {
            builder.when_first_row().assert_zero(cur[i].clone() - pis[i].clone()); // C_i: seed col_i = pub_i
        }
        for i in 0..WIDE_W {
            builder.when_transition().assert_zero(nxt[i].clone() - cur[i].clone() - AB::Expr::ONE); // C_{W+i}: col_i' = col_i + 1
        }
    }
}

/// A DEGREE-3 inner (Phase 7 "wire it", quotient half): 2 columns `[a, c]` with a counter `a'=a+1` and a
/// CUBIC constraint `c = a³` (every row). Max constraint degree 3 ⇒ p3 splits the quotient into
/// nqc = next_pow2(3−1) = 2 chunks, so the monolith must open 2·nqc = 4 quotient reduced-opening terms and
/// RECOMPOSE quotient(ζ) = Σ_i zps_i·chunk_i over the 2 chunks (vs the nqc=1 `c0+c1·X`). Still a single-block
/// quotient leaf (2·nqc=4 ≤ RATE), so it isolates the multi-CHUNK recompose from the multi-BLOCK quotient
/// leaf (the degree-4 CubeAir's bigger sibling). Emission: C0 first-row a-seed, C1 cubic c−a³, C2 a'−a−1.
pub struct CubeAir;

impl BaseAir<Goldilocks> for CubeAir {
    fn width(&self) -> usize {
        2
    }
    fn num_public_values(&self) -> usize {
        1 // seed a
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for CubeAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        builder.when_first_row().assert_zero(cur[0].clone() - pis[0].clone()); // C0: a = pub
        let a = cur[0].clone();
        builder.assert_zero(cur[1].clone() - a.clone() * a.clone() * a); // C1: c = a³ (degree 3, every row)
        builder.when_transition().assert_zero(nxt[0].clone() - cur[0].clone() - AB::Expr::ONE); // C2: a' = a + 1
    }
}

/// A DEGREE-4 inner (Phase 7 "wire it", quotient half B2): 2 columns `[a, c]` with a counter `a'=a+1` and a
/// QUARTIC constraint `c = a⁴` (every row). Max constraint degree 4 ⇒ nqc = next_pow2(4−1) = 4 chunks, so
/// 2·nqc = 8 > RATE = 4: the quotient-Merkle leaf spans ceil(8/4) = 2 Poseidon blocks — the smallest inner
/// that exercises the monolith's MULTI-BLOCK QUOTIENT leaf (on top of the multi-chunk recompose). Emission:
/// C0 first-row a-seed, C1 quartic c−a⁴, C2 a'−a−1.
pub struct QuartAir;

impl BaseAir<Goldilocks> for QuartAir {
    fn width(&self) -> usize {
        2
    }
    fn num_public_values(&self) -> usize {
        1 // seed a
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for QuartAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        builder.when_first_row().assert_zero(cur[0].clone() - pis[0].clone()); // C0: a = pub
        let a2 = cur[0].clone() * cur[0].clone();
        builder.assert_zero(cur[1].clone() - a2.clone() * a2); // C1: c = a⁴ (degree 4, every row)
        builder.when_transition().assert_zero(nxt[0].clone() - cur[0].clone() - AB::Expr::ONE); // C2: a' = a + 1
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
