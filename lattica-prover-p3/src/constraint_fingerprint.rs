//! CONSTRAINT-SET FINGERPRINTS — the refactor / audit-continuity oracle.
//!
//! Pins, for every production AIR (and the recursion monolith's two canonical shapes), the tuple
//! `(width, n_periodic, n_publics, n_constraints, max_degree, fnv64(constraint set))`. The fnv64 is a
//! structural hash over the p3 `SymbolicExpression` Debug rendering of every emitted constraint, in
//! emission order (emission order is SEMANTIC: the verifier's α-fold is Horner over it).
//!
//! Any change to a circuit's constraint set — intended or not — trips this test. A refactor that is
//! supposed to be constraint-preserving (motion, dedup, config extraction) must land with these pins
//! UNCHANGED; a deliberate constraint change must re-pin in the same commit with a justification in the
//! commit message (and revalidate the full proving suite + security recomputation).
//!
//! NOTE: the hash is stable for a fixed p3 version (Debug impls live in p3-air 0.6.1); a p3 upgrade may
//! re-render Debug output and require re-pinning — that is fine, the pins guard REFACTORS, not upgrades.

#![cfg(test)]

use p3_air::symbolic::get_symbolic_constraints;
use p3_air::Air;
use p3_goldilocks::Goldilocks;
use p3_uni_stark::{AirLayout, SymbolicAirBuilder};

type Val = Goldilocks;

/// (width, n_periodic, n_publics, n_constraints, max_degree, fnv64-of-constraints, fnv64-of-periodic)
///
/// The LAST component closes a blind spot the symbolic constraints cannot see: periodic columns enter
/// `get_symbolic_constraints` as content-free placeholder variables, yet their VALUES (one-hot selector
/// row positions, `P_POS_COEFF` 2^d tables, the Poseidon2 round constants in `periodic_table()`) are
/// verifier-semantic — the verifier evaluates these polynomials as part of the AIR. So the fingerprint
/// also hashes `BaseAir::periodic_columns()` content, column by column, value by value.
type Fingerprint = (usize, usize, usize, usize, usize, u64, u64);

fn fingerprint<A>(air: &A) -> Fingerprint
where
    A: Air<SymbolicAirBuilder<Val>> + p3_air::BaseAir<Val>,
{
    use p3_field::PrimeField64;
    let layout = AirLayout::from_air::<Val>(air);
    let cs = get_symbolic_constraints::<Val, A>(air, layout);
    let n = cs.len();
    let maxd = cs.iter().map(|c| c.degree_multiple()).max().unwrap_or(0);
    const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;
    // FNV-1a over the Debug rendering of each constraint, in emission order.
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for c in &cs {
        for b in format!("{c:?}").bytes() {
            h ^= b as u64;
            h = h.wrapping_mul(FNV_PRIME);
        }
        // constraint separator (so concatenation boundaries are unambiguous)
        h ^= 0x1e;
        h = h.wrapping_mul(FNV_PRIME);
    }
    // FNV-1a over the periodic-column CONTENT (canonical u64 LE bytes), column-separated.
    let mut hp: u64 = 0xcbf2_9ce4_8422_2325;
    for col in air.periodic_columns() {
        for v in &col {
            for b in v.as_canonical_u64().to_le_bytes() {
                hp ^= b as u64;
                hp = hp.wrapping_mul(FNV_PRIME);
            }
        }
        hp ^= 0x1f;
        hp = hp.wrapping_mul(FNV_PRIME);
    }
    (air.width(), air.num_periodic_columns(), air.num_public_values(), n, maxd, h, hp)
}

/// The recursion monolith at its two canonical shapes (synthetic geometry — `get_symbolic_constraints`
/// only needs counts/widths, not a real proof): the is_zk=0 db=6 milestone and the is_zk=1 hiding shape.
/// RESEARCH — the recursion module is feature-gated, so these pins compile only under `--features recursion`.
#[cfg(feature = "recursion")]
fn monolith_air(is_zk: usize) -> crate::recursion::monolith::MonolithAir {
    crate::recursion::monolith::MonolithAir {
        counts: vec![],
        binds: if is_zk == 1 { vec![0; 10] } else { vec![0; 9] }, // nb = 3 + cm_rounds (7 hiding / 6 milestone)
        index_binds: vec![],
        n_queries: 1,
        n_terms: if is_zk == 1 { 40 } else { 4 },
        inner_counter: false,
        column_window: false,
        k_instances: 1,
        fold: false, fold_txstmt: false,
        constraints: vec![],
        w_inner_f: 1,
        n_pub_f: 1,
        n_periodic_f: 0,
        is_zk,
        cap_height: 6, narrow_arith: false, narrow_caps: false, narrow_openings: false }
}

#[test]
fn pinned_constraint_fingerprints() {
    #[allow(unused_mut)]
    let mut got: Vec<(&str, Fingerprint)> = vec![
        ("JoinSplitAir", fingerprint(&crate::joinsplit_air::JoinSplitAir)),
        ("HtlcAir", fingerprint(&crate::htlc_air::HtlcAir)),
        ("JoinSplitBatchAir", fingerprint(&crate::batch_joinsplit_air::JoinSplitBatchAir)),
        ("HtlcBatchAir", fingerprint(&crate::batch_htlc_air::HtlcBatchAir)),
        ("Poseidon2RowsAir", fingerprint(&crate::poseidon2_air::Poseidon2RowsAir)),
    ];
    // The recursion monolith pins compile only under `--features recursion` (the module is gated out of the
    // default/production build); the 5 production-AIR pins above are always checked.
    #[cfg(feature = "recursion")]
    {
        got.push(("MonolithAir[is_zk=0,db=6]", fingerprint(&monolith_air(0))));
        got.push(("MonolithAir[is_zk=1,hiding]", fingerprint(&monolith_air(1))));
    }
    for (name, fp) in &got {
        println!("{name}: (width, periodic, publics, n, maxdeg, fnv) = {fp:?}");
    }
    #[allow(unused_mut)]
    let mut pinned: Vec<(&str, Fingerprint)> = vec![
        // Constraint components harvested at the pre-refactor baseline (v3 @ eda58ee) and UNCHANGED
        // through the refactor; the periodic-content fnv (last) was added by the post-refactor review
        // (the symbolic constraints cannot see periodic VALUES) and harvested at 324c45b — the periodic
        // producers were byte-compared against eda58ee at that point. Re-pin policy: module doc.
        ("JoinSplitAir", (19, 33, 26, 81, 8, 10377435458428738100, 2370469867362978521)),
        ("HtlcAir", (36, 43, 31, 145, 8, 399889076546091351, 6527013588378775531)),
        ("JoinSplitBatchAir", (49, 45, 4, 167, 8, 9176787058577691560, 6216047000859822608)),
        ("HtlcBatchAir", (71, 57, 4, 244, 9, 14186304468083107211, 7128159627846454138)),
        ("Poseidon2RowsAir", (8, 11, 8, 16, 8, 4555829733017345773, 3694726246285696047)),
    ];
    // MonolithAir[is_zk=0] re-pinned 2026-07-03 (was maxdeg 13, fnv 2831239969576965911): the merge-link
    // `not_term` migrated from the product Π(1−one_hot) to the row-wise-identical disjoint-one-hot SUM form —
    // the product's degree (7 + cm_rounds + boundary factors) crossed the outer maxdeg-16 / log_nqc-4 budget at
    // the REAL join-split shape (db=12 ⇒ degree 21; caught by phase8_joinsplit_degree_probe). Same exclusions,
    // same trace, degree-1 link. is_zk=1 UNCHANGED. RESEARCH — feature-gated with the recursion module.
    #[cfg(feature = "recursion")]
    {
        pinned.push(("MonolithAir[is_zk=0,db=6]", (193, 56, 53, 380, 9, 8931234269209497483, 4845014777825624174)));
        pinned.push(("MonolithAir[is_zk=1,hiding]", (619, 81, 2271, 875, 9, 5788871046264575537, 9300941697942390572)));
    }
    for (name, fp) in &pinned {
        let (_, actual) = got.iter().find(|(n, _)| n == name).expect("pinned AIR present");
        assert_eq!(actual, fp, "{name}: constraint fingerprint drifted");
    }
    assert_eq!(pinned.len(), got.len(), "every computed fingerprint must be pinned (harvest run: pins empty)");
}
