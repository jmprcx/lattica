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

/// (width, n_periodic, n_publics, n_constraints, max_degree, fnv64-of-constraints)
type Fingerprint = (usize, usize, usize, usize, usize, u64);

fn fingerprint<A>(air: &A) -> Fingerprint
where
    A: Air<SymbolicAirBuilder<Val>> + p3_air::BaseAir<Val>,
{
    let layout = AirLayout::from_air::<Val>(air);
    let cs = get_symbolic_constraints::<Val, A>(air, layout);
    let n = cs.len();
    let maxd = cs.iter().map(|c| c.degree_multiple()).max().unwrap_or(0);
    // FNV-1a over the Debug rendering of each constraint, in emission order.
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for c in &cs {
        for b in format!("{c:?}").bytes() {
            h ^= b as u64;
            h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
        // constraint separator (so concatenation boundaries are unambiguous)
        h ^= 0x1e;
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    (air.width(), air.num_periodic_columns(), air.num_public_values(), n, maxd, h)
}

/// The recursion monolith at its two canonical shapes (synthetic geometry — `get_symbolic_constraints`
/// only needs counts/widths, not a real proof): the is_zk=0 db=6 milestone and the is_zk=1 hiding shape.
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
        fold: false,
        constraints: vec![],
        w_inner_f: 1,
        n_pub_f: 1,
        n_periodic_f: 0,
        is_zk,
    }
}

#[test]
fn pinned_constraint_fingerprints() {
    let got: Vec<(&str, Fingerprint)> = vec![
        ("JoinSplitAir", fingerprint(&crate::joinsplit_air::JoinSplitAir)),
        ("HtlcAir", fingerprint(&crate::htlc_air::HtlcAir)),
        ("JoinSplitBatchAir", fingerprint(&crate::batch_joinsplit_air::JoinSplitBatchAir)),
        ("HtlcBatchAir", fingerprint(&crate::batch_htlc_air::HtlcBatchAir)),
        ("Poseidon2RowsAir", fingerprint(&crate::poseidon2_air::Poseidon2RowsAir)),
        ("MonolithAir[is_zk=0,db=6]", fingerprint(&monolith_air(0))),
        ("MonolithAir[is_zk=1,hiding]", fingerprint(&monolith_air(1))),
    ];
    for (name, fp) in &got {
        println!("{name}: (width, periodic, publics, n, maxdeg, fnv) = {fp:?}");
    }
    let pinned: &[(&str, Fingerprint)] = &[
        // Harvested at the pre-refactor baseline (v3 @ eda58ee); see module doc for the re-pin policy.
        ("JoinSplitAir", (19, 33, 26, 81, 8, 10377435458428738100)),
        ("HtlcAir", (36, 43, 31, 145, 8, 399889076546091351)),
        ("JoinSplitBatchAir", (49, 45, 4, 167, 8, 9176787058577691560)),
        ("HtlcBatchAir", (71, 57, 4, 244, 9, 14186304468083107211)),
        ("Poseidon2RowsAir", (8, 11, 8, 16, 8, 4555829733017345773)),
        ("MonolithAir[is_zk=0,db=6]", (193, 56, 53, 380, 13, 2831239969576965911)),
        ("MonolithAir[is_zk=1,hiding]", (619, 81, 2271, 875, 9, 5788871046264575537)),
    ];
    for (name, fp) in pinned {
        let (_, actual) = got.iter().find(|(n, _)| n == name).expect("pinned AIR present");
        assert_eq!(actual, fp, "{name}: constraint fingerprint drifted");
    }
    assert_eq!(pinned.len(), got.len(), "every computed fingerprint must be pinned (harvest run: pins empty)");
}
