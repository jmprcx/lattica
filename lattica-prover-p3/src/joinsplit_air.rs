//! Join-split (N-in / M-out) spend circuit — the audit-target shape, with the soundness fixes baked
//! in (A1 position-consistency, A2 domain separation, A3 fee range-check). Built fresh; the 1-in/1-out
//! `full_spend_air` is kept intact as the simpler reference.
//!
//! This file (so far) is the **native oracle** + design — the statement computed in plain Rust, which
//! pins the hash layouts, the nullifier/position binding, the multi-input membership to a shared
//! anchor, and the value balance. The AIR is built on top of it next, and is differential-tested
//! against this oracle.
//!
//! ## Hashes (A2 — domain separation)
//! Every data hash carries a distinct **domain tag in lane 0** of the Poseidon2 input, so a digest
//! produced in one context can't be reinterpreted in another:
//!   * ownership  `recipient = H(DOM_OWN ‖ nk)`
//!   * commitment `cm        = H(DOM_CM  ‖ recipient(4) ‖ value ‖ rho ‖ rcm)`   (input & output notes)
//!   * nullifier  `nf        = H(DOM_NF  ‖ nk ‖ rho ‖ pos)`
//! The Merkle **merge** `H(l(4) ‖ r(4))` fills all 8 lanes (no tag); it is structurally separated —
//! it only ever appears as an internal node over two 4-element digests, and the leaf entering the
//! tree is constrained to be a `DOM_CM`-tagged commitment, so a node can't be presented as a leaf.
//! (Documented for the auditor; see docs A4.)
//!
//! ## Nullifier / position (A1)
//! `pos = Σ_d bits_d · 2^d` — the integer position implied by the membership path bits — is fed into
//! the nullifier. So a note at tree position p has exactly one nullifier; it cannot be nullified
//! "as if" at a different position (which would otherwise allow a second, undetected spend).

use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::Goldilocks;

use crate::poseidon2_air::native_permute;

pub const N_IN: usize = 2; // inputs per transaction
pub const M_OUT: usize = 2; // outputs per transaction
pub const DEPTH: usize = 32; // Merkle depth
pub const BITS: usize = 52; // value range bound (2·2^BITS < p ⇒ no wraparound)
pub const DIGEST: usize = 4;
const W: usize = 8;

// A2 domain-separation tags (lane 0 of each data hash). Distinct, nonzero.
pub const DOM_OWN: u64 = 1;
pub const DOM_CM: u64 = 2;
pub const DOM_NF: u64 = 3;

type Val = Goldilocks;

/// Domain-tagged fixed-input hash: `H(domain ‖ elems)`, digest = first `DIGEST` lanes of the
/// permutation output. `elems.len()` must be ≤ 7 (lane 0 holds the domain).
fn h(domain: u64, elems: &[Val]) -> [Val; DIGEST] {
    debug_assert!(elems.len() <= W - 1);
    let mut s = [Val::ZERO; W];
    s[0] = Val::from_u64(domain);
    s[1..1 + elems.len()].copy_from_slice(elems);
    native_permute(s)[..DIGEST].try_into().unwrap()
}

pub fn recipient_of(nk: Val) -> [Val; DIGEST] {
    h(DOM_OWN, &[nk])
}

pub fn commit(recipient: [Val; DIGEST], value: Val, rho: Val, rcm: Val) -> [Val; DIGEST] {
    let mut e = [Val::ZERO; 7];
    e[..DIGEST].copy_from_slice(&recipient);
    e[DIGEST] = value;
    e[DIGEST + 1] = rho;
    e[DIGEST + 2] = rcm;
    h(DOM_CM, &e)
}

pub fn nullifier(nk: Val, rho: Val, pos: Val) -> [Val; DIGEST] {
    h(DOM_NF, &[nk, rho, pos])
}

/// Untagged 2-to-1 Merkle compression `H(l ‖ r)` (fills all 8 lanes).
pub fn merge(l: [Val; DIGEST], r: [Val; DIGEST]) -> [Val; DIGEST] {
    let mut s = [Val::ZERO; W];
    s[..DIGEST].copy_from_slice(&l);
    s[DIGEST..].copy_from_slice(&r);
    native_permute(s)[..DIGEST].try_into().unwrap()
}

/// `pos = Σ_d bits[d]·2^d` (A1): the integer tree position implied by the path bits.
pub fn pos_of(bits: &[bool; DEPTH]) -> Val {
    let mut p: u64 = 0;
    for d in (0..DEPTH).rev() {
        p = (p << 1) | bits[d] as u64;
    }
    Val::from_u64(p)
}

/// Fold a leaf up a general-position path to the root.
pub fn fold(leaf: [Val; DIGEST], sib: &[[Val; DIGEST]; DEPTH], bits: &[bool; DEPTH]) -> [Val; DIGEST] {
    let mut node = leaf;
    for d in 0..DEPTH {
        node = if bits[d] { merge(sib[d], node) } else { merge(node, sib[d]) };
    }
    node
}

#[derive(Clone)]
pub struct Input {
    pub nk: u64,
    pub value: u64,
    pub rho: Val,
    pub rcm: Val,
    pub sib: [[Val; DIGEST]; DEPTH],
    pub bits: [bool; DEPTH],
}

#[derive(Clone, Copy)]
pub struct Output {
    pub recipient: [Val; DIGEST],
    pub value: u64,
    pub rho: Val,
    pub rcm: Val,
}

#[derive(Clone)]
pub struct Witness {
    pub inputs: [Input; N_IN],
    pub outputs: [Output; M_OUT],
    pub fee: u64,
    pub tx_binding: [Val; DIGEST],
}

pub struct PublicOutputs {
    pub anchor: [Val; DIGEST],
    pub nullifiers: [[Val; DIGEST]; N_IN],
    pub out_cms: [[Val; DIGEST]; M_OUT],
}

/// Compute the public outputs from a witness, and assert the relation holds (all inputs under one
/// anchor; value balance). Panics on an inconsistent witness — the prover-side oracle.
pub fn native_outputs(w: &Witness) -> PublicOutputs {
    // per-input commitment, membership (shared anchor), nullifier
    let mut anchor: Option<[Val; DIGEST]> = None;
    let mut nullifiers = [[Val::ZERO; DIGEST]; N_IN];
    let mut in_sum: u128 = 0;
    for (i, inp) in w.inputs.iter().enumerate() {
        let nk = Val::from_u64(inp.nk);
        let recipient = recipient_of(nk);
        let cm = commit(recipient, Val::from_u64(inp.value), inp.rho, inp.rcm);
        let root = fold(cm, &inp.sib, &inp.bits);
        match anchor {
            None => anchor = Some(root),
            Some(a) => assert_eq!(a, root, "input {i} folds to a different anchor"),
        }
        nullifiers[i] = nullifier(nk, inp.rho, pos_of(&inp.bits));
        in_sum += inp.value as u128;
    }
    // per-output commitment
    let mut out_cms = [[Val::ZERO; DIGEST]; M_OUT];
    let mut out_sum: u128 = 0;
    for (j, out) in w.outputs.iter().enumerate() {
        out_cms[j] = commit(out.recipient, Val::from_u64(out.value), out.rho, out.rcm);
        out_sum += out.value as u128;
    }
    // value balance (A3: all values range-bounded ⇒ no wraparound)
    assert_eq!(in_sum, out_sum + w.fee as u128, "value balance Σin = Σout + fee");
    PublicOutputs { anchor: anchor.unwrap(), nullifiers, out_cms }
}

// --- sparse Merkle test helper: N leaves at positions 0..N (leftmost), shared anchor -----------

#[cfg(test)]
pub(crate) fn empty_hashes() -> [[Val; DIGEST]; DEPTH] {
    let mut e = [[Val::ZERO; DIGEST]; DEPTH];
    for d in 1..DEPTH {
        e[d] = merge(e[d - 1], e[d - 1]);
    }
    e
}

/// Build a tree holding `leaves` at positions 0..leaves.len() (a power of two) in the leftmost
/// subtree, the rest empty. Returns the anchor and each leaf's (sib, bits) authentication path.
#[cfg(test)]
pub(crate) fn build_paths(
    leaves: &[[Val; DIGEST]],
) -> ([Val; DIGEST], Vec<([[Val; DIGEST]; DEPTH], [bool; DEPTH])>) {
    let n = leaves.len();
    assert!(n.is_power_of_two());
    let k = n.trailing_zeros() as usize; // explicit subtree depth
    let e = empty_hashes();

    // explicit levels 0..=k over the n leaves
    let mut levels: Vec<Vec<[Val; DIGEST]>> = vec![leaves.to_vec()];
    for d in 0..k {
        let cur = &levels[d];
        let next: Vec<[Val; DIGEST]> = (0..cur.len() / 2).map(|i| merge(cur[2 * i], cur[2 * i + 1])).collect();
        levels.push(next);
    }
    let subtree_root = levels[k][0];

    // anchor: fold subtree_root with empty siblings up to DEPTH (subtree is the left child all the way)
    let mut node = subtree_root;
    for d in k..DEPTH {
        node = merge(node, e[d]);
    }
    let anchor = node;

    // per-leaf path
    let mut paths = Vec::with_capacity(n);
    for p in 0..n {
        let mut sib = [[Val::ZERO; DIGEST]; DEPTH];
        let mut bits = [false; DEPTH];
        for d in 0..k {
            let idx = p >> d;
            sib[d] = levels[d][idx ^ 1];
            bits[d] = (idx & 1) == 1;
        }
        for d in k..DEPTH {
            sib[d] = e[d];
            bits[d] = false; // subtree is the left child above level k
        }
        paths.push((sib, bits));
    }
    (anchor, paths)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A valid 2-in/2-out witness whose two input commitments sit at positions 0 and 1 of a shared
    /// tree, balanced so Σin = Σout + fee.
    pub(crate) fn sample() -> Witness {
        let in0 = (1000u64, 7u64, 11u64, 100u64); // value, nk, rho, rcm
        let in1 = (500u64, 9u64, 13u64, 101u64);
        let cm0 = commit(recipient_of(Val::from_u64(in0.1)), Val::from_u64(in0.0), Val::from_u64(in0.2), Val::from_u64(in0.3));
        let cm1 = commit(recipient_of(Val::from_u64(in1.1)), Val::from_u64(in1.0), Val::from_u64(in1.2), Val::from_u64(in1.3));
        let (_, paths) = build_paths(&[cm0, cm1]);
        let mk_in = |v: (u64, u64, u64, u64), pth: &([[Val; DIGEST]; DEPTH], [bool; DEPTH])| Input {
            nk: v.1,
            value: v.0,
            rho: Val::from_u64(v.2),
            rcm: Val::from_u64(v.3),
            sib: pth.0,
            bits: pth.1,
        };
        let inputs = [mk_in(in0, &paths[0]), mk_in(in1, &paths[1])];
        let outputs = [
            Output { recipient: recipient_of(Val::from_u64(77)), value: 900, rho: Val::from_u64(21), rcm: Val::from_u64(22) },
            Output { recipient: recipient_of(Val::from_u64(88)), value: 500, rho: Val::from_u64(23), rcm: Val::from_u64(24) },
        ];
        // Σin = 1500, Σout = 1400, fee = 100
        Witness { inputs, outputs, fee: 100, tx_binding: core::array::from_fn(|i| Val::from_u64(0xABCD + i as u64)) }
    }

    #[test]
    fn native_relation_holds() {
        let o = native_outputs(&sample());
        // both inputs fold to the same anchor (assert inside native_outputs); nullifiers distinct
        assert_ne!(o.nullifiers[0], o.nullifiers[1]);
        assert_ne!(o.out_cms[0], o.out_cms[1]);
    }

    #[test]
    fn domain_separation_distinguishes_hashes() {
        // same field inputs, different domains ⇒ different digests (A2)
        let x = Val::from_u64(42);
        assert_ne!(h(DOM_OWN, &[x]), h(DOM_NF, &[x]));
        assert_ne!(h(DOM_CM, &[x]), h(DOM_NF, &[x]));
        assert_ne!(h(DOM_OWN, &[x]), h(DOM_CM, &[x]));
    }

    #[test]
    fn pos_matches_path_bits() {
        // pos = Σ bits·2^d (A1)
        let mut bits = [false; DEPTH];
        bits[0] = true;
        bits[3] = true; // pos = 1 + 8 = 9
        assert_eq!(pos_of(&bits), Val::from_u64(9));
    }

    #[test]
    #[should_panic(expected = "value balance")]
    fn unbalanced_witness_panics() {
        let mut w = sample();
        w.fee = 101; // 1500 != 1400 + 101
        native_outputs(&w);
    }

    #[test]
    fn distinct_positions_give_distinct_nullifiers() {
        // same note key/rho at different positions ⇒ different nullifiers (A1 prevents replay)
        let nk = Val::from_u64(5);
        let rho = Val::from_u64(6);
        let mut b0 = [false; DEPTH];
        let mut b1 = [false; DEPTH];
        b1[0] = true;
        assert_ne!(nullifier(nk, rho, pos_of(&b0)), nullifier(nk, rho, pos_of(&b1)));
        let _ = &mut b0;
    }
}
