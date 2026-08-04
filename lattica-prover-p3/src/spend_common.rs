//! Shared native primitives for the two spend circuits (`joinsplit_air`, `htlc_air`).
//!
//! These are the **context-free crypto plumbing** an auditor wants to read exactly ONCE: the
//! domain-tagged hashes, the note commitment, the nullifier, the Merkle compression/fold, and the
//! position encoding — plus the sparse-tree test helper. They pin the hash layouts that both
//! circuits' constraints and the Zig node reproduce. What deliberately stays per-circuit is the
//! *geometry and constraint system* (column layout, `P_*`/`PI_*` indices, row calculators,
//! `periodic()`, `eval_spend`, `build_trace`) — that half of each file IS the audit spec and is read
//! linearly against `docs/{joinsplit,htlc}-constraint-audit.md`.
//!
//! Both circuit files `pub use` these, so every existing `joinsplit_air::merge` / `htlc_air::commit`
//! path keeps resolving unchanged.

use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::Goldilocks;

use crate::domains::{DOM_CM, DOM_NF, DOM_OWN};
use crate::poseidon2_air::native_permute;

pub const N_IN: usize = 2; // inputs per transaction
pub const M_OUT: usize = 2; // outputs per transaction
pub const DEPTH: usize = 32; // production Merkle depth
pub const BITS: usize = 52; // value range bound (2·2^BITS < p ⇒ no wraparound)
pub const DIGEST: usize = 4;
pub(crate) const W: usize = 8;

type Val = Goldilocks;

/// Domain-tagged fixed-input hash: `H(domain ‖ elems)`, digest = first `DIGEST` lanes of the
/// permutation output. `elems.len()` must be ≤ 7 (lane 0 holds the domain).
pub(crate) fn h(domain: u64, elems: &[Val]) -> [Val; DIGEST] {
    debug_assert!(elems.len() <= W - 1);
    let mut s = [Val::ZERO; W];
    s[0] = Val::from_u64(domain);
    s[1..1 + elems.len()].copy_from_slice(elems);
    native_permute(s)[..DIGEST].try_into().unwrap()
}

/// Diversified ownership tag: `recipient = H(DOM_OWN ‖ nk0 ‖ nk1 ‖ d)`. The 128-bit key `nk` is the
/// single spend authority; the diversifier `d` makes per-address tags unlinkable while remaining
/// spendable by the same `nk`. (`d = 0` is a non-diversified address.)
pub fn recipient_of(nk0: Val, nk1: Val, d: Val) -> [Val; DIGEST] {
    h(DOM_OWN, &[nk0, nk1, d])
}

/// Two-permutation (128-bit-randomness) commitment:
///   H1 = perm([DOM_CM, owner(4), value, rho0, rho1])     (8 lanes, full)
///   cm = perm([H1(4), rcm0, rcm1, asset, note_type])     (Merkle-Damgård chain)
/// rho/rcm are each two field elements ⇒ 128-bit note randomness + hiding (vs 64-bit before). The
/// second block is merge-shaped; the chaining value (256-bit) gives 128-bit collision resistance.
/// `owner` is the recipient digest for a PLAIN note (`H(DOM_OWN‖nk‖div)`) or the `htlc_root` for an
/// HTLC note; the commitment treats it uniformly (it's the 4-lane H1 owner slot). `note_type`
/// (0=PLAIN, 1=HTLC) is committed in lane 7 so the spend can distinguish the two. `joinsplit_air`
/// calls this with `note_type = 0` via its 5-arg wrapper (lane 7 stays 0 = PLAIN).
pub fn commit(
    owner: [Val; DIGEST],
    value: Val,
    rho: [Val; 2],
    rcm: [Val; 2],
    asset: Val,
    note_type: Val,
) -> [Val; DIGEST] {
    let mut a = [Val::ZERO; W];
    a[0] = Val::from_u64(DOM_CM);
    a[1..1 + DIGEST].copy_from_slice(&owner);
    a[1 + DIGEST] = value;
    a[1 + DIGEST + 1] = rho[0];
    a[1 + DIGEST + 2] = rho[1];
    let chain = native_permute(a);
    let mut b = [Val::ZERO; W];
    b[..DIGEST].copy_from_slice(&chain[..DIGEST]);
    b[DIGEST] = rcm[0];
    b[DIGEST + 1] = rcm[1];
    b[DIGEST + 2] = asset; // lane 6: hidden asset id
    b[DIGEST + 3] = note_type; // lane 7: note type (0=PLAIN, 1=HTLC)
    native_permute(b)[..DIGEST].try_into().unwrap()
}

/// Plain-note nullifier: `nf = H(DOM_NF ‖ nk0 ‖ nk1 ‖ rho0 ‖ rho1 ‖ pos)`.
pub fn nullifier(nk0: Val, nk1: Val, rho: [Val; 2], pos: Val) -> [Val; DIGEST] {
    h(DOM_NF, &[nk0, nk1, rho[0], rho[1], pos])
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
pub fn fold(
    leaf: [Val; DIGEST],
    sib: &[[Val; DIGEST]; DEPTH],
    bits: &[bool; DEPTH],
) -> [Val; DIGEST] {
    let mut node = leaf;
    for d in 0..DEPTH {
        node = if bits[d] {
            merge(sib[d], node)
        } else {
            merge(node, sib[d])
        };
    }
    node
}

/// The circuit's public outputs: the shared anchor + the per-input nullifiers + the per-output cms.
pub struct PublicOutputs {
    pub anchor: [Val; DIGEST],
    pub nullifiers: [[Val; DIGEST]; N_IN],
    pub out_cms: [[Val; DIGEST]; M_OUT],
}

// --- sparse Merkle test helper: N leaves at positions 0..N (leftmost), shared anchor -----------

pub(crate) fn empty_hashes() -> [[Val; DIGEST]; DEPTH] {
    let mut e = [[Val::ZERO; DIGEST]; DEPTH];
    for d in 1..DEPTH {
        e[d] = merge(e[d - 1], e[d - 1]);
    }
    e
}

/// Build a tree holding `leaves` at positions 0..leaves.len() (a power of two) in the leftmost
/// subtree, the rest empty. Returns the anchor and each leaf's (sib, bits) authentication path.
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
        let next: Vec<[Val; DIGEST]> = (0..cur.len() / 2)
            .map(|i| merge(cur[2 * i], cur[2 * i + 1]))
            .collect();
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
