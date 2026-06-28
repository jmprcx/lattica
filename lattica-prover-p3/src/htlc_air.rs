//! # htlc_air — v3 shielded HTLC spend circuit (redeem / refund)
//!
//! **Status: in-circuit HTLC spend COMPLETE** (pending external audit). The AIR proves/verifies HTLC
//! notes: owner = htlc_root (span-end chain over redeem_tag/refund_tag/hashlock/timeout, carried into
//! commit_a via the OWNER columns), note_type-gated commitment + mode-independent owner-nullifier, the
//! spend access control (tag-match: claim == mode-selected party), the redeem hashlock binding (==
//! public redeem_hashlock = SHA256(preimage)), and the time-lock (redeem height<timeout / refund
//! height>=timeout via a range argument on current_height vs the committed timeout). All positive +
//! adversarial-negative tested. Remaining for v3: the ShieldedHtlcTx node integration + the v3 audit.
//!
//! This started as a faithful clone of `joinsplit_air` (the audited v1 circuit)
//! so the HTLC circuit reuses its proven machinery — Poseidon2 blocks, the two-permutation commitment
//! (with the substrate's hidden `asset_id` in lane 6), multi-input membership to a shared anchor,
//! value balance + range, the position-bound nullifier, and the `tx_binding` Fiat-Shamir binding. It
//! currently behaves identically to the join-split; the HTLC extensions are layered on next.
//!
//! ## Planned HTLC extensions (see the v3 plan, Phase A1)
//! - commitment lane 7 = `note_type ∈ {PLAIN, HTLC}`; `owner` = `recipient = H(DOM_OWN‖nk‖div)` (PLAIN)
//!   or `htlc_root = MD-chain(DOM_HTLC ‖ redeem_tag ‖ refund_tag ‖ hashlock ‖ timeout)` (HTLC);
//! - two spend modes gated by one persistent `MODE` boolean: redeem (claim == redeem_tag,
//!   `height < timeout`, bind `hashlock == redeem_hashlock` public = SHA256(preimage)) vs refund
//!   (claim == refund_tag, `height >= timeout`); timeout compare reuses the range columns;
//! - **CRITICAL soundness:** the nullifier is mode/party-independent — `nf = H(DOM_NF ‖ owner ‖ rho ‖
//!   pos)` (NOT the claiming `nk`), else a note is spendable once per mode (double-spend);
//! - public inputs gain `current_height` + `redeem_hashlock`.
//!
//! Every binding is differential-tested against the native oracle below and probed with adversarial
//! corrupted-trace tests (as in `joinsplit_air`), because this is atomic-swap fund-critical.
//!
//! ## AIR layout note (block adjacency — learned the hard way)
//! The recipient link (`own.out → commit_a.in`) and the chain/membership links are **block-adjacent**
//! (cur→nxt) constraints. So the 4 htlc_root blocks CANNOT be inserted between ownership and commit_a
//! (that breaks the own→commit_a adjacency). The correct layout puts the htlc_root chain at the
//! **span end** (after the nullifier), carries the selected owner in 4 persistent `OWNER` columns
//! (`OWNER = note_type ? htlc_root : recipient`), binds `commit_a.in[owner] == OWNER` (local, no
//! adjacency), and binds `OWNER` to `own.out` (PLAIN) / the htlc chain output (HTLC) at those rows.
//! Adding span-end blocks also requires extending the persistence region (`P_REGION_LAST`) and the
//! NK/RHO/VAL/POSACC fills to the new span end. This is the remaining AIR work.
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
use p3_air::symbolic::AirLayout;
use p3_uni_stark::{prove, verify, Proof, ProvenSecurity, StarkConfig, StarkSecurityParams};
use rand_chacha::ChaCha20Rng;
use rand::SeedableRng;

use crate::poseidon2_air::{ext_linear, int_linear, native_permute, native_steps, periodic_table, pow7, BLOCK};

pub const N_IN: usize = 2; // inputs per transaction
pub const M_OUT: usize = 2; // outputs per transaction
pub const DEPTH: usize = 32; // production Merkle depth
pub const BITS: usize = 52; // value range bound (2·2^BITS < p ⇒ no wraparound)
pub const DIGEST: usize = 4;
const W: usize = 8;

// A2 domain-separation tags (lane 0 of each data hash). Distinct, nonzero.
pub const DOM_OWN: u64 = 1;
pub const DOM_CM: u64 = 2;
pub const DOM_NF: u64 = 3;
pub const DOM_HTLC: u64 = 4; // htlc_root = MD-chain over (redeem_tag, refund_tag, hashlock, timeout)
pub const DOM_NF_HTLC: u64 = 5; // nullifier of an HTLC note (owner-based, mode-independent)

/// Note types (committed in commitment lane 7).
pub const NOTE_PLAIN: u64 = 0;
pub const NOTE_HTLC: u64 = 1;

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

/// Diversified ownership tag: `recipient = H(DOM_OWN ‖ nk0 ‖ nk1 ‖ d)`. The 128-bit key `nk` is the
/// single spend authority; the diversifier `d` makes per-address tags unlinkable while remaining
/// spendable by the same `nk`. (`d = 0` is a non-diversified address.)
pub fn recipient_of(nk0: Val, nk1: Val, d: Val) -> [Val; DIGEST] {
    h(DOM_OWN, &[nk0, nk1, d])
}

/// Two-permutation (128-bit-randomness) commitment:
///   H1 = perm([DOM_CM, recipient(4), value, rho0, rho1])     (8 lanes, full)
///   cm = perm([H1(4), rcm0, rcm1, 0, 0])                      (Merkle-Damgård chain)
/// rho/rcm are each two field elements ⇒ 128-bit note randomness + hiding (vs 64-bit before). The
/// second block is merge-shaped; the chaining value (256-bit) gives 128-bit collision resistance.
/// `owner` is the recipient digest for a PLAIN note (`H(DOM_OWN‖nk‖div)`) or the `htlc_root` for an
/// HTLC note; the commitment treats it uniformly (it's the 4-lane H1 owner slot). `note_type`
/// (0=PLAIN, 1=HTLC) is committed in lane 7 so the spend can distinguish the two.
pub fn commit(owner: [Val; DIGEST], value: Val, rho: [Val; 2], rcm: [Val; 2], asset: Val, note_type: Val) -> [Val; DIGEST] {
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

pub fn nullifier(nk0: Val, nk1: Val, rho: [Val; 2], pos: Val) -> [Val; DIGEST] {
    h(DOM_NF, &[nk0, nk1, rho[0], rho[1], pos])
}

/// HTLC owner = `htlc_root`: a domain-tagged Merkle-Damgård chain over the two party tags, the
/// hashlock, and the timeout. Block 0 injects `DOM_HTLC` and absorbs `redeem_tag`; blocks 1-3 are
/// merge-shaped (chain ‖ data) absorbing `refund_tag`, `hashlock`, then `[timeout,0,0,0]`. Binding all
/// four into the committed owner means a spender can't substitute different terms (the cm wouldn't be
/// in the tree).
pub fn htlc_root(redeem_tag: [Val; DIGEST], refund_tag: [Val; DIGEST], hashlock: [Val; DIGEST], timeout: Val) -> [Val; DIGEST] {
    let mut s0 = [Val::ZERO; W];
    s0[0] = Val::from_u64(DOM_HTLC);
    s0[DIGEST..].copy_from_slice(&redeem_tag);
    let c0: [Val; DIGEST] = native_permute(s0)[..DIGEST].try_into().unwrap();
    let mut s1 = [Val::ZERO; W];
    s1[..DIGEST].copy_from_slice(&c0);
    s1[DIGEST..].copy_from_slice(&refund_tag);
    let c1: [Val; DIGEST] = native_permute(s1)[..DIGEST].try_into().unwrap();
    let mut s2 = [Val::ZERO; W];
    s2[..DIGEST].copy_from_slice(&c1);
    s2[DIGEST..].copy_from_slice(&hashlock);
    let c2: [Val; DIGEST] = native_permute(s2)[..DIGEST].try_into().unwrap();
    let mut s3 = [Val::ZERO; W];
    s3[..DIGEST].copy_from_slice(&c2);
    s3[DIGEST] = timeout;
    native_permute(s3)[..DIGEST].try_into().unwrap()
}

/// Nullifier of an HTLC note: derived from the note's `owner` (= `htlc_root`), NOT the claiming
/// party's `nk`, so it is identical whether the note is redeemed or refunded — one note ⇒ one
/// nullifier (else a note could be spent once per mode = double-spend). Layout `[DOM_NF_HTLC ‖
/// owner(4) ‖ rho0 ‖ rho1 ‖ pos]`.
pub fn nullifier_owner(owner: [Val; DIGEST], rho: [Val; 2], pos: Val) -> [Val; DIGEST] {
    h(DOM_NF_HTLC, &[owner[0], owner[1], owner[2], owner[3], rho[0], rho[1], pos])
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
    pub nk: [u64; 2], // 128-bit nullifier key / spend authority (the claiming party for an HTLC note)
    pub div: Val, // diversifier of the address this note was sent to (recipient = H(nk ‖ div))
    pub asset: Val, // hidden asset id (all notes in a tx share one asset)
    pub note_type: Val, // 0 = PLAIN, 1 = HTLC
    pub value: u64,
    pub rho: [Val; 2], // 128-bit note randomness
    pub rcm: [Val; 2], // 128-bit commitment trapdoor
    pub sib: [[Val; DIGEST]; DEPTH],
    pub bits: [bool; DEPTH],
    // HTLC fields (note_type == HTLC): the owner is htlc_root = MD-chain(DOM_HTLC ‖ redeem_tag ‖
    // refund_tag ‖ hashlock ‖ timeout); the claiming party proves nk owns redeem_tag (redeem) or
    // refund_tag (refund). Ignored for PLAIN notes.
    pub mode: Val, // 1 = redeem, 0 = refund
    pub redeem_tag: [Val; DIGEST],
    pub refund_tag: [Val; DIGEST],
    pub hashlock: [Val; DIGEST], // SHA256(preimage) as 4 field limbs
    pub timeout: u64,
}

#[derive(Clone, Copy)]
pub struct Output {
    pub recipient: [Val; DIGEST], // the note owner: a recipient digest (PLAIN) or an htlc_root (HTLC)
    pub asset: Val, // hidden asset id (must equal the inputs' asset)
    pub note_type: Val, // 0 = PLAIN, 1 = HTLC
    pub value: u64,
    pub rho: [Val; 2],
    pub rcm: [Val; 2],
}

#[derive(Clone)]
pub struct Witness {
    pub inputs: [Input; N_IN],
    pub outputs: [Output; M_OUT],
    pub fee: u64,
    pub mint: u64, // public issuance (0 for a normal tx; > 0 for coinbase)
    pub tx_binding: [Val; DIGEST],
    pub current_height: u64, // public: the block height the tx is validated at (HTLC timeout compare)
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
    let asset = w.inputs[0].asset; // the single (hidden) asset of this tx
    let htlc = Val::from_u64(NOTE_HTLC);
    for (i, inp) in w.inputs.iter().enumerate() {
        assert_eq!(inp.asset, asset, "input {i} uses a different asset (single-asset tx)");
        let (nk0, nk1) = (Val::from_u64(inp.nk[0]), Val::from_u64(inp.nk[1]));
        let claim_tag = recipient_of(nk0, nk1, inp.div); // the claiming party's ownership tag
        let is_htlc = inp.note_type == htlc;
        // owner = htlc_root (HTLC) or the claiming recipient tag (PLAIN).
        let owner = if is_htlc {
            htlc_root(inp.redeem_tag, inp.refund_tag, inp.hashlock, Val::from_u64(inp.timeout))
        } else {
            claim_tag
        };
        if is_htlc {
            // The claiming party must own the tag selected by `mode`; and the timeout window must hold.
            let redeeming = inp.mode == Val::from_u64(1);
            let want = if redeeming { inp.redeem_tag } else { inp.refund_tag };
            assert_eq!(claim_tag, want, "input {i}: claim does not match the selected HTLC party");
            if redeeming {
                assert!(w.current_height < inp.timeout, "input {i}: redeem requires height < timeout");
            } else {
                assert!(w.current_height >= inp.timeout, "input {i}: refund requires height >= timeout");
            }
        }
        let cm = commit(owner, Val::from_u64(inp.value), inp.rho, inp.rcm, inp.asset, inp.note_type);
        let root = fold(cm, &inp.sib, &inp.bits);
        match anchor {
            None => anchor = Some(root),
            Some(a) => assert_eq!(a, root, "input {i} folds to a different anchor"),
        }
        // Nullifier: mode/party-independent for HTLC (owner-based), nk-based for PLAIN.
        let pos = pos_of(&inp.bits);
        nullifiers[i] = if is_htlc { nullifier_owner(owner, inp.rho, pos) } else { nullifier(nk0, nk1, inp.rho, pos) };
        in_sum += inp.value as u128;
    }
    // per-output commitment (the output owner — a recipient digest or an htlc_root — is a free witness)
    let mut out_cms = [[Val::ZERO; DIGEST]; M_OUT];
    let mut out_sum: u128 = 0;
    for (j, out) in w.outputs.iter().enumerate() {
        assert_eq!(out.asset, asset, "output {j} uses a different asset (single-asset tx)");
        out_cms[j] = commit(out.recipient, Val::from_u64(out.value), out.rho, out.rcm, out.asset, out.note_type);
        out_sum += out.value as u128;
    }
    // value balance (A3: all values range-bounded ⇒ no wraparound)
    assert_eq!(in_sum + w.mint as u128, out_sum + w.fee as u128, "value balance Σin + mint = Σout + fee");
    PublicOutputs { anchor: anchor.unwrap(), nullifiers, out_cms }
}

// ==============================================================================================
// AIR — stage 1: multi-input membership to a shared anchor (domain-tagged ownership + commitment).
// Later stages add nullifiers (A1 pos-binding), accumulator balance + range (A3), outputs, and the
// per-instance public bindings. Built incrementally; each stage differential-tested vs the oracle.
// ==============================================================================================

// ownership, commit_a, commit_b, DEPTH merges, nullifier, then 4 htlc_root blocks at the span END
// (kept after the nullifier so the existing PLAIN block adjacencies are untouched; the HTLC owner is
// carried into commit_a via the persistent OWNER columns rather than block adjacency).
const HTLC_BLOCKS: usize = 4;
const SPAN_BLOCKS: usize = 4 + DEPTH + HTLC_BLOCKS;
const OUT_BLOCKS: usize = 2; // out_cm perm_a + perm_b (2-permutation commitment; also 64 rows for the value range)
const FEE_BLOCKS: usize = 2; // fee binding + range
const MINT_BLOCKS: usize = 2; // mint (issuance) binding + range
const USED_BLOCKS: usize = N_IN * SPAN_BLOCKS + M_OUT * OUT_BLOCKS + FEE_BLOCKS + MINT_BLOCKS;
const NUM_BLOCKS: usize = USED_BLOCKS.next_power_of_two();
const HEIGHT: usize = NUM_BLOCKS * BLOCK;

// columns
const BIT: usize = 8; // membership position bit
const NK: usize = 9; // local-persistent within an input span
const RHO: usize = 10; // rho limb 0 (local-persistent)
const VAL: usize = 11; // value within input / output / fee / mint region
const POSACC: usize = 12; // Σ bit_d·2^d within an input's membership (A1)
const VALACC: usize = 13; // global balance accumulator: +in +mint −out −fee ⇒ 0
const REM: usize = 14; // range running remainder
const RBIT: usize = 15;
const NK1: usize = 16; // second limb of the 128-bit nullifier key (NK = limb 0)
const RHO1: usize = 17; // rho limb 1 (local-persistent; 128-bit note randomness)
const ASSET: usize = 18; // hidden asset id — GLOBAL-persistent (constant across the whole tx)
// OWNER0..3: the note's owner digest (recipient for PLAIN, htlc_root for HTLC), local-persistent in
// the span. Carries the owner into commit_a without block-adjacency, so the htlc_root (computed in the
// span-end blocks) can feed commit_a (audit/AIR layout note in the header).
const OWNER0: usize = 19;
const NT: usize = 23; // note_type (0=PLAIN, 1=HTLC), local-persistent; == committed commit_b lane 7
// CLAIM0..3: the claiming party's tag = own.out = H(DOM_OWN ‖ nk ‖ div), local-persistent. For an
// HTLC note the spend proves CLAIM == the mode-selected party tag (redeem_tag / refund_tag).
const CLAIM0: usize = 24;
const MODE: usize = 28; // 1 = redeem, 0 = refund (local-persistent, boolean)
// HTLC timeout compare (range argument, reusing REM/RBIT in the free span-end htlc region):
const TIMEOUT: usize = 29; // the committed timeout (== htlc block 3 input lane 4), local-persistent
const DIFF: usize = 30; // redeem: timeout-height-1 ; refund: height-timeout ; range-checked ≥ 0
const WIDTH: usize = 31; // …, MODE=28, TIMEOUT=29, DIFF=30

// periodic-column indices: 0..11 round schedule (period 32), then fixed (length HEIGHT) selectors.
// The commitment is two permutations (commit_a -> chain -> commit_b -> cm); outputs likewise.
const P_OWN_IN: usize = 11;
const P_RECIP_LINK: usize = 12; // own.out -> commit_a.in recipient lanes
const P_COMMIT_A_IN: usize = 13; // input commit_a: DOM_CM, value, rho0, rho1
const P_CHAIN_LINK: usize = 14; // commit_a.out -> commit_b.in[0..4] (input & output commitments)
const P_COMMIT_B: usize = 15; // commit_b.in pad lanes = 0 (input & output commitments)
const P_MEM_LINK: usize = 16;
const P_POS_COEFF: usize = 17; // 2^d at each membership link
const P_ROOT: usize = 18;
const P_NULL_IN: usize = 19;
const P_OUT_A_IN: usize = 20; // output out_a: DOM_CM, out_value
const P_FEE_IN: usize = 21;
const P_MINT_IN: usize = 22; // issuance amount binding row
const P_REGION_LAST: usize = 23; // last row of each region (gates local-persistent columns)
const P_RANGE_SEED: usize = 24; // rem = VAL (each value's first range row)
const P_RANGE_ACTIVE: usize = 25; // decomposition rows
const P_RANGE_CLOSE: usize = 26; // rem = 0 (value < 2^BITS)
const P_ROW0: usize = 27; // VALACC = 0
const P_FINAL: usize = 28; // VALACC = 0 (balance)
const P_IN_COMMIT_B: usize = 29; // input commit_b ONLY (binds lane 7 = note_type); outputs free
const P_HTLC_IN0: usize = 30; // htlc block 0 input: lane0=DOM_HTLC, lanes1-3=0
const P_HTLC_LINK: usize = 31; // htlc blocks 0,1,2 OUTPUT: chain link out[0..4] -> next in[0..4]
const P_HTLC_IN3: usize = 32; // htlc block 3 input: capacity lanes 5,6,7 = 0
const P_HTLC_ROOT: usize = 33; // htlc block 3 OUTPUT = htlc_root (owner gate when HTLC)
const P_HTLC_IN1: usize = 34; // htlc block 1 input (refund_tag in lanes 4..8 — for the refund tag-match)
const P_HTLC_IN2: usize = 35; // htlc block 2 input (hashlock in lanes 4..8 — for the redeem hashlock bind)
const P_TO_SEED: usize = 36; // timeout range seed (REM = TIMEOUT), in the htlc region
const P_DIFF_SEED: usize = 37; // diff range seed (REM = DIFF) + the height/timeout compare
const P_HEIGHT_SEED: usize = 38; // current_height range seed (REM = pis[PI_HEIGHT]); single global window
const P_NULLOUT: usize = 39; // N_IN one-hots: nf_i binding
const P_OUTOUT: usize = 39 + N_IN; // M_OUT one-hots: out_cm_j binding
const N_PERIODIC: usize = 39 + N_IN + M_OUT;

// public inputs: anchor(4) ‖ nf_i(4·N) ‖ out_cm_j(4·M) ‖ fee(1) ‖ mint(1) ‖ tx_binding(4) ‖
//                current_height(1) ‖ redeem_hashlock(4)
const PI_ANCHOR: usize = 0;
const PI_NF: usize = 4;
const PI_OUTCM: usize = 4 + N_IN * DIGEST;
const PI_FEE: usize = 4 + N_IN * DIGEST + M_OUT * DIGEST;
const PI_MINT: usize = PI_FEE + 1;
const PI_TXBIND: usize = PI_MINT + 1;
const PI_HEIGHT: usize = PI_TXBIND + DIGEST; // current block height (HTLC timeout compare)
const PI_HASHLOCK: usize = PI_HEIGHT + 1; // SHA256(preimage) = the redeemed note's committed hashlock
const N_PUBLIC: usize = PI_HASHLOCK + DIGEST;

const fn input_base(i: usize) -> usize {
    i * SPAN_BLOCKS
}
const fn own_in_row(i: usize) -> usize {
    input_base(i) * BLOCK
}
const fn own_out_row(i: usize) -> usize {
    input_base(i) * BLOCK + BLOCK - 1
}
const fn commit_a_in_row(i: usize) -> usize {
    (input_base(i) + 1) * BLOCK
}
const fn commit_a_out_row(i: usize) -> usize {
    (input_base(i) + 1) * BLOCK + BLOCK - 1
}
const fn commit_b_in_row(i: usize) -> usize {
    (input_base(i) + 2) * BLOCK
}
const fn root_row(i: usize) -> usize {
    (input_base(i) + 2 + DEPTH) * BLOCK + BLOCK - 1
}
const fn null_block(i: usize) -> usize {
    input_base(i) + 3 + DEPTH
}
const fn null_in_row(i: usize) -> usize {
    null_block(i) * BLOCK
}
const fn null_out_row(i: usize) -> usize {
    null_block(i) * BLOCK + BLOCK - 1
}
/// htlc_root chain blocks live at the span END (blocks 4+DEPTH .. 7+DEPTH of input `i`).
const fn htlc_block(i: usize, k: usize) -> usize {
    input_base(i) + 4 + DEPTH + k
}
const fn htlc_out_row(i: usize, k: usize) -> usize {
    htlc_block(i, k) * BLOCK + BLOCK - 1
}
/// The last row of an input span (now the final htlc_root block) — the region-persistence boundary.
const fn span_last_row(i: usize) -> usize {
    htlc_out_row(i, HTLC_BLOCKS - 1)
}
/// A single global range window for the public current_height, seeded at input 0's first membership
/// merge block (blocks ≥ base+3 use the BIT column, not REM/RBIT, so the range columns are free for the
/// BITS+1-row decomposition). v3 defense-in-depth: range-check current_height in-circuit so the timeout
/// compare is sound without trusting the node for height < 2^BITS.
const fn height_seed_row() -> usize {
    (input_base(0) + 3) * BLOCK
}
const fn out_base(j: usize) -> usize {
    N_IN * SPAN_BLOCKS + j * OUT_BLOCKS
}
const fn out_in_row(j: usize) -> usize {
    out_base(j) * BLOCK // out_a input (DOM_CM, recipient, value, rho0, rho1); value-range seed
}
const fn out_a_out_row(j: usize) -> usize {
    out_base(j) * BLOCK + BLOCK - 1
}
const fn out_b_in_row(j: usize) -> usize {
    (out_base(j) + 1) * BLOCK
}
const fn out_out_row(j: usize) -> usize {
    (out_base(j) + 1) * BLOCK + BLOCK - 1 // out_b output = public out_cm_j
}
const fn fee_base() -> usize {
    N_IN * SPAN_BLOCKS + M_OUT * OUT_BLOCKS
}
const fn fee_in_row() -> usize {
    fee_base() * BLOCK
}
const fn mint_base() -> usize {
    fee_base() + FEE_BLOCKS
}
const fn mint_in_row() -> usize {
    mint_base() * BLOCK
}

fn one_hot(rows: &[usize]) -> Vec<Val> {
    let mut c = vec![Val::ZERO; HEIGHT];
    for &r in rows {
        c[r] = Val::ONE;
    }
    c
}

fn periodic() -> Vec<Vec<Val>> {
    let mut cols = periodic_table(); // 11 round-schedule columns, period 32
    let own_in: Vec<usize> = (0..N_IN).map(own_in_row).collect();
    let recip: Vec<usize> = (0..N_IN).map(own_out_row).collect(); // own output → commit_a recipient
    let commit_a_in: Vec<usize> = (0..N_IN).map(commit_a_in_row).collect();
    // chain links: commit_a.out → commit_b.in (inputs) and out_a.out → out_b.in (outputs)
    let mut chain_link: Vec<usize> = (0..N_IN).map(commit_a_out_row).collect();
    chain_link.extend((0..M_OUT).map(out_a_out_row));
    // commit_b input rows (inputs & outputs): the pad lanes (6,7) are constrained to 0
    let mut commit_b: Vec<usize> = (0..N_IN).map(commit_b_in_row).collect();
    commit_b.extend((0..M_OUT).map(out_b_in_row));
    // membership links + the 2^d position coefficient at each link (A1). Leaf = commit_b output.
    let mut mem: Vec<usize> = Vec::new();
    let mut pos_coeff = vec![Val::ZERO; HEIGHT];
    for i in 0..N_IN {
        for d in 0..DEPTH {
            let row = (input_base(i) + 2 + d) * BLOCK + BLOCK - 1;
            mem.push(row);
            pos_coeff[row] = Val::from_u64(1u64 << d);
        }
    }
    let root: Vec<usize> = (0..N_IN).map(root_row).collect();
    let null_in: Vec<usize> = (0..N_IN).map(null_in_row).collect();
    let out_a_in: Vec<usize> = (0..M_OUT).map(out_in_row).collect();
    // region-last rows (gate local-persistent columns at region boundaries)
    let mut region_last: Vec<usize> = (0..N_IN).map(span_last_row).collect(); // span end (after htlc blocks)
    region_last.extend((0..M_OUT).map(|j| out_in_row(j) + OUT_BLOCKS * BLOCK - 1));
    region_last.push(fee_in_row() + FEE_BLOCKS * BLOCK - 1);
    region_last.push(mint_in_row() + MINT_BLOCKS * BLOCK - 1);
    // range windows: one per value (each input value at commit_a, output value at out_a, fee, mint)
    let mut seeds: Vec<usize> = (0..N_IN).map(commit_a_in_row).collect();
    seeds.extend((0..M_OUT).map(out_in_row));
    seeds.push(fee_in_row());
    seeds.push(mint_in_row());
    let mut range_active: Vec<usize> = Vec::new();
    let mut range_close: Vec<usize> = Vec::new();
    for &s in &seeds {
        range_active.extend(s..s + BITS);
        range_close.push(s + BITS);
    }
    // HTLC timeout-compare range windows (reuse REM/RBIT in the free span-end htlc region): a TIMEOUT
    // window at htlc block 0 and a DIFF window at htlc block 2 (each ≤ 53 rows; blocks 0-1 and 2-3 are
    // disjoint). Their SEEDs read TIMEOUT/DIFF (separate selectors); active/close share the generic
    // REM decomposition below.
    let to_seeds: Vec<usize> = (0..N_IN).map(|i| htlc_block(i, 0) * BLOCK).collect();
    let diff_seeds: Vec<usize> = (0..N_IN).map(|i| htlc_block(i, 2) * BLOCK).collect();
    for &s in to_seeds.iter().chain(diff_seeds.iter()) {
        range_active.extend(s..s + BITS);
        range_close.push(s + BITS);
    }
    // the single global current_height window (in input 0's membership region; REM/RBIT free there)
    range_active.extend(height_seed_row()..height_seed_row() + BITS);
    range_close.push(height_seed_row() + BITS);

    cols.push(one_hot(&own_in)); // P_OWN_IN
    cols.push(one_hot(&recip)); // P_RECIP_LINK
    cols.push(one_hot(&commit_a_in)); // P_COMMIT_A_IN
    cols.push(one_hot(&chain_link)); // P_CHAIN_LINK
    cols.push(one_hot(&commit_b)); // P_COMMIT_B
    cols.push(one_hot(&mem)); // P_MEM_LINK
    cols.push(pos_coeff); // P_POS_COEFF
    cols.push(one_hot(&root)); // P_ROOT
    cols.push(one_hot(&null_in)); // P_NULL_IN
    cols.push(one_hot(&out_a_in)); // P_OUT_A_IN
    cols.push(one_hot(&[fee_in_row()])); // P_FEE_IN
    cols.push(one_hot(&[mint_in_row()])); // P_MINT_IN
    cols.push(one_hot(&region_last)); // P_REGION_LAST
    cols.push(one_hot(&seeds)); // P_RANGE_SEED
    cols.push(one_hot(&range_active)); // P_RANGE_ACTIVE
    cols.push(one_hot(&range_close)); // P_RANGE_CLOSE
    cols.push(one_hot(&[0])); // P_ROW0
    cols.push(one_hot(&[mint_in_row() + MINT_BLOCKS * BLOCK - 1])); // P_FINAL (after mint contribution)
    let in_commit_b: Vec<usize> = (0..N_IN).map(commit_b_in_row).collect(); // input commit_b only
    cols.push(one_hot(&in_commit_b)); // P_IN_COMMIT_B
    // htlc_root chain selectors (span-end blocks 0..HTLC_BLOCKS of each input)
    let htlc_in0: Vec<usize> = (0..N_IN).map(|i| htlc_block(i, 0) * BLOCK).collect();
    let mut htlc_link: Vec<usize> = Vec::new();
    for i in 0..N_IN {
        for k in 0..HTLC_BLOCKS - 1 {
            htlc_link.push(htlc_out_row(i, k)); // block k output → block k+1 input (chain)
        }
    }
    let htlc_in3: Vec<usize> = (0..N_IN).map(|i| htlc_block(i, HTLC_BLOCKS - 1) * BLOCK).collect();
    let htlc_root_out: Vec<usize> = (0..N_IN).map(|i| htlc_out_row(i, HTLC_BLOCKS - 1)).collect();
    cols.push(one_hot(&htlc_in0)); // P_HTLC_IN0
    cols.push(one_hot(&htlc_link)); // P_HTLC_LINK
    cols.push(one_hot(&htlc_in3)); // P_HTLC_IN3
    cols.push(one_hot(&htlc_root_out)); // P_HTLC_ROOT
    let htlc_in1: Vec<usize> = (0..N_IN).map(|i| htlc_block(i, 1) * BLOCK).collect();
    cols.push(one_hot(&htlc_in1)); // P_HTLC_IN1
    let htlc_in2: Vec<usize> = (0..N_IN).map(|i| htlc_block(i, 2) * BLOCK).collect();
    cols.push(one_hot(&htlc_in2)); // P_HTLC_IN2
    cols.push(one_hot(&to_seeds)); // P_TO_SEED
    cols.push(one_hot(&diff_seeds)); // P_DIFF_SEED
    cols.push(one_hot(&[height_seed_row()])); // P_HEIGHT_SEED (single global window for current_height)
    for i in 0..N_IN {
        cols.push(one_hot(&[null_out_row(i)])); // P_NULLOUT + i
    }
    for j in 0..M_OUT {
        cols.push(one_hot(&[out_out_row(j)])); // P_OUTOUT + j
    }
    cols
}

pub struct HtlcAir;

impl BaseAir<Goldilocks> for HtlcAir {
    fn width(&self) -> usize {
        WIDTH
    }
    fn num_public_values(&self) -> usize {
        N_PUBLIC // anchor ‖ N nullifiers ‖ M out_cms ‖ fee ‖ tx_binding
    }
    fn num_periodic_columns(&self) -> usize {
        N_PERIODIC
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        periodic()
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for HtlcAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        let pis: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
        let one = AB::Expr::ONE;
        let two = AB::Expr::TWO;
        let dom_own = AB::Expr::from(Goldilocks::from_u64(DOM_OWN));
        let dom_cm = AB::Expr::from(Goldilocks::from_u64(DOM_CM));
        let dom_nf = AB::Expr::from(Goldilocks::from_u64(DOM_NF));
        let dom_htlc = AB::Expr::from(Goldilocks::from_u64(DOM_HTLC));
        let dom_nf_htlc = AB::Expr::from(Goldilocks::from_u64(DOM_NF_HTLC));

        let is_init = p[0].clone();
        let is_full = p[1].clone();
        let is_partial = p[2].clone();
        let rc: Vec<AB::Expr> = (0..8).map(|i| p[3 + i].clone()).collect();

        // ---- Poseidon2 round constraints on the state columns (period-32 schedule) ----
        let mut init_s: [AB::Expr; 8] = core::array::from_fn(|i| cur[i].clone());
        ext_linear(&mut init_s);
        let mut full_s: [AB::Expr; 8] = core::array::from_fn(|i| pow7(cur[i].clone() + rc[i].clone()));
        ext_linear(&mut full_s);
        let mut part_s: [AB::Expr; 8] =
            core::array::from_fn(|i| if i == 0 { pow7(cur[0].clone() + rc[0].clone()) } else { cur[i].clone() });
        int_linear(&mut part_s);
        for i in 0..8 {
            let round = is_init.clone() * (nxt[i].clone() - init_s[i].clone())
                + is_full.clone() * (nxt[i].clone() - full_s[i].clone())
                + is_partial.clone() * (nxt[i].clone() - part_s[i].clone());
            builder.when_transition().assert_zero(round);
        }

        // ---- local-persistent columns: constant within a region, free at region boundaries ----
        // RHO1 MUST be here: it is read at both commit_a (lane 7) and the nullifier (lane 4); without
        // persistence a prover could use one rho1 in the commitment and another in the nullifier,
        // minting a fresh nullifier for a real note ⇒ double-spend.
        let not_last = one.clone() - p[P_REGION_LAST].clone();
        for &c in &[
            NK, NK1, RHO, RHO1, VAL, OWNER0, OWNER0 + 1, OWNER0 + 2, OWNER0 + 3, NT,
            CLAIM0, CLAIM0 + 1, CLAIM0 + 2, CLAIM0 + 3, MODE, TIMEOUT,
        ] {
            builder.when_transition().assert_zero(not_last.clone() * (nxt[c].clone() - cur[c].clone()));
        }
        // ASSET is GLOBAL-persistent: constant across the whole trace (one hidden asset per tx), so
        // every note's committed asset (bound at commit_b below) equals this single value.
        builder.when_transition().assert_zero(nxt[ASSET].clone() - cur[ASSET].clone());
        // pos_acc: += bit·2^d at membership links, else constant within the span (A1)
        let bit = nxt[BIT].clone();
        builder.when_transition().assert_zero(
            not_last.clone()
                * (nxt[POSACC].clone() - cur[POSACC].clone() - p[P_MEM_LINK].clone() * (bit.clone() * p[P_POS_COEFF].clone())),
        );
        builder.assert_zero(p[P_OWN_IN].clone() * cur[POSACC].clone()); // reset to 0 at span start

        // ---- global value accumulator: +in (commit), −out, −fee ⇒ 0 ----
        builder.assert_zero(p[P_ROW0].clone() * cur[VALACC].clone());
        let acc_delta = (p[P_COMMIT_A_IN].clone() + p[P_MINT_IN].clone() - p[P_OUT_A_IN].clone() - p[P_FEE_IN].clone())
            * cur[VAL].clone();
        builder.when_transition().assert_zero(nxt[VALACC].clone() - cur[VALACC].clone() - acc_delta);
        builder.assert_zero(p[P_FINAL].clone() * cur[VALACC].clone()); // balance: Σin = Σout + fee

        // ---- range: rem=VAL at seed, rem=2·rem'+rbit (rbit boolean), rem=0 at close (A3) ----
        builder.assert_zero(p[P_RANGE_SEED].clone() * (cur[REM].clone() - cur[VAL].clone()));
        let ra = p[P_RANGE_ACTIVE].clone();
        builder
            .when_transition()
            .assert_zero(ra.clone() * (cur[REM].clone() - (two.clone() * nxt[REM].clone() + cur[RBIT].clone())));
        builder.when_transition().assert_zero(ra.clone() * (cur[RBIT].clone() * (one.clone() - cur[RBIT].clone())));
        builder.assert_zero(p[P_RANGE_CLOSE].clone() * cur[REM].clone());

        // ---- ownership input: [DOM_OWN, nk0, nk1, d, 0,0,0,0] ----
        // `d` (lane 3) is the diversifier — a FREE input: the spender uses the note's actual
        // diversifier (else the recomputed recipient → cm won't be in the tree), so no extra
        // constraint is needed (matching someone else's tag is a 2^128 preimage). recipient = H(DOM_OWN
        // ‖ nk0 ‖ nk1 ‖ d).
        let own = p[P_OWN_IN].clone();
        builder.assert_zero(own.clone() * (cur[0].clone() - dom_own.clone()));
        builder.assert_zero(own.clone() * (cur[1].clone() - cur[NK].clone()));
        builder.assert_zero(own.clone() * (cur[2].clone() - cur[NK1].clone()));
        for i in 4..8 {
            builder.assert_zero(own.clone() * cur[i].clone());
        }

        // ---- owner binding (note_type-gated) ----
        // NT is boolean (PLAIN=0 / HTLC=1).
        builder.assert_zero(p[P_OWN_IN].clone() * cur[NT].clone() * (cur[NT].clone() - one.clone()));
        let nt = cur[NT].clone();
        let not_htlc = one.clone() - nt.clone();
        // PLAIN: OWNER == own.out (the recipient digest) at the ownership output.
        let rl = p[P_RECIP_LINK].clone();
        for k in 0..DIGEST {
            builder.assert_zero(rl.clone() * not_htlc.clone() * (cur[OWNER0 + k].clone() - cur[k].clone()));
        }
        // HTLC: OWNER == htlc_root (= htlc block 3 output) at the htlc_root row.
        let hr = p[P_HTLC_ROOT].clone();
        for k in 0..DIGEST {
            builder.assert_zero(hr.clone() * nt.clone() * (cur[OWNER0 + k].clone() - cur[k].clone()));
        }
        // ---- htlc_root chain: MD-chain(DOM_HTLC ‖ redeem_tag ‖ refund_tag ‖ hashlock ‖ timeout) binds
        //      all four HTLC terms into the committed owner (else cm wouldn't be in the tree). ----
        let h0 = p[P_HTLC_IN0].clone();
        builder.assert_zero(h0.clone() * (cur[0].clone() - dom_htlc.clone())); // block 0 lane0 = DOM_HTLC
        for k in 1..DIGEST {
            builder.assert_zero(h0.clone() * cur[k].clone()); // capacity lanes 1..4 = 0 (redeem_tag in lanes 4..8)
        }
        let hl = p[P_HTLC_LINK].clone();
        for k in 0..DIGEST {
            builder.when_transition().assert_zero(hl.clone() * (nxt[k].clone() - cur[k].clone())); // chain out[0..4] → next in[0..4]
        }
        let h3 = p[P_HTLC_IN3].clone();
        for k in (DIGEST + 1)..8 {
            builder.assert_zero(h3.clone() * cur[k].clone()); // block 3 capacity lanes 5,6,7 = 0 (timeout in lane 4)
        }

        // ---- claim tag + HTLC tag-match (access control: who may spend the HTLC note) ----
        // CLAIM == own.out = H(DOM_OWN ‖ nk ‖ div), the claiming party's tag (all notes).
        for k in 0..DIGEST {
            builder.assert_zero(rl.clone() * (cur[CLAIM0 + k].clone() - cur[k].clone()));
        }
        // MODE boolean (redeem=1 / refund=0).
        let mode = cur[MODE].clone();
        builder.assert_zero(own.clone() * mode.clone() * (mode.clone() - one.clone()));
        // HTLC tag-match: the claiming party must own the mode-selected party tag. redeem_tag is block 0
        // input lanes 4..8 (gated by MODE); refund_tag is block 1 input lanes 4..8 (gated by 1-MODE).
        for k in 0..DIGEST {
            builder.assert_zero(h0.clone() * nt.clone() * mode.clone() * (cur[DIGEST + k].clone() - cur[CLAIM0 + k].clone()));
        }
        let h1 = p[P_HTLC_IN1].clone();
        for k in 0..DIGEST {
            builder.assert_zero(h1.clone() * nt.clone() * (one.clone() - mode.clone()) * (cur[DIGEST + k].clone() - cur[CLAIM0 + k].clone()));
        }
        // HTLC redeem: the note's hashlock (block 2 input lanes 4..8) == public redeem_hashlock =
        // SHA256(preimage). The cross-chain atomic link — the node checks the revealed preimage hashes
        // to it. Bound only on redeem (refund needs no preimage).
        let h2 = p[P_HTLC_IN2].clone();
        for k in 0..DIGEST {
            builder.assert_zero(h2.clone() * nt.clone() * mode.clone() * (cur[DIGEST + k].clone() - pis[PI_HASHLOCK + k].clone()));
        }

        // ---- HTLC timeout compare (range argument on current_height vs the committed timeout) ----
        // TIMEOUT == htlc block 3 input lane 4 (the committed timeout).
        builder.assert_zero(h3.clone() * (cur[TIMEOUT].clone() - cur[DIGEST].clone()));
        // Range seeds: REM = TIMEOUT, REM = DIFF (the generic REM decomposition + REM=0 close come from
        // the shared P_RANGE_ACTIVE / P_RANGE_CLOSE, whose windows were extended to cover the htlc
        // region) ⇒ TIMEOUT, DIFF ∈ [0, 2^BITS).
        builder.assert_zero(p[P_TO_SEED].clone() * (cur[REM].clone() - cur[TIMEOUT].clone()));
        builder.assert_zero(p[P_DIFF_SEED].clone() * (cur[REM].clone() - cur[DIFF].clone()));
        // DIFF compute (HTLC only): redeem ⇒ timeout-height-1 ; refund ⇒ height-timeout. With TIMEOUT,
        // DIFF, **and** current_height all range-bounded < 2^BITS (the height window just below), DIFF ≥ 0
        // holds iff the timeout window does — redeem ⟺ height < timeout, refund ⟺ height ≥ timeout.
        let height = pis[PI_HEIGHT].clone();
        let redeem_diff = cur[TIMEOUT].clone() - height.clone() - one.clone();
        let refund_diff = height.clone() - cur[TIMEOUT].clone();
        let diff_expr = mode.clone() * redeem_diff + (one.clone() - mode.clone()) * refund_diff;
        builder.assert_zero(p[P_DIFF_SEED].clone() * nt.clone() * (cur[DIFF].clone() - diff_expr));
        // v3 hardening (defense-in-depth — the node also pins/bounds height in applyHtlc): range-check
        // the public current_height in-circuit (REM = height at its seed; shared decomposition + REM=0
        // close), so the timeout compare is sound WITHOUT trusting the node for height < 2^BITS — closing
        // the wrap-around forgery where a near-p height makes a refund DIFF spuriously small.
        builder.assert_zero(p[P_HEIGHT_SEED].clone() * (cur[REM].clone() - pis[PI_HEIGHT].clone()));
        // v3 hardening (defense-in-depth — the node also rejects mint ≠ 0 in applyHtlc): an HTLC spend
        // never issues, so force mint = 0 in-circuit. Without this, the htlc_air verifier (reused in any
        // context) would accept a value-inflating mint > 0.
        builder.assert_zero(pis[PI_MINT].clone());

        // ---- commit_a input: [DOM_CM, OWNER(4), value, rho0, rho1] ----
        let ca = p[P_COMMIT_A_IN].clone();
        builder.assert_zero(ca.clone() * (cur[0].clone() - dom_cm.clone()));
        for k in 0..DIGEST {
            builder.assert_zero(ca.clone() * (cur[1 + k].clone() - cur[OWNER0 + k].clone())); // owner lanes
        }
        builder.assert_zero(ca.clone() * (cur[1 + DIGEST].clone() - cur[VAL].clone())); // value (lane 5)
        builder.assert_zero(ca.clone() * (cur[2 + DIGEST].clone() - cur[RHO].clone())); // rho0  (lane 6)
        builder.assert_zero(ca.clone() * (cur[3 + DIGEST].clone() - cur[RHO1].clone())); // rho1 (lane 7)

        // ---- chain link: commit_b.in[0..4] = commit_a.out[0..4] (also out_b ← out_a) ----
        let cl = p[P_CHAIN_LINK].clone();
        for k in 0..DIGEST {
            builder.when_transition().assert_zero(cl.clone() * (nxt[k].clone() - cur[k].clone()));
        }

        // ---- commit_b input: [chain(4), rcm0, rcm1, 0, 0] — pad lanes 6,7 pinned to 0 (rcm free) ----
        let cb = p[P_COMMIT_B].clone();
        builder.assert_zero(cb.clone() * (cur[DIGEST + 2].clone() - cur[ASSET].clone())); // lane 6 = hidden asset id (in & out)
        // lane 7 = note_type: bound to NT for INPUT commitments (the spend gates on it); free for
        // outputs (part of the recipient's note, like out_recipient / out_rho).
        builder.assert_zero(p[P_IN_COMMIT_B].clone() * (cur[DIGEST + 3].clone() - cur[NT].clone()));

        // ---- membership links: place running digest (= commit_b output) by the bit ----
        let ml = p[P_MEM_LINK].clone();
        for k in 0..DIGEST {
            let placed = (one.clone() - bit.clone()) * (nxt[k].clone() - cur[k].clone())
                + bit.clone() * (nxt[DIGEST + k].clone() - cur[k].clone());
            builder.when_transition().assert_zero(ml.clone() * placed);
        }
        builder.when_transition().assert_zero(ml.clone() * (bit.clone() * (one.clone() - bit.clone())));

        // ---- root: every input folds to the shared public anchor ----
        let pr = p[P_ROOT].clone();
        for k in 0..DIGEST {
            builder.assert_zero(pr.clone() * (cur[k].clone() - pis[PI_ANCHOR + k].clone()));
        }

        // ---- nullifier input (A1: pos = pos_acc), note_type-gated ----
        // PLAIN: [DOM_NF, nk0, nk1, rho0, rho1, pos, 0, 0]
        // HTLC : [DOM_NF_HTLC, owner(4), rho0, rho1, pos]  — owner-based ⇒ mode/party-independent, so
        //        one HTLC note has exactly one nullifier across redeem and refund (no double-spend).
        let ni = p[P_NULL_IN].clone();
        let nip = ni.clone() * not_htlc.clone();
        builder.assert_zero(nip.clone() * (cur[0].clone() - dom_nf.clone()));
        builder.assert_zero(nip.clone() * (cur[1].clone() - cur[NK].clone()));
        builder.assert_zero(nip.clone() * (cur[2].clone() - cur[NK1].clone()));
        builder.assert_zero(nip.clone() * (cur[3].clone() - cur[RHO].clone()));
        builder.assert_zero(nip.clone() * (cur[4].clone() - cur[RHO1].clone()));
        builder.assert_zero(nip.clone() * (cur[5].clone() - cur[POSACC].clone()));
        builder.assert_zero(nip.clone() * cur[6].clone());
        builder.assert_zero(nip.clone() * cur[7].clone());
        let nih = ni.clone() * nt.clone();
        builder.assert_zero(nih.clone() * (cur[0].clone() - dom_nf_htlc.clone()));
        for k in 0..DIGEST {
            builder.assert_zero(nih.clone() * (cur[1 + k].clone() - cur[OWNER0 + k].clone()));
        }
        builder.assert_zero(nih.clone() * (cur[1 + DIGEST].clone() - cur[RHO].clone()));
        builder.assert_zero(nih.clone() * (cur[2 + DIGEST].clone() - cur[RHO1].clone()));
        builder.assert_zero(nih.clone() * (cur[3 + DIGEST].clone() - cur[POSACC].clone()));
        // ---- nullifier output: per-input public nf_i ----
        for i in 0..N_IN {
            let sel = p[P_NULLOUT + i].clone();
            for k in 0..DIGEST {
                builder.assert_zero(sel.clone() * (cur[k].clone() - pis[PI_NF + i * DIGEST + k].clone()));
            }
        }

        // ---- output commit_a: [DOM_CM, out_recipient(free), out_value, out_rho0/1(free)] ----
        // (out_b chain-link + pad lanes are covered by P_CHAIN_LINK / P_COMMIT_B above.)
        let oa = p[P_OUT_A_IN].clone();
        builder.assert_zero(oa.clone() * (cur[0].clone() - dom_cm.clone()));
        builder.assert_zero(oa.clone() * (cur[1 + DIGEST].clone() - cur[VAL].clone())); // out_value (lane 5)
        // ---- output-commitment output (out_b): per-output public out_cm_j ----
        for j in 0..M_OUT {
            let sel = p[P_OUTOUT + j].clone();
            for k in 0..DIGEST {
                builder.assert_zero(sel.clone() * (cur[k].clone() - pis[PI_OUTCM + j * DIGEST + k].clone()));
            }
        }

        // ---- fee region: VAL = public fee (range-checked like any value; A3) ----
        builder.assert_zero(p[P_FEE_IN].clone() * (cur[VAL].clone() - pis[PI_FEE].clone()));

        // ---- mint region: VAL = public mint (issuance; range-checked; added to the balance) ----
        builder.assert_zero(p[P_MINT_IN].clone() * (cur[VAL].clone() - pis[PI_MINT].clone()));

        // tx_binding (pis[PI_TXBIND..]) is bound to the proof by Fiat–Shamir (observed public input).
    }
}

// --- trace + ZK config (stage 1) --------------------------------------------------------------

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
    // The hiding-PCS / Merkle-salt RNG must be a CSPRNG seeded from fresh OS entropy **per proof** —
    // otherwise the zero-knowledge blinding is predictable/identical across proofs and the witness is
    // not actually hidden. ChaCha20Rng is ChaCha-based; `from_os_rng` reseeds each call.
    let val_mmcs = ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), 6, ChaCha20Rng::from_rng(&mut rand::rng()));
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    // production FRI parameters (C-04): ≈103-bit proven / ~127-bit conjectured, smallest-encoding.
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

fn set_block(t: &mut [Val], block: usize, input: [Val; 8]) {
    let rows = native_steps(input);
    for (r, row) in rows.iter().enumerate() {
        let base = (block * BLOCK + r) * WIDTH;
        t[base..base + 8].copy_from_slice(row);
    }
}

/// Range-decompose `value` into the running-remainder columns starting at row `seed`.
fn fill_range(t: &mut [Val], seed: usize, value: u64) {
    let mut rem = value;
    for k in 0..=BITS {
        t[(seed + k) * WIDTH + REM] = Val::from_u64(rem);
        if k < BITS {
            t[(seed + k) * WIDTH + RBIT] = Val::from_u64(rem & 1);
            rem >>= 1;
        }
    }
}

/// Set a local-persistent column to `v` across `[lo, hi]`.
fn fill_col(t: &mut [Val], lo: usize, hi: usize, col: usize, v: Val) {
    for r in lo..=hi {
        t[r * WIDTH + col] = v;
    }
}

fn build_trace(w: &Witness) -> RowMajorMatrix<Val> {
    let mut t = vec![Val::ZERO; HEIGHT * WIDTH];

    // ASSET is global-persistent (one hidden asset id for the whole tx); fill it on every row.
    fill_col(&mut t, 0, HEIGHT - 1, ASSET, w.inputs[0].asset);
    // The single global current_height range window (defense-in-depth; see height_seed_row).
    fill_range(&mut t, height_seed_row(), w.current_height);

    // --- inputs: ownership, commitment, membership, nullifier (+ local-persistent + pos_acc) ---
    for (i, inp) in w.inputs.iter().enumerate() {
        let (nk0, nk1) = (Val::from_u64(inp.nk[0]), Val::from_u64(inp.nk[1]));
        let value = Val::from_u64(inp.value);
        let base = input_base(i);
        let mut own = [Val::ZERO; 8];
        own[0] = Val::from_u64(DOM_OWN);
        own[1] = nk0;
        own[2] = nk1;
        own[3] = inp.div; // diversifier (free input)
        set_block(&mut t, base, own);
        let recipient = recipient_of(nk0, nk1, inp.div);
        // htlc_root chain (the HTLC owner): computed here so it can feed commit_a; the 4 chain blocks
        // are placed at the span END below (reusing these inputs).
        let is_htlc = inp.note_type == Val::from_u64(NOTE_HTLC);
        let mut hs = [[Val::ZERO; 8]; HTLC_BLOCKS];
        hs[0][0] = Val::from_u64(DOM_HTLC);
        hs[0][DIGEST..].copy_from_slice(&inp.redeem_tag);
        let hc0 = native_permute(hs[0]);
        hs[1][..DIGEST].copy_from_slice(&hc0[..DIGEST]);
        hs[1][DIGEST..].copy_from_slice(&inp.refund_tag);
        let hc1 = native_permute(hs[1]);
        hs[2][..DIGEST].copy_from_slice(&hc1[..DIGEST]);
        hs[2][DIGEST..].copy_from_slice(&inp.hashlock);
        let hc2 = native_permute(hs[2]);
        hs[3][..DIGEST].copy_from_slice(&hc2[..DIGEST]);
        hs[3][DIGEST] = Val::from_u64(inp.timeout);
        let htlc_owner: [Val; DIGEST] = native_permute(hs[3])[..DIGEST].try_into().unwrap();
        let owner: [Val; DIGEST] = if is_htlc { htlc_owner } else { recipient };
        // commit_a: H1 = perm([DOM_CM, owner(4), value, rho0, rho1]); its digest is the chain.
        let mut a = [Val::ZERO; 8];
        a[0] = Val::from_u64(DOM_CM);
        a[1..1 + DIGEST].copy_from_slice(&owner);
        a[1 + DIGEST] = value;
        a[1 + DIGEST + 1] = inp.rho[0];
        a[1 + DIGEST + 2] = inp.rho[1];
        set_block(&mut t, base + 1, a);
        let chain = native_permute(a);
        // commit_b: cm = perm([chain(4), rcm0, rcm1, asset, note_type]).
        let mut b = [Val::ZERO; 8];
        b[..DIGEST].copy_from_slice(&chain[..DIGEST]);
        b[DIGEST] = inp.rcm[0];
        b[DIGEST + 1] = inp.rcm[1];
        b[DIGEST + 2] = inp.asset;
        b[DIGEST + 3] = inp.note_type;
        set_block(&mut t, base + 2, b);
        let mut node = commit(owner, value, inp.rho, inp.rcm, inp.asset, inp.note_type); // = perm(b)[..DIGEST]
        for d in 0..DEPTH {
            let (l, r) = if inp.bits[d] { (inp.sib[d], node) } else { (node, inp.sib[d]) };
            let mut min = [Val::ZERO; 8];
            min[..DIGEST].copy_from_slice(&l);
            min[DIGEST..].copy_from_slice(&r);
            set_block(&mut t, base + 3 + d, min);
            t[((base + 3 + d) * BLOCK) * WIDTH + BIT] = if inp.bits[d] { Val::ONE } else { Val::ZERO };
            node = merge(l, r);
        }
        // nullifier block — PLAIN: [DOM_NF, nk0, nk1, rho0, rho1, pos]; HTLC: mode/party-independent
        // [DOM_NF_HTLC, owner(4), rho0, rho1, pos] (owner-based, so one note ⇒ one nullifier).
        let pos = pos_of(&inp.bits);
        let mut nin = [Val::ZERO; 8];
        if is_htlc {
            nin[0] = Val::from_u64(DOM_NF_HTLC);
            nin[1..1 + DIGEST].copy_from_slice(&owner);
            nin[1 + DIGEST] = inp.rho[0];
            nin[2 + DIGEST] = inp.rho[1];
            nin[3 + DIGEST] = pos;
        } else {
            nin[0] = Val::from_u64(DOM_NF);
            nin[1] = nk0;
            nin[2] = nk1;
            nin[3] = inp.rho[0];
            nin[4] = inp.rho[1];
            nin[5] = pos;
        }
        set_block(&mut t, null_block(i), nin);
        // htlc_root chain blocks at the span END (reuse the chain inputs computed above).
        for k in 0..HTLC_BLOCKS {
            set_block(&mut t, htlc_block(i, k), hs[k]);
        }
        // local-persistent nk/rho/value/owner across the span (extends over the span-end htlc blocks)
        let (lo, hi) = (own_in_row(i), span_last_row(i));
        fill_col(&mut t, lo, hi, NK, nk0);
        fill_col(&mut t, lo, hi, NK1, nk1);
        fill_col(&mut t, lo, hi, RHO, inp.rho[0]);
        fill_col(&mut t, lo, hi, RHO1, inp.rho[1]);
        fill_col(&mut t, lo, hi, VAL, value);
        // OWNER = the note owner (recipient for PLAIN; htlc_root for HTLC).
        for k in 0..DIGEST {
            fill_col(&mut t, lo, hi, OWNER0 + k, owner[k]);
        }
        fill_col(&mut t, lo, hi, NT, inp.note_type); // note_type (committed in commit_b lane 7)
        for k in 0..DIGEST {
            fill_col(&mut t, lo, hi, CLAIM0 + k, recipient[k]); // claim tag = own.out (the spender's tag)
        }
        fill_col(&mut t, lo, hi, MODE, inp.mode); // redeem(1)/refund(0)
        // HTLC timeout compare: TIMEOUT (committed), DIFF (redeem: timeout-height-1; refund:
        // height-timeout; 0 for PLAIN), each range-decomposed via REM/RBIT in the free htlc region.
        let diff_value: u64 = if is_htlc {
            if inp.mode == Val::from_u64(1) { inp.timeout - w.current_height - 1 } else { w.current_height - inp.timeout }
        } else {
            0
        };
        fill_col(&mut t, lo, hi, TIMEOUT, Val::from_u64(inp.timeout));
        fill_col(&mut t, lo, hi, DIFF, Val::from_u64(diff_value));
        fill_range(&mut t, htlc_block(i, 0) * BLOCK, inp.timeout); // TIMEOUT ∈ [0, 2^BITS)
        fill_range(&mut t, htlc_block(i, 2) * BLOCK, diff_value); // DIFF ∈ [0, 2^BITS)
        // pos_acc: cumulative Σ bit_d·2^d (jumps after each membership link; leaf = commit_b output)
        let mut acc = 0u64;
        let mut links: Vec<(usize, u64)> = Vec::new();
        for d in 0..DEPTH {
            links.push(((base + 2 + d) * BLOCK + BLOCK - 1, if inp.bits[d] { 1u64 << d } else { 0 }));
        }
        for r in lo..=hi {
            t[r * WIDTH + POSACC] = Val::from_u64(acc);
            for (lr, add) in &links {
                if *lr == r {
                    acc += add;
                }
            }
        }
        // range-check the input value (window starts at commit_a; spans commit_a+commit_b = 64 rows)
        fill_range(&mut t, commit_a_in_row(i), inp.value);
    }

    // --- outputs: 2-permutation commitment (out_a, out_b) + value range ---
    for (j, out) in w.outputs.iter().enumerate() {
        let mut oa = [Val::ZERO; 8];
        oa[0] = Val::from_u64(DOM_CM);
        oa[1..1 + DIGEST].copy_from_slice(&out.recipient);
        oa[1 + DIGEST] = Val::from_u64(out.value);
        oa[1 + DIGEST + 1] = out.rho[0];
        oa[1 + DIGEST + 2] = out.rho[1];
        set_block(&mut t, out_base(j), oa);
        let chain = native_permute(oa);
        let mut ob = [Val::ZERO; 8];
        ob[..DIGEST].copy_from_slice(&chain[..DIGEST]);
        ob[DIGEST] = out.rcm[0];
        ob[DIGEST + 1] = out.rcm[1];
        ob[DIGEST + 2] = out.asset;
        ob[DIGEST + 3] = out.note_type;
        set_block(&mut t, out_base(j) + 1, ob); // out_b: cm = perm(ob)[..DIGEST]
        let (lo, hi) = (out_in_row(j), out_in_row(j) + OUT_BLOCKS * BLOCK - 1);
        fill_col(&mut t, lo, hi, VAL, Val::from_u64(out.value));
        fill_range(&mut t, out_in_row(j), out.value);
    }

    // --- fee region: VAL = fee, range-checked (A3) ---
    set_block(&mut t, fee_base(), [Val::ZERO; 8]);
    set_block(&mut t, fee_base() + 1, [Val::ZERO; 8]);
    let (flo, fhi) = (fee_in_row(), fee_in_row() + FEE_BLOCKS * BLOCK - 1);
    fill_col(&mut t, flo, fhi, VAL, Val::from_u64(w.fee));
    fill_range(&mut t, fee_in_row(), w.fee);

    // --- mint region: VAL = mint (issuance), range-checked ---
    set_block(&mut t, mint_base(), [Val::ZERO; 8]);
    set_block(&mut t, mint_base() + 1, [Val::ZERO; 8]);
    let (mlo, mhi) = (mint_in_row(), mint_in_row() + MINT_BLOCKS * BLOCK - 1);
    fill_col(&mut t, mlo, mhi, VAL, Val::from_u64(w.mint));
    fill_range(&mut t, mint_in_row(), w.mint);

    // --- padding blocks: valid permutations of zero ---
    for b in USED_BLOCKS..NUM_BLOCKS {
        set_block(&mut t, b, [Val::ZERO; 8]);
    }

    // --- global value accumulator: +in (commit) +mint −out −fee ⇒ 0 ---
    let mut delta = vec![0i128; HEIGHT];
    for (i, inp) in w.inputs.iter().enumerate() {
        delta[commit_a_in_row(i)] += inp.value as i128;
    }
    for (j, out) in w.outputs.iter().enumerate() {
        delta[out_in_row(j)] -= out.value as i128;
    }
    delta[fee_in_row()] -= w.fee as i128;
    delta[mint_in_row()] += w.mint as i128;
    let mut acc: i128 = 0;
    for r in 0..HEIGHT {
        t[r * WIDTH + VALACC] = if acc >= 0 {
            Val::from_u64(acc as u64)
        } else {
            -Val::from_u64((-acc) as u64)
        };
        acc += delta[r];
    }
    RowMajorMatrix::new(t, WIDTH)
}

/// The circuit's public inputs: `anchor ‖ nf_i ‖ out_cm_j ‖ fee ‖ tx_binding`.
pub fn public_values(w: &Witness) -> Vec<Val> {
    let o = native_outputs(w);
    let mut pis = vec![Val::ZERO; N_PUBLIC];
    pis[PI_ANCHOR..PI_ANCHOR + DIGEST].copy_from_slice(&o.anchor);
    for i in 0..N_IN {
        pis[PI_NF + i * DIGEST..PI_NF + (i + 1) * DIGEST].copy_from_slice(&o.nullifiers[i]);
    }
    for j in 0..M_OUT {
        pis[PI_OUTCM + j * DIGEST..PI_OUTCM + (j + 1) * DIGEST].copy_from_slice(&o.out_cms[j]);
    }
    pis[PI_FEE] = Val::from_u64(w.fee);
    pis[PI_MINT] = Val::from_u64(w.mint);
    pis[PI_TXBIND..PI_TXBIND + DIGEST].copy_from_slice(&w.tx_binding);
    pis[PI_HEIGHT] = Val::from_u64(w.current_height);
    // redeem_hashlock = SHA256(preimage) = the redeemed HTLC note's committed hashlock (node computes
    // it from the publicly-revealed preimage). Bound in-circuit only for an HTLC redeem input.
    for inp in w.inputs.iter() {
        if inp.note_type == Val::from_u64(NOTE_HTLC) && inp.mode == Val::from_u64(1) {
            pis[PI_HASHLOCK..PI_HASHLOCK + DIGEST].copy_from_slice(&inp.hashlock);
            break;
        }
    }
    pis
}

pub fn prove_verify_with(w: &Witness, pis: &[Val]) -> Result<(), String> {
    let config = make_config();
    let air = HtlcAir;
    let trace = build_trace(w);
    let proof = prove(&config, &air, trace, pis);
    verify(&config, &air, &proof, pis).map_err(|e| format!("{e:?}"))
}

pub fn prove_verify(w: &Witness) -> Result<(), String> {
    prove_verify_with(w, &public_values(w))
}

/// Number of public-input field elements: `anchor ‖ N·nf ‖ M·out_cm ‖ fee ‖ tx_binding`.
pub const NUM_PUBLIC_INPUTS: usize = N_PUBLIC;

/// Prove a join-split and return canonical (postcard) proof bytes.
pub fn prove_to_bytes(w: &Witness) -> Vec<u8> {
    let config = make_config();
    let trace = build_trace(w);
    let proof = prove(&config, &HtlcAir, trace, &public_values(w));
    postcard::to_allocvec(&proof).expect("proof serialization is infallible")
}

/// Verify canonical proof bytes against public inputs. **Fail-closed** on any error.
pub fn verify_bytes(proof_bytes: &[u8], pis: &[Val]) -> bool {
    if pis.len() != N_PUBLIC {
        return false;
    }
    let proof: Proof<MyConfig> = match postcard::from_bytes(proof_bytes) {
        Ok(p) => p,
        Err(_) => return false,
    };
    verify(&make_config(), &HtlcAir, &proof, pis).is_ok()
}

/// A representative valid join-split witness (2 inputs at tree positions 0,1; balanced).
pub fn demo_witness() -> Witness {
    let in_values = [1000u64, 500];
    let nks: [[u64; 2]; N_IN] = core::array::from_fn(|i| [7 + i as u64, 700 + i as u64]);
    let in_rho = |i: usize| [Val::from_u64(11 + i as u64), Val::from_u64(211 + i as u64)];
    let in_rcm = |i: usize| [Val::from_u64(100 + i as u64), Val::from_u64(300 + i as u64)];
    let in_div = |i: usize| Val::from_u64(500 + i as u64); // per-input diversifier
    let asset = Val::from_u64(42); // single (hidden) asset for the whole tx
    let cms: Vec<[Val; DIGEST]> = (0..N_IN)
        .map(|i| {
            commit(
                recipient_of(Val::from_u64(nks[i][0]), Val::from_u64(nks[i][1]), in_div(i)),
                Val::from_u64(in_values[i]),
                in_rho(i),
                in_rcm(i),
                asset,
                Val::ZERO, // PLAIN
            )
        })
        .collect();
    let (_, paths) = build_paths(&cms);
    let inputs = core::array::from_fn(|i| Input {
        nk: nks[i],
        div: in_div(i),
        asset,
        note_type: Val::ZERO,
        value: in_values[i],
        rho: in_rho(i),
        rcm: in_rcm(i),
        sib: paths[i].0,
        bits: paths[i].1,
        mode: Val::ZERO,
        redeem_tag: [Val::ZERO; DIGEST],
        refund_tag: [Val::ZERO; DIGEST],
        hashlock: [Val::ZERO; DIGEST],
        timeout: 0,
    });
    let outputs = core::array::from_fn(|j| Output {
        recipient: recipient_of(Val::from_u64(77 + j as u64), Val::from_u64(j as u64), Val::from_u64(600 + j as u64)),
        asset,
        note_type: Val::ZERO,
        value: [900u64, 500][j],
        rho: [Val::from_u64(21 + j as u64), Val::from_u64(221 + j as u64)],
        rcm: [Val::from_u64(22 + j as u64), Val::from_u64(222 + j as u64)],
    });
    Witness { inputs, outputs, fee: 100, mint: 0, tx_binding: core::array::from_fn(|i| Val::from_u64(0xABCD + i as u64)), current_height: 0 }
}

/// A demo HTLC **redeem** witness (input 0 = an HTLC note redeemed before timeout by the redeem party;
/// input 1 = a zero-value PLAIN dummy) for the C-ABI / integration prove path.
pub fn demo_htlc_witness() -> Witness {
    let asset = Val::from_u64(42);
    let (nk_r, div_r) = ([7u64, 70u64], Val::from_u64(1));
    let (nk_f, div_f) = ([9u64, 90u64], Val::from_u64(2));
    let redeem_tag = recipient_of(Val::from_u64(nk_r[0]), Val::from_u64(nk_r[1]), div_r);
    let refund_tag = recipient_of(Val::from_u64(nk_f[0]), Val::from_u64(nk_f[1]), div_f);
    let hashlock = [Val::from_u64(0x51), Val::from_u64(0x52), Val::from_u64(0x53), Val::from_u64(0x54)];
    let (timeout, height) = (10u64, 5u64);
    let owner = htlc_root(redeem_tag, refund_tag, hashlock, Val::from_u64(timeout));
    let (v, rho, rcm) = (1000u64, [Val::from_u64(11), Val::from_u64(211)], [Val::from_u64(100), Val::from_u64(300)]);
    let cm0 = commit(owner, Val::from_u64(v), rho, rcm, asset, Val::from_u64(NOTE_HTLC));
    let (drho, drcm) = ([Val::from_u64(13), Val::from_u64(213)], [Val::from_u64(101), Val::from_u64(301)]);
    let d_rcp = recipient_of(Val::from_u64(nk_r[0]), Val::from_u64(nk_r[1]), div_r);
    let cm1 = commit(d_rcp, Val::ZERO, drho, drcm, asset, Val::ZERO);
    let (_, paths) = build_paths(&[cm0, cm1]);
    let in0 = Input {
        nk: nk_r, div: div_r, asset, note_type: Val::from_u64(NOTE_HTLC), value: v, rho, rcm,
        sib: paths[0].0, bits: paths[0].1, mode: Val::from_u64(1), redeem_tag, refund_tag, hashlock, timeout,
    };
    let in1 = Input {
        nk: nk_r, div: div_r, asset, note_type: Val::ZERO, value: 0, rho: drho, rcm: drcm,
        sib: paths[1].0, bits: paths[1].1, mode: Val::ZERO,
        redeem_tag: [Val::ZERO; DIGEST], refund_tag: [Val::ZERO; DIGEST], hashlock: [Val::ZERO; DIGEST], timeout: 0,
    };
    let outputs = [
        Output { recipient: recipient_of(Val::from_u64(77), Val::from_u64(7), Val::from_u64(601)), asset, note_type: Val::ZERO, value: v, rho: [Val::from_u64(21), Val::from_u64(221)], rcm: [Val::from_u64(22), Val::from_u64(222)] },
        Output { recipient: recipient_of(Val::from_u64(88), Val::from_u64(8), Val::from_u64(602)), asset, note_type: Val::ZERO, value: 0, rho: [Val::from_u64(23), Val::from_u64(223)], rcm: [Val::from_u64(24), Val::from_u64(224)] },
    ];
    Witness { inputs: [in0, in1], outputs, fee: 0, mint: 0, tx_binding: core::array::from_fn(|i| Val::from_u64(0xABCD + i as u64)), current_height: height }
}

/// (proof bytes, prove ms, verify ms, proven security bits) for a representative join-split.
pub fn measure(w: &Witness) -> (usize, u128, u128, usize) {
    let config = make_config();
    let trace = build_trace(w);
    let pis = public_values(w);
    let t0 = std::time::Instant::now();
    let proof = prove(&config, &HtlcAir, trace, &pis);
    let prove_ms = t0.elapsed().as_millis();
    let bytes = postcard::to_allocvec(&proof).unwrap();
    let t1 = std::time::Instant::now();
    assert!(verify(&config, &HtlcAir, &proof, &pis).is_ok());
    let verify_ms = t1.elapsed().as_millis();
    // proven security at this trace height
    let perm = default_goldilocks_poseidon2_8();
    let vm = ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm), 6, ChaCha20Rng::seed_from_u64(1));
    let fri = FriParameters {
        log_blowup: 4,
        log_final_poly_len: 0,
        max_log_arity: 4,
        num_queries: 96,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 16,
        mmcs: ChallengeMmcs::new(vm),
    };
    let layout = AirLayout::from_air::<Goldilocks>(&HtlcAir);
    let params = StarkSecurityParams::from_air::<Val, Challenge, HtlcAir, ChallengeMmcs>(&fri, &HtlcAir, layout, 127, 128, 2);
    let proven = ProvenSecurity::compute(&params, 1usize << (HEIGHT.trailing_zeros() as usize + 1)).security_bits();
    (bytes.len(), prove_ms, verify_ms, proven)
}

/// Prove with the witness's real public inputs, verify against `verify_pis` (tests FS binding).
#[allow(dead_code)]
pub fn prove_real_verify_with(w: &Witness, verify_pis: &[Val]) -> Result<(), String> {
    let config = make_config();
    let air = HtlcAir;
    let trace = build_trace(w);
    let proof = prove(&config, &air, trace, &public_values(w));
    verify(&config, &air, &proof, verify_pis).map_err(|e| format!("{e:?}"))
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
        let in0 = (1000u64, [7u64, 70u64], 11u64, 100u64, 501u64); // value, nk(2), rho, rcm, div
        let in1 = (500u64, [9u64, 90u64], 13u64, 101u64, 502u64);
        let rho2 = |x: u64| [Val::from_u64(x), Val::from_u64(x + 200)];
        let rcm2 = |x: u64| [Val::from_u64(x), Val::from_u64(x + 300)];
        let asset = Val::from_u64(42); // single hidden asset for the tx
        let cmf = |v: &(u64, [u64; 2], u64, u64, u64)| {
            commit(recipient_of(Val::from_u64(v.1[0]), Val::from_u64(v.1[1]), Val::from_u64(v.4)), Val::from_u64(v.0), rho2(v.2), rcm2(v.3), asset, Val::ZERO)
        };
        let (_, paths) = build_paths(&[cmf(&in0), cmf(&in1)]);
        let mk_in = |v: (u64, [u64; 2], u64, u64, u64), pth: &([[Val; DIGEST]; DEPTH], [bool; DEPTH])| Input {
            nk: v.1,
            div: Val::from_u64(v.4),
            asset,
            note_type: Val::ZERO,
            value: v.0,
            rho: rho2(v.2),
            rcm: rcm2(v.3),
            sib: pth.0,
            bits: pth.1,
            mode: Val::ZERO,
            redeem_tag: [Val::ZERO; DIGEST],
            refund_tag: [Val::ZERO; DIGEST],
            hashlock: [Val::ZERO; DIGEST],
            timeout: 0,
        };
        let inputs = [mk_in(in0, &paths[0]), mk_in(in1, &paths[1])];
        let outputs = [
            Output { recipient: recipient_of(Val::from_u64(77), Val::from_u64(7), Val::from_u64(601)), asset, note_type: Val::ZERO, value: 900, rho: rho2(21), rcm: rcm2(22) },
            Output { recipient: recipient_of(Val::from_u64(88), Val::from_u64(8), Val::from_u64(602)), asset, note_type: Val::ZERO, value: 500, rho: rho2(23), rcm: rcm2(24) },
        ];
        // Σin = 1500, Σout = 1400, fee = 100
        Witness { inputs, outputs, fee: 100, mint: 0, tx_binding: core::array::from_fn(|i| Val::from_u64(0xABCD + i as u64)), current_height: 0 }
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

    /// Build a balanced witness with the given input/output values + fee (computes Merkle paths).
    fn witness_with(in_values: [u64; N_IN], out_values: [u64; M_OUT], fee: u64) -> Witness {
        let nk = |i: usize| [7 + i as u64, 700 + i as u64];
        let in_rho = |i: usize| [Val::from_u64(11 + i as u64), Val::from_u64(211 + i as u64)];
        let in_rcm = |i: usize| [Val::from_u64(100 + i as u64), Val::from_u64(300 + i as u64)];
        let in_div = |i: usize| Val::from_u64(500 + i as u64);
        let asset = Val::from_u64(42); // single hidden asset for the tx
        let cms: Vec<[Val; DIGEST]> = (0..N_IN)
            .map(|i| {
                commit(
                    recipient_of(Val::from_u64(nk(i)[0]), Val::from_u64(nk(i)[1]), in_div(i)),
                    Val::from_u64(in_values[i]),
                    in_rho(i),
                    in_rcm(i),
                    asset,
                    Val::ZERO,
                )
            })
            .collect();
        let (_, paths) = build_paths(&cms);
        let inputs = core::array::from_fn(|i| Input {
            nk: nk(i),
            div: in_div(i),
            asset,
            note_type: Val::ZERO,
            value: in_values[i],
            rho: in_rho(i),
            rcm: in_rcm(i),
            sib: paths[i].0,
            bits: paths[i].1,
            mode: Val::ZERO,
            redeem_tag: [Val::ZERO; DIGEST],
            refund_tag: [Val::ZERO; DIGEST],
            hashlock: [Val::ZERO; DIGEST],
            timeout: 0,
        });
        let outputs = core::array::from_fn(|j| Output {
            recipient: recipient_of(Val::from_u64(77 + j as u64), Val::from_u64(j as u64), Val::from_u64(600 + j as u64)),
            asset,
            note_type: Val::ZERO,
            value: out_values[j],
            rho: [Val::from_u64(21 + j as u64), Val::from_u64(221 + j as u64)],
            rcm: [Val::from_u64(22 + j as u64), Val::from_u64(222 + j as u64)],
        });
        Witness { inputs, outputs, fee, mint: 0, tx_binding: core::array::from_fn(|i| Val::from_u64(0xABCD + i as u64)), current_height: 0 }
    }

    #[test]
    fn joinsplit_verifies() {
        prove_verify(&witness_with([1000, 500], [900, 500], 100)).expect("valid join-split should verify");
    }

    #[test]
    fn zk_blinding_is_fresh_per_proof() {
        // Two proofs of the *same* witness must differ — the hiding-PCS blinding is fresh CSPRNG
        // randomness per proof (would fail with the old fixed-seed RNG).
        let w = witness_with([1000, 500], [900, 500], 100);
        let a = prove_to_bytes(&w);
        let b = prove_to_bytes(&w);
        assert_ne!(a, b, "ZK proofs of the same statement must be re-randomized");
        // both still verify
        assert!(verify_bytes(&a, &public_values(&w)));
        assert!(verify_bytes(&b, &public_values(&w)));
    }

    #[test]
    fn htlc_mint_issuance_is_rejected() {
        // v3 hardening (defense-in-depth with the node's applyHtlc mint!=0 reject): an HTLC spend never
        // issues, so the circuit forces mint==0. A balanced mint>0 witness (which the join-split AIR
        // would accept as a coinbase) must NOT verify here.
        let mut w = witness_with([0, 0], [1000, 0], 0);
        w.mint = 1000; // Σin(0) + mint(1000) = Σout(1000) + fee(0) — balanced, but issuance is forbidden
        let proof = prove_to_bytes(&w);
        assert!(!verify_bytes(&proof, &public_values(&w)), "HTLC mint>0 must be rejected (no issuance)");
    }

    #[test]
    fn wrong_mint_rejected() {
        let mut w = witness_with([0, 0], [1000, 0], 0);
        w.mint = 1000;
        let mut pis = public_values(&w);
        pis[PI_MINT] += Val::ONE; // claim a different issuance ⇒ mint binding fails
        assert!(prove_verify_with(&w, &pis).is_err());
    }

    #[test]
    fn dummy_notes_pad_smaller_transactions() {
        // A 1-real-in / 1-real-out transaction, padded to the fixed 2-in/2-out shape with
        // zero-value dummy notes (Σin = 1000 = 900 + 100 = Σout + fee). This is how variable
        // (N, M) is supported without a variable-shape circuit.
        prove_verify(&witness_with([1000, 0], [900, 0], 100)).expect("dummy-padded tx should verify");
    }

    #[test]
    fn wrong_anchor_rejected() {
        let w = witness_with([1000, 500], [900, 500], 100);
        let mut pis = public_values(&w);
        pis[PI_ANCHOR] += Val::ONE;
        assert!(prove_verify_with(&w, &pis).is_err());
    }

    #[test]
    fn wrong_nullifier_rejected() {
        let w = witness_with([1000, 500], [900, 500], 100);
        let mut pis = public_values(&w);
        pis[PI_NF + DIGEST] += Val::ONE; // tamper input 1's nullifier
        assert!(prove_verify_with(&w, &pis).is_err());
    }

    #[test]
    fn wrong_out_cm_rejected() {
        let w = witness_with([1000, 500], [900, 500], 100);
        let mut pis = public_values(&w);
        pis[PI_OUTCM] += Val::ONE;
        assert!(prove_verify_with(&w, &pis).is_err());
    }

    #[test]
    fn wrong_fee_rejected() {
        let w = witness_with([1000, 500], [900, 500], 100);
        let mut pis = public_values(&w);
        pis[PI_FEE] += Val::ONE; // fee region binds VAL == public fee
        assert!(prove_verify_with(&w, &pis).is_err());
    }

    #[test]
    fn out_of_range_value_rejected() {
        // input 0 value ≥ 2^BITS; fee chosen so the balance still holds ⇒ only range fails.
        let big = 1u64 << 53;
        let w = witness_with([big, 500], [900, 500], big + 500 - 1400);
        assert!(prove_verify(&w).is_err());
    }

    #[test]
    fn wrong_tx_binding_rejected() {
        let w = witness_with([1000, 500], [900, 500], 100);
        let mut pis = public_values(&w);
        pis[PI_TXBIND] += Val::ONE; // Fiat–Shamir binds the proof to the tx
        assert!(prove_real_verify_with(&w, &pis).is_err());
    }

    #[test]
    fn distinct_positions_give_distinct_nullifiers() {
        // same note key/rho at different positions ⇒ different nullifiers (A1 prevents replay)
        let (nk0, nk1) = (Val::from_u64(5), Val::from_u64(50));
        let rho = [Val::from_u64(6), Val::from_u64(66)];
        let b0 = [false; DEPTH];
        let mut b1 = [false; DEPTH];
        b1[0] = true;
        assert_ne!(nullifier(nk0, nk1, rho, pos_of(&b0)), nullifier(nk0, nk1, rho, pos_of(&b1)));
    }

    /// Robust "this corrupted trace must not yield a verifying proof" (debug: prove's constraint
    /// check panics; release: verify rejects).
    fn corrupt_trace_rejected(trace: RowMajorMatrix<Val>, pis: Vec<Val>) -> bool {
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let proof = prove(&make_config(), &HtlcAir, trace, &pis);
            verify_bytes(&postcard::to_allocvec(&proof).unwrap(), &pis)
        }));
        matches!(outcome, Ok(false) | Err(_))
    }

    /// For each persistent key/randomness limb fed to BOTH the commitment/ownership AND the nullifier,
    /// forge a trace that uses a different value in the nullifier (publishing the matching forged nf),
    /// so ONLY that limb's persistence constraint is violated. Each must be unprovable — this is the
    /// corrupted-trace coverage whose absence hid the original rho1 double-spend gap. Covers
    /// nk0(NK), nk1(NK1), rho0(RHO), rho1(RHO1).
    #[test]
    fn forged_nullifier_limbs_are_rejected() {
        let cols = [NK, NK1, RHO, RHO1];
        for limb in 0..4usize {
            let w = sample();
            let mut trace = build_trace(&w);
            let (nk0, nk1) = (Val::from_u64(w.inputs[0].nk[0]), Val::from_u64(w.inputs[0].nk[1]));
            let mut vals = [nk0, nk1, w.inputs[0].rho[0], w.inputs[0].rho[1]];
            let pos = pos_of(&w.inputs[0].bits);
            vals[limb] += Val::ONE; // bump the limb the nullifier consumes
            // rewrite input 0's nullifier block to bind the bumped limb (commitment/ownership keep the
            // real value, so cm/anchor still verify); make the local nullifier binding hold.
            let nin = [Val::from_u64(DOM_NF), vals[0], vals[1], vals[2], vals[3], pos, Val::ZERO, Val::ZERO];
            set_block(&mut trace.values, null_block(0), nin);
            for r in null_in_row(0)..=null_out_row(0) {
                trace.values[r * WIDTH + cols[limb]] = vals[limb];
            }
            let mut pis = public_values(&w);
            let nfp = nullifier(vals[0], vals[1], [vals[2], vals[3]], pos);
            pis[PI_NF..PI_NF + DIGEST].copy_from_slice(&nfp);
            assert!(corrupt_trace_rejected(trace, pis), "forged nullifier limb {limb} must not verify");
        }
    }

    /// The commitment chain link (`commit_b.in[0..4] = commit_a.out[0..4]`) must be non-vacuous: a
    /// trace that feeds an arbitrary chain value into commit_b would forge the commitment.
    #[test]
    fn forged_commitment_chain_is_rejected() {
        let w = sample();
        let mut trace = build_trace(&w);
        // Corrupt input 0's commit_b input lane 0 (the chaining value) — no longer = commit_a output.
        let row = commit_b_in_row(0);
        trace.values[row * WIDTH + 0] += Val::ONE;
        // public inputs unchanged: the forged chain breaks the chain-link (and downstream cm), which
        // must make the proof unverifiable regardless of the published statement.
        let pis = public_values(&w);
        assert!(corrupt_trace_rejected(trace, pis), "a forged commitment chaining value must not verify");
    }

    /// The hidden-asset binding must be non-vacuous: a prover must not turn the inputs' asset into a
    /// different output asset. Forge output 0's committed asset (≠ the global ASSET) and publish the
    /// matching out_cm, so ONLY the `lane6 == ASSET` binding is violated.
    #[test]
    fn output_with_mismatched_asset_is_rejected() {
        let w = sample(); // asset = 42 on every note
        let mut trace = build_trace(&w);
        let out0 = w.outputs[0];
        let alt = out0.asset + Val::ONE; // a different asset for the output
        // recompute output 0's commit_b (out_a output = chain; lane6 = forged asset).
        let mut oa = [Val::ZERO; 8];
        oa[0] = Val::from_u64(DOM_CM);
        oa[1..1 + DIGEST].copy_from_slice(&out0.recipient);
        oa[1 + DIGEST] = Val::from_u64(out0.value);
        oa[1 + DIGEST + 1] = out0.rho[0];
        oa[1 + DIGEST + 2] = out0.rho[1];
        let chain = native_permute(oa);
        let mut ob = [Val::ZERO; 8];
        ob[..DIGEST].copy_from_slice(&chain[..DIGEST]);
        ob[DIGEST] = out0.rcm[0];
        ob[DIGEST + 1] = out0.rcm[1];
        ob[DIGEST + 2] = alt;
        ob[DIGEST + 3] = out0.note_type;
        set_block(&mut trace.values, out_base(0) + 1, ob);
        let new_cm: [Val; DIGEST] = native_permute(ob)[..DIGEST].try_into().unwrap();
        let mut pis = public_values(&w);
        pis[PI_OUTCM..PI_OUTCM + DIGEST].copy_from_slice(&new_cm);
        assert!(corrupt_trace_rejected(trace, pis), "a mismatched output asset must not verify");
    }

    // ---- HTLC native-oracle tests (the spec the htlc_air AIR will be differential-tested against) ----

    /// Build a 2-in/2-out witness whose input 0 is an HTLC note (owner = htlc_root) claimed in
    /// `redeem`/refund mode at `height`, and input 1 a zero-value PLAIN dummy owned by the claimer.
    pub(crate) fn htlc_witness(redeem: bool, height: u64, hashlock: [Val; DIGEST], timeout: u64) -> Witness {
        let asset = Val::from_u64(42);
        let (nk_r, div_r) = ([7u64, 70u64], Val::from_u64(1));
        let (nk_f, div_f) = ([9u64, 90u64], Val::from_u64(2));
        let redeem_tag = recipient_of(Val::from_u64(nk_r[0]), Val::from_u64(nk_r[1]), div_r);
        let refund_tag = recipient_of(Val::from_u64(nk_f[0]), Val::from_u64(nk_f[1]), div_f);
        let owner = htlc_root(redeem_tag, refund_tag, hashlock, Val::from_u64(timeout));
        let (v, rho, rcm) = (1000u64, [Val::from_u64(11), Val::from_u64(211)], [Val::from_u64(100), Val::from_u64(300)]);
        let cm0 = commit(owner, Val::from_u64(v), rho, rcm, asset, Val::from_u64(NOTE_HTLC));
        // claimer = redeem party (redeem) or refund party (refund); also owns the dummy input.
        let (cnk, cdiv) = if redeem { (nk_r, div_r) } else { (nk_f, div_f) };
        let (drho, drcm) = ([Val::from_u64(13), Val::from_u64(213)], [Val::from_u64(101), Val::from_u64(301)]);
        let d_rcp = recipient_of(Val::from_u64(cnk[0]), Val::from_u64(cnk[1]), cdiv);
        let cm1 = commit(d_rcp, Val::ZERO, drho, drcm, asset, Val::ZERO);
        let (_, paths) = build_paths(&[cm0, cm1]);
        let in0 = Input {
            nk: cnk, div: cdiv, asset, note_type: Val::from_u64(NOTE_HTLC), value: v, rho, rcm,
            sib: paths[0].0, bits: paths[0].1, mode: Val::from_u64(redeem as u64),
            redeem_tag, refund_tag, hashlock, timeout,
        };
        let in1 = Input {
            nk: cnk, div: cdiv, asset, note_type: Val::ZERO, value: 0, rho: drho, rcm: drcm,
            sib: paths[1].0, bits: paths[1].1, mode: Val::ZERO,
            redeem_tag: [Val::ZERO; DIGEST], refund_tag: [Val::ZERO; DIGEST], hashlock: [Val::ZERO; DIGEST], timeout: 0,
        };
        let outs = [
            Output { recipient: recipient_of(Val::from_u64(77), Val::from_u64(7), Val::from_u64(601)), asset, note_type: Val::ZERO, value: v, rho: [Val::from_u64(21), Val::from_u64(221)], rcm: [Val::from_u64(22), Val::from_u64(222)] },
            Output { recipient: recipient_of(Val::from_u64(88), Val::from_u64(8), Val::from_u64(602)), asset, note_type: Val::ZERO, value: 0, rho: [Val::from_u64(23), Val::from_u64(223)], rcm: [Val::from_u64(24), Val::from_u64(224)] },
        ];
        Witness { inputs: [in0, in1], outputs: outs, fee: 0, mint: 0, tx_binding: core::array::from_fn(|i| Val::from_u64(0xABCD + i as u64)), current_height: height }
    }

    #[test]
    fn htlc_redeem_and_refund_native_ok() {
        let hl = [Val::from_u64(0x51), Val::from_u64(0x52), Val::from_u64(0x53), Val::from_u64(0x54)];
        // redeem before timeout, refund at/after timeout — both must satisfy the oracle.
        let r = native_outputs(&htlc_witness(true, 5, hl, 10));
        let f = native_outputs(&htlc_witness(false, 10, hl, 10));
        // input 0's nullifier is owner-based (htlc_root), not nk-based.
        let owner = htlc_root(
            recipient_of(Val::from_u64(7), Val::from_u64(70), Val::from_u64(1)),
            recipient_of(Val::from_u64(9), Val::from_u64(90), Val::from_u64(2)),
            hl, Val::from_u64(10),
        );
        let pos = pos_of(&htlc_witness(true, 5, hl, 10).inputs[0].bits);
        assert_eq!(r.nullifiers[0], nullifier_owner(owner, [Val::from_u64(11), Val::from_u64(211)], pos));
        let _ = f;
    }

    /// THE critical soundness property: the same HTLC note redeemed vs refunded yields the SAME
    /// nullifier (mode/party-independent), so it can be spent at most once across both modes.
    #[test]
    fn htlc_nullifier_is_mode_independent() {
        let hl = [Val::from_u64(1), Val::from_u64(2), Val::from_u64(3), Val::from_u64(4)];
        let redeem = native_outputs(&htlc_witness(true, 5, hl, 10));
        let refund = native_outputs(&htlc_witness(false, 10, hl, 10));
        assert_eq!(redeem.nullifiers[0], refund.nullifiers[0], "HTLC nullifier must not depend on mode/party");
    }

    /// In-circuit: an HTLC note (owner = htlc_root, owner-based nullifier) proves and verifies through
    /// the AIR, matching the native oracle. Exercises the span-end htlc_root chain + the owner MUX +
    /// the note_type-gated nullifier.
    #[test]
    fn htlc_redeem_air_verifies() {
        let hl = [Val::from_u64(0x51), Val::from_u64(0x52), Val::from_u64(0x53), Val::from_u64(0x54)];
        prove_verify(&htlc_witness(true, 5, hl, 10)).expect("HTLC redeem must verify in-circuit");
    }

    #[test]
    fn htlc_refund_air_verifies() {
        let hl = [Val::from_u64(7), Val::from_u64(8), Val::from_u64(9), Val::from_u64(10)];
        prove_verify(&htlc_witness(false, 10, hl, 10)).expect("HTLC refund must verify in-circuit");
    }

    /// Access control (soundness): the refund party cannot spend the REDEEM branch. Take a valid refund
    /// witness and flip MODE→redeem in the trace; the claimant is the refund party, so the redeem
    /// tag-match (claim == redeem_tag) fails. Public inputs are unchanged (the HTLC nullifier is
    /// owner-based, not mode/nk-based), so only the tag-match can reject — and it must.
    #[test]
    fn htlc_wrong_party_for_mode_is_rejected() {
        let hl = [Val::from_u64(1), Val::from_u64(2), Val::from_u64(3), Val::from_u64(4)];
        let w = htlc_witness(false, 10, hl, 10); // refund: claimer = refund party, MODE=0
        let mut trace = build_trace(&w);
        let (lo, hi) = (own_in_row(0), span_last_row(0));
        for r in lo..=hi {
            trace.values[r * WIDTH + MODE] = Val::ONE; // claim the redeem branch with the refund party
        }
        let pis = public_values(&w);
        assert!(corrupt_trace_rejected(trace, pis), "refund party must not pass the redeem tag-match");
    }

    /// Atomicity: a redeem must reveal the preimage of the committed hashlock. Prove a valid redeem,
    /// then verify against a wrong public redeem_hashlock — the hashlock binding must reject.
    #[test]
    fn htlc_redeem_wrong_hashlock_is_rejected() {
        let hl = [Val::from_u64(0x51), Val::from_u64(0x52), Val::from_u64(0x53), Val::from_u64(0x54)];
        let w = htlc_witness(true, 5, hl, 10);
        let trace = build_trace(&w);
        let mut pis = public_values(&w);
        pis[PI_HASHLOCK] += Val::ONE; // a hashlock the revealed preimage does NOT hash to
        assert!(corrupt_trace_rejected(trace, pis), "redeem with a wrong hashlock must not verify");
    }

    /// Time-lock: redeem requires height < timeout. Prove a valid redeem (height 5 < timeout 10), then
    /// verify against current_height = timeout — the DIFF compute (timeout-height-1 would be negative)
    /// no longer matches the range-bounded DIFF, so it must reject.
    #[test]
    fn htlc_redeem_at_timeout_is_rejected_in_circuit() {
        let hl = [Val::from_u64(1), Val::from_u64(2), Val::from_u64(3), Val::from_u64(4)];
        let w = htlc_witness(true, 5, hl, 10);
        let trace = build_trace(&w);
        let mut pis = public_values(&w);
        pis[PI_HEIGHT] = Val::from_u64(10); // height == timeout ⇒ redeem window closed
        assert!(corrupt_trace_rejected(trace, pis), "redeem at/after timeout must not verify");
    }

    /// Time-lock: refund requires height >= timeout. Prove a valid refund (height 10 == timeout), then
    /// verify against current_height < timeout — must reject.
    #[test]
    fn htlc_refund_before_timeout_is_rejected_in_circuit() {
        let hl = [Val::from_u64(1), Val::from_u64(2), Val::from_u64(3), Val::from_u64(4)];
        let w = htlc_witness(false, 10, hl, 10);
        let trace = build_trace(&w);
        let mut pis = public_values(&w);
        pis[PI_HEIGHT] = Val::from_u64(9); // height < timeout ⇒ refund window not open
        assert!(corrupt_trace_rejected(trace, pis), "refund before timeout must not verify");
    }

    /// Boundary: redeem at height = timeout-1 is the latest valid redeem (DIFF = 0).
    #[test]
    fn htlc_redeem_boundary_verifies() {
        let hl = [Val::from_u64(5), Val::from_u64(6), Val::from_u64(7), Val::from_u64(8)];
        prove_verify(&htlc_witness(true, 9, hl, 10)).expect("redeem at timeout-1 must verify");
    }

    /// v3 hardening: an out-of-range current_height (≥ 2^BITS) is rejected by the in-circuit height
    /// range-check. A refund satisfies its timeout window for an arbitrarily large height (height ≥
    /// timeout), so WITHOUT the height range-check a near-2^BITS height could wrap the field subtraction
    /// in the DIFF compute; the range-check closes that.
    #[test]
    fn htlc_out_of_range_height_is_rejected() {
        let hl = [Val::from_u64(1), Val::from_u64(2), Val::from_u64(3), Val::from_u64(4)];
        // refund (height ≥ timeout) with height = 2^BITS — native window OK, but height ∉ [0, 2^BITS).
        let w = htlc_witness(false, 1u64 << BITS, hl, 10);
        let proof = prove_to_bytes(&w);
        assert!(!verify_bytes(&proof, &public_values(&w)), "current_height ≥ 2^BITS must be rejected");
    }

    #[test]
    fn htlc_root_binds_its_terms() {
        let a = recipient_of(Val::from_u64(7), Val::from_u64(70), Val::from_u64(1));
        let b = recipient_of(Val::from_u64(9), Val::from_u64(90), Val::from_u64(2));
        let hl1 = [Val::from_u64(1), Val::from_u64(2), Val::from_u64(3), Val::from_u64(4)];
        let hl2 = [Val::from_u64(1), Val::from_u64(2), Val::from_u64(3), Val::from_u64(5)];
        assert_ne!(htlc_root(a, b, hl1, Val::from_u64(10)), htlc_root(a, b, hl2, Val::from_u64(10)), "hashlock must bind");
        assert_ne!(htlc_root(a, b, hl1, Val::from_u64(10)), htlc_root(a, b, hl1, Val::from_u64(11)), "timeout must bind");
        assert_ne!(htlc_root(a, b, hl1, Val::from_u64(10)), htlc_root(b, a, hl1, Val::from_u64(10)), "party order must bind");
    }

    #[test]
    #[should_panic(expected = "claim does not match")]
    fn htlc_wrong_party_rejected() {
        // redeem mode but claim with the refund party's key ⇒ claim_tag != redeem_tag ⇒ oracle rejects.
        let hl = [Val::from_u64(1), Val::from_u64(2), Val::from_u64(3), Val::from_u64(4)];
        let mut w = htlc_witness(true, 5, hl, 10);
        w.inputs[0].nk = [9, 90]; // the refund party's nk, claiming the redeem branch
        w.inputs[0].div = Val::from_u64(2);
        let _ = native_outputs(&w);
    }

    #[test]
    #[should_panic(expected = "redeem requires height < timeout")]
    fn htlc_redeem_after_timeout_rejected() {
        let hl = [Val::from_u64(1), Val::from_u64(2), Val::from_u64(3), Val::from_u64(4)];
        let _ = native_outputs(&htlc_witness(true, 10, hl, 10)); // height == timeout, redeem ⇒ reject
    }

    #[test]
    #[should_panic(expected = "refund requires height >= timeout")]
    fn htlc_refund_before_timeout_rejected() {
        let hl = [Val::from_u64(1), Val::from_u64(2), Val::from_u64(3), Val::from_u64(4)];
        let _ = native_outputs(&htlc_witness(false, 9, hl, 10)); // height < timeout, refund ⇒ reject
    }
}
