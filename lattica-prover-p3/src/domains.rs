//! DOMAIN-SEPARATION TAGS + note-type discriminants — the normative, consensus-frozen table.
//!
//! Every protocol hash is domain-separated: `H(dom ‖ payload…)` with `dom` one of the tags below
//! (soundness fix A2 — cross-domain preimage reuse is a forgery vector, e.g. a nullifier that is
//! also a valid commitment). These values are CONSENSUS: the Zig node recomputes the same hashes
//! natively (`src/poseidon2.zig`, KAT-pinned by `dump_p2`), so a change here is a hard fork.
//!
//! | tag           | value | hash                                                             |
//! |---------------|-------|------------------------------------------------------------------|
//! | `DOM_OWN`     | 1     | ownership / recipient tag: `H(1, nk0, nk1, divers…)`             |
//! | `DOM_CM`      | 2     | note commitment (2-permutation sponge; asset lane 6, note-type 7)|
//! | `DOM_NF`      | 3     | plain-note nullifier: `H(3, nk, rho, pos)` (pos-bound, A1)       |
//! | `DOM_HTLC`    | 4     | `htlc_root` MD-chain over (redeem_tag, refund_tag, hashlock, timeout) |
//! | `DOM_NF_HTLC` | 5     | HTLC-note nullifier (owner-based, mode-independent)              |
//! | `DOM_TXROOT`  | 6     | per-tx statement digest + the block tx-root Merkle–Damgård fold  |
//!
//! Note-type discriminants (commitment lane 7): `NOTE_PLAIN`=0, `NOTE_HTLC`=1.

/// Ownership / recipient-tag hash domain.
pub const DOM_OWN: u64 = 1;
/// Note-commitment hash domain.
pub const DOM_CM: u64 = 2;
/// Plain-note nullifier hash domain (position-bound, soundness fix A1).
pub const DOM_NF: u64 = 3;
/// HTLC root (MD-chain over redeem_tag, refund_tag, hashlock, timeout).
pub const DOM_HTLC: u64 = 4;
/// HTLC-note nullifier hash domain (owner-based, mode-independent).
pub const DOM_NF_HTLC: u64 = 5;
/// Per-tx statement digest + block tx-root fold domain (the batch/aggregation seam).
pub const DOM_TXROOT: u64 = 6;

/// Note-type discriminant: a plain (join-split) note.
pub const NOTE_PLAIN: u64 = 0;
/// Note-type discriminant: an HTLC note (commitment lane 7 = 1).
pub const NOTE_HTLC: u64 = 1;
