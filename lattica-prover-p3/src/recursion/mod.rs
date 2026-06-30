//! Recursion (Phase B of `docs/recursion-design.md`) — building a recursive STARK verifier as an AIR.
//!
//! This module is kept SEPARATE from the frozen audited circuits (`joinsplit_air`, `htlc_air`,
//! `batch_*_air`); it only *reuses* their `pub`/`pub(crate)` primitives. See
//! `docs/recursion-verifier-audit.md` for the in-circuit verifier spec + constraint budget.
//!
//! `fri_merkle` is the B1 spike: an in-circuit FRI-query Merkle-opening verifier — the dominant,
//! most-repeated operation in a FRI verifier — used to retire the feasibility risk and benchmark the
//! per-query hashing cost on the existing Plonky3 prover.

pub mod fri_fold;
pub mod fri_merkle;
pub mod native_verify;
pub mod transcript;
