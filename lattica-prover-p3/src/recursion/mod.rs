//! Recursion (Phase B of `docs/recursion-design.md`) — building a recursive STARK verifier as an AIR.
//!
//! ⚠️ RESEARCH — NOT PRODUCTION, NOT SOUND, NOT AUDITED. This module is feasibility spikes + a porting
//! blueprint: validated in-circuit *primitives* (`fri_merkle`, `transcript`, `fri_fold`, each
//! differential-tested vs the real Plonky3 functions) and a *native* re-verifier (`native_verify`) that
//! re-implements `p3-uni-stark::verify` and agrees with `p3::verify`. **The in-circuit recursive verifier
//! itself is NOT built** (multi-week; see `docs/recursion-design.md` §10). Do not treat as a production
//! or audited artifact.
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
pub mod native_fri; // B3b WIRING (work in progress): native FRI verify, the in-circuit-port blueprint
pub mod native_verify;
pub mod transcript;
pub mod verifier_air;
