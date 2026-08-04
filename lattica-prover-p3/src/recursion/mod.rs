//! Recursion (Phase B of `docs/recursion-design.md`) — the recursive STARK verifier as an AIR.
//!
//! ⚠️ RESEARCH — NOT PRODUCTION, NOT AUDITED. **The in-circuit verifier IS built**: `monolith` is a
//! single AIR (proven with the audited `p3_uni_stark::prove`/`verify`) that accepts iff
//! `p3::verify(inner_proof)` accepts — validated for non-hiding inners across W/nqc/FRI-depth
//! (ConstAir/Counter/Fibonacci/Mul/Periodic/Wide/Cube/Quart, db≤8), for the K-inner tiled aggregator
//! emitting the block tx-root, and for HIDING (is_zk=1) inners end-to-end. The external audit remains
//! the production gate; production verifies real (db=12) statements via the aggregation tree, not one
//! giant monolith.
//!
//! Support layers: `native_fri`/`native_verify` are the NATIVE re-verifiers + witness oracles (the
//! porting blueprint, differential-tested against `p3::verify`); `fri_fold`/`fri_merkle`/`transcript`
//! hold the early standalone primitives (partly superseded by the monolith's fused regions, kept as
//! the differential-test record — the only NON-test live piece is `fri_fold::native_fold` (the
//! monolith trace builders); ModelChallenger / native_fold_chain / `fri_merkle`'s prove-verify
//! wrappers serve the cfg(test) differential harnesses).
//!
//! This module is kept SEPARATE from the frozen audited circuits (`joinsplit_air`, `htlc_air`,
//! `batch_*_air`); it only *reuses* their `pub`/`pub(crate)` primitives. See
//! `docs/recursion-verifier-audit.md` for the in-circuit verifier spec + constraint budget.

pub mod aggregation;
pub mod fri_fold;
pub mod fri_merkle;
pub mod monolith; // the monolithic in-circuit verifier AIR (accept-iff-p3::verify; hiding incl.)
pub mod native_fri; // native FRI verify + witness oracles — the in-circuit-port blueprint
pub mod native_verify; // native re-verifier (hiding config) + the hiding witness/test harness
pub mod transcript;
/// SUPERSEDED by `monolith` (zero non-test consumers): the eight standalone per-component verifier
/// AIRs, kept under cfg(test) as the validation-lineage differential record.
#[cfg(test)]
pub mod verifier_air;
