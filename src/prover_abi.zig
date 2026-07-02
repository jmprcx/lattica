//! Single source of the `lattica_*` extern "C" declarations — the production C ABI implemented by
//! `lattica-prover-p3` (`liblattica_prover_p3.a`). The normative signatures live in
//! `lattica-prover-p3/include/lattica_prover_p3.h`; these declarations mirror them EXACTLY.
//! Import this module (`@import("prover_abi.zig")`) instead of re-declaring extern blocks, so the
//! node has one Zig-side copy of the seam to keep in lockstep with the header.
//!
//! Conventions (per the header): verify → 0 = accept, nonzero = reject (fail-closed);
//! prove → 0 = ok, 1 = malformed/invalid input or internal failure, 2 = an output buffer was too
//! small (`*_len` outputs written only on rc = 0). No call unwinds across the boundary.

// --- single-transaction join-split ------------------------------------------------------------

pub extern fn lattica_joinsplit_verify(
    proof: [*]const u8,
    proof_len: usize,
    pi: [*]const u8,
    pi_len: usize,
) callconv(.c) i32;
pub extern fn lattica_joinsplit_prove(
    witness_ptr: [*]const u8,
    witness_len: usize,
    proof_out: [*]u8,
    proof_cap: usize,
    proof_len: *usize,
    pi_out: [*]u8,
    pi_cap: usize,
    pi_len: *usize,
) callconv(.c) i32;
/// Demo prover (fixed internal witness) — dev/integration only.
pub extern fn lattica_joinsplit_prove_demo(
    proof_out: [*]u8,
    proof_cap: usize,
    proof_len: *usize,
    pi_out: [*]u8,
    pi_cap: usize,
    pi_len: *usize,
) callconv(.c) i32;

// --- single-transaction HTLC spend (redeem/refund) ---------------------------------------------

pub extern fn lattica_htlc_verify(
    proof: [*]const u8,
    proof_len: usize,
    pi: [*]const u8,
    pi_len: usize,
) callconv(.c) i32;
pub extern fn lattica_htlc_prove(
    witness_ptr: [*]const u8,
    witness_len: usize,
    proof_out: [*]u8,
    proof_cap: usize,
    proof_len: *usize,
    pi_out: [*]u8,
    pi_cap: usize,
    pi_len: *usize,
) callconv(.c) i32;
/// Demo prover (fixed internal witness) — dev/integration only.
pub extern fn lattica_htlc_prove_demo(
    proof_out: [*]u8,
    proof_cap: usize,
    proof_len: *usize,
    pi_out: [*]u8,
    pi_cap: usize,
    pi_len: *usize,
) callconv(.c) i32;

// --- batch: one proof per block (tx-root = 32-byte digest, the only public input) --------------

pub extern fn lattica_batch_verify(
    proof: [*]const u8,
    proof_len: usize,
    root: [*]const u8,
    root_len: usize,
) callconv(.c) i32;
pub extern fn lattica_batch_prove(
    witness_ptr: [*]const u8,
    witness_len: usize,
    n_tx: usize,
    proof_out: [*]u8,
    proof_cap: usize,
    proof_len: *usize,
    root_out: [*]u8,
    root_cap: usize,
    root_len: *usize,
) callconv(.c) i32;
pub extern fn lattica_htlc_batch_verify(
    proof: [*]const u8,
    proof_len: usize,
    root: [*]const u8,
    root_len: usize,
) callconv(.c) i32;
pub extern fn lattica_htlc_batch_prove(
    witness_ptr: [*]const u8,
    witness_len: usize,
    n_tx: usize,
    proof_out: [*]u8,
    proof_cap: usize,
    proof_len: *usize,
    root_out: [*]u8,
    root_cap: usize,
    root_len: *usize,
) callconv(.c) i32;
