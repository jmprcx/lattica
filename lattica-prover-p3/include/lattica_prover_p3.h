/* lattica_prover_p3.h — the C ABI of liblattica_prover_p3.a (single source of truth).
 *
 * The Zig node's extern declarations (src/ffi_integration.zig, src/integration_node.zig) and the C
 * integration test (tests/ffi_integration.c) mirror these EXACT signatures; the Rust definitions live
 * in lattica-prover-p3/src/lib.rs (#[no_mangle] extern "C"). Changing anything here is a node-seam
 * (and, for the wire formats, consensus) break.
 *
 * CONVENTIONS
 *   - Return codes: verify → 0 = accept, nonzero = reject (fail-closed).
 *                   prove  → 0 = ok, 1 = malformed/invalid input or internal failure, 2 = an output
 *                   buffer was too small. On rc=2 the *_len outputs are NOT written (the caps are
 *                   checked before any store); size the buffers from MAX_PROOF_LEN / the fixed PI
 *                   widths. *_len are written only on rc=0.
 *   - No call unwinds across the boundary (Rust catches panics); NULL pointers fail closed.
 *   - proof bytes: postcard-serialized p3-uni-stark Proof under the production config (see
 *     src/config.rs; pinned to p3 0.6.1 + the production FRI parameters). Verify rejects
 *     proof_len > MAX_PROOF_LEN (1 << 21, mirrored by src/ffi.zig).
 *   - digests: 32 bytes = 4 canonical little-endian Goldilocks u64 limbs (non-canonical ⇒ reject).
 *   - public inputs (little-endian, byte-exact):
 *       join-split (208 B): anchor(32) ‖ nf0(32) ‖ nf1(32) ‖ out_cm0(32) ‖ out_cm1(32) ‖
 *                           tx_binding(32) ‖ fee(u64) ‖ mint(u64)
 *       HTLC (248 B):       the join-split layout ‖ current_height(u64) ‖ redeem_hashlock(32)
 *   - witnesses (wallet → prover): fixed-length records; JS_WITNESS_LEN = 2464 B,
 *     HTLC_WITNESS_LEN = 2728 B (field order per src/lib.rs js_witness_len / htlc_witness_len).
 *     Batch proving takes n_tx concatenated records (witness_len must equal n_tx * record length;
 *     1 ≤ padded_tiles(n_tx) ≤ MAX_BATCH_TILES = 64).
 */
#ifndef LATTICA_PROVER_P3_H
#define LATTICA_PROVER_P3_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* --- single-transaction join-split ------------------------------------------------------------ */
int32_t lattica_joinsplit_verify(const uint8_t *proof_ptr, size_t proof_len,
                                 const uint8_t *pi_ptr, size_t pi_len);
int32_t lattica_joinsplit_prove(const uint8_t *witness_ptr, size_t witness_len,
                                uint8_t *proof_out, size_t proof_cap, size_t *proof_len,
                                uint8_t *pi_out, size_t pi_cap, size_t *pi_len);
/* demo prover (fixed internal witness) — dev/integration only */
int32_t lattica_joinsplit_prove_demo(uint8_t *proof_out, size_t proof_cap, size_t *proof_len,
                                     uint8_t *pi_out, size_t pi_cap, size_t *pi_len);

/* --- single-transaction HTLC spend (redeem/refund) --------------------------------------------- */
int32_t lattica_htlc_verify(const uint8_t *proof_ptr, size_t proof_len,
                            const uint8_t *pi_ptr, size_t pi_len);
int32_t lattica_htlc_prove(const uint8_t *witness_ptr, size_t witness_len,
                           uint8_t *proof_out, size_t proof_cap, size_t *proof_len,
                           uint8_t *pi_out, size_t pi_cap, size_t *pi_len);
int32_t lattica_htlc_prove_demo(uint8_t *proof_out, size_t proof_cap, size_t *proof_len,
                                uint8_t *pi_out, size_t pi_cap, size_t *pi_len);

/* --- batch: one proof per block (tx-root = 32-byte digest, the only public input) -------------- */
int32_t lattica_batch_verify(const uint8_t *proof_ptr, size_t proof_len,
                             const uint8_t *root_ptr, size_t root_len);
int32_t lattica_batch_prove(const uint8_t *witness_ptr, size_t witness_len, size_t n_tx,
                            uint8_t *proof_out, size_t proof_cap, size_t *proof_len,
                            uint8_t *root_out, size_t root_cap, size_t *root_len);
int32_t lattica_joinsplit_tree_verify(const uint8_t *proof_ptr, size_t proof_len,
                                      const uint8_t *root_ptr, size_t root_len, size_t n_tx);
int32_t lattica_joinsplit_tree_prove(const uint8_t *witness_ptr, size_t witness_len, size_t n_tx,
                                     uint8_t *proof_out, size_t proof_cap, size_t *proof_len,
                                     uint8_t *root_out, size_t root_cap, size_t *root_len);
int32_t lattica_htlc_batch_verify(const uint8_t *proof_ptr, size_t proof_len,
                                  const uint8_t *root_ptr, size_t root_len);
int32_t lattica_htlc_batch_prove(const uint8_t *witness_ptr, size_t witness_len, size_t n_tx,
                                 uint8_t *proof_out, size_t proof_cap, size_t *proof_len,
                                 uint8_t *root_out, size_t root_cap, size_t *root_len);

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* LATTICA_PROVER_P3_H */
