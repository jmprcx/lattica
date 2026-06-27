/* End-to-end FFI integration test for the join-split verify seam: prove (Rust) -> verify (Rust) ->
 * tamper rejected -> double-spend rejected. Exercises the same C ABI the Zig node uses
 * (ffi.zig::JoinSplitPublicInputs / setJoinSplitBackend). Built with the system toolchain because
 * Zig 0.16's linkers can't handle this host's crt1.o .sframe section.
 *
 * Build + run (after `cargo build --release`):
 *   cc tests/ffi_integration.c target/release/liblattica_prover_p3.a -lpthread -ldl -lm -o /tmp/it && /tmp/it
 */
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>

extern int32_t lattica_joinsplit_prove_demo(uint8_t *proof, size_t proof_cap, size_t *proof_len,
                                            uint8_t *pi, size_t pi_cap, size_t *pi_len);
extern int32_t lattica_joinsplit_verify(const uint8_t *proof, size_t proof_len,
                                        const uint8_t *pi, size_t pi_len);

#define DIGEST 32
/* a trivial nullifier set */
static uint8_t seen[64][DIGEST];
static int seen_n = 0;
static int is_spent(const uint8_t *nf) {
    for (int i = 0; i < seen_n; i++) if (!memcmp(seen[i], nf, DIGEST)) return 1;
    return 0;
}
/* node-side apply: verify, then reject if any nullifier already spent; else insert */
static int apply_spend(const uint8_t *proof, size_t pl, const uint8_t *pi, size_t pil) {
    if (lattica_joinsplit_verify(proof, pl, pi, pil) != 0) return 0;
    const uint8_t *nf0 = pi + 32, *nf1 = pi + 64; /* anchor(32) | nf0 | nf1 | ... */
    if (is_spent(nf0) || is_spent(nf1)) return 0;
    memcpy(seen[seen_n++], nf0, DIGEST);
    memcpy(seen[seen_n++], nf1, DIGEST);
    return 1;
}

int main(void) {
    uint8_t *proof = malloc(1 << 20);
    size_t proof_len = 0, pi_len = 0;
    uint8_t pi[256];
    if (lattica_joinsplit_prove_demo(proof, 1 << 20, &proof_len, pi, sizeof pi, &pi_len)) { printf("FAIL prove\n"); return 1; }
    if (pi_len != 200) { printf("FAIL pi_len=%zu\n", pi_len); return 1; }
    printf("proved: proof=%zu bytes, pi=%zu bytes\n", proof_len, pi_len);

    if (lattica_joinsplit_verify(proof, proof_len, pi, pi_len) != 0) { printf("FAIL verify-valid\n"); return 1; }
    printf("verify(real proof): ACCEPT\n");

    uint8_t orig = pi[0]; pi[0] ^= 1;
    if (lattica_joinsplit_verify(proof, proof_len, pi, pi_len) == 0) { printf("FAIL tamper-accepted\n"); return 1; }
    pi[0] = orig;
    printf("verify(tampered anchor): REJECT\n");

    if (!apply_spend(proof, proof_len, pi, pi_len)) { printf("FAIL first-spend\n"); return 1; }
    printf("first spend: ACCEPT (nullifiers inserted)\n");
    if (apply_spend(proof, proof_len, pi, pi_len)) { printf("FAIL double-spend-accepted\n"); return 1; }
    printf("double spend (replay): REJECT\n");

    free(proof);
    printf("OK: prove -> verify -> tamper-reject -> double-spend-reject\n");
    return 0;
}
