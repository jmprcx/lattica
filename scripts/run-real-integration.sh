#!/usr/bin/env bash
# Exercise the REAL cross-language prove/verify path end to end — the seam `zig build test` cannot
# cover, because this host's Zig linker can't link the libc-dependent Rust staticlib (the .sframe crt
# issue). The fix: compile the Zig side to a relocatable object and let the SYSTEM toolchain (cc) do
# the final link, which handles gcc's crt fine.
#
# Two checks:
#   (1) C FFI harness — Rust prove_demo -> Rust verify -> tamper-reject -> double-spend-reject.
#   (2) In-node integration — the live Zig node (node.zig) driving the REAL Rust prover/verifier:
#       Zig builds the witness -> Rust proves -> Zig reconstructs the public inputs -> Rust verifies
#       -> node applies; replay + tampered output are rejected by the real verifier.
#
# Usage: scripts/run-real-integration.sh   (exits non-zero on any failure)
set -euo pipefail
cd "$(dirname "$0")/.."
OUT="${TMPDIR:-/tmp}/lattica-real-integration"
mkdir -p "$OUT"

echo "== building the prover staticlib (release) =="
( cd lattica-prover-p3 && cargo build --release )
LIB="lattica-prover-p3/target/release/liblattica_prover_p3.a"

echo "== (1) C FFI harness =="
cc lattica-prover-p3/tests/ffi_integration.c "$LIB" -lpthread -ldl -lm -o "$OUT/ffi_it"
"$OUT/ffi_it"

echo "== (2) in-node integration (live node + REAL Rust prove/verify) =="
# -fno-stack-check: omit __zig_probe_stack so the system linker (not Zig's) resolves all symbols.
zig build-obj src/integration_node.zig -OReleaseSafe -lc -fno-stack-check -femit-bin="$OUT/it_node.o"
cc "$OUT/it_node.o" "$LIB" -lpthread -ldl -lm -o "$OUT/it_node"
"$OUT/it_node"

echo "== real integration: ALL PASS =="
