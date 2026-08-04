# Lattica

Lattica is a clean-slate, post-quantum shielded-payment protocol and working proof of concept. It combines a Zig wallet and node state machine with Plonky3 zero-knowledge STARK circuits written in Rust. The protocol avoids elliptic curves and discrete-log assumptions throughout its production proof path.

The repository contains an audited CPU proof/verifier baseline, a complete shielded transaction demonstration, production batch circuits, and feature-gated research into GPU proving, out-of-core proving, and recursive aggregation. It is not a complete cryptocurrency node and is not cleared for value-bearing deployment.

## Start here

- [Protocol specification](SPEC.md) defines the transaction model and cryptographic construction.
- [Documentation map](docs/README.md) separates current guidance, normative references, research, and historical audit records.
- [Audit handoff](docs/AUDITORS.md) defines the reviewed surface, assumptions, reproduction commands, and exclusions.
- [Current status](docs/audit-readiness-status.md) records the production baseline and active development boundary.
- [Remediation status](docs/remediation-status.md) maps audit findings to their resolutions.

## What it provides

Lattica replaces the elliptic-curve components normally found in shielded payment systems:

| Function | Lattica construction |
|---|---|
| Zero-knowledge authorization | Transparent Plonky3 FRI-STARK with a hiding PCS |
| Circuit and protocol hash | Poseidon2 over the Goldilocks field |
| Note encryption | ML-KEM-768 and ChaCha20-Poly1305 |
| Key hierarchy | ML-DSA-44 plus hash-derived spending and viewing material |
| Transaction authorization | Join-split proof of spend-key knowledge, bound to a canonical `tx_binding` digest |
| Value conservation | In-circuit balance equations and range checks |

The production circuits cover individual join-splits, shielded HTLCs, and batch forms of both. The Zig node checks anchors, nullifiers, supply transitions, transaction bindings, and proof validity before atomically applying state.

## Repository layout

| Path | Purpose |
|---|---|
| `src/` | Zig protocol, wallet, codecs, state machine, cryptography, and Rust FFI |
| `lattica-prover-p3/` | Production Plonky3 circuits, prover/verifier, C ABI, and research backends |
| `docs/` | Specifications, audit material, operational guidance, and research notes |
| `scripts/` | Cross-language integration and support scripts |
| `framework-spike/`, `plonky2-spike/`, `plonky3-spike/` | Historical framework experiments |
| `lattica-prover/` | Reference-only Winterfell differential oracle |

## Build and verify

Requirements: Zig 0.16, Rust 1.96, and a C toolchain.

```sh
cd lattica-prover-p3
cargo test --release
cd ..

zig build test
scripts/run-real-integration.sh
zig build run -- demo
```

The integration script exercises the real Zig-to-Rust boundary: proof generation, verification, state application, transaction-root agreement, tamper rejection, and double-spend rejection.

## Status and security boundary

The default CPU implementation at `v3-batch-audit` is the frozen ten-symbol audit target and includes the join-split, HTLC, batch join-split, and batch HTLC paths. The current development tree adds two join-split proof-tree container symbols, bringing its default ABI to twelve; that post-tag seam is not covered by the frozen audit. The documented soundness budget for the underlying production proof family is approximately 103 bits proven and 127 bits conjectured.

GPU acceleration, streaming/out-of-core proving, and recursion are opt-in research features. They do not alter the underlying production verifier or leaf-proof format. Recursion remains excluded from the default static library; the development proof-tree container is a non-recursive aggregation seam and must not be mistaken for audited recursive aggregation.

The following remain outside this repository's production claim:

- block consensus, networking, mempool policy, reorg handling, and emissions;
- host-chain release integration and startup attestation;
- operational wallet and prover key management;
- production recursive aggregation;
- final independent sign-off on the documented cryptographic assumptions.

Read [the audit handoff](docs/AUDITORS.md) before treating any component as security-sensitive.
