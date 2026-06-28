# Lattica — quantum-safe shielded payments (design spec + PoC)

A clean-slate, Zcash-style shielded payment protocol built entirely on **post-quantum
primitives** — no elliptic-curve / discrete-log dependency anywhere. It pairs a full
**protocol specification** ([`SPEC.md`](./SPEC.md)) with a runnable **proof of concept**: a
**Plonky3 zero-knowledge join-split circuit** (Rust) driven by a **Zig** protocol + node layer
that demonstrates a complete shielded transaction lifecycle.

> **Auditing this?** Start at **[`docs/AUDITORS.md`](docs/AUDITORS.md)** — the audit scope, security
> properties, build/reproduce commands, and known limitations.

Why: Zcash's shielded pools rely on the elliptic-curve discrete log, which Shor's algorithm
breaks. Lattica replaces every such primitive with a hash- or lattice-based one:

| Concern | Zcash (broken by Shor) | Lattica (quantum-safe) |
|---|---|---|
| Zero-knowledge proof | Halo 2 (Pasta curves) | **Plonky3 FRI-STARK** (transparent, hash-soundness), Poseidon2-Goldilocks, hiding FRI = ZK |
| Note encryption | ECDH (Jubjub) | ML-KEM-768 (FIPS 203) + ChaCha20-Poly1305 |
| Tx authorization | RedPallas binding sig | the **join-split proof** (knowledge of the spend key) bound to a canonical **`tx_binding`** digest |
| Commitments / balance | Pedersen (homomorphic) | Poseidon2 hash commitment; per-tx balance + range proven **in-circuit** |

Post-quantum + symmetric primitives come from Zig's `std.crypto` (ML-KEM-768, ML-DSA-44 in the key
hierarchy, SHA3, ChaCha20-Poly1305); the in-circuit hash is Poseidon2-Goldilocks, identical on-chain
(`src/poseidon2.zig`) and in the circuit. No cryptography is hand-rolled — the proof system is Plonky3.

## Layout

```
build.zig               Zig build: the wallet exe, the `test` step, `check-production` (M-09/M-10 probe)
lattica-prover-p3/      Rust: the production Plonky3 join-split circuit + verify/prove C ABI
  src/joinsplit_air.rs    the single production AIR (N-in/M-out join-split statement)
  src/poseidon2_air.rs    the Poseidon2-Goldilocks permutation AIR
  src/lib.rs              the C ABI (lattica_joinsplit_verify / _prove) + canonical (de)serialization
src/
  primitives.zig        ML-KEM, ML-DSA, SHA3/PRF/KDF, AEAD, the Poseidon2 note commitment helper
  field.zig             Goldilocks field (p = 2^64-2^32+1)
  poseidon2.zig         Poseidon2-Goldilocks — the on-chain hash, KAT-equal to the circuit
  tree.zig              incremental Merkle commitment tree (anchors)
  tx.zig                notes, key hierarchy, diversified addresses, incoming viewing key, ML-KEM encryption
  ffi.zig               fail-closed verify/prove boundary to the Rust prover (pluggable backend)
  codec.zig             canonical, overflow-safe byte (de)serialization
  protocol.zig          public supply model (SupplyState, live) + reference tx codec
  node.zig              chain state + shielded join-split validation (verify → anchor → nullifier → apply)
  wallet.zig            keygen, scanning, transfer builder, end-to-end demo (CLI)
  integration_node.zig  the live node driving the REAL Rust prover/verifier in-process
  production_probe.zig  compile probe: builds the consensus surface with test-only APIs gated out
  tests.zig            test aggregator for `zig build test`
SPEC.md                 the protocol specification
docs/AUDITORS.md        external audit handoff (start here)
```

## Run it

Requires **Zig 0.16** and **Rust 1.96** (+ a C compiler for the cross-language link).

```sh
# Build the Rust prover/verifier, then run the circuit + ABI tests.
cd lattica-prover-p3 && cargo test --release && cd ..

# The Zig protocol suite (incl. Poseidon2 KATs that pin on-chain == circuit) + the production probe.
zig build test

# The REAL cross-language path: Zig node → real Rust prove → real Rust verify → tamper/double-spend reject.
scripts/run-real-integration.sh

# End-to-end shielded transfer, narrated (uses a mock backend for the demo).
zig build run -- demo
```

The `demo` mints a shielded note to Alice, has her pay Bob via a **hidden-value join-split proof**
bound to the transaction (the `tx_binding` digest replaces a binding signature), verifies it at the
node, lets Bob trial-decrypt his note, and shows a replay rejected as a double-spend.

## Status

Proof of concept, **not cleared for value-bearing production** (see `docs/AUDITORS.md` §5 and
`docs/remediation-status.md`). What is implemented and tested end to end:

- The production **Plonky3 join-split** circuit — ownership (128-bit spend key), Merkle membership
  under a published anchor, nullifier correctness with position binding, value balance
  `Σin + mint = Σout + fee` with in-circuit range checks, domain separation, and a `tx_binding` public
  input — proving and verifying in **zero-knowledge** (hiding FRI PCS), ~103-bit proven / ~127-bit
  conjectured soundness (`docs/soundness-budget.md`).
- The live Zig node validates transactions solely through the proof (fail-closed, panic-isolated across
  the C ABI), with a public supply accumulator, atomic state application, and diversified addresses + a
  delegatable incoming viewing key.

Out of scope (host chain `rubble-node-zig`): block consensus / PoW / mempool / networking / emission
schedule and block-level state commitments. See [`docs/AUDITORS.md`](docs/AUDITORS.md) for the full
scope, threat model, and the deliberate sign-off items.
