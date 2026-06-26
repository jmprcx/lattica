# Lattica — quantum-safe shielded payments (design spec + PoC)

A clean-slate, Zcash-style shielded payment protocol built entirely on **post-quantum
primitives** — no elliptic-curve / discrete-log dependency anywhere. It pairs a full
**protocol specification** ([`SPEC.md`](./SPEC.md)) with a runnable **proof of concept** in
**Zig** that demonstrates a complete shielded transaction lifecycle.

Why: Zcash's shielded pools rely on the elliptic-curve discrete log, which Shor's algorithm
breaks. Lattica replaces every such primitive with a hash- or lattice-based one:

| Concern | Zcash (broken by Shor) | Lattica (quantum-safe) |
|---|---|---|
| Zero-knowledge proof | Halo 2 (Pasta curves) | FRI-STARK, transparent, hash-soundness |
| Note encryption | ECDH (Jubjub) | ML-KEM-768 (FIPS 203) + ChaCha20-Poly1305 |
| Signatures | RedPallas / ECDSA | ML-DSA-44 (FIPS 204) |
| Commitments / balance | Pedersen (homomorphic) | hash commitment; balance checked in-proof |

All post-quantum and symmetric primitives come from Zig's standard library (`std.crypto`):
ML-KEM-768, ML-DSA-44, SHA3-256, and ChaCha20-Poly1305. No cryptography is hand-rolled.

## Layout

```
build.zig              Zig build: the wallet executable + the `test` step
src/
  primitives.zig       ML-KEM, ML-DSA, SHA3 commitments/nullifiers/PRF/KDF, AEAD
  tree.zig             incremental Merkle commitment tree
  tx.zig               notes, keys, addresses, ML-KEM note encryption
  circuit.zig          spend-authorization proof (STUB — see Status)
  node.zig             chain state + shielded-transaction validation
  wallet.zig           keygen, scanning, transfer builder, end-to-end demo (CLI)
  tests.zig            test aggregator for `zig build test`
SPEC.md                the protocol specification
```

## Run it

Requires **Zig 0.16**.

```sh
zig build test                       # 35 unit + integration tests across all modules
zig build run -- demo                # end-to-end shielded transfer, narrated
zig build run -Doptimize=ReleaseFast -- bench   # proof/verify timings and primitive sizes
zig build run -- keygen              # print a deterministic account (restorable from seed)
```

The `demo` mints a shielded note to Alice, has her pay Bob with an authorization proof and an
ML-DSA binding signature, verifies it at the node, lets Bob trial-decrypt his note, and shows a
replay rejected as a double-spend.

## Status

Proof of concept. The post-quantum primitives (ML-KEM-768, ML-DSA-44, SHA3, ChaCha20-Poly1305)
are real `std.crypto` implementations, and the full shielded lifecycle — commitments,
nullifiers, Merkle membership, note encryption, balance, and the ML-DSA binding signature — is
implemented and tested end to end.

Two deliberate differences from the original Rust PoC:

- **Wallet keys are derived deterministically from the 32-byte seed** (ML-KEM and ML-DSA both
  support seeded keygen), so a wallet restores from the seed alone — the production fix the
  spec calls for.
- **The FRI-STARK spend-authorization proof is a stub in this port.** A transparent, hash-based
  FRI-STARK prover has no `std.crypto` equivalent, so `circuit.zig` ships a clearly-labeled
  placeholder that preserves the relation shape (the 1024-step `x → x³ + C` authorization image)
  and binds proof↔image so tampering is detectable, but **proves nothing in zero knowledge**.
  Membership, nullifier, balance, and the binding signature are enforced by the node exactly as
  in the reference. Implementing a genuine FRI-STARK in Zig is the documented next phase.

Zero-knowledge trace masking and a one-way in-circuit hash remain the documented steps to
production — see [`SPEC.md` §8](./SPEC.md). None require changing the post-quantum primitive
choices.
