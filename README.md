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
  field.zig            Goldilocks field (p = 2^64-2^32+1), roots of unity, NTT
  stark.zig            from-scratch FRI-STARK: Merkle, transcript, FRI, prover/verifier
  tree.zig             incremental Merkle commitment tree
  tx.zig               notes, keys, addresses, ML-KEM note encryption
  circuit.zig          spend-authorization proof (façade over stark.zig)
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
- **The FRI-STARK spend-authorization proof is implemented from scratch in Zig** (`stark.zig`),
  since no `std.crypto` equivalent exists. It is a genuine **zero-knowledge**, transparent,
  hash-based STARK over the Goldilocks field — Merkle-committed trace LDE, a Fiat-Shamir random
  constraint composition, FRI low-degree testing, and query openings binding the composition to
  the trace. No trusted setup, no elliptic curve; soundness rests on SHA3. **Zero-knowledge** is
  achieved by blinding the trace polynomial with `Z_H(x)·b(x)` (random `b`), so every opened
  trace value is uniform, and by running FRI on `CP + ζ·g` for a committed random polynomial
  `g`, so the FRI-layer openings reveal nothing about the witness. Proofs are randomized
  (different each time, all verifying). A 1-in/1-out transfer carries a ~265 KB proof
  (prove ~170 ms, verify ~5 ms, release).

Remaining documented steps to production (see [`SPEC.md` §8](./SPEC.md)): a vetted one-way
in-circuit hash in place of the algebraic `x → x³ + C` relation, folding
membership/nullifier/balance into the AIR, and production-grade STARK parameters (the
zero-knowledge here is honest-verifier and PoC-grade, not formally proven). None require
changing the post-quantum primitive choices.
