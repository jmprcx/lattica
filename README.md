# Lattica — quantum-safe shielded payments (design spec + PoC)

A clean-slate, Zcash-style shielded payment protocol built entirely on **post-quantum
primitives** — no elliptic-curve / discrete-log dependency anywhere. It pairs a full
**protocol specification** ([`SPEC.md`](./SPEC.md)) with a runnable **proof of concept** in
Rust that demonstrates a complete shielded transaction lifecycle.

Why: Zcash's shielded pools rely on the elliptic-curve discrete log, which Shor's algorithm
breaks. Lattica replaces every such primitive with a hash- or lattice-based one:

| Concern | Zcash (broken by Shor) | Lattica (quantum-safe) |
|---|---|---|
| Zero-knowledge proof | Halo 2 (Pasta curves) | FRI-STARK, transparent, hash-soundness |
| Note encryption | ECDH (Jubjub) | ML-KEM-768 (FIPS 203) + ChaCha20-Poly1305 |
| Signatures | RedPallas / ECDSA | ML-DSA-44 (FIPS 204) |
| Commitments / balance | Pedersen (homomorphic) | hash commitment; balance checked in-proof |

## Layout

```
crates/
  lattica-primitives   ML-KEM, ML-DSA, SHA3 commitments/nullifiers/PRF/KDF, AEAD
  lattica-tree         incremental Merkle commitment tree
  lattica-tx           notes, keys, addresses, ML-KEM note encryption
  lattica-circuit      FRI-STARK spend-authorization proof (Winterfell)
  lattica-node         chain state + shielded-transaction validation
  lattica-wallet       keygen, scanning, transfer builder, end-to-end demo
SPEC.md                the protocol specification
```

## Run it

```sh
cargo test --workspace                      # 35 tests across all crates
cargo run -p lattica-wallet -- demo         # end-to-end shielded transfer, narrated
cargo run --release -p lattica-wallet -- bench   # prove/verify timings and sizes
```

The `demo` mints a shielded note to Alice, has her pay Bob with a real ~27 KB FRI proof and
an ML-DSA binding signature, verifies it at the node, lets Bob trial-decrypt his note, and
shows a replay rejected as a double-spend.

## Status

Proof of concept. The FRI proof of spend authorization is real and verifying; Merkle
membership, nullifier, and balance checks are enforced by the node and specified for
in-circuit folding. Zero-knowledge trace masking and a one-way in-circuit hash are the
documented remaining steps to production — see [`SPEC.md` §8](./SPEC.md). None require
changing the post-quantum primitive choices.
