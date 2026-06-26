# Lattica — A Quantum-Safe Shielded Payment Protocol

**Status:** design specification + proof of concept · **Version:** 0.1 (2026-06)

Lattica is a clean-slate, Zcash-style shielded payment protocol whose security rests
entirely on **post-quantum assumptions**. It reproduces Zcash's privacy model — fully
shielded value transfer validated by zero-knowledge proofs — while removing every
elliptic-curve / discrete-log dependency that Shor's algorithm would break.

This document specifies the protocol. A working proof of concept of every component lives
alongside it in the `lattica/` Cargo workspace; see [§10](#10-implementation-map).

---

## 1. Motivation

Zcash's shielded pools (Sapling, Orchard) derive privacy and soundness from the hardness of
the elliptic-curve discrete-log problem (ECDLP). A cryptographically relevant quantum
computer running Shor's algorithm solves ECDLP efficiently, which would break — in order of
severity — the soundness of the zk-SNARK proof system, the binding of value commitments,
the unforgeability of spend-authorization signatures, and the confidentiality of the ECDH
key agreement used to encrypt notes. Zcash's own roadmap (quantum-recoverable wallets in
2026, a targeted post-quantum transition by ~2027, "Project Tachyon") treats this as the
central long-term threat.

Lattica asks: *if we were starting today with no backward-compatibility constraint, what
would a fully post-quantum shielded protocol look like?*

## 2. Goals and non-goals

**Goals.** Pure post-quantum security (hash- and lattice-based only); no trusted setup;
preserve Zcash's privacy properties (shielded amounts, recipients, and spend-graph
unlinkability); a concrete, testable reference implementation of the hard parts.

**Non-goals (for this PoC).** A production mainnet, networking/mempool/consensus at scale,
multi-asset support, and wallet UX. These are deferred and noted where relevant.

## 3. Threat model

The adversary is a polynomial-time quantum algorithm with access to the full public ledger
(all commitments, nullifiers, proofs, ciphertexts, and signatures). Security reduces to:

- **Collision/preimage resistance of hashes** (SHA3/Keccak out-of-circuit; an
  arithmetization-friendly hash in-circuit) — believed to retain ~½ of its classical bit
  security under Grover, so parameters are sized accordingly.
- **Module-lattice hardness** (MLWE/MSIS) underlying ML-KEM and ML-DSA.
- **Symmetric security** of ChaCha20-Poly1305 with 256-bit keys (~128-bit post-quantum).

No assumption depends on the hardness of any group discrete log or factoring.

## 4. Quantum-vulnerability mapping

| Component | Zcash today (ECDLP) | Lattica (post-quantum) |
|---|---|---|
| Proof system | Halo 2 / Groth16 over Pasta/BLS12-381 | FRI-STARK (Winterfell); hash-soundness, transparent |
| Note/commitment hash | Sinsemilla / Bowe–Hopwood Pedersen | SHA3 (PoC) → Poseidon2/Rescue in-circuit |
| Value balance | Homomorphic Pedersen commitments | Checked **inside the proof** over cleartext values |
| Spend authorization | RedPallas re-randomizable signatures | Proven **in-circuit** (knowledge of spend secret) |
| Binding signature | RedPallas | ML-DSA-44 (FIPS 204) |
| Note encryption (key agreement) | ECDH on Jubjub | ML-KEM-768 (FIPS 203) + ChaCha20-Poly1305 |
| Nullifier / PRF | curve-based PRF / BLAKE2 | keyed SHA3 (→ in-circuit hash) |
| Commitment tree | Merkle tree (Sinsemilla) | Merkle tree, identical structure, PQ hash |
| Transparent signatures | ECDSA | ML-DSA-44 |
| Proof-of-work | Equihash | hash-PoW with doubled width (Grover margin) |

## 5. Primitives and parameters

- **ML-KEM-768** (FIPS 203) — note-encryption key agreement. ek 1184 B, ct 1088 B, shared
  secret 32 B. NIST security level 3.
- **ML-DSA-44** (FIPS 204) — binding/transparent signatures. pk 1312 B, sig 2420 B. Raise
  to ML-DSA-65/87 for higher margins.
- **ChaCha20-Poly1305** — AEAD note encryption, 256-bit key, 96-bit nonce.
- **SHA3-256 (Keccak)** — out-of-circuit hashing, with length-prefixed, domain-separated
  framing (`hash_domain`) so a digest for one purpose can never be reinterpreted as another.
- **FRI-STARK** over a STARK field — the proof system (§8).

## 6. Key hierarchy, notes, addresses

A 32-byte **spending seed** is the root of the wallet. From it:

- `nk = PRF_expand(seed, "nk")` — nullifier key.
- an **ML-KEM keypair** (note encryption) and an **ML-DSA keypair** (authorization). The Zig
  reference derives both **deterministically from the seed** (the 64-byte ML-KEM seed and the
  32-byte ML-DSA seed are expanded from it), so the wallet restores from the seed alone.
- **Address** = (`ivk_tag`, `kem_ek`), where `ivk_tag = H_IVK(seed, nk)`. The recipient
  identifier bound into commitments is `recipient_id = H_IVK(ivk_tag, kem_ek)`.

A **note** is `(value, recipient_id, rho, rcm)`:

- **Commitment** `cm = H_NoteCommit(recipient_id, value, rho, rcm)`. Hiding via the random
  trapdoor `rcm`; binding via collision resistance. There is deliberately no homomorphic
  property — balance is enforced in-proof instead.
- **Nullifier** `nf = PRF_nf(nk, rho, position)`, revealed on spend; detects double-spends
  without revealing which note was spent.

## 7. Note encryption

To send a note to an address:

1. `(shared_secret, kem_ct) = ML-KEM.Encaps(address.kem_ek)`.
2. `(key, nonce) = KDF(shared_secret, kem_ct, cm)` — bound to the commitment so a ciphertext
   cannot be replayed against a different note.
3. `ciphertext = AEAD.Seal(key, nonce, note_plaintext, aad = cm)`.

The on-chain **transmitted note** is `(cm, kem_ct, ciphertext)`. The recipient trial-decrypts
by decapsulating with their ML-KEM secret key, re-deriving the key, and opening the AEAD; a
recovered note is accepted only if it re-commits to `cm` and is addressed to the recipient
(defending against a malicious sender).

## 8. The shielded statement and proving system

A spend proves, in zero knowledge, the conjunction:

1. **Membership** — `cm` is a leaf under the public anchor (Merkle authentication path).
2. **Nullifier correctness** — `nf = PRF_nf(nk, rho, position)` for that note.
3. **Spend authorization** — knowledge of the spend secret (preimage under a one-way hash),
   folded into the proof instead of a re-randomizable signature (no standardized PQ
   re-randomizable signature exists yet).
4. **Balance** — `Σ input values = Σ output values + fee`, over cleartext values inside the
   proof (no homomorphic value commitment to lean on, by design).

**Proof system: FRI-STARK.** Soundness depends only on a collision-resistant hash; the
setup is transparent (no toxic waste). This is the load-bearing quantum-safe choice,
replacing Halo 2 whose soundness rests on ECDLP.

**Implementation in the Zig reference.** A transparent FRI-STARK prover has no `std.crypto`
equivalent, so it is implemented from scratch in `src/stark.zig` over the **Goldilocks** field
(`p = 2^64 - 2^32 + 1`). The in-circuit relation for constraint (3) is **knowledge of a preimage
of an arithmetization-friendly hash** (`src/rescue.zig`): a Poseidon-style SPN (S-box `x^7`, MDS
diffusion, full rounds), arithmetised as a **multi-column AIR** — one trace column per state
element, one row per round, with the round constants supplied as periodic low-degree columns.
The trace is interpolated (NTT) and Merkle-committed over an LDE coset; a Fiat-Shamir-random
combination of the per-element transition quotients and the boundary quotients forms the
composition polynomial; **FRI** folds it to a constant; and queries open the trace rows, the mask,
and the FRI layers, with the verifier checking Merkle paths, the algebraic composition⇔trace link,
and fold consistency. This **closes gap R1** — the relation is a genuine one-way hash, replacing
the earlier algebraic `x³ + C`. Parameters are PoC-grade (32 queries, rate 1/4, 64-bit field →
effective conjectured ~50-bit, bounded by the field; see [`parameters.md`](./parameters.md)).

**Zero-knowledge.** The proof is zero-knowledge (honest-verifier, via Fiat-Shamir). Two
blindings make the openings reveal nothing about the witness: (1) the trace polynomial is masked
as `T'(x) = T(x) + Z_H(x)·b(x)` for a random `b` of degree ≥ the number of trace openings — since
`Z_H` vanishes on the constraint domain the masked trace still satisfies every constraint, but
each opened LDE value is uniform; and (2) FRI runs on `H(x) = CP(x) + ζ·g(x)` for a committed
uniformly-random polynomial `g` and a Fiat-Shamir `ζ`, so the FRI-layer openings reveal nothing
about the witness-derived composition (the verifier recovers `g` from its own commitment and
checks `H = CP + ζ·g` at each query). Proofs are randomized. The ZK here is PoC-grade and not
formally proven.

**PoC scope and honest gaps.**

- Constraint (3) authorization is a **real, zero-knowledge FRI-STARK** proving knowledge of a
  hash preimage (`src/stark.zig` + `src/rescue.zig`). **Constraint (1) membership is now also
  in-circuit** as a standalone ZK proof (`src/membership.zig`): a multi-column AIR folding a leaf
  up `DEPTH` field-hash compressions to the public anchor. **(R3, circuit complete)** A single proof
  now folds **all four constraints** (`src/spend.zig`): for public `(anchor, nf, send, fee)` and
  hidden `(value, ρ, nk, path)` it proves `cm=H(value,ρ)`, that `cm` folds up the path to
  `anchor`, `nf=H(nk,ρ)`, and `value=send+fee` — with `ρ` wired equal across regions by an id/σ
  grand-product copy constraint and `cm`→leaf wired by adjacency. `cm` stays hidden. Soundness
  tests reject a wrong anchor, wrong nf, unbalanced tx, wrong path, and an inconsistent `ρ`.
  Remaining is hardening/integration, not new mechanism: the full commitment opening
  (`recipient`/`rcm`) + owner binding, general path positions, ZK blinding, switching the
  protocol's commitment/nullifier/Merkle hashing to the field hash, and node integration. See
  [`soundness.md §6`](./soundness.md).
- **Zero-knowledge (R2).** Implemented (trace blinding + masked FRI; see above). Honest-verifier
  and PoC-grade — a formal ZK proof and production parameters are future work.
- **One-way in-circuit hash (R1).** Closed: the authorization relation is a Poseidon-style SPN
  hash (`x^7` S-box, MDS, full rounds). The *construction* is standard; the specific MDS and
  round constants are deterministically generated, not yet a standardized/vetted instance —
  production must use published constants and the spec's round count.

## 9. Transaction format, validation, and consensus shell

A **ShieldedTx** is `{ spends[], outputs[], fee, binding_pk, binding_sig }`. The
`binding_sig` is an ML-DSA signature over a canonical, domain-separated digest of the whole
body (everything but the signature).

**Node validation** (`Chain.verifyAndApply`), all-or-nothing:

1. Binding signature verifies over the tx digest.
2. For each spend: anchor is a known historical root; Merkle path verifies `cm` under it;
   nullifier is unseen (in the chain and within the tx); authorization STARK verifies.
3. Value balance holds.
4. Apply: insert nullifiers; append output commitments; publish the new anchor.

**Consensus shell (specified, deferred in PoC).** Block = (header, txs); the header commits
to the post-block anchor and nullifier-set root. Proof-of-work uses a standard hash with
doubled output width so Grover's quadratic speedup leaves a full security margin; difficulty
retargeting and longest-chain selection are conventional. Proof-of-stake is a viable
alternative. Networking, mempool, and fee-market are out of PoC scope.

## 10. Implementation map

The reference implementation is a **Zig** (0.16) workspace; every post-quantum and symmetric
primitive comes from `std.crypto`.

| Module | Responsibility |
|---|---|
| `src/primitives.zig` | ML-KEM, ML-DSA, SHA3 hashing/commitments/nullifiers/PRF/KDF, AEAD |
| `src/field.zig` | Goldilocks field, roots of unity, NTT/iNTT |
| `src/stark.zig` | from-scratch FRI-STARK: Merkle, Fiat-Shamir transcript, FRI, prover/verifier |
| `src/tree.zig` | incremental Merkle commitment tree + authentication paths |
| `src/tx.zig` | notes, keys (seed-deterministic), addresses, ML-KEM note encryption / trial decryption |
| `src/circuit.zig` | spend-authorization proof (façade over `stark.zig`) |
| `src/node.zig` | chain state + shielded-transaction validation rules |
| `src/wallet.zig` | keygen, scanning, transfer builder, end-to-end `demo` (CLI) |

## 11. Performance

Measured on the Zig reference (release build, single core, zero-knowledge proof, 1024-step
authorization AIR over Goldilocks, blowup ×16, 32 FRI queries):

| Metric | Lattica | For comparison |
|---|---|---|
| Prove (authorization) | ~170 ms | Orchard full action proof ~hundreds of ms |
| Verify (authorization) | ~5 ms | — |
| Proof size | ~265 KB | Orchard (Halo 2) ~3 KB; Sapling (Groth16) ~0.2 KB |
| Binding signature | 2420 B | RedPallas 64 B |
| ML-KEM ciphertext / note | 1088 B | Jubjub ECDH ephemeral key 32 B |

The proof is large because this from-scratch STARK is unoptimized (no DEEP composition, FRI
folded fully to a constant, every layer opened per query) and the zero-knowledge blinding adds a
random mask polynomial and a larger LDE. DEEP-ALI, batched openings, and proof
recursion/aggregation are the standard levers to shrink it; they are future work.

The headline cost is **proof and signature size**: post-quantum primitives are larger, and
FRI proofs are ~10× a Halo 2 proof. In exchange Lattica needs **no trusted setup** and is
**quantum-safe**. Recursion/aggregation (FRI folding, with no elliptic-curve wrap) is the
standard lever to amortize proof size across many actions; it is future work.

## 12. Security analysis (summary)

Privacy and soundness reduce to hash collision/preimage resistance and MLWE/MSIS hardness,
both believed quantum-safe; symmetric confidentiality to 256-bit ChaCha20-Poly1305. No
component depends on a group discrete log or on a trusted setup. The known gaps to a
production-grade shielded protocol are explicitly the three in [§8](#8-the-shielded-statement-and-proving-system):
ZK trace masking, a one-way in-circuit hash, and folding all four constraints into a single
AIR — none of which require a change to the primitive choices above.

## 13. References

- Zcash Protocol Specification (NU6.1) and the Orchard Book.
- NIST FIPS 203 (ML-KEM), FIPS 204 (ML-DSA), FIPS 205 (SLH-DSA).
- Ben-Sasson et al., *Scalable, transparent, and post-quantum secure computational
  integrity* (STARKs); the FRI protocol.
- Winterfell STARK prover (the FRI implementation used here).
