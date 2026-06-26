# Lattica — Production-Readiness Assessment

**Audience:** CTO / technical diligence · **Subject:** Lattica quantum-safe shielded payment protocol (PoC)
**Version assessed:** 0.1 (2026-06) · **Assessment date:** 2026-06-25
**Basis:** Full source review of the `lattica` Cargo workspace, `SPEC.md`, `README.md`; tests and benchmarks re-run locally for this report.

> **Note on framing.** This document is an honest engineering assessment, not marketing. Lattica is a **proof of concept**: its purpose is to prove that a Zcash-style private-payment system can be built with *zero* elliptic-curve dependence. It succeeds at that. It is **not** a deployable network, and the gaps between "PoC" and "mainnet" are real and are catalogued below. Timeline, team, and cost figures are informed estimates for planning, not commitments.

> **Implementation update (post-assessment).** The codebase has since been **ported from Rust to Zig 0.16**, with every post-quantum and symmetric primitive (ML-KEM-768, ML-DSA-44, SHA3-256, ChaCha20-Poly1305) now sourced from `std.crypto`, and wallet keys derived **deterministically from the seed**. The FRI-STARK proof — which has no `std.crypto` equivalent — was **reimplemented from scratch in Zig** (`src/stark.zig`): a genuine transparent, hash-based STARK over the Goldilocks field (NTT-interpolated trace LDE, Fiat-Shamir constraint composition, FRI low-degree testing, query openings binding composition to trace; no trusted setup). It is real and verifying, though unoptimized — a 1-in/1-out transfer carries a ~200 KB proof (prove ~43 ms, verify ~2 ms). The security analysis below still applies: the STARK is sound and transparent but **not yet zero-knowledge**, still uses the algebraic `x → x³ + C` relation rather than a vetted one-way hash, and proves only constraint (3) (membership/nullifier/balance remain node-enforced) — the same gaps catalogued throughout. Commands referencing `cargo` should be read as `zig build`.

---

## 1. Executive Summary

Lattica is a ~1,750-line Rust reference implementation of a **fully post-quantum, Zcash-style shielded payment protocol**. Where Zcash's privacy rests on the elliptic-curve discrete-log problem — which a large quantum computer running Shor's algorithm would break — Lattica replaces *every* such primitive with a hash-based or lattice-based equivalent: NIST-standard ML-KEM and ML-DSA, SHA3, and a transparent FRI-STARK proof system with no trusted setup. It ships with a complete protocol specification and a runnable end-to-end demo (mint → shielded transfer → recipient decryption → double-spend rejection) that we executed successfully during this review.

**The thesis it proves:** post-quantum shielded payments are *feasible today* with standardized primitives and no exotic cryptographic assumptions. That de-risks the single biggest question an investor in this space has — "can it even be built?" — at the level of a working artifact rather than a whitepaper.

**What it is not:** a network. There is no peer-to-peer layer, no consensus, no persistence, no mempool, and no wallet product. The zero-knowledge proof is sound and transparent but **not yet zero-knowledge** (privacy-leaking), uses a **placeholder one-way function** in the circuit, and folds only one of four spend constraints into the proof. These are documented by the authors, well-understood, and addressable — but they are the difference between a demo and a system that can hold real value.

### Maturity at a glance

Legend: ✅ solid / production-grade choice · ⚠️ partial / works but not production-shaped · ❌ missing / deferred

| Dimension | Status | One-line read |
|---|---|---|
| Post-quantum primitive choices | ✅ | FIPS 203/204 + SHA3 + transparent STARK; no ECDLP anywhere |
| Cryptographic engineering (own code) | ⚠️ | Clean, tested, but unaudited; 3 documented proof-system gaps |
| Proof system (FRI-STARK) | ⚠️ | Real and verifying, but not yet ZK; placeholder relation; partial circuit |
| End-to-end protocol logic | ✅ | Full lifecycle works; 35 tests pass |
| Wallet / user experience | ⚠️ | CLI demo only; no recovery, no product UX |
| Node / consensus / networking | ❌ | In-memory single-process simulator; no P2P, no persistence |
| Operations (deploy/monitor/CI) | ❌ | No CI, Docker, logging, or metrics |
| Documentation | ✅ | Strong spec; gaps are disclosed, not hidden |

**Verdict:** A high-quality research artifact and feasibility proof. The cryptographic core is credible and built on standards. Reaching mainnet is a substantial but well-scoped engineering program (estimated ~12–18 months, 4–6 specialists, plus external audit) — see §9. **Do not put real funds near version 0.1.**

---

## 2. What Lattica Is (General)

### The problem
Privacy coins like Zcash let users transact without revealing amounts, recipients, or the spend graph. That privacy is enforced by zero-knowledge proofs and commitments whose **soundness depends on the elliptic-curve discrete-log problem (ECDLP)**. A cryptographically relevant quantum computer running Shor's algorithm solves ECDLP efficiently, which would — in rough order of severity — break the soundness of the proof system, the binding of value commitments, the unforgeability of spend signatures, and the confidentiality of the ECDH key agreement used to encrypt notes. This is not a fringe concern: Zcash's own roadmap treats post-quantum migration as a central long-term threat, with quantum-recoverable wallets targeted for 2026 and a broader transition ("Project Tachyon") aimed at ~2027.

The threat is also retroactive for confidentiality: encrypted data captured today can be stored and decrypted later once quantum hardware exists ("harvest now, decrypt later"). For a privacy chain, that means transaction confidentiality has a shelf life unless the cryptography is post-quantum *now*.

### The approach
Lattica asks the clean-slate question: *if you started today with no backward-compatibility constraint, what would a fully post-quantum shielded protocol look like?* It preserves Zcash's privacy model — shielded amounts, shielded recipients, and spend-graph unlinkability via nullifiers — while removing every quantum-vulnerable primitive.

### Value proposition
- **Quantum-safe by construction.** No component depends on discrete-log or factoring hardness. Security reduces to hash collision/preimage resistance, module-lattice hardness (MLWE/MSIS), and 256-bit symmetric strength.
- **No trusted setup.** The proof system is a transparent FRI-STARK; there is no toxic-waste ceremony that, if compromised, would let an attacker forge money. This is a meaningful governance and trust advantage over SNARK-based designs.
- **Standards-based.** Key agreement and signatures use NIST FIPS 203 (ML-KEM) and FIPS 204 (ML-DSA) via audited libraries, not home-grown cryptography.

### Primitive mapping (Zcash → Lattica)

| Concern | Zcash today (quantum-vulnerable) | Lattica (post-quantum) |
|---|---|---|
| Zero-knowledge proof | Halo 2 / Groth16 over Pasta / BLS12-381 | FRI-STARK (Winterfell); hash-soundness, transparent |
| Note encryption | ECDH on Jubjub | ML-KEM-768 (FIPS 203) + ChaCha20-Poly1305 |
| Signatures | RedPallas / ECDSA | ML-DSA-44 (FIPS 204) |
| Value balance | Homomorphic Pedersen commitments | Checked inside the proof over cleartext values |
| Commitments / nullifiers | Sinsemilla / curve-based PRF | SHA3 (PoC) → arithmetization-friendly hash in-circuit |
| Proof-of-work (consensus) | Equihash | Hash-PoW with doubled output width (Grover margin) — *specified, not built* |

---

## 3. Architecture & Scope

### Workspace
A six-crate Cargo workspace, Rust 1.85+, ~1,750 lines of implementation. The dependency graph is clean and layered: primitives → tree/tx → circuit → node → wallet.

| Crate | Responsibility |
|---|---|
| `lattica-primitives` | ML-KEM-768, ML-DSA-44, SHA3 domain-separated hashing, commitments, nullifiers, PRF, KDF, ChaCha20-Poly1305 AEAD |
| `lattica-tree` | Incremental Merkle commitment tree (depth 32 → 2³² note capacity) with empty-subtree pruning and authentication paths |
| `lattica-tx` | Notes, key hierarchy, addresses, ML-KEM note encryption / trial decryption |
| `lattica-circuit` | FRI-STARK spend-authorization proof (Winterfell) |
| `lattica-node` | In-memory chain state and `verify_and_apply` transaction-validation rules |
| `lattica-wallet` | CLI: `keygen`, `demo` (narrated end-to-end transfer), `bench` |

### Tech stack
Rust + Cargo. Cryptography is delegated to standards-tracking crates rather than hand-rolled: `fips203` (ML-KEM-768), `fips204` (ML-DSA-44), `sha3`, `chacha20poly1305`, and `winterfell` 0.13 for the FRI-STARK prover/verifier. This is the right instinct — the project does not reimplement any primitive itself.

### What works end-to-end today (verified in this review)
We ran `cargo test --workspace` (**35 tests, all passing**) and the `demo` command. The demo executes the complete shielded lifecycle:
1. **Mint** 1000 units to Alice as a shielded note; commitment inserted into the tree; Alice trial-decrypts to confirm value.
2. **Transfer** 900 to Bob with a 100 fee — produces a real FRI-STARK authorization proof (~27 KB), an ML-DSA binding signature, and an ML-KEM-encrypted output note. Total transaction ~31 KB.
3. **Validation** — the node checks binding signature, Merkle membership, nullifier-unseen, STARK proof, and value balance, all-or-nothing, and accepts.
4. **Scan** — Bob trial-decrypts on-chain notes and recovers his 900.
5. **Double-spend** — replaying the same transaction is rejected (nullifier already spent).

### What is deliberately out of scope (the PoC boundary)
`lattica-node` is an **in-process, in-memory state validator**, not a full node. There is no networking, mempool, block production, proof-of-work/stake, persistence, or RPC. The consensus shell (block format, PoW with Grover margins, fee market) is *specified* in `SPEC.md §9` but not implemented. In short: Lattica today is a **single-node consensus simulator** that demonstrates the per-transaction rules; the distributed-system shell around it is future work.

---

## 4. Security Posture

This is the heart of the assessment. The honest summary: **the cryptographic design and primitive choices are credible and standards-based; the proof-system implementation has three disclosed gaps that are production blockers; and none of Lattica's own code has been independently audited.**

### 4.1 Post-quantum primitives — credible
| Primitive | Standard / strength | Use |
|---|---|---|
| ML-KEM-768 | FIPS 203, NIST Level 3 | Note-encryption key agreement (ek 1184 B, ct 1088 B) |
| ML-DSA-44 | FIPS 204, NIST Level 2 | Transaction binding signatures (pk 1312 B, sig 2420 B) |
| SHA3-256 | FIPS 202, domain-separated | Commitments, nullifiers, PRF, KDF, Merkle nodes |
| ChaCha20-Poly1305 | 256-bit key (~128-bit PQ via Grover) | Authenticated note encryption |
| FRI-STARK (Winterfell) | Hash-soundness, transparent | Spend-authorization proof; no trusted setup |

All five are appropriate, standardized choices, used through audited libraries. There is **no elliptic-curve dependency and no trusted setup anywhere** — the central design claim holds up under code review. The security assumptions reduce to hash collision/preimage resistance, MLWE/MSIS lattice hardness, and 256-bit symmetric strength — all currently believed quantum-safe.

Note the deliberate design choice on **value balance**: Lattica drops Zcash's homomorphic Pedersen commitments (which rely on a group structure) in favour of a plain hash commitment, and instead enforces `sum(inputs) == sum(outputs) + fee` *inside the proof* over cleartext values. This is sound and removes a curve dependency; it does, however, make balance correctness contingent on the circuit being complete (see gap 3 below).

### 4.2 The three documented production gaps (proof system)
These are disclosed by the authors in `SPEC.md §8` and confirmed in `lattica-circuit`. They are the difference between "sound demo" and "private money."

1. **Not yet zero-knowledge.** Winterfell STARKs as used here are *sound and transparent but not zero-knowledge* — the low-degree extension of the execution trace can leak information about the witness. For a privacy protocol this is material: the proof itself could leak data about the spender. The fix (standard ZK randomization — masked trace / random columns) is well-understood and supported by the proving framework, but it is **not yet enabled**.

2. **Placeholder one-way relation.** The authorization circuit currently proves knowledge of a secret through an *algebraic* transition (`x → x³ + C`) chosen for clarity. This is **not cryptographically one-way** — it is algebraically invertible — so in the current PoC the authorization relation does not provide real spend security. Production must substitute a vetted arithmetization-friendly hash (e.g. Poseidon2 or Rescue, with margins for recent Poseidon cryptanalysis). This is the single most important cryptographic item before any real value is at stake.

3. **Only one of four constraints is in-circuit.** The STARK currently proves only spend authorization (constraint 3). The other three — Merkle membership, nullifier correctness, and value balance — are enforced *natively by the node* rather than inside the proof. End-to-end validation is therefore complete and correct *for a trusted validator*, but full zero-knowledge soundness requires folding all four constraints into a single AIR. The authors argue, plausibly, that this is additive engineering rather than a redesign, since the same commitment/nullifier/Merkle framing is reused.

### 4.3 Parameter and process caveats
- **Field size and soundness.** The circuit uses a 128-bit field with proof options the code itself annotates as *"~conjectured 100+ bit security; tune for production."* Acceptable for a PoC; not a basis for securing funds. Production needs a deliberate parameter-selection exercise with a written soundness argument.
- **Signature level.** ML-DSA-44 (Level 2) is chosen for compact signatures; the spec notes production may raise to ML-DSA-65/87 for higher margins.
- **Key derivation.** For PoC clarity, ML-KEM/ML-DSA keypairs are generated from the OS CSPRNG and stored *beside* the seed rather than derived deterministically from it (`crates/lattica-tx/src/keys.rs`). Consequence: **the 32-byte seed alone cannot currently restore a wallet.** Both schemes support seeded keygen, so this is a known, straightforward fix.
- **No external audit.** Only the *wrapped dependencies* (the NIST/RustCrypto crates) carry external review. Lattica's own circuit, transaction logic, and integration code have **not** been independently audited. No formal verification, fuzzing, property-based tests, or known-answer test vectors are present — test coverage is solid happy-path-plus-tampering unit tests (see §7), but not adversarial-grade.

### 4.4 Threat-model summary
- **Quantum adversary:** addressed by design — no ECDLP/factoring assumptions.
- **Forgery of spends (today):** *not* prevented in the PoC because of the placeholder relation (gap 2). Must be closed before mainnet.
- **Privacy leakage via proofs (today):** possible because proofs are not yet ZK (gap 1).
- **Double-spend:** prevented by the nullifier set (verified working).
- **Malicious sender / mis-addressed notes:** defended — a decrypted note is accepted only if it re-commits to the on-chain commitment and is addressed to the recipient.
- **Side channels / constant-time:** the wrapped primitives may be constant-time, but Lattica's own code carries no explicit constant-time guarantees; this needs review during the audit phase.

---

## 5. User Friendliness

**Current state: developer demo, not a product.** This is appropriate for a PoC, but a CTO should size the wallet/UX work realistically — historically the hardest part of shipping a privacy coin is not the cryptography but safe, usable key and note management.

### What exists
- A single CLI binary with three subcommands: `keygen` (print an account), `demo` (narrated end-to-end transfer), `bench` (performance).
- The `demo` is genuinely good as *documentation*: it narrates every cryptographic step in plain language and is reproducible.
- Errors are modelled cleanly via a `TxError` enum with human-readable messages (`unknown anchor`, `double-spend`, `value imbalance`, …), which is a good foundation for real error UX.

### What a real product needs (gaps)
- **No persistent wallet.** State is ephemeral per process; there is no account store, no balance view, no note management.
- **No recovery story.** No BIP39/SLIP39 seed phrase, no encrypted wallet export, no hardware-wallet support. And per §4.3, the seed alone cannot yet reconstruct keys — a blocker for any recoverable wallet.
- **Unwieldy addresses.** An address is `ivk_tag(32 B) + kem_ek(1184 B) = 1216 bytes` of raw material — there is no bech32-style encoding, checksum, or QR-friendly form. Post-quantum keys are inherently large; production will need an addressing scheme (and likely a directory/alias layer) so users never copy-paste 1.2 KB blobs.
- **Scanning cost.** Recipients find their notes by trial-decrypting every on-chain note (O(chain size)). This is the standard shielded-wallet cost; at scale it needs the usual mitigations (view keys, light-client/oblivious scanning, batching).
- **Transaction size.** A 1-in/1-out transfer is ~31 KB today (≈27 KB proof + 2.4 KB signature + ~1.1 KB KEM ciphertext + note). This affects bandwidth, fees, and UX; proof recursion/folding is the known lever to amortize it (see §6 and §8).

---

## 6. Node Operator Information

**Current state: there is no operable node.** `lattica-node` is an in-memory validator used by tests and the demo, not a daemon an operator can run, sync, or monitor. Everything in this section is therefore mostly a description of *what must be built*, plus the one thing that is real and measurable: per-transaction validation performance.

### The validation core (the part that is real)
The node exposes `Chain::verify_and_apply(tx)`, which atomically checks, per transaction: binding signature (ML-DSA) → for each spend: known anchor, Merkle membership, nullifier-unseen, authorization STARK → value balance → then applies (record nullifiers, append commitments, publish new anchor). The consensus *rules* are clear, documented, and tested. This is the asset a production node would be built around.

### Measured performance envelope (re-run for this report)
Release build, single core, on the review machine:

| Metric | Measured (this machine) | SPEC reference |
|---|---|---|
| Prove (authorization) | 8.74 ms | ~12.7 ms |
| Verify (authorization) | 0.20 ms | ~0.4 ms |
| Proof size | 26,765 B (~26.8 KB) | ~26.8 KB |
| ML-DSA signature | 2,420 B | 2,420 B |
| ML-KEM ciphertext / note | 1,088 B | 1,088 B |

Sizes match the spec exactly; our timings were faster than the spec's reference machine. The headline operator-relevant fact is that **verification is cheap (~0.2 ms/proof)** — a validator can check many transactions per second — while **proofs are large (~27 KB)**, which dominates bandwidth and storage. For comparison, Orchard (Halo 2) proofs are ~3 KB and Sapling (Groth16) ~0.2 KB; Lattica trades ~10× proof size for transparency and quantum safety, with recursion/aggregation as the future amortization lever.

### Operator gap list (all deferred)
- **Persistence:** none — state is in-memory `HashSet`/`Vec`; lost on restart. Needs a real store (e.g. RocksDB) with a commitment-tree/nullifier-set schema.
- **Networking / P2P:** none. No peer protocol, gossip, or block sync.
- **Consensus shell:** specified (hash-PoW with doubled width for Grover margin, longest-chain selection) but unimplemented; PoS is named as an alternative.
- **Mempool / fee market:** none.
- **Block format:** specified (header commits to post-block anchor and nullifier-set root) but unimplemented.
- **Observability:** no structured logging, metrics, or health endpoints — output is `println!` to stdout.
- **Deployment:** no Dockerfile, systemd unit, config file, or tunable parameters (tree depth etc. are hardcoded).
- **CI/CD:** none — no automated test/build pipeline.

---

## 7. Production-Readiness Assessment

### Consolidated maturity matrix
| Area | Component | Status |
|---|---|---|
| Crypto primitives | ML-KEM-768, ML-DSA-44, SHA3, ChaCha20-Poly1305 | ✅ standards-based, via audited crates |
| Proof system | FRI-STARK, transparent, no trusted setup | ⚠️ sound but not ZK; placeholder relation; partial circuit |
| Commitment tree | Merkle, depth 32, PQ hash | ✅ implemented and tested |
| Note encryption | ML-KEM + AEAD, replay-bound, malicious-sender defended | ✅ implemented and tested |
| Tx validation rules | binding sig / membership / nullifier / proof / balance | ✅ implemented and tested (in a single validator) |
| Wallet / UX | CLI demo | ⚠️ demo-grade; no recovery, addressing, persistence |
| Node / consensus / net | in-memory simulator | ❌ no P2P, persistence, consensus, mempool |
| Operations | CI, logging, metrics, deploy | ❌ none |
| Assurance | tests / audit / formal methods | ⚠️ 35 unit+integration tests pass; no audit, fuzzing, KATs, or property tests |

### Ranked production blockers
1. **Replace the placeholder one-way relation** with a vetted arithmetization-friendly hash (Poseidon2/Rescue). *Without this, spend authorization is not secure.* (Cryptographic — highest priority.)
2. **Add zero-knowledge masking** to the proofs so they stop leaking witness information. (Cryptographic — privacy-critical.)
3. **Fold all four constraints into the AIR** so soundness is enforced by the proof, not the validator. (Cryptographic/protocol.)
4. **Select and justify production parameters** (field size, FRI queries, ML-DSA level) with a written soundness argument. (Cryptographic.)
5. **External security audit** of all of Lattica's own code. (Assurance — gating for mainnet.)
6. **Build the consensus + networking shell** (block format, PoW/PoS, P2P, mempool). (Distributed systems.)
7. **Add persistence** for chain state. (Systems.)
8. **Wallet productization** — deterministic key derivation from seed, recovery, addressing, scanning at scale. (Product.)
9. **Operations** — CI, logging, metrics, deployment tooling. (Ops.)

### Test coverage (assurance detail)
35 tests across the workspace, all passing: 16 in primitives (round-trips, tampering, domain separation), 6 tree, 5 tx (encryption, trial-decryption, malicious-sender), 4 circuit (valid proof, tamper rejection), 4 node (end-to-end lifecycle, double-spend, balance, signature). This is good for a PoC. It is **not** assurance-grade: no fuzzing, no property-based tests, no known-answer/test-vector suites, no CI gating, and adversarial coverage is limited to bit-flip tampering.

---

## 8. Risk Register

Likelihood (L) and Impact (I): Low / Med / High. Risks are about reaching *production*, not about the PoC's stated scope.

| # | Risk | L | I | Mitigation |
|---|---|---|---|---|
| R1 | Authorization relation remains insecure (placeholder `x³+C`) if rushed | Low | High | Prioritize Poseidon2/Rescue swap; treat as gating before any real value; external crypto review of the chosen hash and its parameters |
| R2 | Proofs leak witness data (not yet ZK) | Med | High | Enable Winterfell ZK randomization (masked trace/random columns); add tests that assert non-leakage properties |
| R3 | Soundness gap from partial circuit / small field / conjectured parameters | Med | High | Fold all four constraints into the AIR; commission a parameter-selection study with a written soundness bound; consider larger field/extension |
| R4 | Unaudited own-code contains exploitable bugs | Med | High | Independent security audit; add fuzzing, property tests, and KAT vectors before audit to maximize its value |
| R5 | Proof/tx size (~27 KB/~31 KB) limits throughput, raises fees and bandwidth | High | Med | Implement FRI folding/recursion and batched actions; size the consensus parameters (block size, fees) around it |
| R6 | Consensus/networking is greenfield — schedule and correctness risk | High | High | Reuse a proven consensus stack rather than inventing; staged testnets; the per-tx rules are already specified and tested, lowering integration risk |
| R7 | Wallet key-recovery gap (seed can't restore keys; no mnemonic) | High | Med | Switch to deterministic seeded keygen (both schemes support it); add BIP39/SLIP39 and encrypted backup |
| R8 | UX of 1.2 KB addresses / large keys deters adoption | Med | Med | Design an encoded address format + alias/directory layer; QR and checksum support |
| R9 | Specialist talent dependency (PQ + STARK + privacy + consensus is a rare skill set) | Med | High | Budget for senior cryptography hires/consultants early; the standards-based choices reduce bespoke-crypto risk |
| R10 | PQ standards or cryptanalysis shift (e.g. Poseidon analysis, ML-DSA params) | Low | Med | Standards-tracking dependencies and parameter agility; design for primitive upgradability |

---

## 9. Roadmap to Production

> Estimates assume a focused, well-funded team and run several workstreams in parallel. They are planning figures, not commitments. Cryptography and audit are on the critical path; build the consensus shell in parallel.

**Phase 1 — Cryptographic hardening (≈3–5 months; 2–3 cryptography engineers).**
Close the three documented proof-system gaps: swap in a vetted arithmetization-friendly hash (R1), enable ZK masking (R2), and fold all four constraints into a single AIR (R3). Choose and document production parameters (field, FRI queries, ML-DSA level). Add fuzzing, property tests, and KAT vectors. *Exit criteria:* a fully zero-knowledge, fully in-circuit spend proof with a written soundness argument.

**Phase 2 — Protocol & consensus shell (≈4–6 months; 2–3 distributed-systems engineers, parallel to Phase 1).**
Implement block format, the PoW (with Grover margins) or PoS layer, P2P networking, mempool, and a persistent state store (commitment tree, nullifier set, anchors). Stand up a multi-node testnet. *Exit criteria:* multiple nodes reach consensus on shielded blocks over a network and survive restarts.

**Phase 3 — Wallet & UX (≈3–4 months; 1–2 engineers + design, overlapping Phase 2).**
Deterministic seeded key derivation (R7), mnemonic backup/recovery, an encoded address format with checksums (R8), persistent wallet with balances and note management, and scalable scanning (view keys / light client). *Exit criteria:* a non-expert can create, back up, restore, send, and receive on the testnet.

**Phase 4 — Operations, audit & hardening (≈2–3 months, with external audit running across Phases 1–3).**
CI/CD, structured logging, metrics, deployment tooling; performance and aggregation work to bring proof/tx size down (R5); and an **independent security audit (R4)** of all own-code plus a parameter review. *Exit criteria:* a clean external audit and an incentivized public testnet ahead of any mainnet decision.

**Indicative total:** ~12–18 months, a peak team of ~4–6 specialists plus external audit. The dominant risks are consensus/networking execution (R6) and securing scarce PQ-cryptography talent (R9) — not the feasibility of the cryptography, which this PoC has already demonstrated.

### Recommended next funded milestone
Fund **Phase 1 (cryptographic hardening) plus an audit-readiness pass** as a discrete, ~4–6 month deliverable. It is the highest-leverage spend: it converts the proof system from "sound demo" to "secure, private, and externally reviewable," directly retiring risks R1–R4 — the risks that actually gate whether real value can ever be at stake. It is also independently meaningful to a technical buyer or partner even before the consensus shell exists.

---

## 10. Competitive Positioning

| Project / approach | Privacy model | Post-quantum stance | Trusted setup | Note |
|---|---|---|---|---|
| **Lattica** | Full shielded (amounts, recipients, spend graph) | **Fully PQ, clean-slate** (lattice + hash) | **None** (transparent STARK) | PoC; standards-based; pays a proof-size cost |
| Zcash + "Project Tachyon" | Full shielded | PQ *transition* of an existing curve-based chain | Historically yes (Sapling); migrating | Mature network; retrofitting PQ onto deployed cryptography and a large value base |
| QRL | Transparent (hash-based signatures, XMSS) | PQ signatures | None | PQ but **not a shielded/private** protocol — different problem |
| Generic STARK L2s (e.g. zk-rollups) | Usually not private | Hash-based proofs are PQ-leaning | None | Optimized for scaling, not for shielded payments |

**Where Lattica differentiates:** it is, to the standard of a working artifact, a *fully* post-quantum *and* fully shielded design with *no trusted setup* — the intersection few others occupy. Zcash is far more mature but is migrating an existing curve-based system (with the inertia, compatibility, and harvest-now-decrypt-later exposure that implies); QRL is post-quantum but transparent, not private; generic STARK systems are post-quantum-leaning but aimed at scaling rather than privacy.

**Where it pays a cost:** post-quantum primitives and FRI proofs are large. ~27 KB proofs and ~31 KB transactions, 1.2 KB addresses, and ~1 KB ciphertexts per note are the price of dropping elliptic curves. Recursion/aggregation can amortize the proof cost, but Lattica will not match the byte-efficiency of curve-based SNARKs — its edge is quantum safety and trust-minimization, not compactness.

**Strategic read:** Lattica is positioned for a future in which the quantum threat is taken as a design requirement from day one, rather than retrofitted. Its value is highest to anyone who needs *durable* transaction privacy — confidentiality that survives the arrival of quantum computers — and who is willing to trade bytes for that guarantee.

---

## 11. Bottom Line / Recommendation

**What is de-risked.** The hardest conceptual question — *can a Zcash-style shielded protocol be built with no elliptic-curve dependency, using standardized post-quantum primitives and no trusted setup?* — is answered **yes**, at the level of a clean, tested, runnable implementation with a thorough specification. The primitive choices are sound, the engineering is disciplined (no hand-rolled crypto), and the authors are commendably honest about what is and isn't done.

**What is unproven.** Everything between a sound demo and a live network: a *secure* (real one-way relation) and *private* (zero-knowledge) proof, production parameters with a soundness argument, an independent audit, and the entire distributed-system shell (consensus, networking, persistence) plus a usable wallet. None of these are blocked by a fundamental unknown; they are scoped engineering and assurance work.

**Recommendation.** Treat version 0.1 as a **successful feasibility proof and a strong technical foundation — not as software to put value into.** The highest-leverage next step is to fund cryptographic hardening to an audit-ready state (Phase 1, ~4–6 months), which retires the security-gating risks and produces something a technical partner or acquirer can evaluate on its own. Stand up the consensus and wallet workstreams in parallel only once that funding and the specialist cryptography talent are secured. The technology bet here is credible; the remaining risk is execution and assurance, not science.

---

*Prepared from a direct review of the Lattica source, specification, and a local re-run of its test suite (35 tests passing) and benchmarks. In the Zig port these are reproducible via `zig build test` and `zig build run -Doptimize=ReleaseFast -- bench`. (The performance figures in §6 are from the original Winterfell FRI-STARK reference; the Zig port stubs the proof, so only the ML-DSA / ML-KEM sizes apply to it directly.)*
