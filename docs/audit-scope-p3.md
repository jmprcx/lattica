# Lattica spend circuit — external audit scope, threat model & readiness (Plonky3 stack)

Auditor handoff for the **production** proving stack (`lattica-prover-p3/`). It defines what is in
scope, the trust/threat model, the frozen parameters, known limitations, and the pre-audit readiness
checklist. Companion docs: `docs/soundness-budget.md` (C-04), `docs/plonky3-port-plan.md` (how the
circuit was built), `docs/remediation-status.md` (audit-finding tracker), `docs/audit-scope.md` (the
older *Winterfell* reviewer guide — reference only; superseded by this for production).

> **Status: NOT YET READY FOR AUDIT.** This document is the scope/threat artifact only. The circuit
> still has open soundness items (§5) and is **1-in/1-out**, whereas the audited target is
> **join-split N-in/M-out** (§6). The audit should run against the artifact described in §3/§6 once
> §5 and §7 are complete.

## 1. Scope

**In scope (to be audited):**
- The circuit: `lattica-prover-p3/src/{poseidon2_air,spend_air,full_spend_air}.rs` — the AIR
  constraints, trace generation, periodic columns, and the cross-region binding.
- The verifier boundary: `lattica-prover-p3/src/lib.rs` — `lattica_spend_verify` C ABI, the
  `SpendPublicInputs` parsing, canonical field-element checks, fail-closed behavior, proof
  (de)serialization.
- The Zig protocol seam: `src/ffi.zig` (ABI shape), `src/protocol.zig` (tx encoding, supply model,
  tx-binding digest), `src/codec.zig` (canonical encoding) — **specifically the requirement that the
  on-chain hashes equal the in-circuit hashes** (see §5 / C-03).
- The frozen parameter set and proof format (§4).

**Out of scope (this round):**
- Recursive / batch aggregation (`batch_measure` is a measurement prototype, not production).
- The live consensus node (`rubble-node-zig`) beyond the verify seam; networking; mempool; P2P.
- The wallet/prover key management and note-discovery.
- Performance (covered by `docs/soundness-budget.md`; not a security gate).

**Reference only (not audited as production):** the Winterfell `lattica-prover/` crate — kept as a
differential oracle for the hashes, not a production artifact.

## 2. Trust model & assumptions

- **Roles.** The **prover** (wallet) is fully untrusted. The **verifier** (node, via
  `lattica_spend_verify`) is the security boundary. A spend proof is a *validity witness*; the node
  enforces the stateful checks the proof does not (nullifier-set non-membership = double-spend
  prevention; anchor is a known tree root; fee policy).
- **Cryptographic assumptions.**
  - **Poseidon2-Goldilocks** (vetted `p3-goldilocks` constants) modeled as collision-resistant /
    random-oracle-like. *A dedicated Poseidon2 parameter & algebraic-attack review is explicitly
    requested as part of this audit.*
  - **FRI / STARK soundness** per ethSTARK (2021/582) and the proven bounds (2024/1553, 2025/2055);
    Fiat–Shamir in the ROM. Soundness level **≈103-bit proven / ~127-bit conjectured**, machine-
    checked (`docs/soundness-budget.md`, `production_security_budget` test).
  - **Transparency:** no trusted setup. **Post-quantum:** no elliptic curves / pairings. Stable Rust.
- **What the proof guarantees** (for one spend, current 1-in/1-out — generalized in §6): there exist
  hidden `(nk, value, rho, rcm, path)` such that the spent note `cm = H(recipient,value,rho,rcm)`
  with `recipient = H(nk)` is a leaf at the proven path under the public `anchor`; the revealed `nf`
  is its nullifier; the public `out_cm` commits to `out_value`; `value = out_value + fee`;
  `value, out_value < 2^BITS`; and the proof is bound to the public `tx_binding`.
- **What the proof does NOT guarantee (node's responsibility):** `nf` not already spent; `anchor` is
  a valid historical root; `fee` matches policy; transaction-level authorization/signatures outside
  the shielded statement.

## 3. The statement under audit (current artifact)

Eight Poseidon2 blocks, height 2048, hiding (ZK) FRI PCS. Public inputs (17 field elements):
`root(4) ‖ nf(4) ‖ out_cm(4) ‖ fee(1) ‖ tx_binding(4)`.

| # | Region | Constraint |
|---|---|---|
| 0 | ownership | `recipient = H(nk)` (4-element digest) |
| 1 | commitment | `cm = H(recipient, value, rho, rcm)` |
| 2..5 | membership | `cm` folds up a **general-position** depth-`DEPTH` path to the public `root` |
| 6 | nullifier | `nf = H(nk, rho, pos)` (public) |
| 7 | output | `out_cm = H(out_recipient, out_value, out_rho, out_rcm)` (public) |
| — | balance | `value = out_value + fee` |
| — | range | `value, out_value < 2^BITS` (running-remainder; no wraparound mod p) |
| — | tx-binding | bound via Fiat–Shamir (public input) |

Cross-region binding uses **persistent columns** (`nk, rho, value, out_value`, constant across the
trace, pinned per block) and **period-256 one-hot boundary selectors**; within-block Poseidon2 rounds
use the period-32 round schedule. Hash inputs use the **vetted** Poseidon2-Goldilocks constants, so
the in-circuit hash equals the protocol's native `Poseidon2Goldilocks` (differential-tested).

## 4. Frozen parameters & proof format

| Item | Value |
|---|---|
| Base field | Goldilocks `p = 2^64 − 2^32 + 1` |
| Challenge field | `F_p²` (BinomialExtensionField, degree 2) |
| Hash | Poseidon2, width 8, S-box `x^7`, 8 full + 22 partial rounds, vetted `GOLDILOCKS_POSEIDON2_RC_8_*` |
| Merkle/leaf hash | Poseidon2 sponge/compression, 4-Goldilocks digest |
| FRI | `log_blowup=4`, `num_queries=96`, `query_pow=16`, `commit_pow=0`, `max_log_arity=4`, `cap_height=6` |
| Soundness | ≈103-bit proven / ~127-bit conjectured |
| Circuit params | `DEPTH=32`, `BITS=52`, `recipient`=4-element digest |
| Proof serialization | postcard; `SpendPublicInputs` = `anchor‖nullifier‖out_cm‖tx_binding (4×32) ‖ fee(8 LE)` = 136 bytes |
| Proof size / verify | ~421 KB / ~8 ms (single spend, `DEPTH=32`) |

These freeze for the audited artifact. Join-split (§6) adds `N` (inputs) and `M` (outputs)
parameters and widens the public inputs accordingly; the freeze is re-confirmed once §6 lands.

## 5. Known limitations & open items (must close before audit)

Tracked in detail in `docs/remediation-status.md`. The soundness-relevant ones:

- **A1 — position-consistency.** `nf = H(nk, rho, pos)` uses `pos` as a *free* witness; it is **not**
  yet tied to the membership path's position bits. Must constrain `pos` ↔ the proven path (or remove
  `pos` from the nullifier) to prevent position/nullifier mismatch. **Open.**
- **A2 — domain separation.** The four hashes share one permutation with zero-padding and **no
  per-hash domain tag**; cross-context collisions are a theoretical attack. Add domain constants
  (and mirror them on the protocol side). **Open.**
- **A3 — fee soundness.** `fee` is a public input and is **not** range-checked in-circuit; decide
  trusted-from-node vs constrain `fee < 2^BITS`. **Open.**
- **A4 — nullifier-derivation argument.** A written analysis that `nf` derivation resists
  faerie-gold / nullifier-collision attacks. **Open.**
- **C-03 — protocol/circuit hash match.** `src/{tx,primitives}.zig` still hash with SHA3; the
  on-chain `noteCommitment`/`nullifier`/Merkle **must** switch to the exact in-circuit
  Poseidon2-Goldilocks layouts (incl. A2 domain tags), guarded by shared known-answer vectors.
  **Open** (the seam is unaudited until matched).
- Single-asset; no memo field; coinbase/mint/burn not yet modeled (§6).

## 6. Audit target shape — **join-split (N-in / M-out)** *(decision: 2026-06-26)*

The audited circuit will be generalized from the current 1-in/1-out spend to a **join-split**:
- **N input notes**, each with ownership (`recipient = H(nk)`), commitment opening, membership under a
  **shared `anchor`**, and a revealed **nullifier `nf_i`**.
- **M output notes**, each a published commitment `out_cm_j` binding `out_value_j`.
- **Value balance:** `Σ_i in_value_i = Σ_j out_value_j + fee`, with every `in_value_i`, `out_value_j`
  range-checked (no wraparound).
- **One `tx_binding`** for the whole transaction.

Open design questions to settle as part of the generalization (and to state for the auditor):
- Fixed `(N, M)` vs a small set of supported shapes vs padded-variable; trace-height implications
  (each input ≈ ownership+commitment+membership blocks; each output ≈ one block).
- Public-input growth (`N` nullifiers + `M` output commitments + `anchor` + `fee` + `tx_binding`),
  and whether to commit them via an **aggregate public-input hash** (keeps the public-input vector
  bounded and dovetails with future per-block batching).
- Per-input distinct `nk`/`rho` (the persistent-column binding becomes per-input, not global).

This is a material redesign; auditing 1-in/1-out and then redesigning would force a re-audit, so the
generalization lands **before** the audit.

## 7. Pre-audit readiness checklist

| Item | Status |
|---|---|
| Full spend statement, ZK, on stable (M1–M5) | ✅ |
| C-04 soundness budget (machine-checked) | ✅ |
| Production parameters + proof-size tuning | ✅ |
| Differential vs native Poseidon2 oracle | ✅ (per-region) |
| Verifier ABI fail-closed tests | ✅ (basic) |
| **A1 position-consistency** | ❌ |
| **A2 domain separation** | ❌ |
| **A3 fee soundness** | ❌ |
| **A4 nullifier-derivation argument** | ❌ |
| **B — join-split (N-in/M-out) generalization** | ❌ (decided; not built) |
| **C-03 protocol↔circuit hash match + shared KATs** | ❌ |
| **End-to-end FFI integration test** (Zig: mint→prove→verify→double-spend) | ❌ |
| **Constraint-accounting self-audit** (every column/constraint, no vacuous binding) | ❌ |
| ABI fuzz / adversarial tests (beyond fail-closed) | ❌ |
| Threat model + scope + frozen params (this doc) | ✅ |

## 8. Reproduce / verify

- `cd lattica-prover-p3 && cargo test --release` — 22 tests (circuit, ABI, security budget).
- `cargo run --release --bin lattica-prover-p3` — end-to-end demo (M1/M2 + M4a/b/c + C-04 report).
- `cargo run --release --bin sweep` / `--bin batch` / `--bin field_compare` — parameter / batch /
  field measurements behind `docs/soundness-budget.md`.
- `production_security_budget` test gates proven ≥ 100, conjectured ≥ 128.
- Native-hash differential checks: the `native_*` tests in each circuit module.
