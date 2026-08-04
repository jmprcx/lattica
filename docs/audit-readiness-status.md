# Lattica — audit-readiness status & roadmap

> **Document role:** Current status summary. The audited artifact is the `v3-batch-audit` tag; uncommitted or later changes require separate review.

**Status (2026-07-06): COMPLETE — W1–W10 done; artifact frozen at the `v3-batch-audit` tag.** Batch aggregation has a constraint-by-constraint audit (`batch-constraint-audit.md`), C-ABI verifier fuzz (`tests/fuzz_batch.rs`), a four-lens internal adversarial round + remediation (`v3-batch-internal-audit.md` — no critical/high break; F1/F2 fixes), an evidence pass, and a handoff (`v3-batch-audit-handoff.md`). The tagged tip **additionally carries the full external-scope security audit** (`v3-external-audit-report.md` — five adversarial lenses over the join-split + HTLC circuits, the C-ABI/verify boundary, the Zig node, and crypto/ZK: no critical/high) **and its M-EXT-1 (proof malleability) + L-node (mint parity) remediations**, all re-validated (Rust 102 passed / 0 failed, `zig build test` green). The production CPU path is audit-ready; recursion/GPU/streaming stay research/out-of-gate. Entry points: `docs/AUDITORS.md` + `docs/v3-batch-audit-handoff.md` + `docs/v3-external-audit-report.md`; closed findings in `docs/remediation-status.md`.

## 1. Assessment — the three questions

**1.1 Is the CPU prover production-ready? — Yes, within the frozen scope.** There is one production config (`lattica-prover-p3/src/config.rs` — `HidingFriPcs` over the CPU `Radix2DitParallel` DFT + salted `MerkleTreeHidingMmcs`, four random codewords, FRI `log_blowup=4` / `96` queries / `pow_bits=16` / `cap_height=6`), one canonical serializer, and one fail-closed verification core. The four production circuits and the ten-symbol ABI frozen at `v3-batch-audit` funnel through it. The current branch's additional proof-tree container seam is later development and is not automatically audited.

**1.2 Are the GPU / streaming / recursion implementations production-ready? — No.** All three are opt-in and outside the frozen audit. The ABI-symbol gate confirms that no recursion symbol enters the default static library. GPU and streaming remain alternative proving backends under the unchanged verifier. The twelve-symbol development ABI includes a non-recursive proof-tree container, not the feature-gated recursive aggregator.

**1.3 Has the codebase been refactored for simplicity/auditability? — Yes, essentially complete.** The 2026-07-02 A1–I8 whole-crate refactor added a constraint-fingerprint oracle (`src/constraint_fingerprint.rs`) that mechanically pins every production AIR's `(width, periodic, publics, n_constraints, max_degree, fnv)` so any motion/dedup is provably constraint-preserving; single-sourced the FRI config + domain tags (killing 8×/6× literal duplication); deleted a ~150-line duplicated constraint fork (`eval_spend`); collapsed the ABI to one fail-closed core; split the 8,181-line monolith into six files; and quarantined every superseded AIR behind `cfg(test)`. Production code now carries **0 TODO/FIXME, 1 clippy-allow, 2 dead-code allows**. The only deferred item is test-only churn inside the research recursion module — no open production-refactor work.

## 2. Frozen baseline and later development

The original `v3-audit` artifact was followed by a 222-commit production delta containing batch aggregation, a constraint-fingerprint-guarded crate refactor, and exchange deposit mode. That delta completed the W1–W10 review track below and is frozen at `v3-batch-audit`.

The tag, rather than the mutable branch tip or a dirty working tree, is the reproducible audit baseline. Later changes must preserve the frozen ABI and constraint fingerprints or receive explicit delta review. Feature-gated GPU, streaming, and recursion work remains outside the baseline even when its tests pass.

At RC `8be9b17`, the default suite reported **102 passed / 20 ignored**, all 20 ignored audit gates passed when run explicitly, the ABI-symbol gate confirmed ten production externs and zero recursion symbols, and the real Zig/Rust integration passed the individual and batch paths. The subsequent external-scope audit and remediations are included in the tagged artifact.

## 3. Roadmap — the batch-delta audit-readiness track (W1–W10)

| WS | What | Status | Artifact |
|---|---|---|---|
| **W1** | Feature-gate research (recursion/gpu/stream) out of the production staticlib + an ABI-symbol gate | ✅ | `lattica-prover-p3/scripts/check-abi-symbols.sh` (green) |
| **W2** | Batch C-ABI fuzz / adversarial tests | ✅ | `lattica-prover-p3/tests/fuzz_batch.rs` (`772dffb`) |
| **W3** | Batch constraint-by-constraint self-audit | ✅ | `docs/batch-constraint-audit.md` (`b87fe4f`) |
| **W4** | Audit-doc truth pass — stale claims / scope / repro numbers | ✅ | `AUDITORS.md`, `audit-scope-p3.md`, `production-readiness.md` (`d97c1f1`) |
| **W5** | Internal adversarial round on the batch delta (4 lenses) | ✅ | `docs/v3-batch-internal-audit.md` (`8be9b17`) |
| **W6** | Fix wave (F1 verify-cap, F2 overflow, OBS-1 debug-panic, OBS-2 oracle) | ✅ | `8be9b17` (validated green) |
| **W7** | Full gate-run evidence pass at the RC commit | ✅ | RC `8be9b17`: 102/20, `--ignored` 20, ABI gate + real integration green |
| **W8** | New external handoff for the batch tip | ✅ | `docs/v3-batch-audit-handoff.md` |
| **W9** | Final consistency sweep | ✅ | this doc |
| **W10** | Maintainer tags `v3-batch-audit` (freeze the artifact) | ✅ | tagged `v3-batch-audit` (this commit) |

The batch-delta track is **complete (W1–W10)** and the artifact is frozen at the `v3-batch-audit` tag,
which also carries the full external-scope audit + its remediations. Scope was the **production-surface
delta only** — recursion/GPU/streaming research are explicitly out.

## 4. Standing auditor sign-off items

- **~103-bit *proven* soundness** (~127 conjectured) — the Goldilocks `F_p²` ceiling; raising it is a field migration. Machine-checked (`proven_security_meets_production_floor`, asserts ≥100). **The one deliberate parameter needing explicit auditor acceptance** (`docs/soundness-budget.md`).
- **A dedicated Poseidon2 parameter / algebraic-attack review** — requested in `audit-scope-p3.md` §2, deferred to audit time (the RO/CR assumption underpins every hash binding).
- **A4 residuals** — the untagged Merkle `merge` (collision would need a Poseidon2 preimage/collision) and the **`rho`-uniqueness invariant on note creation** (a protocol-level assumption flagged for the auditor).
- **Batch ABI fuzz / adversarial coverage** — the four batch externs have round-trip + fail-closed tests but no mutation fuzz yet (= W2).

## 5. Scope — out of the lattica audit gate (reaffirmed)

- **Host chain `rubble-node-zig`** — block consensus/PoW/mempool/networking/emission, reorg undo, header-committed roots, and the 8 production release gates in `docs/full-node-security-integration.md`. `node.zig` here is an in-memory state machine; the lattica-side P-01 enablers (`stateRoot`/`eventRoot`/`positionOf`/`applyHtlc` height-pinning) are built for the host chain to bind.
- **Cross-chain `rubble-xchain-xfer`** — the HTLC engine / swap protocol / Phase-B `await_lock`/timeout cushion.
- **GPU / streaming / recursion** — research, feature-gated, verified under the prod verifier (§1.2).
- **Wallet / prover key management + note discovery.**

## 6. Doc hygiene + batch-delta artifacts + see also

The doc-truth pass (W4) corrected stale claims that would mislead an auditor: the reproduction test counts in `AUDITORS.md` §3, the "coinbase/mint/burn not yet modeled" line and the C-03 checklist row in `audit-scope-p3.md`, an explicit out-of-scope listing for GPU + streaming, a hardened historical banner on `production-readiness.md`, and the crate-relative path to `check-abi-symbols.sh`.

**Batch-delta audit artifacts (W2–W8):** `docs/v3-batch-audit-handoff.md` (the handoff — start here for the delta), `docs/batch-constraint-audit.md` (constraint-by-constraint audit), `docs/v3-batch-internal-audit.md` (the four-lens adversarial round + F1/F2 remediation), `lattica-prover-p3/tests/fuzz_batch.rs` (C-ABI verifier fuzz).

**See also:** `docs/AUDITORS.md` · `docs/audit-scope-p3.md` · `docs/remediation-status.md` · `docs/soundness-budget.md` · `docs/full-node-security-integration.md` · `docs/gpu-acceleration.md` · `docs/recursion-aggregation-status.md`.

**See also:** `docs/AUDITORS.md` (handoff) · `docs/audit-scope-p3.md` (scope/threat model/frozen params) · `docs/remediation-status.md` (closed findings) · `docs/soundness-budget.md` (the proven floor) · `docs/full-node-security-integration.md` (host-chain gates) · `docs/gpu-acceleration.md` · `docs/recursion-aggregation-status.md`.
