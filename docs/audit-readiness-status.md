# Lattica — audit-readiness status & roadmap

**Status (2026-07-05): the production CPU path is audit-ready in principle, but the frozen audit artifact (`v3-audit`, 2026-06-28) is ~222 commits stale — the batch-aggregation delta that is now production is uncovered by any audit round, and the batch-delta audit-prep track (W1–W10) is ~10% done (only W1).** This doc is the live map: it answers "is it ready?", "are CPU/GPU production-ready?", and "is it refactored for auditability?", and lists the concrete work to reach a re-frozen `v3-batch-audit` artifact. Entry point for the external audit remains `docs/AUDITORS.md`; closed findings are in `docs/remediation-status.md`.

## 1. Assessment — the three questions

**1.1 Is the CPU prover production-ready? — Yes, and it is the single audited path.** There is exactly one production config (`lattica-prover-p3/src/config.rs` — `HidingFriPcs` over the CPU `Radix2DitParallel` DFT + salted `MerkleTreeHidingMmcs`, `is_zk` with 4 random codewords, FRI `log_blowup=4` / `96` queries / `pow_bits=16` / `cap_height=6`), one prove path (`config::proof_to_bytes`), one fail-closed verify gate (`config::verify_proof_bytes`). All four production circuits (`joinsplit_air`, `htlc_air`, `batch_joinsplit_air`, `batch_htlc_air`) and all ten frozen `lattica_*` C-ABI externs (`src/lib.rs`) funnel through it. It is validated end-to-end, cross-language (Poseidon2 KATs + PI byte layout), and adversarially (corrupted-trace / forged-column / verifier-fuzz / exhaustive differential). It passed three internal pre-audit rounds + a Codex remediation pass (`docs/remediation-status.md`) — **but only at the `v3-audit` tag** (see §2).

**1.2 Are the GPU / streaming / recursion implementations production-ready? — No, by design: research / prove-only / opt-in, out of the audit gate.** All three are feature-gated OFF (`--features gpu` / `stream` / `recursion`), prove-only, byte-compatible and verified under the *unchanged* production verifier, and **absent from the default staticlib** — mechanically enforced by `lattica-prover-p3/scripts/check-abi-symbols.sh` (verified green: exactly 10 `lattica_*` externs, zero recursion symbols). None is wired to the C-ABI or the node seam, and **none is audited.** The CPU wire format carries production; the accelerators sit behind it. See `docs/gpu-acceleration.md` and `docs/recursion-aggregation-status.md`. Per the current decision these stay research and out of scope.

**1.3 Has the codebase been refactored for simplicity/auditability? — Yes, essentially complete.** The 2026-07-02 A1–I8 whole-crate refactor added a constraint-fingerprint oracle (`src/constraint_fingerprint.rs`) that mechanically pins every production AIR's `(width, periodic, publics, n_constraints, max_degree, fnv)` so any motion/dedup is provably constraint-preserving; single-sourced the FRI config + domain tags (killing 8×/6× literal duplication); deleted a ~150-line duplicated constraint fork (`eval_spend`); collapsed the ABI to one fail-closed core; split the 8,181-line monolith into six files; and quarantined every superseded AIR behind `cfg(test)`. Production code now carries **0 TODO/FIXME, 1 clippy-allow, 2 dead-code allows**. The only deferred item is test-only churn inside the research recursion module — no open production-refactor work.

## 2. The gap — the audit target is stale

`git describe --tags` = **`v3-audit-222-g636741f`**: the current tip is **222 commits ahead of the frozen `v3-audit` tag (2026-06-28)**. Landed since the tag and **covered by no internal or Codex round**:
- **Batch aggregation** (`batch_joinsplit_air` / `batch_htlc_air` + the node `applyBatch` path) — now **production** (`docs/audit-scope-p3.md` promotes it "formally in scope"), but never adversarially reviewed as a delta.
- The **whole-crate refactor** (§1.3) — constraint-fingerprint-guarded, but the fingerprints are a continuity oracle, not an audit.
- **Exchange deposit mode** (shared-KEM, the new IK-CCA assumption) — wallet-layer, but new to the threat model.

There is **no `v3-batch-audit` tag yet.** An auditor handed the current tip would be reviewing 222 commits of unfrozen delta against a handoff (`AUDITORS.md`) written for the tag.

*Green ≠ audited.* At `636741f` the current tip passes all gates — the default suite is **101 passed / 17 ignored** (`--ignored`: 17 passed), the ABI-symbol gate confirms the frozen 10-extern surface (zero recursion symbols), and `scripts/run-real-integration.sh` passes end-to-end **including the batch path** (real prove → verify → tamper-reject → double-spend-reject; the Zig node's tx-root equals the Rust circuit's). Passing gates is necessary but not sufficient: **no adversarial round has covered the batch delta** (that is W5).

## 3. Roadmap — the batch-delta audit-readiness track (W1–W10)

| WS | What | Status | Artifact |
|---|---|---|---|
| **W1** | Feature-gate research (recursion/gpu/stream) out of the production staticlib + an ABI-symbol gate | ✅ **done** | `lattica-prover-p3/scripts/check-abi-symbols.sh` (green) |
| **W2** | Batch C-ABI fuzz / adversarial tests (the HTLC precedent is `tests/fuzz_htlc.rs`) | ❌ | `lattica-prover-p3/tests/fuzz_batch.rs` (absent) |
| **W3** | Batch constraint-by-constraint self-audit (the join-split precedent is `joinsplit-constraint-audit.md`) | ❌ | `docs/batch-constraint-audit.md` (absent) |
| **W4** | Audit-doc truth pass — stale claims / scope / repro numbers | 🟡 **this pass** | `AUDITORS.md`, `audit-scope-p3.md`, `production-readiness.md` |
| **W5** | Internal adversarial round on the batch delta | ❌ | `docs/v3-batch-internal-audit.md` (absent) |
| **W6** | Fix wave from W5 | ⬜ blocked on W5 | — |
| **W7** | Full gate-run evidence pass at the RC commit | ⬜ | (re-run the §"Build/test" gates) |
| **W8** | New external handoff for the batch tip | ❌ | `docs/v3-batch-audit-handoff.md` (absent) |
| **W9** | Final consistency sweep + freeze | ⬜ | — |
| **W10** | **USER** tags `v3-batch-audit` (never autonomous) | ❌ | tag (still `v3-audit`) |

The substantive lifts are **W2 (batch fuzz), W3 (batch constraint audit), W5 (internal adversarial round)**; W7–W10 are evidence/handoff/freeze. Scope of the track is the **production-surface delta only** — recursion/GPU/streaming research are explicitly out.

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

## 6. Doc hygiene (refreshed in this pass) + see also

This pass corrected stale claims that would mislead an auditor: the reproduction test counts in `AUDITORS.md` §3, the "coinbase/mint/burn not yet modeled" line and the C-03 checklist row in `audit-scope-p3.md` (both since resolved), the ABI-fuzz status (HTLC done, batch open), an explicit out-of-scope listing for GPU + streaming, a hardened historical banner on `production-readiness.md`, and the crate-relative path to `check-abi-symbols.sh`.

**See also:** `docs/AUDITORS.md` (handoff) · `docs/audit-scope-p3.md` (scope/threat model/frozen params) · `docs/remediation-status.md` (closed findings) · `docs/soundness-budget.md` (the proven floor) · `docs/full-node-security-integration.md` (host-chain gates) · `docs/gpu-acceleration.md` · `docs/recursion-aggregation-status.md`.
