# Lattica — v3 batch-delta audit handoff (supplements AUDITORS.md)

> **Frozen record:** Evidence and scope for the completed `v3-batch-audit` artifact. Statements describing W10 as pending record the pre-tag handoff stage; W10 is now complete.

**Read `docs/AUDITORS.md` first** — it is the external handoff for the v1 join-split + v3 shielded-HTLC
surface, audited + remediated at the `v3-audit` tag (2026-06-28). This doc adds the **production delta
since that tag**: batch aggregation (now production), the whole-crate refactor, and exchange mode. It
is the entry point for auditing the current tip. Live status + roadmap: `docs/audit-readiness-status.md`.

## 1. What is new since `v3-audit` (~222 commits)

- **Batch aggregation is production** — `batch_joinsplit_air` / `batch_htlc_air` ("one proof per block":
  K single-tx tiles → one proof binding a single 32-byte tx-root) + the node `applyBatch` / `applyHtlcBatch`
  path + the 4 batch C-ABI externs. This is the **main new audit surface**.
- **Whole-crate refactor (A1–I8, 2026-07-02)** — a constraint-fingerprint oracle (`constraint_fingerprint.rs`)
  guarantees each motion/dedup is constraint-preserving; single-sourced config + domain tags; deleted a
  ~150-line duplicated constraint fork (`eval_spend` now shared single-tx ↔ batch); collapsed the ABI to
  one fail-closed core; split the 8,181-line recursion monolith; quarantined superseded AIRs behind `cfg(test)`.
- **Exchange deposit mode** — a shared-KEM O(1)-detection wallet mode (no circuit change); adds an ML-KEM
  IK-CCA anonymity assumption (`audit-scope-p3.md` §2). Wallet-layer.

## 2. Scope

**In scope (this delta):** the batch circuits + their C-ABI + the node apply path; the refactor (as a
constraint-preserving transform — verify the fingerprint continuity); exchange mode's wallet-layer
assumption. Plus everything AUDITORS.md already scopes (join-split, HTLC, Poseidon2, the seam).

**Out of scope (unchanged):** the host chain `rubble-node-zig` (consensus/blocks/mempool/reorg/emission
+ the release gates in `docs/full-node-security-integration.md`); the cross-chain `rubble-xchain-xfer`
stack; **GPU / streaming / recursion** (research, feature-gated OFF, prove-only, verified under the
unchanged verifier, absent from the default staticlib — `lattica-prover-p3/scripts/check-abi-symbols.sh`);
wallet key management.

## 3. New audit artifacts (read in this order)

1. **`docs/batch-constraint-audit.md`** (W3) — the constraint-by-constraint self-audit of the batch delta:
   tiling isolation, the tx-root Merkle–Damgård fold (8 constraint groups), the single-PI binding, and the
   **one load-bearing trust seam** (§5 — the node recomputes `batch_root` over its canonical set + dummy
   count; the circuit does not label real vs dummy tiles). Establishes the per-tile body is inherited
   *verbatim* from the single-tx audits (fingerprint-pinned identical).
2. **`docs/v3-batch-internal-audit.md`** (W5) — the internal adversarial round (four independent lenses:
   cross-tile leakage, fold forgery, refactor regression, C-ABI/node seam). Bottom line: **no critical/high
   soundness break.** Two seam-robustness fixes (F1, F2) and audit-ergonomics fixes (OBS-1/2) were found and
   **remediated** (W6):
   - **F1** — `MAX_BATCH_TILES` was prove-only; the verifier now caps the trace height so the ≥100-bit floor
     is intrinsic to the verify seam (`config::verify_proof_bytes` `max_trace_height`).
   - **F2** — a prove-side `padded_tiles` overflow (UB + panic escaping `extern "C"`) is closed by an
     overflow-safe `n_tx > MAX_BATCH_TILES` cap.
   - **OBS-1** — the `wrong_*_rejected` soundness tests now reject cleanly under debug (were a panic).
   The report's §"Node-side obligations" lists what the host chain MUST enforce (pre-cap, root-recompute,
   anchor-freshness window, `tx_binding` meaning, js/HTLC routing, aggregate issuance).
3. **`tests/fuzz_batch.rs`** (W2) — executable batch verifier-robustness fuzz (mutates a real 2-tile proof +
   its tx-root thousands of ways: never-accept-mutated, never-accept-tampered-root, never-panic).

## 4. Build, test & reproduce (evidence at RC `8be9b17`)

```sh
cd lattica-prover-p3
cargo test --release              # 102 passed, 20 ignored
cargo test --release -- --ignored # 20 passed (fuzz_batch, corrupted-trace, differential, the F1 cap test)
bash scripts/check-abi-symbols.sh # exactly 10 lattica_* externs, 0 recursion symbols
cargo run --release --bin dump_p2 # regenerate the Poseidon2 KATs (Zig node must reproduce)
```
```sh
# from the repo root — the REAL cross-language path incl. the batch (Zig node ↔ Rust circuit):
scripts/run-real-integration.sh   # ALL PASS: join-split + HTLC + batch + HTLC-batch prove→verify→
                                  # tamper-reject→apply→double-spend-reject; node tx-root == circuit
```
Evidence at RC: default **102/20**, `--ignored` **20 passed**, ABI gate green, real integration **ALL PASS**,
constraint fingerprints **unchanged** (the batch delta + all W6 fixes are ABI/verify/test only — no AIR
constraint-set change). Toolchain / `.sframe` caveat: as in AUDITORS.md §3 (real backends via the script).

## 5. Sign-off items (auditor) + node obligations

- **~103-bit *proven* soundness** (~127 conjectured) — the Goldilocks `F_p²` ceiling; the batch inherits it
  (`batch_proven_security_floor` pins ≥100 at `MAX_BATCH_TILES = 64`, <100 at 128). The one deliberate
  parameter needing explicit acceptance (`docs/soundness-budget.md`).
- A dedicated **Poseidon2 parameter / algebraic-attack review** (the fold + every hash binding rest on it).
- **A4 residuals** — the untagged Merkle `merge`; the `rho`-uniqueness note-creation invariant.
- **Node-side (host chain, out of repo)** — the trust seam: pre-cap the tile count and verify against a
  **self-recomputed** `batchRoot(txs)`; apply each tx against its own anchor within a freshness window;
  validate `tx_binding`'s meaning off-STARK; route js vs HTLC batch proofs to the matching verifier;
  bound aggregate block issuance. Detailed in `docs/v3-batch-internal-audit.md`.

## 6. Status

W1–W10 of the batch-delta audit-readiness track are complete: feature gating and the ABI gate, batch
fuzzing, constraint audit, documentation review, internal adversarial review and remediation, evidence
capture, external handoff, consistency sweep, and the maintainer-created `v3-batch-audit` tag. See
`audit-readiness-status.md` for the current boundary between that frozen artifact and later development.
