# Remediation status

Current state of audit-finding remediation. **Entry point for reviewers: `docs/AUDITORS.md`.**

## Current live path (M6 cutover — COMPLETE)

The live node runs the **Plonky3 join-split** path end to end:
- `src/node.zig` authorizes transactions solely via `ffi.verifyJoinSplit` →
  `lattica_joinsplit_verify` (fail-closed, panic-isolated). The wallet proves via
  `lattica_joinsplit_prove`.
- On-chain hashing is Poseidon2-Goldilocks (`src/poseidon2.zig`), KAT-equal to the circuit, so the
  node-reconstructed public inputs equal the proof's.
- The pre-Plonky3 cluster (`stark.zig`, `rescue.zig`, `circuit.zig`, the Winterfell `lattica-prover`,
  `lattica_spend_verify`) has been **removed**. References to those in older revisions of this file
  are obsolete.

So the earlier "✅ in new stack (not live)" caveats are resolved: the new stack **is** the live path.

## Original transaction-stack audit (`docs/transaction-stack-audit.md`) — closed / superseded

| Finding | Status |
|---|---|
| L-01 value overflow | ✅ closed (live; `TxError.ValueOverflow` + tests) |
| I-01 malleable encoding | ✅ closed (`codec.zig` rejects ≥P / trailing, overflow-safe bounds) |
| C-05 unvetted hash | ✅ superseded — vetted Poseidon2-Goldilocks AIR == on-chain hash |
| I-02 RNG via debug assert | ✅ superseded — production prover RNG (ChaCha20 CSPRNG, reseeded per proof) |
| I-03 engine duplication | ✅ superseded — single production circuit (`joinsplit_air`); hand-rolled engines removed |
| C-04 ~50-bit soundness | ✅ resolved — `F_p²` challenges + hardened FRI ⇒ ≈103-bit proven / ~127 conjectured (`docs/soundness-budget.md`) |
| C-01/C-02 auth + full spend not live | ✅ resolved — live node verifies the full join-split statement |
| C-03 protocol hash match | ✅ resolved — `poseidon2.zig` KAT-equal to the circuit |
| ZK-01 not zero-knowledge | ✅ resolved — hiding FRI PCS (ZK) on Plonky3 |

## Implementation audit (`docs/lattica-implementation-audit.md`, Codex, 2026-06-27) — remediated

**Round 1** — C-01 (critical ghost-coin binding), H-01 (supply accumulator), H-02 (validation order),
M-01..M-04 (ABI/codec/alloc hardening), L-01/L-02 (docs + format). All addressed; the re-audit
**verified** them.

**Round 2** (re-audit new findings) — also addressed:
- **H-03** atomic state on error — `SupplyState.apply` assigns only after all arithmetic succeeds;
  `applyChecked`/`bootstrapMint` are two-phase (reserve capacity + copy, then infallible commit).
- **H-04** transmitted-note ownership — chain deep-copies ciphertexts and frees them in `deinit`.
- **M-05** verifier size limits — proof/ciphertext byte caps before verification.
- **M-06** issuance API — `Chain.mint` → `bootstrapMint` (genesis/test-only contract).
- **M-07** full-node consensus surface — lattica-layer parts done; block-level commitments/reorg/mempool
  remain host-chain scope (see "Out of lattica's scope" below).
- **L-01/L-02** — pre-Plonky3 docs banner'd reference-only; `AUDITORS.md` §4 lists canonical vs historical.

**Round 3** (re-audit new findings) — also addressed:
- **M-08** verifier-seam size limit — `ffi.verifyJoinSplit` and the Rust `lattica_joinsplit_verify`
  reject oversize proofs before the backend/deserializer (matching `MAX_PROOF_LEN`).
- **M-09/M-10** test-only APIs compile-gated — `bootstrapMint` and `node.mock` are unavailable in a
  build whose root sets `lattica_production = true` (referencing them is a compile error). The probe
  `src/production_probe.zig` + `zig build check-production` (run by `zig build test`) assert the live
  consensus surface compiles without them.
- **L-03** README rewritten to the Plonky3 join-split path (removed-file refs deleted; `tx_binding`
  replaces the ML-DSA binding-signature flow); points to `AUDITORS.md`.

**v3-audit re-audit** (Codex, 2026-06-28, against tag `v3-audit`) — new findings addressed:
- **M-11** legacy one-input spend FFI surface removed — `SpendPublicInputs`/`verifySpend`/`setBackend`/
  `clearBackend` deleted from `src/ffi.zig` (the live node uses the join-split + HTLC seams, both
  size-guarded); `ffi.zig` header + `docs/audit-scope-p3.md` (trust model, proof-serialization layout,
  frozen-params note) rewritten to the `lattica_joinsplit_verify`/`lattica_htlc_verify` shapes.
- **P-01** full-node consensus integration — out of lattica's scope (host chain); the HTLC-specific
  production requirements are specified in `docs/full-node-security-integration.md`. No in-package change.

See the **Developer Remediation Response** tables (Round 1–3 + the v3-audit re-audit) in
`docs/lattica-implementation-audit.md` for the finding-by-finding mapping. Re-validated each round (the
Rust circuit/ABI suite + the exhaustive `--ignored` audit suite, the full Zig suite incl. the
production-mode probe, `zig build check-production`, and the real cross-language integration — incl. the
v3 HTLC lock→redeem lifecycle).

## Out of lattica's scope (host chain `rubble-node-zig`)

Block consensus / PoW / mempool / networking / emission schedule, and block-level commitments
(state-root, nullifier-set-root, event-root, header) + reorg undo logs. lattica provides the
shielded-tx + issuance *mechanisms* and the node-visible supply accumulator; the host chain owns
block-level supply recomputation and commitments.
