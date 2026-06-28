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

All findings (C-01 critical ghost-coin binding; H-01 supply accumulator; H-02 validation order;
M-01..M-04 hardening; L-01/L-02 docs + format consolidation) addressed on the audit branch. See the
**Developer Remediation Response** table at the end of `docs/lattica-implementation-audit.md` for the
finding-by-finding mapping. Re-validated: 30 Rust tests, full Zig suite, and the real cross-language
integration (which rejects the C-01 ghost-coin attack through the real Rust verifier).

## Out of lattica's scope (host chain `rubble-node-zig`)

Block consensus / PoW / mempool / networking / emission schedule, and block-level commitments
(state-root, nullifier-set-root, event-root, header) + reorg undo logs. lattica provides the
shielded-tx + issuance *mechanisms* and the node-visible supply accumulator; the host chain owns
block-level supply recomputation and commitments.
