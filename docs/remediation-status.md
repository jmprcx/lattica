# Transaction-stack audit — remediation status

Tracks `docs/transaction-stack-audit.md` findings against the approved plan (shielded-only in
rubble-node-zig; vetted transparent-PQ STARK framework via FFI; `lattica` as a Zig package).
Phases per the plan: P0 framework spike · P1 protocol finalization · P2 production circuit ·
P3 external audit · P4 rubble integration · P5 testnet.

| Finding | Sev | Status | Where / notes |
|---|---|---|---|
| **L-01** value overflow | L | ✅ **Done** | `node.zig`: `std.math.add` in `buildTransfer` + `verifyAndApply`; `TxError.ValueOverflow`; overflow test. |
| **I-01** malleable encoding | I | ✅ **Done (reference layer)** | `stark.zig` reader rejects field elements ≥ `P` (`NonCanonical`) and trailing bytes (`TrailingBytes`); 2 adversarial tests. Re-apply to the final unified-tx serialization in P1. |
| **C-04** ~50-bit soundness | C | ⏳ Subsumed by framework (P0/P2) | Vetted framework draws extension-field challenges; document ≥128-bit budget. |
| **C-05** unvetted hash | C | ⏳ Subsumed by framework (P0/P2) | Use the framework's vetted hash (e.g. Poseidon2 std constants). |
| **I-02** RNG via debug assert | I | ⏳ Subsumed (P2) | Prover RNG owned by the framework; Zig reference engine stays test-only. |
| **I-03** engine duplication | I | ⏳ Subsumed (P2) | Hand-rolled engines leave the production path; keep one as a differential-test oracle. |
| **C-01** auth not bound to spend authority | C | 🔜 Core circuit work (P2) | Production circuit binds ownership+nullifier+commitment+membership+balance+tx-binding. |
| **C-02** full spend not live | C | 🔜 Core circuit work (P2/P4) | Node verifies the single proof; native checks demoted to public-input consistency. |
| **C-03** demo-depth / not protocol-complete | C | 🔜 Core circuit work (P2) | Depth-32, real note commitment (`recipient`/`rcm`) + exact nullifier derivation. |

Legend: ✅ done · 🔜 scheduled core work · ⏳ subsumed by the framework decision.

## Done this iteration
- L-01, I-01 (the two findings the plan keeps in the Zig protocol layer) — closed with tests.
- Phase 0 spike kicked off (see `framework-spike/`): re-express the spend statement in a
  transparent post-quantum FRI-STARK framework and record a framework decision.
