# Transaction-stack audit — remediation status

Tracks `docs/transaction-stack-audit.md` findings against the approved plan (shielded-only in
rubble-node-zig; vetted transparent-PQ STARK framework via FFI; `lattica` as a Zig package).
Phases per the plan: P0 framework spike · P1 protocol finalization · P2 production circuit ·
P3 external audit · P4 rubble integration · P5 testnet.

| Finding | Sev | Status | Where / notes |
|---|---|---|---|
| **L-01** value overflow | L | ✅ **Done** | `node.zig`: `std.math.add` in `buildTransfer` + `verifyAndApply`; `TxError.ValueOverflow`; overflow test. |
| **I-01** malleable encoding | I | ✅ **Done (reference layer)** | `stark.zig` reader rejects field elements ≥ `P` (`NonCanonical`) and trailing bytes (`TrailingBytes`); 2 adversarial tests. Re-apply to the final unified-tx serialization in P1. |
| **C-04** ~50-bit soundness | C | ⏳ Framework selected; shown in spike | Winterfell with `FieldExtension::Quadratic` → **127-bit** in the spike (vs ~50-bit). Final budget in P5. |
| **C-05** unvetted hash | C | ⏳ Framework selected; shown in spike | Winterfell ships vetted Rescue-Prime `Rp64_256`; used in the spike. Full sponge AIR in P2. |
| **I-02** RNG via debug assert | I | ⏳ Subsumed (P2) | Prover RNG owned by Winterfell; Zig reference engine stays test-only. |
| **I-03** engine duplication | I | ⏳ Subsumed (P2) | Hand-rolled engines leave the production path; keep one as a differential-test oracle. |
| **C-01** auth not bound to spend authority | C | 🔜 Core circuit work (P2) | Production circuit binds ownership+nullifier+commitment+membership+balance+tx-binding. |
| **C-02** full spend not live | C | 🔜 Core circuit work (P2/P4) | Node verifies the single proof; native checks demoted to public-input consistency. |
| **C-03** demo-depth / not protocol-complete | C | 🔜 Core circuit work (P2) | Depth-32, real note commitment (`recipient`/`rcm`) + exact nullifier derivation. |

Legend: ✅ done · 🔜 scheduled core work · ⏳ subsumed by the framework decision.

## Done this iteration
- L-01, I-01 (the two findings the plan keeps in the Zig protocol layer) — closed with tests.
- **Phase 0 complete:** framework decision = **Winterfell** (see `docs/framework-decision.md`).
  The spike (`framework-spike/`) proves+verifies the authorization-proof core (x⁷ S-box) on
  Winterfell with Goldilocks `f64` + vetted `Rp64_256` + F_p² challenges at **127-bit**
  conjectured security; 3/3 spike tests pass.

## Next
- **Phase 1:** finalize the `lattica` Zig protocol package + canonical unified-tx serialization
  (re-apply the I-01 rule there); wire the hand-rolled STARK as a differential-test oracle.
- **Phase 2:** full spend circuit (Rescue sponge + depth-32 membership + nullifier + balance +
  tx-binding) in a `lattica-prover` Winterfell crate over a C ABI (closes C-01/C-02/C-03).
