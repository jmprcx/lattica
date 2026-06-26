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
| **C-05** unvetted hash | C | ✅ **In-circuit, validated** | `lattica-prover` AIR for Rescue-Prime `Rp64_256` reproduces the native permutation (differential-tested); the vetted hash *is* the in-circuit hash. |
| **I-02** RNG via debug assert | I | ✅ Subsumed | Prover RNG owned by Winterfell; Zig reference engine stays test-only. |
| **I-03** engine duplication | I | ✅ Subsumed | Production proving is the single Winterfell engine; hand-rolled Zig STARK is the differential-test oracle only. |
| **C-01** auth not bound to spend authority | C | 🟡 Foundation built (P2) | Hash AIR validated; binding ownership+nullifier+commitment+membership+balance+tx-binding into one statement is the remaining P2 work. |
| **C-02** full spend not live | C | 🟡 Foundation built (P2/P4) | Verify boundary (`src/ffi.zig`) + fail-closed ABI in place; node wiring is P4. |
| **C-03** demo-depth / not protocol-complete | C | 🟡 Foundation built (P2) | Vetted-hash AIR done; depth-32 membership + real note commitment + exact nullifier derivation are the remaining P2 increments. |

Legend: ✅ done · 🔜 scheduled core work · ⏳ subsumed by the framework decision.

## Done this iteration
- L-01, I-01 (the two findings the plan keeps in the Zig protocol layer) — closed with tests.
- **Phase 0 complete:** framework decision = **Winterfell** (see `docs/framework-decision.md`).
  The spike (`framework-spike/`) proves+verifies the authorization-proof core (x⁷ S-box) on
  Winterfell with Goldilocks `f64` + vetted `Rp64_256` + F_p² challenges at **127-bit**
  conjectured security; 3/3 spike tests pass.

## Phase 1 — done
`src/codec.zig` (canonical encoding), `src/protocol.zig` (unified shielded tx + canonical
serialization + tx-binding digest + checked-arithmetic supply model), `src/ffi.zig` (spend verify
boundary: `SpendPublicInputs` + C ABI shape + fail-closed pluggable backend). 97/97 Zig tests.

## Phase 2 — in progress (hash + membership validated)
`lattica-prover/` (Winterfell), 9/9 Rust tests:
- **Rescue-Prime `Rp64_256` permutation AIR**, cross-validated against the native hash
  (`trace_output_matches_native_oracle`), valid-verifies, tamper-rejected. The vetted in-circuit
  hash (C-05 in-circuit).
- **Merkle membership AIR** (`membership.rs`): a multi-permutation trace folding a private leaf up
  a **general-position** authentication path (position-bit column + periodic round/link selector)
  to a public root via the Rescue 2-to-1 compression. Validated: `native_merge` equals
  `Rp64_256::merge`; the AIR trace root equals the native fold; valid-verifies; wrong-root and
  tampered-path rejected. **The heart of C-02.**
- **Spend AIR** (`spend.rs`): one proof for public `(root, nf)` proving (1) `cm =
  H(recipient, value, rho, rcm)`, (2) `cm` folds up a general-position path to `root`, (3) `nf =
  H(nk, rho, pos)` — with the **same `rho`** in (1) and (3), bound by a **persistent `rho` column**
  (no auxiliary grand-product segment). Per-boundary periodic selectors gate round / merge-link /
  nullifier-load / row-0 constraints. Validated: `cm`/`nf` equal `Rp64_256::hash_elements`; AIR
  `root`/`nf` equal the native fold/hash; valid-verifies; wrong-root, wrong-nf, tampered-opening,
  and **inconsistent-`rho`** (commitment vs nullifier) all rejected. **C-01/C-02/C-03 core.**
- `lattica_spend_verify` C ABI is **real** (lib.rs): parses the `SpendPublicInputs` byte layout
  from `src/ffi.zig` (canonical field-element + length checks), deserializes the Winterfell proof,
  and calls `verify_spend` — fail-closed on any parse error. Round-trip tested (accept / tampered-
  root reject / malformed-length fail-closed). 19/19 Rust tests (incl. the range AIR).

### Remaining within Phase 2
1. ~~Merkle membership (general position).~~ **Done.**
2. ~~Commitment opening + leaf binding.~~ **Done.**
3. ~~Nullifier + shared-`rho` binding.~~ **Done** (`spend.rs`). `recipient`/`nk`/`pos` are single
   field elements (demo); `DEPTH=6` (8 blocks, pow-2 trace) — depth-32 needs a block-count pad.
4. ~~Bind the public **tx-binding** digest.~~ **Done** (`spend.rs`): `tx_binding` is a public input
   absorbed into the Fiat-Shamir transcript; a proof for one tx fails against another
   (`wrong_tx_binding_rejected`). 16/16 Rust tests.
5. **Ownership** (recipient ↔ `nk`) and **position-consistency** (nullifier `pos` ↔ the path),
   reusing the persistent-column binding technique.
6. **Range** (no field wraparound): standalone AIR **done** (`range.rs`) — remainder-decomposition,
   `value < 2^BITS`, in-range verifies / out-of-range rejected / handles `value=0`. **Balance**
   `in = out + fee` (+ `mint`/`burn`) with `out_cm` binding and the range tied to the *hidden*
   note/output values: remaining (integration into `spend.rs` via persistent value columns).
7. ~~The real `lattica_spend_verify` over `SpendPublicInputs`.~~ **Done** (lib.rs): canonical
   public-input parsing + Winterfell proof (de)serialization, fail-closed. A `lattica_spend_prove`
   ABI (wallet side) and linking the static lib into a Zig integration test remain.
8. Differential test the whole statement vs. the hand-rolled reference; production parameters +
   written soundness budget (Phase 5).

Then **Phase 3** (external audit of the circuit + protocol + FFI glue) gates value-bearing use.
