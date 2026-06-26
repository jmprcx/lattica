# Transaction-stack audit — remediation status

Tracks `docs/transaction-stack-audit.md` findings against the approved plan (shielded-only in
rubble-node-zig; vetted transparent-PQ STARK framework via FFI; `lattica` as a Zig package).
Phases per the plan: P0 framework spike · P1 protocol finalization · P2 production circuit ·
P3 external audit · P4 rubble integration · P5 testnet.

**Important framing:** remediation was done by building a **parallel production stack**
(`lattica-prover` Rust crate + `src/{codec,protocol,ffi}.zig`) plus two live-layer fixes (L-01,
I-01). The **live node (`node.zig`) is otherwise unchanged** — it still runs the hand-rolled
`stark.zig` generic-preimage proof with native checks. So a "✅ in new stack" finding is **fixed by
construction in the production design but not yet on the live path** (that is the Phase-4 cutover).
None of the audit's 8 release gates are met; the Phase-3 external audit has not run.

| Finding | Sev | Status | Where / notes |
|---|---|---|---|
| **L-01** value overflow | L | ✅ **Closed (live)** | `node.zig` `std.math.add` + `TxError.ValueOverflow`; overflow test. |
| **I-01** malleable encoding | I | ✅ **Closed** | `stark.zig` rejects ≥`P`/trailing bytes; generalized in `codec.zig` with tests. |
| **C-05** unvetted hash | C | ✅ in new stack (not live) | `lattica-prover` AIR for vetted `Rp64_256`, differential-tested. Live node still uses `rescue.zig`. |
| **I-02** RNG via debug assert | I | ✅ in new stack (not live) | Production prover RNG is Winterfell's; live node still uses `stark.zig`. |
| **I-03** engine duplication | I | ✅ in new stack (not live) | Production = single Winterfell engine; hand-rolled engines remain in `src/` and on the live path. |
| **C-04** ~50-bit soundness | C | 🟡 mechanism in place | `FieldExtension::Quadratic` (127-bit in the spike). Production params + **written soundness budget** pending (P5). |
| **C-01** auth not bound | C | 🟡 circuit built, **NOT live** | `spend.rs` binds ownership+nullifier+commitment+membership+balance+tx-binding (validated). But `node.zig` still calls `circuit.verifyAuthorization` (generic preimage). Cutover = P4. |
| **C-02** full spend not live | C | 🟡 circuit + ABI built, **NOT live** | Full spend AIR + real `lattica_spend_verify` exist; `verifyAndApply` does not call them yet. Cutover = P4. |
| **C-03** demo-depth / not protocol-complete | C | 🟡 partly | Binds ownership/balance/range, but `DEPTH=4` (not 32), `recipient` is 1 element (not full digest), and the in-circuit `Rp64_256` does **not** match the protocol's SHA3 `noteCommitment`/`nullifier` in `tx.zig`/`primitives.zig`. |
| **ZK-01** spend proof not zero-knowledge *(found in the remediation review)* | C | ❌ **Open (blocking)** | Winterfell 0.13 has no ZK (its "Randomized AIR" = multiset/aux args, not ZK); `spend.rs` has no trace blinding → FRI openings leak the witness. The hand-rolled `spend.zig` had ZK; the port lost it. A shielded proof must be ZK. |

Legend: ✅ closed · 🟡 partial (mechanism built, not closed) · ❌ open · ⏳ subsumed.

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

## Phase 2 — spend statement built & validated (not yet live; not yet ZK)
`lattica-prover/` (Winterfell). **Current totals: 21/21 Rust tests, 97/97 Zig tests.** (Per-bullet
counts below are historical, from the iteration that added each piece.)
- **Rescue-Prime `Rp64_256` permutation AIR**, cross-validated against the native hash
  (`trace_output_matches_native_oracle`), valid-verifies, tamper-rejected. The vetted in-circuit
  hash (C-05 in-circuit).
- **Merkle membership AIR** (`membership.rs`): a multi-permutation trace folding a private leaf up
  a **general-position** authentication path (position-bit column + periodic round/link selector)
  to a public root via the Rescue 2-to-1 compression. Validated: `native_merge` equals
  `Rp64_256::merge`; the AIR trace root equals the native fold; valid-verifies; wrong-root and
  tampered-path rejected. **The heart of C-02.**
- **Spend AIR** (`spend.rs`): one proof for public `(root, nf, out_cm, tx_binding, fee)` proving
  (0) **ownership** `recipient = H(nk)[0]`, (1) `cm = H(recipient, value, rho, rcm)`, (2) `cm` folds
  up a general-position path to `root`, (3) `nf = H(nk, rho, pos)`, (4) `out_cm =
  H(out_recipient, out_value, out_rho, out_rcm)`, (5) **value-balance** `value = out_value + fee`,
  (6) **range** (`value`/`out_value < 2^BITS`), (7) **tx-binding** — with the **same `rho`** in
  (1)/(3) and the **same `nk`** in (0)/(3). Cross-region binding via **persistent columns**
  (`rho`, `value`, `out_value`, `nk`); `recipient` flows ownership→commitment by adjacency; no
  auxiliary grand-product segment. Per-boundary periodic selectors gate round / commit-load /
  merge-link / nullifier-load / output-load / row-0 / range. Validated: `recipient`/`cm`/`nf`/
  `out_cm` equal the native hashes; AIR `root`/`nf`/`out_cm` equal the native oracles;
  valid-verifies; wrong-root, wrong-nf, wrong-out_cm, tampered-opening, **inconsistent-`rho`**,
  **wrong-`nk`** (ownership), **unbalanced**, **out-of-range**, and **wrong-tx-binding** all
  rejected. **C-01/C-02/C-03 core + ownership + value-balance + range.**
- `lattica_spend_verify` C ABI is **real** (lib.rs): parses the `SpendPublicInputs` byte layout
  from `src/ffi.zig` (canonical field-element + length checks), deserializes the Winterfell proof,
  and calls `verify_spend` — fail-closed on any parse error. Round-trip tested (accept / tampered-
  root reject / malformed-length fail-closed). 19/19 Rust tests (incl. the range AIR).

### Remaining within Phase 2
1. ~~Merkle membership (general position).~~ **Done.**
2. ~~Commitment opening + leaf binding.~~ **Done.**
3. ~~Nullifier + shared-`rho` binding.~~ **Done** (`spend.rs`). `recipient`/`nk`/`pos` are single
   field elements (demo); `DEPTH=4` (8 blocks, pow-2 trace) — depth-32 needs a block-count pad.
4. ~~Bind the public **tx-binding** digest.~~ **Done** (`spend.rs`): `tx_binding` is a public input
   absorbed into the Fiat-Shamir transcript; a proof for one tx fails against another
   (`wrong_tx_binding_rejected`). 16/16 Rust tests.
5. ~~**Ownership** (recipient ↔ `nk`).~~ **Done** (`spend.rs`): ownership block `recipient =
   H(nk)[0]`, with the same `nk` driving the nullifier (`wrong_nk_breaks_membership`). Demo-strength
   (1-element recipient; production = full 4-element digest). **Position-consistency** (nullifier
   `pos` ↔ the membership path) remains.
6. ~~**Balance** `value = out_value + fee` with `out_cm` binding + **range** (no wraparound).~~
   **Done** (`spend.rs`): output-commitment region + value-conservation (`fee` a given public
   input, `unbalanced_rejected`) + two parallel `rem` columns carrying the range decompositions of
   the *hidden* `value`/`out_value`, seeded at row 0 and closed by `rem[BITS]=0`
   (`out_of_range_value_rejected`). Value-balance is now wraparound-sound. `mint`/`burn` for the
   coinbase/issuance path remains.
7. ~~The real `lattica_spend_verify` over `SpendPublicInputs`.~~ **Done** (lib.rs): canonical
   public-input parsing + Winterfell proof (de)serialization, fail-closed. A `lattica_spend_prove`
   ABI (wallet side) and linking the static lib into a Zig integration test remain.
8. Differential test the whole statement vs. the hand-rolled reference; production parameters +
   written soundness budget (Phase 5).

## Open items not yet closed (the gaps the remediation review surfaced)
- **ZK-01 (blocking):** the spend proof is **not zero-knowledge** under Winterfell — FRI openings
  would leak the hidden witness. **Path validated:** the `plonky2-spike/` proves the full spend-core
  statement with zero-knowledge on (vetted Poseidon + range/select gadgets, Goldilocks, FRI/PQ;
  `ZK re-randomized: true`, 5/5 tests). Recommendation (`docs/framework-decision.md` "ZK-01 spike
  result"): a ZK-capable framework is needed (Winterfell has none). Options evaluated — **plonky2**
  (ZK, gadgets/small audit surface; *nightly*), **Plonky3** (ZK + **stable** + **proven-security**;
  AIR-style, our AIR ports), **zkVM** (ZK by construction; heavy, large TCB). All three spiked:
  plonky2 (`plonky2-spike/`, full spend core, ZK ✓) and Plonky3 (`plonky3-spike/`, degree-7 core,
  ZK on **stable** ✓, `ZK re-randomized: true`). **Recommended: Plonky3** (only option with ZK +
  stable + proven security). **Decided: Plonky3.** Port started (`lattica-prover-p3/`,
  `docs/plonky3-port-plan.md`): **M1 done** — vetted Poseidon2-Goldilocks AIR proves/verifies on
  stable, hash matches the protocol's native `Poseidon2Goldilocks` (addresses C-03 at the hash
  level). **M2 done** — the foundation now proves/verifies in **zero-knowledge** (hiding FRI PCS +
  `DuplexChallenger`, `F_p²` challenges) on stable. Remaining: C-04 budget; M3 lookup framework
  (`p3-lookup`/LogUp exists); M4 full spend statement; M5 differential tests + C ABI; M6 Phase-4
  node cutover. Winterfell `lattica-prover` kept as the differential oracle.
- **C-03 protocol match:** the in-circuit `Rp64_256` hash must match the protocol's
  `noteCommitment`/`nullifier` (switch `tx.zig`/`primitives.zig` to the field hash); full note
  format; `recipient` → 4-element digest; `DEPTH` → 32; widen `BITS`.
- **C-01/C-02 live cutover (Phase 4):** wire `lattica_spend_verify` into `node.zig:verifyAndApply`
  (via `ffi.setBackend`), add `lattica_spend_prove`, link the static lib, demote native checks.
- **C-04:** finalize production parameters + the ≥120-bit soundness budget.
- Position-consistency (nullifier `pos` ↔ path); `mint`/`burn` issuance.

Then **Phase 3** (external audit of the circuit + protocol + FFI glue) gates value-bearing use; none
of the audit's 8 release gates are met yet.
