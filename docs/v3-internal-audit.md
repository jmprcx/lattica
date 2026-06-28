# v3 shielded-HTLC — internal pre-audit report

A full internal security audit of the v3 lattica surface (`htlc_air` + `ShieldedHtlcTx` + the seam),
conducted **before** the external Codex audit to find and fix issues early. Method: four independent
adversarial reviewers (one per dimension), each blind to having built the code, plus a constraint-level
soundness read. Where a safety/sanity check could live at the solver (circuit) **or** the node level,
it was added at **both** (defense-in-depth). All fixes landed as validated green increments on `v3`.

**Headline verdict: no live soundness break found.** Every HTLC-critical binding is non-vacuously
enforced and persisted; the central property — *one HTLC note ⇒ exactly one nullifier across redeem
and refund* (no redeem-and-refund double-spend) — holds. The pass produced **defense-in-depth
hardening** (two solver checks the circuit previously delegated to the node, two node backstops to the
verifier), an **error-taxonomy** fix, and **regression tests** over the persistence class that hid the
v1 `rho1` double-spend. The residual items are feature-completion or host-chain-scope, documented in §5.

## 1. Scope & method
In scope (the v3 delta over the audited v1; v1 itself is `docs/AUDITORS.md` / `joinsplit-constraint-audit.md`):
- **Circuit** — `lattica-prover-p3/src/htlc_air.rs` (the HTLC spend AIR), `bin/dump_p2.rs` (KATs).
- **C ABI** — `lattica-prover-p3/src/lib.rs` (`lattica_htlc_verify`/`_prove`/`_prove_demo`, the public-input
  + witness codecs).
- **Node/seam** — `src/{node,ffi,poseidon2,primitives,tx,production_probe}.zig`.

Four parallel adversarial reviewers: **(A)** circuit soundness/vacuity, **(B)** cross-language byte
layouts, **(C)** node consensus/apply path, **(D)** C-ABI robustness. Each produced a falsifiable
findings list. Reviewers B and D returned **clean** (exact byte agreement on all four layouts; the HTLC
ABI fully matches the v1 hardening — null checks, canonical parse, size caps, panic isolation, buffer
bounds). Reviewers A and C produced the findings below.

## 2. Findings & disposition
Severity: Crit / High / Med / Low / Nit. Layer = where the fix belongs.

| # | Finding | Sev | Layer | Status |
|---|---|---|---|---|
| A‑F1 / C‑F1 | `current_height` was range-checked at **neither** layer; the timeout compare's no-wrap soundness rested on an unstated node invariant (`height < 2^BITS`). A near-`p` height could make a refund `DIFF=height−timeout` spuriously small ⇒ early refund / theft. | High | both | **Fixed** |
| A‑F4 / C‑(mint) | `mint` not forced to 0 in-circuit for an HTLC spend; a balanced `mint>0` would verify (value inflation) if the verifier were reused outside the node's `mint!=0` reject. | Med | both | **Fixed** |
| C‑F2 | Node keyed the byte-valued nullifier set without a canonical-encoding check; a non-canonical limb is a different key for the same field element ⇒ double-spend **if** a backend reduced instead of rejecting. | Med | both | **Fixed** |
| C‑F4 | Height mismatch returned `TxError.Internal`, conflating a tx-reject with a node bug; build-time prove failure likewise. | Med | node | **Fixed** |
| C‑F6 | No node-side `fee < 2^BITS` bound (only the circuit range-checked it). | Low | both | **Fixed** |
| C‑F3a | The production probe didn't reference the HTLC consensus surface, so `check-production` couldn't catch a test-only helper leaking into `applyHtlc`/`buildHtlcSpend`. | Med | node | **Fixed** |
| A‑F3 | No adversarial/negative coverage of the HTLC persistence columns (OWNER/CLAIM/MODE/NT/TIMEOUT) — the exact class that hid the v1 `rho1` double-spend. | Med | tests | **Fixed (OWNER + double-spend)** |
| D‑O3 | HTLC C ABI had only happy-path tests; a future edit could silently drop a hardening check. | Low | tests | **Fixed** |
| A‑F2 / C‑F8 | The redeem hashlock binding's SHA256 half is out-of-circuit (by design). | Med | design | **Verified sound** (see §4) — preimage-reveal mechanism. **Correction (round 2):** the *circuit* keeps `mode` private, but the **transaction** does NOT hide redeem vs refund — a redeem carries a revealed preimage + nonzero `redeem_hashlock`, a refund neither. So an observer can tell redeem from refund (and bound the timeout from the spend height). See `v3-internal-audit-round2.md` (privacy). |
| A‑F7 / C‑(nf) | Intra-tx nullifier distinctness is not enforced in-circuit. | Low | node | **Already enforced** (the `seen` set in `applyHtlc`/`applyChecked` rejects duplicates) |
| C‑F3b | No production path to **create** an HTLC note (only test-only `bootstrapNote`); `applyHtlc` was sound but only reachable in tests. | Med | feature | **Fixed** (`buildHtlcLock`, commit `7deab14`) |
| C‑F5 | No bounded anchor window / reorg-undo / commitment index (HTLC watch-by-cm). | Med | host-chain | **Documented** (§5) |
| A‑F5 | Output `note_type` boolean-ness / `htlc_root` well-formedness unvalidated at creation (an unspendable note — sender footgun, not a soundness hole; wallet-prevented). | Low | solver/wallet | **Documented** (§5) |
| A‑F6 | One `redeem_hashlock` public input ⇒ at most one distinct-hashlock HTLC redeem per tx. | Low | design | **Documented** (§5; the 1-HTLC-per-leg use case is unaffected) |
| C‑F7 | Output ciphertext length bounded above but not exactly. | Low | node | **Documented** (§5) |
| D‑O1/O2 | `*_prove_demo` not `catch_unwind`-wrapped (test-only, fixed witness); u64 witness fields read non-canonically (sound — caught by the prove-path `catch_unwind`). | Nit | — | Accepted (matches join-split) |

## 3. Fixes applied (defense-in-depth at both layers)
- **Solver (`htlc_air`)** — commit `850fdb5`: force `pis[PI_MINT] == 0`; range-check `current_height`
  in-circuit via a single global window (`P_HEIGHT_SEED`, seeded `REM = pis[PI_HEIGHT]`, in input 0's
  free membership region). Negatives `htlc_mint_issuance_is_rejected`, `htlc_out_of_range_height_is_rejected`.
- **Node (`node.zig`)** — commit `4c0acc2`: `applyHtlc` rejects `current_height >= 2^RANGE_BITS`
  (`OversizeHeight`) and `fee >= 2^RANGE_BITS` (`OversizeFee`); `applyHtlc` + `applyChecked` reject
  non-canonical public 32-byte fields (`NonCanonicalField`, limb `>= p`, before they key the nullifier
  set or enter the tree); height mismatch → `HeightMismatch`, build prove-failure → `ProveFailed`;
  `production_probe.zig` now covers the HTLC surface. `at_height` is documented as consensus-sourced,
  never tx-sourced.
- **Tests** — commits `0b2df7e`, `e7680e6`: HTLC negative ABI tests (oversize proof, null pointers,
  non-canonical limb/bit); `htlc_redeem_and_refund_publish_the_same_nullifier` (the chain-level
  no-double-spend property) and `forged_htlc_owner_nullifier_is_rejected` (OWNER-persistence regression).

The bound `2^RANGE_BITS` (`RANGE_BITS = 52`) is the circuit's range width, now shared by name with the
node, so values / fee / height are bounded identically at both layers.

## 4. The preimage / hashlock trust boundary (A‑F2) — why it is sound
SHA256 is deliberately **out of circuit** (it is the cross-chain secret, shared with the BTC leg). The
mechanism is sound as built: the node derives `redeem_hashlock` **from** the revealed preimage
(`SHA256(preimage)`, reduced to a canonical 4-limb digest) — it does not accept `redeem_hashlock` from
the wire — and the circuit binds, on redeem only, `committed_hashlock == redeem_hashlock`. Therefore:
- A redeem cannot verify without a preimage: with `redeem_preimage = none` the node sets
  `redeem_hashlock = 0`, and the in-tree `committed_hashlock != 0`, so the (MODE-gated) binding fails.
- A redeem with a **wrong** preimage fails: `committed != SHA256(wrong)`.
- The preimage rides the tx body and is bound by `tx_binding`, so it is public once the redeem is
  posted — exactly what lets the counterparty claim the other leg (atomicity).
The trust reduces to the node's SHA256 implementation and the public-input binding, both in scope.
Intra-tx and cross-chain nullifier-distinctness are enforced by the node's nullifier set (A‑F7).

## 5. Documented residuals (not fixed — rationale)
- **C‑F3b — production HTLC-note creation (the "lock"): FIXED post-audit.** `node.buildHtlcLock` (commit
  `7deab14`) builds the production lock — an `htlc_air` tx with PLAIN inputs and an HTLC-typed output
  (owner = `htlc_root`) + change; no circuit change was needed. The full **real** lock → redeem (and
  refund-before-timeout reject) lifecycle is now exercised in `scripts/run-real-integration.sh`. The
  new HTLC note is watched by commitment; the redeemer learns its opening via the off-chain communicated
  lock (the cm→position index that lets a watcher *locate* it on-chain remains host-chain scope, F5).
- **C‑F5 — anchor window / reorg-undo / commitment index.** The in-memory node keeps an unbounded
  anchor set and no reorg-undo or `cm→position` index. These are host-chain (`rubble-node-zig`)
  consensus responsibilities, already out of scope per `AUDITORS.md` §7 and
  `full-node-security-integration.md`. The HTLC watch-by-commitment index is a Phase A2 RPC feature.
- **A‑F5 — output note malformation.** A sender that builds an output with `note_type ∉ {0,1}` or an
  owner that is not a real `htlc_root` creates an unspendable note (their own funds locked); not a
  soundness or theft vector. The wallet builders always emit valid outputs. An in-circuit output
  `note_type` boolean is a cheap optional hardening; the `htlc_root` well-formedness cannot be checked
  at creation without recomputing the chain (it is proven at spend).
- **A‑F6 — one redeem hashlock per tx.** Two HTLC redeem inputs with different hashlocks in one tx are
  unprovable. A swap leg redeems a single HTLC note, so this is not a limitation in practice.
- **C‑F7 — exact output ciphertext length.** Lengths are bounded above (`MAX_NOTE_CIPHERTEXT_LEN`) and
  bound by `tx_binding`; an under-length ciphertext only makes the note unspendable by its recipient
  (no consensus break). A future exact-length admission policy is a refinement.

## 6. Validation
`v3` tip after this pass: **73 Rust tests** (incl. the new circuit + ABI negatives), the full **Zig**
suite (incl. the HTLC lock→redeem lifecycle + the new node-reject tests), **`zig build
check-production`** (the full HTLC surface incl. `buildHtlcLock`), and
**`scripts/run-real-integration.sh`** — which now drives a **real** join-split plus a full HTLC
**lock → refund-before-timeout-reject → redeem** lifecycle through the live node (both 469 KB proofs
accepted) — all green. Audit commits: `850fdb5` (solver hardening), `4c0acc2` (node hardening),
`0b2df7e` (ABI negatives), `e7680e6` (soundness regression tests), `7deab14` (`buildHtlcLock`, F3b).
This internal pass does not replace the external Codex audit — it front-loads the fixes.
