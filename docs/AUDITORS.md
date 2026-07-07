# Lattica — external audit handoff (start here)

Lattica is a **quantum-safe, Zcash-style shielded transaction layer** (it replaces Zcash
Sapling/Orchard): a Plonky3 zero-knowledge circuit + a Zig protocol layer, on a shielded-only value
model. This is the entry point for the external security audit. Read this first, then the deep-dive
docs in §4.

> **This branch is the v3 audit artifact.** It is the audited+remediated **v1 single-asset** protocol
> (the join-split circuit) **plus the v3 shielded-HTLC layer**: a hidden asset id committed in every
> note, and an `htlc_air` spend circuit + `ShieldedHtlcTx` node path that let two parties redeem/refund
> a shielded HTLC note **with the asset type hidden on-chain** (the rubble leg of a noncustodial
> rubble↔BTC atomic swap). v1 was already audited+remediated (three Codex rounds, all verified — see
> §5); v3 builds on that, preserving every v1 remediation invariant. The cross-repo xchain swap stack
> (`rubble-xchain-xfer`) and host chain (`rubble-node-zig`) remain **out of scope** (see §7).

## 1. What to audit (scope)

**In scope:**
- **The circuits** — `lattica-prover-p3/src/joinsplit_air.rs` (the v1 N-in/M-out join-split statement,
  now with the substrate's hidden `asset`) **and `htlc_air.rs` (v3: the shielded-HTLC spend — a superset
  of join-split adding the HTLC note type, `htlc_root` owner, redeem/refund modes, the time-lock, the
  hashlock binding, and the mode-independent nullifier)**, with building blocks `poseidon2_air.rs` (the
  Poseidon2-Goldilocks permutation AIR). The verify/prove **C ABI** + (de)serialization
  + canonical field parsing in `lattica-prover-p3/src/lib.rs` (both the `joinsplit_*` and `htlc_*` ABIs).
- **The Zig protocol seam** — `src/poseidon2.zig` (on-chain hashing incl. `htlcRoot`/`nullifierHtlc` +
  the `note_type` lane, must equal the circuit), `src/{tx,tree,primitives}.zig` (note model + the
  `note_type` field, commitment, nullifier, Merkle tree, key hierarchy + diversified addresses +
  incoming viewing key), `src/node.zig` (the shielded-tx state machine: verify→anchor→nullifier→apply,
  incl. **`ShieldedHtlcTx` + `Chain.applyHtlc` + the `buildHtlcSpend` wallet flow**), `src/ffi.zig` (the
  fail-closed verifier/prover boundary, incl. `verifyHtlc`/`proveHtlc`).

Detailed file/line scope, trust model, frozen parameters, and the readiness checklist are in
**`docs/audit-scope-p3.md`** (§1–§7).

**Out of scope** (by design): the host chain `rubble-node-zig` (consensus, blocks, PoW, mempool,
networking, the emission schedule); the cross-chain swap stack `rubble-xchain-xfer`; and all
forward-looking roadmap docs (§6).

## 2. Security properties claimed

- **Zero-knowledge** — hiding FRI PCS + salted Merkle (MerkleTreeHidingMmcs), blinding RNG is a
  **CSPRNG reseeded per proof** (ChaCha20Rng from OS entropy).
- **Soundness** — ~**103-bit proven** (UDR), ~**127-bit conjectured** (the Goldilocks F_p² ceiling);
  see `docs/soundness-budget.md`. This is the one deliberate parameter needing sign-off (§5).
- **The spend statement** (per input/output, all values + commitments hidden): ownership
  `recipient = H(DOM_OWN ‖ nk0 ‖ nk1 ‖ div)` (**128-bit** spend key `nk`); membership of each input
  commitment under a **published anchor**; nullifier correctness with **position binding** (A1, so a
  note has exactly one nullifier); value balance `Σin + mint = Σout + fee` with every value
  **range-checked** (A3, no field wraparound); **domain separation** on every hash (A2); **128-bit**
  note randomness `rho`/`rcm` (two-permutation commitment).
- **Binding & liveness** — a canonical `tx_binding` digest of the whole body is a public input
  (Fiat-Shamir), so outputs/anchor can't be swapped; the verifier is **fail-closed** (no backend ⇒
  reject) and **panic-isolated** (malformed proofs reject, never UB across the C ABI).
- **Keys** — diversified addresses (unlinkable per-payment) + a delegatable **incoming viewing key**
  (detect/decrypt without spend authority). Two scan modes: privacy-max **wallet mode** (per-address KEM
  key, O(addresses) detection) and **exchange mode** (one shared KEM key across deposit addresses,
  O(1) detection, routes by the cm-bound recipient) — both wallet-layer, same `recipient = H(nk‖div)` and
  circuit; exchange mode adds an ML-KEM anonymity (IK-CCA) assumption (see `audit-scope-p3.md` §2).
- **v3 shielded HTLC** (`htlc_air`) — an HTLC note's owner is `htlc_root = H(DOM_HTLC ‖ redeem_tag ‖
  refund_tag ‖ hashlock ‖ timeout)`, committed (so the terms are immutable). A spend proves: the
  correct **party** for the mode (redeem ⇒ owns `redeem_tag`, refund ⇒ owns `refund_tag`); the
  **time-lock** (redeem ⟺ `height < timeout`, refund ⟺ `height ≥ timeout`, via a range argument, no
  wrap); on redeem, the committed `hashlock == redeem_hashlock` public input (= `SHA256(preimage)`, the
  cross-chain atomic link); the **hidden asset** is preserved (`input.asset == output.asset`); and —
  critically — the nullifier is **owner-based and mode/party-independent** (`nf = H(DOM_NF_HTLC ‖ owner
  ‖ rho ‖ pos)`), so one HTLC note has **exactly one nullifier** across both spend windows (no
  redeem-and-refund double-spend). The asset type stays hidden on-chain throughout.

## 3. Build, test & reproduce

Toolchain: **Rust 1.96** (edition 2021, no pinned toolchain), **Zig 0.16.0**, a C compiler (GCC 16
here) for the cross-language link.

```sh
# 1. Circuit + ABI tests (incl. adversarial corrupted-trace soundness tests, the htlc_air redeem/
#    refund + negative tests, and the htlc prove/verify C-ABI round-trips).
#    v3-audit tag: 82 passed, 3 ignored. Current tip (636741f): 101 passed, 17 ignored.
cd lattica-prover-p3 && cargo test --release

# 1b. Slower ignored audit tests (exhaustive/fuzz-style HTLC checks). v3-audit: 3 passed; current tip: 17 passed.
cd lattica-prover-p3 && cargo test --release -- --ignored

# 2. The Zig protocol suite — incl. the Poseidon2 KATs that pin on-chain == circuit byte-for-byte.
zig build test            # (from the repo root)

# 3. The REAL cross-language path: prove (Rust) → verify (Rust) → tamper-reject → double-spend-reject,
#    plus the live node driving the real prover/verifier in-process — for BOTH join-split AND a v3 HTLC
#    redeem (Zig builds the witness → Rust proves → node verifies/applies; refund-before-timeout is
#    rejected by the real prover). Builds the Zig side as an object and links with the system cc.
scripts/run-real-integration.sh

# 4. Regenerate the Poseidon2 known-answer vectors and re-confirm Zig == circuit.
cd lattica-prover-p3 && cargo run --release --bin dump_p2

# 5. Production-mode compile gate: builds the consensus surface with the genesis/test-only helpers
#    (bootstrapMint, the mock backend) gated out — a successful compile proves the live path uses none
#    (audit M-09/M-10). A production consumer sets `pub const lattica_production = true;` in its root.
zig build check-production   # (also run as part of `zig build test`)
```

**Toolchain caveat (documented, not a defect):** this host's Zig 0.16 linker cannot link the
libc-dependent Rust staticlib (a `.sframe`/crt relocation issue), so `zig build test` uses *mock*
verify/prove backends, and the **real** in-node prove→verify is exercised via
`scripts/run-real-integration.sh`, which compiles the Zig node to an object and links it with the
system `cc`. On a host whose linker handles the crt, the real backends install directly.

## 4. What to read, in order

1. **`docs/audit-scope-p3.md`** — scope, threat model, trust assumptions, frozen parameters, the
   readiness checklist, and the self-review notes.
2. **`docs/joinsplit-constraint-audit.md`** — the **constraint-by-constraint** self-audit: every
   committed column, why each binding is non-vacuous, and the public-output soundness chain. The core
   correctness argument.
2a. **`docs/htlc-constraint-audit.md`** (v3) — the same treatment for `htlc_air`, covering only the
   **deltas** over join-split: the `note_type`/`htlc_root`/owner-MUX/tag-match/hashlock/timeout columns
   and constraints, and especially the **mode-independent-nullifier** double-spend argument. Read after
   the join-split audit.
2b. **`docs/v3-internal-audit{,-round2,-round3}.md`** (v3) — the three-round internal pre-audit run
   before this external audit. R1 (4 reviewers): defense-in-depth fixes at both layers. R2 (8 reviewers
   + a refutation skeptic): Poseidon2, FRI config, join-split-under-v3, memory, encryption, economic,
   tree/codec — foundational layers sound; fixed 2 leaks + M-3 + **H-1 (a HIGH recipient-deanonymization
   oracle in the deterministic note encryption), remediated with the OVK fix**. R3 (audit-the-fixes +
   executable evidence): caught **M-1** (a bug in an R2 fix — non-canonical zero-hashlock bypass, fixed)
   and otherwise *empirically* confirmed soundness (verifier fuzz; harness-validated exhaustive
   corrupted-trace 51/51; differential native-vs-AIR; forgery rejection). Two required gates beyond
   `cargo test`/`zig build test`: **`scripts/run-real-integration.sh`** (cross-language witness/PI
   byte-match) and **`cargo test --release -- --ignored`** (the exhaustive corrupted-trace/differential
   audit suite, `#[ignore]`'d for speed). Both round-3 recommended hardenings were then implemented: the
   in-circuit `PI_HASHLOCK != 0`-on-redeem backstop (`htlc_air`, see htlc-constraint-audit §5a) and the
   removal of dead `spend_air`. The only remaining open items are **out of lattica's scope** — Phase-B
   `await_lock`/timeout (xchain repo) and host-chain reorg/anchor-window/cm-index.
3. **`docs/soundness-budget.md`** — the C-04 proven/conjectured security accounting (~103 / ~127-bit).
4. **`docs/protocol-v1-decisions.md`** — the deliberate v1 parameter decisions + limitations
   (single-asset, key model, note randomness, issuance, the deterministic-encryption interaction).

Also current: **`docs/v3-batch-audit-handoff.md`** (the handoff for the post-`v3-audit` batch tip — start
here for the batch-aggregation delta: its constraint audit, C-ABI fuzz, and internal adversarial round),
`docs/audit-readiness-status.md` (audit-readiness status + roadmap),
`docs/lattica-implementation-audit.md` (the implementation audit + remediation log) and
`docs/remediation-status.md` (live status). `docs/full-node-security-integration.md` is the production
full-node checklist (host-chain scope). A **pre-v1 forward-looking** design note,
`docs/hash-function-analysis.md` (why Poseidon2 stays the in-circuit/on-chain hash for v1, vs Monolith/Tip5),
is **not part of the audit artifact**. **Everything else in `docs/` is historical / reference-only**
(each carries a banner pointing back here) — `audit-scope.md`, `soundness.md`,
`transaction-stack-audit.md`, `framework-decision.md`, `plonky3-port-plan.md`, `production-readiness.md`,
and `parameters.md` predate the Plonky3 cutover and are not part of the audit artifact.

## 5. Known limitations / sign-off items (consolidated)

- **Proven soundness ~103-bit** (~127 conjectured) — the Goldilocks F_p² ceiling; raising it needs a
  larger field (a major migration). The one parameter needing explicit sign-off.
- **Deterministic note encryption** — the AEAD key+nonce derive from the commitment (chosen for
  seed-restorability); the (key,nonce)-uniqueness margin is the commitment's 128-bit collision
  resistance. Differs from a randomized scheme; see `protocol-v1-decisions.md §3`.
- **PoC chain scope** — `node.zig` is an in-memory state machine. It now keeps a node-visible public
  **supply accumulator** (`Chain.supply`, the `issued − burned == shielded_pool + fees` invariant from
  public mint/fee deltas), but block-level commitments (state-root, nullifier-set-root, event-root,
  header) and PoW/mempool/networking/reorg-undo belong to the host chain (`rubble-node-zig`). The audit
  target is the circuit + the tx-validation logic, not a full node.
- **Toolchain** — the `.sframe` linker caveat above (real prove/verify via the script, not `zig build`).

**Self-review history (transparency):** four adversarial recheck passes during development found and
fixed real bugs — a fixed-seed (non-CSPRNG) ZK-blinding RNG; a node-layer `mint` **inflation** hole; a
verifier **panic** across the C ABI; and a missing `rho1` **persistence** constraint that would have
allowed a forged second nullifier per note. Each has a regression test.

**Implementation audit + remediation re-audit (Codex, 2026-06-28):** see
`docs/lattica-implementation-audit.md` and read the newest current re-audit section first. The original
**critical ghost-coin bug (C-01)** remains remediated; Round 2 live-node fixes for state-update
atomicity, transmitted-note ownership, and admission size checks were verified; Round 3 fixes for the
reusable verifier size cap, production compile-gating of genesis/test-only APIs and mock backends, and
README cleanup were verified. Production remains blocked on host-chain full-node consensus integration
(committed roots, reorg/snapshot/mempool policy, emission schedule, verifier attestation). Budget
independent review especially in the areas below.

## 6. Highest-risk areas to focus

- **AIR soundness** (`joinsplit_air.rs eval`) — that *every* public binding and persistent column is
  non-vacuous (the `rho1` bug was a missing persistence constraint that all happy-path tests passed).
  The corrupted-trace tests (`forged_*`, `*_persistence`) probe this class; extend them adversarially.
- **Cross-language consistency** — the Poseidon2 KATs + the witness / public-input **byte layouts**
  between `node.zig`/`lib.rs` (the node reconstructs the public inputs; a mismatch is silent without
  the real backend linked).
- **The verify boundary** (`ffi.zig` + `lib.rs`) — fail-closed + panic-isolation on adversarial proof
  bytes (now also `verifyHtlc` + the htlc public-input/witness codecs).
- **Double-spend / nullifier** logic in `node.zig` + the A1 position binding.
- **(v3) `htlc_air` soundness** (`docs/htlc-constraint-audit.md`) — focus on: the
  **mode-independent owner-nullifier** (the property that prevents a redeem-AND-refund double-spend —
  the highest-stakes v3 invariant); the **timeout compare** (direction + no field-wrap — a bug = a
  wrong-time spend, breaking swap safety); the `note_type`-gated MUXes being mutually exclusive and
  non-vacuous; and the **redeem hashlock binding** + its off-circuit SHA256 trust boundary (the node
  computes `redeem_hashlock = SHA256(preimage)`; the circuit proves equality only). Corrupted-trace
  negatives (`htlc_*_rejected`, the timeout/party/hashlock tests) probe these; extend adversarially.
- **(v3) `current_height` trust** — it is a node-pinned public input (`applyHtlc` rejects a mismatch);
  confirm the node cannot be made to validate at an attacker-chosen height, and that the `height <
  2^BITS` assumption the timeout argument relies on holds.

## 7. Out of scope — forward-looking roadmap (NOT audited)

The **cross-repo xchain swap stack** (`rubble-xchain-xfer`: the HTLC engine, the shielded backend, the
P2P swap protocol/versioning that drive a rubble↔BTC swap over `htlc_air`) and the **host chain**
(`rubble-node-zig`: block consensus/PoW/mempool/networking, committed roots, reorg undo, emission) are
**future / separate-repo work**, not part of this artifact. `docs/multi-asset-exchanges-issuance-cto.md`
(exchange integration, issuance/bridging beyond the single-hidden-asset substrate) is also future
design. The v3 audit gate covers the lattica side: `htlc_air` + `ShieldedHtlcTx` + their seam.

**Recursion (`lattica-prover-p3/src/recursion/`) is RESEARCH — NOT production, NOT audited, out of this
gate.** The in-circuit recursive STARK verifier ("the monolith", `MonolithAir`) **is built + validated
(R1–R5)**: one AIR that accepts iff `p3::verify(inner)` accepts (a real `JoinSplitAir` inner, non-hiding
and hiding), plus an aggregator that verifies K inner join-split proofs and folds them into a block
tx-root **byte-identical to `batch_joinsplit_air::batch_root`**. It is feature-gated behind
`--features recursion` (zero recursion symbols in the default staticlib — `lattica-prover-p3/scripts/check-abi-symbols.sh`),
on no production path, not externally audited, and the deeper self-recursion tree is deferred behind a
wrap. It is **not part of this audit gate**; the consolidated status + the review/improvement surface is
**`docs/recursion-aggregation-status.md`** (with `docs/recursion-design.md` §10,
`docs/recursion-verifier-audit.md`, and `docs/recursion-aggregation-params.md`).
**Batch aggregation, by contrast, IS production + validated** (`batch_joinsplit_air`/
`batch_htlc_air` + the node `applyBatch` path); include it in scope if this round covers the batch path.
