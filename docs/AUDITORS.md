# Lattica — external audit handoff (start here)

Lattica is a **quantum-safe, Zcash-style shielded transaction layer** (it replaces Zcash
Sapling/Orchard): a Plonky3 zero-knowledge **join-split** circuit + a Zig protocol layer, on a
shielded-only value model. This is the entry point for the external security audit of the **v1
single-asset** protocol. Read this first, then the deep-dive docs in §4.

> **Audit commit:** the tip of this branch (single-asset v1). Forward-looking multi-asset / bridge /
> cross-chain work is deliberately **not** on this branch (see §6) — the audit is the gate before it.

## 1. What to audit (scope)

**In scope:**
- **The circuit** — `lattica-prover-p3/src/joinsplit_air.rs` (the single production AIR: the N-in/M-out
  join-split statement), with building blocks `poseidon2_air.rs` (the Poseidon2-Goldilocks permutation
  AIR) and `spend_air.rs`. The verify/prove **C ABI** + (de)serialization + canonical field parsing in
  `lattica-prover-p3/src/lib.rs`.
- **The Zig protocol seam** — `src/poseidon2.zig` (on-chain hashing, must equal the circuit),
  `src/{tx,tree,primitives}.zig` (note model, commitment, nullifier, Merkle tree, key hierarchy +
  diversified addresses + incoming viewing key), `src/node.zig` (the shielded-tx state machine:
  verify→anchor→nullifier→apply), `src/ffi.zig` (the fail-closed verifier/prover boundary).

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
  (detect/decrypt without spend authority).

## 3. Build, test & reproduce

Toolchain: **Rust 1.96** (edition 2021, no pinned toolchain), **Zig 0.16.0**, a C compiler (GCC 16
here) for the cross-language link.

```sh
# 1. Circuit + ABI tests (incl. adversarial corrupted-trace soundness tests).
cd lattica-prover-p3 && cargo test --release

# 2. The Zig protocol suite — incl. the Poseidon2 KATs that pin on-chain == circuit byte-for-byte.
zig build test            # (from the repo root)

# 3. The REAL cross-language path: prove (Rust) → verify (Rust) → tamper-reject → double-spend-reject,
#    plus the live node driving the real prover/verifier in-process. Builds the Zig side as an object
#    and links with the system cc (see the caveat below).
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
3. **`docs/soundness-budget.md`** — the C-04 proven/conjectured security accounting (~103 / ~127-bit).
4. **`docs/protocol-v1-decisions.md`** — the deliberate v1 parameter decisions + limitations
   (single-asset, key model, note randomness, issuance, the deterministic-encryption interaction).

Also current: `docs/lattica-implementation-audit.md` (the implementation audit + remediation log) and
`docs/remediation-status.md` (live status). `docs/full-node-security-integration.md` is the production
full-node checklist (host-chain scope). **Everything else in `docs/` is historical / reference-only**
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
**critical ghost-coin bug (C-01)** remains remediated, and Round 2 live-node fixes for state-update
atomicity, transmitted-note ownership, and admission size checks were verified. Production is still
blocked on full-node consensus integration plus hardening of the reusable verifier boundary,
genesis/test-only issuance APIs, mock backend build gating, and stale public docs. Budget independent
review especially in the areas below.

## 6. Highest-risk areas to focus

- **AIR soundness** (`joinsplit_air.rs eval`) — that *every* public binding and persistent column is
  non-vacuous (the `rho1` bug was a missing persistence constraint that all happy-path tests passed).
  The corrupted-trace tests (`forged_*`, `*_persistence`) probe this class; extend them adversarially.
- **Cross-language consistency** — the Poseidon2 KATs + the witness / public-input **byte layouts**
  between `node.zig`/`lib.rs` (the node reconstructs the public inputs; a mismatch is silent without
  the real backend linked).
- **The verify boundary** (`ffi.zig` + `lib.rs`) — fail-closed + panic-isolation on adversarial proof
  bytes.
- **Double-spend / nullifier** logic in `node.zig` + the A1 position binding.

## 7. Out of scope — forward-looking roadmap (NOT audited)

`docs/multi-asset-exchanges-issuance-cto.md` (multi-asset, exchange integration, issuance/bridging
designs) and the shielded-cross-chain-swap plan are **future work**, gated *behind* this audit. The
multi-asset substrate (a first step) is parked on the `v3/multi-asset` branch, intentionally excluded
from this audit artifact.
