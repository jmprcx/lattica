# Block Production & Miner Incentives — heartbeat consensus (host-chain design)

> **Design note:** This describes host-chain policy outside Lattica's audited proof-system boundary.

**Status: design decision, recorded — not implemented in lattica.** Block production (cadence, PoW,
emission, fee distribution, miner payouts, finality, reorg) is **host-chain (`rubble-node-zig`)**
territory; this document records the agreed design and the primitives Lattica provides for it, and flags
the (future) lattica-side changes it would eventually need. Nothing here changes the audited shielded
core.

See also: `full-node-security-integration.md` (the consensus-critical validation pipeline + reorg/anchor
rules), `soundness-budget.md` (proof-size + the batch/recursion scaling story), `recursion-design.md`
(the scaling path referenced below), `multi-asset-exchanges-issuance-cto.md` (the shared-KEM deposit
scheme reused for payouts).

## 1. The decision in one paragraph
The chain mines a **header-only "heartbeat" block every 1.5 minutes** at **uniform PoW difficulty**, and
a **transaction block every 12 minutes** — i.e. each 12-minute cycle is **8 block slots: 7 heartbeats +
1 transaction block**. Transaction blocks carry exactly one batch proof (≤64 transactions, "one proof
per block"); heartbeats carry no transactions and no shielded state. A transaction block's fees (plus the
accrued heartbeat subsidies) are split **deterministically, weighted toward the transaction-block
producer**, with the remainder shared equally among the 7 heartbeat miners of the cycle. Miner payouts go
to **shared-KEM exchange-style deposit addresses** so a receiving pool/exchange detects its many small
reward payments in O(1).

## 2. Block cadence (the heartbeat model)
- **1.5-min heartbeat period, uniform difficulty.** Every block — heartbeat or transaction — is mined at
  the same PoW difficulty. *Uniform difficulty is mandatory*: a cheaper heartbeat would make rewriting a
  run of heartbeats cheap, which is exactly the work that buries (confirms) a transaction block.
- **Transaction block every 12 min** = every 8th slot ⇒ 7 heartbeats then 1 transaction block per cycle.
- **Sizes.** A heartbeat is just a header (~240 B; see §6 — no in-block coinbase note keeps it this
  small) and carries **no shielded-state delta**. A transaction block carries one batch proof
  (≤64 txs ≈ ~0.8 MB: ~600 KB proof + ~170 KB public data). A fully idle day costs ≈ 225 KB
  (960 heartbeats × ~240 B).
- **Why heartbeats help (Lattica-specific):**
  1. **Steady height↔time.** Lattica's HTLC timeouts are *height-denominated* (`current_height` vs
     `timeout`, pinned by `applyHtlc`/`applyHtlcBatch`), and the anchor window ages in blocks. A constant
     cadence keeps height a reliable proxy for elapsed time, so timeout/anchor windows are predictable.
  2. **Steady security accrual** decoupled from transaction volume.
  3. **Cheap shallow reorgs.** A heartbeat has no nullifiers/commitments/accumulator folds, so
     disconnecting it needs *zero* undo data (contrast the per-block undo data a transaction block
     requires — see `full-node-security-integration.md` §9). Spacing transaction blocks with 7 heartbeats
     means the common shallow reorgs land on state-free blocks.
- **Finality pairing (reasoning, not a built feature).** Pair the cadence with a finality gadget
  (checkpointing/BFT overlay) to *bound* reorg depth absolutely — capping the accumulator-undo cost and
  guaranteeing HTLC cross-chain atomicity. Heartbeats give steady probabilistic accrual; finality gives
  the hard ceiling.

## 3. Throughput and scaling
- **Baseline throughput** = 64 txs / 12 min ≈ **320 tx/hour (≈7,680/day)**, bounded by the ≥100-bit
  proven-soundness floor `MAX_BATCH_TILES = 64` (`src/node.zig`, `batch_joinsplit_air`; see
  `soundness-budget.md`).
- **The real scaling path is recursion** (`recursion-design.md`): a recursive aggregation circuit
  verifies many inner proofs and emits **one** proof regardless of transaction count, so throughput
  grows without linear block growth. The node interface is unchanged (recursion emits the same block
  tx-root).
- **Stopgap only:** a transaction block *could* carry multiple batch proofs / a higher `MAX_BATCH_TILES`,
  but that scales block size **linearly** — use it only as a temporary relief valve, not the plan.
- Other levers (moving note ciphertexts to a data-availability layer; KEM-amortizing payout notes) exist
  but are **out of scope here**; recursion is the chosen direction.

## 4. Miner rewards and lazy settlement
- Heartbeats carry **no in-block coinbase note** — this is what keeps them ~240 B and state-free (a
  shielded coinbase note would add a ~1.26 KB ciphertext + a tree append + a supply mint per block).
- The miner's payout address is named **in the PoW-committed header** (a fresh address per heartbeat —
  see §6), so the proof-of-work binds the reward to that address; it cannot be re-targeted without
  invalidating the block hash.
- **Lazy settlement:** accrued heartbeat subsidies are minted in the **next transaction block's
  coinbase**, routed through the gated `applyCoinbase` (`src/node.zig`) under the supply invariant
  `issued − burned == shielded_pool + fees_paid` (`SupplyState`/`SupplyDelta`, `src/protocol.zig`). All
  issuance stays on the single gated path; emission *amounts* are a host-chain policy (§8).

## 5. Deterministic fee split (weighted)
- **Rule.** For each 12-minute cycle, the transaction block's total public fees + the cycle's accrued
  subsidies are distributed: the **transaction-block producer takes a fixed weight `W`** (it assembled
  the block and carries/verifies the batch proof), and the **remainder splits equally among the 7
  heartbeat miners**. The split must be a **deterministic function of the block + the 7 committed
  heartbeat headers**, so every full node recomputes and validates the coinbase payout.
- **Why share fees (anti-fee-sniping).** Concentrating a block's fees in one payee tempts a miner to
  reorg and re-mine *that* block to grab them. Spreading fees across the heartbeat run dilutes the
  per-block jackpot. The anti-sniping property holds because the payees are fixed by *already-committed*
  headers: capturing the heartbeat shares requires re-mining the whole run (same cost as honest mining),
  so reorging a single transaction block only nets the producer's slice.
- **Realization (the multi-payee coinbase).** A coinbase is a join-split with `M_OUT = 2`, so 8 payees
  (7 heartbeat + 1 producer) need **⌈8/2⌉ = 4 coinbase outputs**. Recommended mechanism: **coinbase tiles
  inside the per-block batch** — the batch circuit already proves per-tile `mint`, so the change is
  mainly node-side: relax the current `mint == 0` rejection in `applyBatch`/`applyHtlcBatch`
  (`src/node.zig`) for a small number of *designated coinbase tiles*, and validate that their mints sum
  to the consensus-authorized `subsidy + fees`. **This is a future lattica-side change** (see §7), not a
  current capability. Alternatives: separate coinbase transactions, or a rolling reward pool that pays a
  bounded number of recipients per block.

## 6. Payout addresses (shared-KEM exchange deposit scheme)
- Payout addresses **reuse the shared-KEM exchange-deposit scheme** (`ExchangeViewingKey`,
  `exchangeAddressAt(index, epoch)`, `exchangeViewingKey(..., epoch)`, `detect`; `src/tx.zig`): one
  shared KEM key lets a
  receiving service attribute its many reward payments in **O(1)** (a single decapsulation per note, then
  a `recipient_id` lookup), instead of scanning a fresh diversified address per heartbeat.
- **Both usages supported:** (a) a self-run mining pool registers its own shared-KEM deposit address and
  detects its payouts in O(1); (b) a miner pays directly into a real exchange's deposit address, and the
  exchange does the O(1) detection.
- **Privacy tradeoff (explicit).** This rests on ML-KEM ciphertext anonymity (IK-CCA): outsiders can't
  link payments by ciphertext, but a leaked *hot* shared-KEM secret deanonymizes that epoch's payments
  (the *spend* key stays cold). Reward amounts are public regardless (they're consensus-authorized
  issuance + public fees). Use **epoch rotation** (the `epoch` parameter of `exchangeAddressAt` /
  `exchangeViewingKey`) to rotate payout addresses.
  Naming a fresh diversified address per heartbeat keeps individual heartbeat payouts unlinkable to
  outsiders; the shared-KEM grouping is the receiver's O(1)-detection convenience. See
  `multi-asset-exchanges-issuance-cto.md`.

## 7. Scope boundary

| Lattica provides (in-repo) | Host chain `rubble-node-zig` owns |
|---|---|
| Gated coinbase issuance (`applyCoinbase`, `mint == reward`) | Block cadence (1.5-min / 12-min), PoW + difficulty retarget |
| Public fee accounting + invariant (`SupplyState`, `fees_paid`) | Emission schedule (subsidy, halvings, cap) |
| Diversified + shared-KEM exchange addresses (`tx.zig`) | The deterministic fee-split rule + weight `W` |
| The ≤64-tx batch proof + `verifyBatch`/`batchRoot` seam | Heartbeat header format + the PoW-committed payout field |
| Height-pinned HTLC (`applyHtlc`, `current_height`) | Finality gadget, anchor-window depth, HTLC reorg cushions |

**Future lattica-side enablers this design implies (not built):**
- *Coinbase tiles inside a batch* — relax `applyBatch`/`applyHtlcBatch`'s `mint == 0` for designated
  coinbase tiles + validate the authorized total (medium effort; node + a small circuit-validation
  change). Enables the multi-payee coinbase in one proof (§5).
- Confirm shared-KEM exchange addresses are valid coinbase output recipients (§6).

## 8. Open host-chain parameters (to be fixed by `rubble-node-zig`)
- PoW difficulty + retarget algorithm; the PoW hash (sized for Grover — doubled output width).
- Block subsidy + emission curve (and whether heartbeat subsidy is non-zero, given lazy settlement).
- The producer fee weight `W` and the exact deterministic split formula.
- Finality interval (checkpoint depth).
- Anchor-window depth (≥ the reorg cushion).
- HTLC timeout cushion, in blocks (so a near-boundary redeem can't be reorged past its timeout).
