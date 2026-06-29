# Lattica Full Node Security Integration Plan

**Status:** production integration guidance  
**Basepoints:** `docs/audit-scope.md`, `docs/transaction-stack-audit.md`, `docs/remediation-status.md`, `SPEC.md`  
**Audience:** full-node, consensus, wallet, prover, and audit-tool implementers

This document turns the transaction-stack audit and supply-audit discussion into a full-node implementation plan. It is intentionally broader than proof verification: ghost-coin prevention depends on proof soundness, canonical consensus rules, supply accounting, state commitments, mempool policy, reorg handling, and independent auditability.

## Goals

- Make total supply publicly recomputable from genesis without decrypting shielded notes.
- Prevent ghost coins from invalid proofs, overflow, duplicate spends, malformed encodings, invalid issuance, or implementation divergence.
- Define which full-node controls are consensus-critical and which are optional operator/auditor enhancements.
- Provide default choices for production while recording viable alternatives.

## Current Repo Status

- Live transaction validation now uses the Plonky3 join-split proof path end to end: ownership, commitment opening, Merkle membership, nullifier derivation, value range, balance, output commitments, `mint`, and `tx_binding` are proven by `lattica-prover-p3` and checked through the Rust C ABI.
- The original C-01 ghost-coin output-commitment binding bug is remediated; see `docs/lattica-implementation-audit.md`.
- Round 2 verified live-node state-update atomicity, transmitted-note ownership, and admission size checks. Round 3 added reusable verifier-boundary size limits (M-08), and **compile-gated** the genesis/test issuance API (`bootstrapMint`) and the mock backend out of production builds (M-09/M-10, via `lattica_production`; see `src/production_probe.zig` / `zig build check-production`). Remaining blockers are host-chain consensus integration: canonical live transaction/block encoding, state-root / nullifier-set-root / event-root commitments, reorg undo logs, snapshot validation, and mempool proof-cache policy.
- The v3 HTLC layer adds `htlc_air` and `ShieldedHtlcTx`: HTLC note ownership, redeem/refund party tags, hashlock binding, timeout checks, hidden asset id, and mode-independent nullifier are proven in-circuit, while the node pins `current_height` to the consensus block height and derives `redeem_hashlock = SHA256(preimage)`.
- This document remains the full-node production checklist: `src/node.zig` is an in-memory shielded transaction state machine, not a complete production consensus node.

## HTLC Full-Node Requirements

The v3 HTLC transaction stack is only safe in production if the full node supplies the off-circuit context deterministically:

- `applyHtlc(tx, at_height)` must receive `at_height` from block consensus state, never from mempool or wallet input. Nodes should reject blocks whose HTLC transaction `current_height` does not equal the block height under the active consensus rules.
- Mempool policy must treat redeem and refund attempts for the same HTLC nullifier as conflicts. A block may include at most one; replay/reorg handling must restore the nullifier set and note roots exactly.
- Redeem preimages are public transaction data and should be indexed in a canonical event stream so cross-chain watchers can claim the opposite leg. The event root should commit preimage events, HTLC note commitments, and transaction ids.
- HTLC lock output 0 intentionally uses a placeholder ciphertext; wallets and watch services need a lock-descriptor/commitment index instead of relying only on note trial decryption.
- Timeout policy must define reorg cushions and cross-chain height/time conversion outside this package. Consensus should specify anchor windows and finality assumptions for accepting lock, redeem, and refund transactions.
- Replay from genesis must recompute identical supply, note-root, nullifier-root, and event-root outcomes without wallet secrets.

## Core Supply Invariant

Every fully validating node must maintain a supply state that can be recomputed from genesis:

```text
issued - burned = transparent_supply + shielded_pool_value + pending_or_paid_fees
```

For a shielded-only deployment, this simplifies to:

```text
issued - burned = shielded_pool_value + pending_or_paid_fees
```

The node must never learn individual shielded note values solely to audit supply. Instead, each accepted transaction must prove a correct public delta:

```text
sum(input_values) + public_deposit + minted
  = sum(output_values) + fee + public_withdrawal + burned
```

Private values stay private. The proof enforces the equation, and public counters track explicit issuance, burns, fees, deposits, and withdrawals.

## Block Production & Miner Incentives

Block production is host-chain (`rubble-node-zig`) scope; the agreed design is recorded in detail in
**`block-production-consensus.md`**. Summary:

- **Cadence:** a header-only **heartbeat block every 1.5 min** at uniform PoW difficulty, and a
  **transaction block every 12 min** — each 12-min cycle = 7 heartbeats + 1 transaction block.
  Heartbeats are ~240 B and carry no shielded-state delta (so shallow reorgs that land on them need no
  per-block undo data — see Reorg and Snapshot Safety); transaction blocks carry one batch proof
  (≤64 txs). Steady cadence keeps height a reliable proxy for time, which the height-denominated HTLC
  timeouts and the anchor window depend on.
- **Rewards:** heartbeats name a payout address in the PoW-committed header but mint no in-block note;
  subsidies settle lazily in the next transaction block's coinbase via the gated `applyCoinbase` under
  the supply invariant above.
- **Fees:** a transaction block's fees + accrued subsidies are split **deterministically, weighted toward
  the transaction-block producer**, remainder equally among the cycle's 7 heartbeat miners — a function
  of the block + the committed heartbeat headers (anti-fee-sniping). Realized via a multi-payee coinbase
  (8 payees ⇒ 4 outputs at `M_OUT = 2`); the recommended mechanism (coinbase tiles inside the batch) is a
  noted future lattica-side change.
- **Payout addresses:** the shared-KEM exchange-deposit scheme (O(1) detection) for pools/exchanges.
- **Scaling:** baseline ~320 tx/hr (64 / 12 min); the scaling path is **recursion** (`recursion-design.md`),
  not linear block growth.

## Consensus-Critical Full Node Pipeline

### 1. Decode and Canonicalize

Reject before expensive checks if any consensus object fails canonical parsing.

- Version and network id must match the active consensus rules.
- Integers must use a single canonical width and endian convention.
- Field elements must be `< P`; no alternate encodings.
- Proofs, signatures, public keys, commitments, and ciphertexts must have exact lengths.
- Trailing bytes are rejected everywhere.
- Transaction ids are computed from canonical bytes only.

**Default:** canonical binary encoding with explicit version byte and domain-separated transaction digest.  
**Option:** use a schema language for tooling, but consensus should verify exact byte layout rather than trusting schema libraries.

### 2. Validate Transaction Context

For each transaction, verify cheap context before proof work.

- Chain id, epoch, feature flags, and tx version are accepted.
- Fee policy and minimum relay fee are met.
- Inputs, outputs, proof count, and byte size are within limits.
- Join-split proof is bound to the canonical `tx_binding` digest; any future host-chain signature
  layer verifies under a separate domain.
- Public mint/deposit/withdraw/burn fields are well formed and permitted by transaction type.

**Default:** one canonical tx digest (`tx_binding`) bound into every join-split proof; any host-chain
signature or authorization layer must use a separate domain if added later.
**Option:** separate digest domains for consensus validation, wallet authorization, and mempool policy to avoid cross-use.

### 3. Verify Shielded Spend Proofs

The production spend proof must prove all private spend facts in one statement:

- note commitment opening matches the committed leaf;
- note is a member of the public anchor tree;
- nullifier is correctly derived from note secrets and position;
- spend authority is bound to the note owner;
- input and output values are in range;
- balance equation holds with no field wraparound;
- output commitments encrypt/commit to the same values used in balance;
- transaction digest is bound into the proof.

**Default:** vetted transparent FRI-STARK framework with extension-field challenges and a documented soundness target above 120 bits.  
**Option:** keep the Zig reference STARK as a differential-test oracle only; it should not be the production verifier.

### 4. Enforce Nullifier and Anchor Rules

For each block and transaction:

- every anchor must be a known historical note commitment root within the permitted anchor window;
- every nullifier must be unseen in the chain state;
- every nullifier must be unique within the transaction and block;
- nullifier insertion happens only after all transaction checks pass.

**Default:** consensus state includes a cryptographic nullifier-set root committed in every block header.  
**Option:** use an append-only nullifier Merkle tree, sparse Merkle tree, or authenticated key-value accumulator; choose one and make it part of consensus.

### 5. Update Supply State With Checked Arithmetic

All supply counters use checked arithmetic and reject overflow.

Required counters:

```text
issued
burned
shielded_pool_delta
transparent_delta
fees_pending
fees_paid
```

Each transaction returns a deterministic `SupplyDelta`:

```text
SupplyDelta {
  issued,
  burned,
  shielded_pool_delta,
  transparent_delta,
  fee,
}
```

For ordinary shielded transfers, `shielded_pool_delta = 0` except fees if fees leave the pool. For mints, burns, bridge deposits, or withdrawals, the corresponding public event must explain the delta.

**Default:** full nodes recompute supply counters from genesis and reject any block whose declared counters do not match.  
**Option:** store per-block supply deltas for fast indexer queries, but treat them as derived data unless committed by consensus.

### 6. Recompute State Commitments

After applying a block, the node recomputes all roots and compares them to the block header.

Required commitments:

```text
BlockCommitments {
  tx_root,
  note_root,
  nullifier_root,
  supply_root,
  event_root,
}
```

Recommended additional commitments:

```text
proof_root,
fee_root,
withdrawal_root,
consensus_params_hash
```

**Default:** block headers commit to all consensus state roots needed for independent replay and light-client verification.  
**Option:** keep some roots out of the header for PoC simplicity, but production should not rely on uncommitted node-local state.

## Security Option Matrix

| Area | Recommended default | Alternative | Security note |
|---|---|---|---|
| Supply model | Shielded-only with explicit mint/burn events | Mixed transparent/shielded turnstile | Turnstiles improve auditability but add bridge accounting risk. |
| Supply audit | Public recomputation from genesis | Trusted auditor reports | Consensus must not depend on trusted reports. |
| Proof system | Vetted transparent FRI-STARK with extension-field challenges | Local/reference STARK | Reference STARK is useful for testing, not production. |
| Hash in circuit | Published Poseidon2/Rescue-Prime parameters | Locally generated constants | Local constants need separate cryptanalysis. |
| Value privacy | Values hidden; balance/range proven | Values public to validators | Public values simplify audit but weaken privacy. |
| View/audit keys | Optional, non-consensus | Mandatory regulated disclosure | Useful for compliance; not a substitute for proof soundness. |
| Nullifier set | Header-committed authenticated set | Node-local hash set | Node-local only is not enough for snapshots/light clients. |
| Snapshots | Root-verified plus checkpointed | Operator-trusted snapshot | Trusted snapshots can hide ghost coins. |
| Mempool | Preverify and cache by canonical tx hash | Verify only at block time | Preverify reduces DoS and invalid block risk. |
| Metrics | Invariant drift alerts and proof failure counters | Logs only | Metrics are operational controls, not consensus. |

## Full Node Interfaces

These are implementation targets, not current Zig APIs.

```zig
const SupplyState = struct {
    issued: u128,
    burned: u128,
    shielded_pool: u128,
    transparent: u128,
    fees_pending: u128,
    fees_paid: u128,
};

const SupplyDelta = struct {
    issued: i128,
    burned: i128,
    shielded_pool: i128,
    transparent: i128,
    fee: u128,
};

const BlockCommitments = struct {
    tx_root: Hash32,
    note_root: Hash32,
    nullifier_root: Hash32,
    supply_root: Hash32,
    event_root: Hash32,
};

const NodeSecurityPolicy = struct {
    proof_policy: ProofPolicy,
    audit_mode: AuditMode,
    mempool_limits: MempoolLimits,
    snapshot_policy: SnapshotPolicy,
};

const VerificationReport = struct {
    txid: Hash32,
    accepted: bool,
    reason: RejectReason,
    supply_delta: SupplyDelta,
    proof_time_ms: u64,
};
```

Implementation requirements:

- reports are deterministic and safe to expose to indexers;
- rejection reasons do not leak private witness values;
- supply deltas are public and root-committed;
- signed/serialized reports are optional operator tooling, not consensus inputs.

## Mempool Security

The mempool should protect full nodes from proof-verification DoS and consensus divergence.

Required policy:

- canonical decode before admission;
- reject duplicate nullifiers already in chain or mempool;
- reject transactions whose anchor is unknown or too old;
- enforce max proof bytes, max actions, and max ciphertext bytes;
- verify signatures before proofs;
- cache proof verification by canonical transaction hash and consensus parameter hash;
- evict cached results when consensus parameters change.

Recommended options:

- **Strict mode:** preverify every proof before relay. Best for security, more CPU.
- **Hybrid mode:** perform cheap checks and queue proof verification before mining/block inclusion. Better throughput, more mempool complexity.
- **Block-only mode:** not recommended for production because it relays invalid expensive transactions too easily.

## Reorg and Snapshot Safety

A production full node must be able to disconnect and reconnect blocks without corrupting audit state.

Per-block undo data:

- inserted note commitments and previous note root;
- inserted nullifiers and previous nullifier root;
- supply delta and previous supply state;
- fee accounting changes;
- event root changes;
- anchor-window changes.

Snapshot acceptance rules:

- snapshot declares block height, block hash, and all consensus state roots;
- node verifies snapshot roots against a trusted checkpoint or replays from genesis;
- supply counters are included in the state root;
- nullifier set and note tree roots are independently checked;
- snapshots do not bypass canonical serialization or proof rules for future blocks.

**Default:** snapshots are performance tools only; genesis replay remains the canonical audit path.

## Observability and Audit Exports

Full nodes should expose enough public data for independent auditors to detect supply issues.

Required audit exports:

- per-block supply delta;
- cumulative supply state;
- note root and nullifier root;
- issuance, burn, deposit, withdrawal, and fee events;
- proof-verification aggregate counts;
- rejected block and transaction reason codes.

Recommended alerts:

- supply invariant drift;
- block header root mismatch;
- duplicate nullifier attempt;
- unexpected issuance event;
- proof failure spike;
- anchor-window failure spike;
- snapshot root mismatch;
- verifier implementation disagreement.

Optional non-consensus tooling:

- threshold view-key audit for regulated deployments;
- auditor-run indexers;
- independent Rust/Zig verifier cross-check service;
- periodic signed audit statements over public counters.

## Implementation Phases

### P1: Protocol Finalization

- Finalize transaction and block formats.
- Decide shielded-only versus mixed transparent/shielded supply model.
- Specify canonical encodings, digest domains, state roots, and supply counters.
- Define public event types for mint, burn, deposit, withdrawal, and fees.

### P2: Production Spend Proof

- Move to vetted FRI-STARK framework with production soundness parameters.
- Implement full spend statement: ownership, commitment opening, membership, nullifier, range, balance, and tx binding.
- Replace local Rescue parameters with published in-circuit hash parameters.
- Add canonical proof serialization and verifier APIs.

### P3: Full Node State Engine

- Implement authenticated note tree and nullifier set roots.
- Add `SupplyState`, `SupplyDelta`, and block commitment verification.
- Implement reorg-safe undo logs and snapshot validation.
- Make all arithmetic checked and all consensus state updates atomic.

### P4: Mempool and Networking

- Add mempool preverification, nullifier conflict checks, fee policy, and proof cache.
- Rate-limit proof verification and large transaction relay.
- Ensure mempool policy cannot weaken consensus validation.

### P5: Audit and Testnet

- Run independent verifier/indexer cross-checks.
- Replay from genesis and compare supply roots across implementations.
- Complete cryptographic audit of the proof statement and framework integration.
- Launch testnet with invariant monitoring and incident response runbooks.

## Test Plan

Consensus tests:

- valid shielded transfer preserves supply;
- forged balance proof rejected;
- value range overflow rejected;
- duplicate nullifier rejected within tx, block, mempool, and chain;
- unknown/stale anchor rejected;
- malformed canonical encoding rejected;
- wrong tx-binding digest rejected;
- wrong public supply delta rejected;
- block header state-root mismatch rejected.

Supply tests:

- genesis replay reproduces final supply state;
- mint increases `issued` and shielded pool exactly once;
- burn decreases shielded pool and increases `burned`;
- fee moves from shielded value to fee accounting without changing total supply;
- deposit/withdrawal events match public event roots;
- all counters reject overflow and underflow.

Operational tests:

- reorg disconnect/reconnect restores note root, nullifier root, and supply state;
- snapshot import verifies all roots and counters;
- proof cache invalidates across consensus parameter changes;
- independent verifier agrees on accepted/rejected blocks;
- metrics fire on duplicate nullifier, proof failure spike, and supply drift.

## Production Release Gates

Do not enable value-bearing production use until:

1. full spend proof is live in node validation;
2. production proof framework and in-circuit hash parameters are selected and audited;
3. public supply counters and state roots are committed by block headers;
4. all value arithmetic uses checked wide counters;
5. canonical serialization is enforced across every consensus object;
6. nullifier set and note tree are authenticated and snapshot-safe;
7. at least two independent implementations or verifier paths replay the same chain to the same roots;
8. monitoring and incident response procedures exist for invariant drift and verifier disagreement.

## Non-Goals

- This document does not define a final block format.
- It does not select a final FRI-STARK framework.
- It does not make view keys mandatory.
- It does not replace a cryptographic audit of the production spend proof.
