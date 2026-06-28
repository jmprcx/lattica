# Lattica Implementation Audit

**Date:** 2026-06-27  
**Entry point:** `docs/AUDITORS.md`  
**Scope covered:** Plonky3 join-split AIR, Rust C ABI, Zig FFI seam, protocol hashing, transaction construction, node state machine, note/key/encryption code, canonical codecs, tests, and operational/security areas needed by a production full node.

## Executive Summary

The Plonky3 join-split stack is a major improvement over the earlier reference design: the production AIR uses Poseidon2-Goldilocks, 128-bit spend authority, 128-bit note randomness, N-in/M-out balance with `mint`, extension-field challenges, and a fail-closed verifier boundary. The documented reproduction suite mostly passes, including the real Rust prover/verifier C harness and the live Zig-node-to-Rust-prover/verifier integration path.

However, the current Zig node has a critical transaction binding gap: the proof binds `out_cms`, but the node appends `outputs[j].cm` to the commitment tree and does not require `outputs[j].cm == out_cms[j]`. This allows a transaction to prove balance for one output commitment while inserting a different, unproven commitment into the note tree. If the inserted commitment is a high-value note known to the attacker, it can later be spent as a ghost coin.

Production use must be blocked until the critical finding is fixed and regression-tested.

## Verification Performed

Commands run:

```sh
cd lattica-prover-p3 && cargo test --release
zig build test
scripts/run-real-integration.sh
```

Results:

- `cargo test --release`: passed; 28 Rust tests.
- `zig build test`: passed.
- `scripts/run-real-integration.sh`: initially failed inside the sandbox while Zig tried to load its stdlib; rerun outside the sandbox passed.
- Real integration pass included Rust prove, Rust verify, tampered-anchor reject, double-spend reject, Zig node real prove/verify accept, replay reject, and tampered `out_cms` reject.

## Critical Findings

### C-01: Node inserts unproven output commitments

**Severity:** Critical  
**Area:** Zig node / join-split public-input binding  
**Files:** `src/node.zig`, `src/ffi.zig`, `lattica-prover-p3/src/lib.rs`

The join-split proof public inputs include `out_cms`:

- `src/node.zig:93-101` builds `JoinSplitPublicInputs` from `self.out_cms`.
- `src/ffi.zig:53-64` encodes `out_cms` into the C ABI public-input layout.
- `lattica-prover-p3/src/lib.rs:51-64` parses those `out_cm_j` field elements for verification.

But the node applies a different value:

- `src/node.zig:344-346` appends `o.cm` from each `TransmittedNote` to the note tree.
- `src/node.zig:73-90` hashes `self.out_cms`, KEM ciphertexts, and encrypted note bytes into `tx_binding`, but not `outputs[j].cm`.
- There is no check that `t.outputs[j].cm == t.out_cms[j]`.

Impact:

1. Attacker builds a valid proof with balanced `out_cms`.
2. Attacker submits `outputs[j].cm` for a different note commitment, e.g. a high-value note whose opening they know.
3. `tx_binding` and proof verification still pass because they do not bind `outputs[j].cm`.
4. The node appends the unproven `outputs[j].cm` to the tree.
5. The attacker later spends that inserted note commitment, creating ghost value.

The existing tamper test at `src/node.zig:493-507` mutates `out_cms[0]`, which correctly fails, but it does not mutate `outputs[0].cm`, which is the consensus-applied value.

Required fix:

- During validation, require `t.outputs[j].cm == t.out_cms[j]` for every output before proof verification or before applying state.
- Prefer eliminating the duplicate source of truth: either store only `out_cms` in `ShieldedTx` and derive transmitted-note commitments from it, or make `publicInputs()` read output commitments from `outputs[j].cm`.
- Add adversarial tests:
  - build a valid transaction;
  - mutate `t.outputs[0].cm` without changing `t.out_cms[0]`;
  - assert `verifyAndApply` rejects;
  - repeat through the real Rust verifier path.

## High Findings

### H-01: No production supply accumulator or block commitment exists in the live node

**Severity:** High for production readiness  
**Area:** full-node supply audit / ghost-coin detection  
**Files:** `src/node.zig`, `src/protocol.zig`, `docs/full-node-security-integration.md`

The in-memory `Chain` tracks commitment tree roots, anchors, nullifiers, and transmitted notes. It does not maintain or commit a production `SupplyState`, per-block supply delta, state root, nullifier-set root, event root, or block header commitment. `applyCoinbase` gates a caller-provided `reward`, but there is no chain-level supply accumulator.

This is consistent with the documented PoC scope, but it is not enough for a production full node. A node must publicly recompute `issued - burned = shielded_pool + fees` from genesis and reject blocks with mismatched committed counters.

Required fix:

- Add consensus-level supply state and block commitments before production.
- Treat `src/protocol.zig`'s `SupplyState` as a starting point, but wire it into the live node/block path.
- Add genesis replay, reorg, snapshot, mint, fee, and burn invariant tests.

### H-02: Live validation does expensive proof verification before cheap consensus rejects

**Severity:** High/Medium DoS risk  
**Area:** node validation order  
**File:** `src/node.zig`

`applyChecked` calls `ffi.verifyJoinSplit` first (`src/node.zig:318-323`), then checks:

- `mint == allowed_mint` (`src/node.zig:324-328`);
- anchor known (`src/node.zig:330-331`);
- nullifier duplicates and spent set (`src/node.zig:333-340`).

This means invalid transactions with illegal issuance, unknown anchors, or already-spent nullifiers still force full proof verification before rejection.

Required fix:

- Reorder cheap deterministic checks before proof verification:
  1. `outputs[j].cm == out_cms[j]`;
  2. mint/issuance gate;
  3. anchor known;
  4. duplicate/spent nullifiers;
  5. proof verification.
- Keep proof verification before state mutation.
- Mirror the order in mempool admission.

## Medium Findings

### M-01: C ABI prover does not validate all output pointer arguments

**Severity:** Medium hardening  
**Area:** C ABI safety  
**File:** `lattica-prover-p3/src/lib.rs`

`lattica_joinsplit_prove` checks `witness_ptr`, `proof_out`, and `pi_out` for null (`src/lib.rs:297-310`), but it writes through `proof_len` and `pi_len` later (`src/lib.rs:330-333`) without null checks. `lattica_joinsplit_prove_demo` similarly writes to output pointers without null checks.

These prover functions are wallet-side, not consensus verification, so this is not a direct remote verifier exploit. Still, the ABI contract says fail-closed behavior, and null output length pointers should return an error rather than causing undefined behavior.

Required fix:

- Reject null `proof_len` and `pi_len`.
- Add C ABI tests for every null pointer argument.
- Apply the same hardening to the demo prover function or clearly mark it test-only and keep it out of production headers.

### M-02: Consensus codec bounds check can overflow before rejecting

**Severity:** Medium/Low parser hardening  
**Area:** canonical encoding  
**File:** `src/codec.zig`

`Reader.getBytes` checks `self.pos + n > self.data.len` (`src/codec.zig:72-76`). In safe builds, a maliciously large `n` can trigger an integer-overflow panic before returning `Error.Truncated`; in optimized builds, wrapping arithmetic can make parser behavior harder to reason about.

Required fix:

- Replace with `if (n > self.data.len - self.pos) return Error.Truncated;`, after ensuring `self.pos <= self.data.len`.
- Add tests with `varBytes` length near `maxInt(u32)` on a short buffer.

### M-03: Witness bit parsing is non-canonical

**Severity:** Medium/Low, wallet/prover boundary  
**Area:** C ABI witness parsing  
**File:** `lattica-prover-p3/src/lib.rs`

`parse_joinsplit_witness` parses membership bits with `b[off] != 0` (`src/lib.rs:224-228`). Any nonzero byte is treated as `true`. This does not affect verifier consensus soundness because witnesses are private prover inputs, but it violates the "canonical witness layout" expectation and can hide tooling bugs.

Required fix:

- Accept only `0` or `1` for path bits.
- Add a malformed witness test using bit byte `2` and expect `lattica_joinsplit_prove` to return nonzero.

### M-04: Zig prover wrapper can return a resized slice without owning-size certainty

**Severity:** Low/Medium memory-management hardening  
**Area:** Zig FFI prover wrapper  
**File:** `src/ffi.zig`

`proveJoinSplit` allocates a 2 MiB buffer and returns `allocator.realloc(buf, proof_len) catch buf[0..proof_len]` (`src/ffi.zig:165-174`). If `realloc` fails, the returned slice length no longer matches the original allocation length for allocators that require exact-size free semantics.

Required fix:

- If shrinking fails, return the original `buf` with original length plus a separate proof length, or copy into a new exact-sized allocation and free the original.
- Add allocator tests with a failing-realloc allocator.

## Low / Documentation Findings

### L-01: Documentation status is inconsistent with the current node cutover

**Severity:** Low, audit-process risk  
**Area:** audit handoff documentation  
**Files:** `docs/remediation-status.md`, `docs/AUDITORS.md`, `src/node.zig`

`docs/AUDITORS.md` describes the current Plonky3 join-split path as the audit target. `src/node.zig` is also cut over to `ffi.verifyJoinSplit`. But `docs/remediation-status.md` still says the full spend is "NOT live" and references older `lattica_spend_verify` cutover tasks.

Required fix:

- Update `docs/remediation-status.md` to reflect the current `lattica_joinsplit_*` path.
- Mark `src/protocol.zig` as either live, transitional, or reference-only.
- Keep one current audit entry point to avoid reviewers auditing obsolete seams.

### L-02: `src/protocol.zig` and `src/node.zig` define divergent transaction shapes

**Severity:** Low/Medium integration risk  
**Area:** transaction format ownership  
**Files:** `src/protocol.zig`, `src/node.zig`

`src/protocol.zig` defines a canonical serialized `ShieldedTx` where outputs contain `cm` and the signable digest covers that `cm`. The live `src/node.zig` `ShieldedTx` separately stores `out_cms` and transmitted `outputs`, and its `txBinding` covers `out_cms` plus output ciphertexts/KEM ciphertexts but not `outputs[j].cm`.

This divergence likely contributed to C-01. Production should have exactly one transaction format and one binding digest implementation.

Required fix:

- Consolidate the live node format and canonical codec.
- Add cross-tests proving `deserialize(serialize(tx))`, `txBinding`, FFI public inputs, and state application all use the same output commitments.

## Positive Findings

- The production AIR has adversarial tests for wrong anchor, wrong nullifier, wrong output commitment, wrong fee, wrong tx binding, out-of-range values, forged commitment chain, dummy-note padding, and position-derived nullifier behavior.
- Public input parsing rejects non-canonical Goldilocks limbs.
- The verifier C ABI catches panics around proof deserialization/verification and returns reject.
- The real cross-language proof path passes when run outside the sandbox.
- Poseidon2 KATs pin native Zig hashing against circuit outputs.
- The node enforces mint authorization through `verifyAndApply` versus `applyCoinbase`.
- Nullifiers are checked both against chain state and for duplicates within the transaction.
- Output note encryption authenticates against the note commitment for wallet decryption.

## Additional Audit Areas Added Beyond `docs/AUDITORS.md`

The handoff document focuses on circuit, ABI, and Zig protocol seam. A production audit should also include:

1. **Full-node supply accounting:** block-level supply accumulators, genesis replay, fee accounting, burns, rewards, and state-root commitments.
2. **Mempool DoS policy:** proof verification cache, fee policy, nullifier conflict handling, anchor freshness, and per-peer limits.
3. **Canonical transaction format ownership:** one source of truth for tx encoding, tx binding, FFI public inputs, and state application.
4. **Reorg and snapshot safety:** undo logs for nullifiers, note roots, output notes, supply counters, and anchor windows.
5. **FFI fuzzing:** arbitrary proof bytes, arbitrary public input bytes, null pointers, oversized lengths, short buffers, panic isolation, and allocator failure.
6. **Wallet/prover witness safety:** canonical witness parsing, path-bit validation, deterministic output randomness uniqueness, and dummy-note policy.
7. **Operational monitoring:** proof failure rates, duplicate nullifier attempts, issuance attempts, state-root mismatches, and independent verifier disagreement.

## Recommended Immediate Fix Order

1. Fix C-01 by enforcing `outputs[j].cm == out_cms[j]` or removing the duplicate commitment field from the state-application path.
2. Add the adversarial test that mutates only `outputs[j].cm`.
3. Reorder `applyChecked` so cheap rejects happen before proof verification.
4. Harden FFI null-pointer checks and witness bit parsing.
5. Fix `codec.Reader.getBytes` overflow-safe bounds check.
6. Consolidate or clearly deprecate the duplicate transaction formats.
7. Update `docs/remediation-status.md` to match the current Plonky3 join-split cutover.

---

# Developer Remediation Response (added post-audit)

All findings addressed on the audit branch. Re-validated end to end: **30 Rust tests**
(`cd lattica-prover-p3 && cargo test --release`), the **full Zig suite** (`zig build test`), and the
**real cross-language integration** (`scripts/run-real-integration.sh`) — which now rejects the C-01
ghost-coin attack through the **real Rust verifier** on a fresh tx.

| Finding | Resolution | Where |
|---|---|---|
| **C-01** unproven output commitments (Critical) | **Eliminated the duplicate source of truth** (the audit's preferred fix). Removed the separate `ShieldedTx.out_cms` field; `outputs[j].cm` is now the single value that is (a) appended to the tree, (b) fed to the verifier as a public input (`publicInputs().out_cms` derives from it via `outCms()`), and (c) hashed into `tx_binding`. A swapped/ghost commitment changes the proof's public inputs *and* the binding ⇒ rejected before any state mutation. | `src/node.zig` (`ShieldedTx`, `outCms()`, `txBinding`, `publicInputs`, `buildTransfer`) |
| C-01 test | New `node.zig` test **C-01: a swapped/ghost output commitment is rejected and not applied** (mutates `outputs[0].cm`, asserts `BadAuthProof` *and* unchanged anchor). Repeated through the **real Rust verifier** in `src/integration_node.zig`. | `src/node.zig`, `src/integration_node.zig` |
| **H-02** verify-before-cheap-checks (DoS) | Reordered `applyChecked`: issuance gate → anchor-known → nullifier dup/spent → **then** proof verification → then apply. (The `outputs[j].cm == out_cms[j]` step is moot under the C-01 single-source fix.) | `src/node.zig:applyChecked` |
| **H-01** no live supply accumulator | Wired `protocol.SupplyState` into the live `Chain`. Every applied tx (and the bootstrap `mint`) updates the **public** delta (mint/fee; checked wide arithmetic), preserving `issued − burned == shielded_pool + fees_paid`. Note values stay hidden — the per-tx hidden-value balance is guaranteed by the proof; this is the node-visible aggregate consensus recomputes. **Block-header / state-root / nullifier-set-root commitments remain host-chain (`rubble-node-zig`) consensus, out of lattica's PoC scope.** New invariant test. | `src/node.zig` (`Chain.supply`, `mint`, `applyChecked`) |
| **M-01** prover ABI null-pointer checks | `lattica_joinsplit_prove` and `_prove_demo` now reject null `proof_len`/`pi_len` (and all output pointers). New ABI test covering every null argument. | `lattica-prover-p3/src/lib.rs` |
| **M-02** codec bounds overflow | `Reader.getBytes` now uses `n > self.data.len - self.pos` (with a `pos <= len` guard) — no `pos + n` overflow. New oversized-`varBytes` test. | `src/codec.zig` |
| **M-03** non-canonical witness bits | `parse_joinsplit_witness` accepts only `0`/`1` for path bits (else fail-closed). New malformed-bit test. | `lattica-prover-p3/src/lib.rs` |
| **M-04** prover wrapper realloc | `proveJoinSplit` returns an exact-sized copy (max-size scratch always freed via `defer`) — the returned slice length always matches its allocation. | `src/ffi.zig` |
| **L-01** stale docs | `docs/remediation-status.md` rewritten to the current `lattica_joinsplit_*` cutover; `src/protocol.zig` header marks `SupplyState` **live** and the `ShieldedTx` codec **reference/transitional**. | `docs/remediation-status.md`, `src/protocol.zig` |
| **L-02** divergent tx formats | The C-01 single-source fix removes the live node's duplicate output-commitment field; `src/protocol.zig`'s `ShieldedTx` is documented as the reference codec (not the live path). | `src/node.zig`, `src/protocol.zig` |

**Scope note on H-01 and the "additional audit areas":** block-level state-root / nullifier-set-root /
event-root / header commitments, mempool DoS policy, reorg undo logs, and FFI fuzzing harnesses are
host-chain / production-full-node concerns beyond lattica's PoC tx-validation scope (`docs/AUDITORS.md`
§1). The node-visible supply accumulator (H-01) is now in place as the lattica-layer starting point.
