# Lattica Implementation Audit

**Date:** 2026-06-27  
**Entry point:** `docs/AUDITORS.md`
**Scope covered:** Plonky3 join-split AIR, Rust C ABI, Zig FFI seam, protocol hashing, transaction construction, node state machine, note/key/encryption code, canonical codecs, tests, and operational/security areas needed by a production full node.

## Current Re-Audit (post-round-3 remediation verification, 2026-06-28)

### Current Verdict

Round 3 remediation was verified against the current codebase. No new Critical or High severity issue was found in the in-scope Lattica transaction stack during this pass.

The following previously open live-code findings are now verified remediated:

- **C-01:** output commitments remain single-source (`outputs[j].cm`) and are bound to public inputs, `tx_binding`, and tree insertion.
- **H-03/H-04:** live node state application is two-phase/atomic and stores chain-owned transmitted-note ciphertexts.
- **M-05/M-08:** proof-size limits are enforced both in live node admission and at the reusable Zig/Rust verifier seam.
- **M-09/M-10:** genesis/test-only `bootstrapMint` and mock backend are compiled out for production roots via `lattica_production = true`, and `zig build check-production` verifies the production surface compiles without those helpers.
- **L-03:** README now describes the Plonky3 join-split path instead of removed pre-Plonky3 components.

Production is still **not cleared** because the full-node consensus layer remains outside this package: canonical block/transaction encoding for the active object, committed note/nullifier/supply/event roots, reorg undo, snapshot validation, mempool policy, proof-cache policy, emission schedule enforcement, and production startup attestation of the real verifier are still host-chain responsibilities. The Goldilocks soundness ceiling and deterministic note-encryption design remain deliberate v1 sign-off items.

### Verification Re-Run

Commands run:

```sh
cd lattica-prover-p3 && cargo test --release
zig build test
zig build check-production
scripts/run-real-integration.sh
```

Results:

- `cargo test --release`: passed, 31 Rust library tests plus 2 binary tests.
- `zig build test`: passed.
- `zig build check-production`: passed.
- `scripts/run-real-integration.sh`: passed; C FFI harness and live Zig-node-to-real-Rust-prover/verifier path accepted a valid tx, rejected tampered output commitment, and rejected replay/double spend.

### Remaining Production-Gate Items

#### P-01: Host-chain full-node consensus integration remains unaudited here

**Severity:** Production blocker outside this package
**Area:** full-node consensus, block validation, replay/snapshot safety
**Files/docs:** `docs/full-node-security-integration.md`, host chain (`rubble-node-zig`)

Lattica now provides a hardened shielded transaction state machine and proof boundary, but it is still an in-memory component. A production full node must commit and replay the surrounding consensus state: canonical block/transaction bytes, tx root, note root, nullifier-set root, supply root, event root, consensus-parameter hash, reorg undo records, snapshot verification, mempool preverification, duplicate-nullifier mempool policy, proof-result caching, fee/emission schedule checks, and real-verifier startup attestation.

**Required before production:**

- Implement the full-node pipeline in `docs/full-node-security-integration.md`.
- Require `lattica_production = true` for production consensus builds.
- Attest real `lattica_joinsplit_verify` parameters/symbols at startup before accepting blocks.
- Add genesis replay and cross-implementation root/supply comparison tests.

#### L-04: Full-node integration text still referenced binding signatures

**Severity:** Low documentation/integration risk
**Area:** docs
**File:** `docs/full-node-security-integration.md`

The active v1 path uses a proof-bound canonical `tx_binding` digest, not a binding signature. One remaining line in the full-node integration plan still described the default as binding a digest into both a spend proof and binding signature. This pass corrected that wording to `tx_binding` and notes that any later host-chain signature layer must use a separate domain.

## Current Re-Audit (post-round-2 remediation, 2026-06-28)

### Current Verdict

The Round 2 remediation commit was checked against the codebase and reproduction suite. The original C-01 ghost-coin bug remains fixed, and the live-node remediations for H-03/H-04/M-05 are verified on the active `src/node.zig` path:

- state/supply application now uses a two-phase pattern: candidate supply, capacity reservation, and chain-owned ciphertext copies occur before consensus mutation;
- `SupplyState.apply` is atomic on arithmetic failure;
- applied transmitted-note ciphertexts are deep-copied into chain-owned memory and freed by `Chain.deinit`;
- live node admission rejects oversize proofs and output ciphertexts before proof verification.

This still does **not** clear the repository for value-bearing production. The remaining issues are mostly production-integration and hardening boundaries: full-node consensus state is outside this package, the reusable FFI verifier wrapper still relies on callers for size limits, genesis/test-only APIs remain publicly callable, mock backends are exported for tests/demo, and `README.md` still describes removed pre-Plonky3 components as if they were live.

### Verification Re-Run

Commands run:

```sh
cd lattica-prover-p3 && cargo test --release
zig build test
scripts/run-real-integration.sh
```

Results:

- `cargo test --release`: passed, 30 Rust tests.
- `zig build test`: passed, including H-03/H-04/M-05 remediation tests.
- `scripts/run-real-integration.sh`: C FFI harness passed in sandbox; the live-node integration hit the documented Zig stdlib sandbox read issue, then passed when rerun outside the sandbox. Real prover/verifier accepted the valid tx, rejected tampered output commitment, and rejected replay/double spend.

### Round 2 Remediation Verification

| Finding | Current status |
|---|---|
| **H-03** non-atomic state on error | Verified fixed for the live node path. `SupplyState.apply` computes locals then assigns, and `applyChecked` reserves capacities/deep-copies before mutation. Remaining production work is block-level atomicity/reorg undo in the host chain. |
| **H-04** transmitted-note ownership | Verified fixed for the live node path. `applyChecked` deep-copies output ciphertexts into chain-owned storage, and `Chain.deinit` frees stored ciphertexts. |
| **M-05** verifier size limits | Partially fixed. `applyChecked` rejects oversize `proof`/ciphertext before calling the verifier. The reusable `ffi.verifyJoinSplit` wrapper and Rust C ABI still accept arbitrary `proof_len` from direct callers, so production should enforce the same cap at that seam too. |
| **M-06** issuance API | Partially fixed. `Chain.mint` was renamed/commented as `bootstrapMint`, but it is still `pub` and callable by any module importing `node.zig`. Production integration should compile-gate or move it to genesis/test/demo code. |
| **M-07** full-node consensus surface | Still open/outside this package: canonical block/tx encoding for the active object, header-committed note/nullifier/supply/event roots, reorg undo logs, snapshots, mempool policy, and proof cache remain host-chain work. |

### New / Still-Open Findings

#### M-08: Reusable verifier boundary does not enforce proof size limits

**Severity:** Medium DoS hardening
**Area:** Zig FFI wrapper / Rust C ABI
**Files:** `src/ffi.zig`, `lattica-prover-p3/src/lib.rs`

The live node now checks `t.proof.len > ffi.MAX_PROOF_LEN` before verification, but `ffi.verifyJoinSplit` itself forwards any proof slice length to the backend (`src/ffi.zig:132-135`), and `lattica_joinsplit_verify` builds a Rust slice for any non-null pointer/length before parsing (`lattica-prover-p3/src/lib.rs:78-95`).

**Impact:** live `Chain.applyChecked` is protected, but direct consumers of the reusable verifier seam can still hand very large proof buffers to proof deserialization. This is a DoS footgun for future mempool/block-verifier integrations and external C callers.

**Required remediation:**
- Enforce `MAX_PROOF_LEN` inside `ffi.verifyJoinSplit`, or expose only a bounded verifier API.
- Mirror the proof-size cap in `lattica_joinsplit_verify` so C callers get fail-closed behavior even if Zig-side checks are bypassed.
- Add tests proving an oversize proof does not invoke the backend/deserializer.

#### M-09: Genesis/test issuance helper remains publicly callable

**Severity:** Medium integration risk
**Area:** issuance API boundaries
**File:** `src/node.zig`

`bootstrapMint` is clearly documented as genesis/test-only, but it remains a public function on `Chain`. The remediation reduces accidental misuse by renaming it, but it does not create a compile-time or type-level production boundary.

**Impact:** a production host-chain/RPC integration can still bypass `applyCoinbase` by calling `bootstrapMint` directly. That would be an integration bug rather than a proof-system break, but issuance APIs should be impossible to misuse in production builds.

**Required remediation:**
- Move bootstrap minting into a genesis/test helper module that production consensus code does not import.
- Alternatively compile-gate it behind an explicit demo/test build option.
- Add a production-mode build/test that proves arbitrary post-genesis minting is unavailable.

#### M-10: Mock prover/verifier backend is exported from the live node module

**Severity:** Medium integration risk
**Area:** backend configuration / build hardening
**File:** `src/node.zig`

`node.mock.install()` is public and installs a 32-byte tx-binding mock backend for tests and the wallet demo. The real integration installs `lattica_joinsplit_prove`/`lattica_joinsplit_verify`, and the default verifier remains fail-closed with no backend, but production builds should not expose a mock verifier path in the same module as consensus validation.

**Impact:** a misconfigured production binary could install the mock backend and accept transactions authorized only by the test binding model, not the real Plonky3 proof.

**Required remediation:**
- Compile-gate `node.mock` behind test/demo builds.
- Make production startup require and attest the real Rust verifier symbols/parameters before accepting blocks.
- Add a production-mode test that `node.mock` is not available.

#### L-03: Public documentation still describes removed pre-Plonky3 components

**Severity:** Low/Medium audit and operator risk
**Area:** documentation / audit handoff
**Files:** `README.md`, selected historical docs

`docs/AUDITORS.md` correctly points reviewers to the Plonky3 join-split path, and several historical docs carry reference-only banners. `README.md` still lists removed Zig files such as `rescue.zig`, `stark.zig`, `membership.zig`, `permutation.zig`, `spend.zig`, and `circuit.zig`, and describes an ML-DSA binding-signature flow rather than the live join-split proof path.

**Impact:** external reviewers, operators, or integrators can audit or build against the wrong transaction model. This does not affect consensus directly, but it is a real production-readiness issue for an audit handoff.

**Required remediation:**
- Rewrite `README.md` to match the current Plonky3 join-split path, or add a clear historical banner and point to `docs/AUDITORS.md`.
- Keep `docs/audit-scope-p3.md` and `docs/remediation-status.md` synchronized with the current live path and reproduction counts.

### Additional Audit Areas Covered

- **AIR soundness:** spot-checked public-input order, nullifier position binding, `RHO1` persistence, output-commitment public binding, range/balance rows, and corrupted-trace tests. No new AIR soundness bug found in this pass.
- **Cross-language consistency:** checked Zig public-input encoding against Rust parsing order and ran real integration.
- **Node state machine:** checked issuance gate, anchor check, nullifier duplicate/spent check, size checks, proof verification, and atomic commit ordering.
- **Supply auditability:** checked atomic `SupplyState.apply`, invariant tests, live `Chain.supply`, and remaining need for host-chain block/header commitments.
- **Wallet/key/encryption path:** checked deterministic note encryption binding to commitment, viewing-key detection, chain-owned ciphertext storage after apply, and deterministic-output-randomness sign-off area.
- **Codec/canonicalization:** checked overflow-safe byte reads, non-canonical field rejection, and transitional status of `src/protocol.zig` codec versus active `node.ShieldedTx`.

### Developer Remediation Response — Round 3 (new findings)

All new findings addressed on the audit branch. Re-validated: **31 Rust tests**, the **full Zig suite**
(incl. the production-mode compile probe), the **real integration**, and `zig build check-production`.

| Finding | Resolution | Where |
|---|---|---|
| **M-08** verifier seam size limit | `ffi.verifyJoinSplit` rejects `proof.len > MAX_PROOF_LEN` **before** invoking the backend, and the Rust `lattica_joinsplit_verify` rejects an oversize `proof_len` **before** building/deserializing the slice (matching `MAX_PROOF_LEN = 1<<21`). Tests: Zig (oversize ⇒ false, backend not called) + Rust (oversize `proof_len` ⇒ reject). | `src/ffi.zig`, `lattica-prover-p3/src/lib.rs` |
| **M-09** genesis/test mint API | `Chain.bootstrapMint` is **compile-gated**: in a build whose root sets `pub const lattica_production = true`, any reference is a compile error (`@compileError`). Verified — a probe calling it fails to compile. | `src/node.zig` |
| **M-10** mock backend in the live module | `node.mock` is **compiled out** of production builds (`pub const mock = if (production) struct {} else …`), so `node.mock.install()` is a compile error there. Verified — a probe calling it fails to compile. | `src/node.zig` |
| production-mode test | `src/production_probe.zig` builds the consensus surface with `lattica_production = true` (test-only APIs gated out); `zig build check-production` — also a dependency of `zig build test` — compiles it. The successful compile *is* the assertion that the live path uses no genesis/test-only helper. | `src/production_probe.zig`, `build.zig` |
| **L-03** stale README | `README.md` rewritten to the Plonky3 join-split path (correct layout, removed-file references deleted, `tx_binding` replaces the ML-DSA binding-signature flow) and points to `docs/AUDITORS.md`. | `README.md` |

**Scope note:** the M-09/M-10 compile-gate prevents a production *build* from including the helpers. The
complementary runtime step — a production node attesting the real Rust verifier symbols/parameters at
startup before accepting blocks — is host-chain (`rubble-node-zig`) scope, as is M-07 (full-node
consensus surface: block format, committed roots, reorg undo, mempool cache).

## Current Re-Audit (post-remediation, 2026-06-27)

### Current Verdict

The original critical ghost-coin finding **C-01 is verified remediated in the current code**. `src/node.zig` no longer carries a separate `ShieldedTx.out_cms`; `outputs[j].cm` is now the single value used for note-tree insertion, verifier public inputs, and `tx_binding`. The real Rust verifier integration rejects a fresh transaction whose `outputs[0].cm` is tampered after proving.

This re-audit does **not** clear the implementation for value-bearing production. The Plonky3 join-split and C ABI hardening are materially stronger than the earlier stack, but the live in-memory node still has production blockers in state-update atomicity, transaction/object ownership, proof-size DoS policy, and full-node consensus integration.

### Verification Re-Run

Commands run from the repository tip:

```sh
cd lattica-prover-p3 && cargo test --release
zig build test
scripts/run-real-integration.sh
```

Results:
- `cargo test --release`: passed, 30 Rust tests. Coverage includes non-canonical public fields, null output-pointer rejection, canonical witness bits, wrong anchor/nullifier/output/fee/tx-binding/mint, range failures, dummy-note padding, forged trace classes, and persistence regressions.
- `zig build test`: passed.
- `scripts/run-real-integration.sh`: C FFI harness passed in sandbox; in-node Zig/Rust integration initially hit the documented Zig stdlib `ReadOnlyFileSystem` sandbox issue, then passed when rerun outside the sandbox. The real integration accepted a valid proof, rejected tampered `out_cm` through the real verifier, rejected replay/double spend, and Bob decrypted 900.

### Remediation Verification

| Original finding | Current status |
|---|---|
| **C-01** unproven output commitments | Verified fixed. Single output commitment source is `outputs[j].cm`; `outCms()`, `publicInputs()`, and `txBinding()` derive from it. Real integration rejects tampered output commitment. |
| **H-01** supply accumulator absent | Partially fixed. `Chain.supply` exists and tests cover normal mint/fee movement, but new finding H-03 below blocks production because rejected/erroring updates can still mutate supply state. |
| **H-02** proof verification before cheap rejects | Verified fixed. `applyChecked` checks issuance, anchor, and nullifier duplicates before calling `ffi.verifyJoinSplit`. |
| **M-01** prover ABI null output length pointers | Verified fixed. `lattica_joinsplit_prove` and demo prover reject null length pointers. |
| **M-02** codec bounds overflow | Verified fixed. `Reader.getBytes` uses subtraction-based bounds checking. |
| **M-03** non-canonical witness bits | Verified fixed. Rust witness parser accepts only `0` and `1`. |
| **M-04** Zig prover wrapper allocation ownership | Verified fixed. `proveJoinSplit` returns an exact-sized copy. |
| **L-01/L-02** stale docs and divergent commitment sources | Partially fixed. Entry-point docs describe the Plonky3 path, but several older docs still describe the pre-Plonky3/Winterfell transaction model and should be archived or clearly marked reference-only. |

### New / Still-Open Findings

#### H-03: Supply and state updates are not transactional on error

**Severity:** High for production consensus robustness
**Area:** supply accounting, node state application
**Files:** `src/protocol.zig`, `src/node.zig`

`SupplyState.apply` mutates fields one at a time (`src/protocol.zig:226-237`). If a later checked arithmetic operation fails, earlier fields remain changed even though the function returns an error. Existing underflow tests assert the error but do not assert that the state is unchanged.

`Chain.applyChecked` then performs several fallible operations after proof verification and supply update (`src/node.zig:370-374`): supply update, nullifier insertion, commitment insertion, and transmitted-note append. `insertCommitment` itself appends to the Merkle tree before inserting the new root into `anchors` (`src/node.zig:298-300`). An allocator failure, tree-full condition, or anchor-map failure can return an error after partial state mutation. The same issue exists in the bootstrap `mint` helper, which updates supply before tree/transmitted-note writes (`src/node.zig:305-315`).

**Impact:** a rejected transaction or failed block application can leave a node with mutated supply counters, inserted nullifiers, advanced note tree roots, or orphaned transmitted-note state. In production, this can cause consensus divergence, failed replays, corrupted snapshots, and incorrect supply audit results. Direct external exploitability depends on reaching a fallible path such as memory pressure, full tree, or malformed block handling, but consensus code must be atomic regardless.

**Required remediation:**
- Make `SupplyState.apply` compute a complete candidate state in locals and assign `self.*` only after all arithmetic succeeds.
- Add regression tests proving underflow/overflow leaves `SupplyState` unchanged.
- Make transaction application two-phase: perform all validation, allocation, capacity reservation, and supply-delta computation before mutating consensus state.
- Add rollback or assume-capacity commit paths for note-tree append, anchor insertion, nullifier insertion, and transmitted-note append.
- Add tests for allocator failure and tree-full rejection preserving anchor, supply, nullifiers, and transmitted notes.

#### H-04: Applied transmitted notes do not have clear chain-owned ciphertext ownership

**Severity:** High for production node correctness; Medium for consensus safety
**Area:** transaction object ownership, wallet scanning, long-running node memory safety
**Files:** `src/node.zig`, `src/tx.zig`

`tx.TransmittedNote.ciphertext` is allocator-owned (`src/tx.zig:214-217`). `Chain.applyChecked` appends each submitted `TransmittedNote` struct by value into `chain.transmitted` (`src/node.zig:372-374`), copying only the slice pointer. `Chain.deinit` deinitializes the array list but does not free stored ciphertext buffers (`src/node.zig:277-281`).

**Impact:** if a production node decodes transactions with a temporary allocator or frees transaction objects after apply, `chain.transmitted` can retain dangling ciphertext pointers. If it uses the chain allocator, long-running nodes leak every transmitted note ciphertext. This can break wallet scanning, event serving, snapshot/export code, and node memory bounds.

**Required remediation:**
- Define ownership explicitly: either chain history owns deep-copied transmitted notes, or it stores canonical block bytes/event records with stable lifetime.
- Deep-copy ciphertexts before appending to `chain.transmitted`, and free them in `Chain.deinit`.
- Add tests that apply a transaction built with a temporary allocator, free that allocator, and still scan/decrypt from chain-owned history.
- Combine with H-03 so deep-copy allocation happens before consensus mutation.

#### M-05: Verifier path lacks explicit proof/ciphertext size limits before expensive parsing

**Severity:** Medium DoS
**Area:** verifier boundary, mempool/block admission
**Files:** `src/ffi.zig`, `lattica-prover-p3/src/lib.rs`, live transaction admission

The prover wrapper has `MAX_PROOF_LEN`, but the verifier path accepts any proof slice length and passes it through the C ABI to Rust proof deserialization (`src/ffi.zig:131-136`, `lattica-prover-p3/src/lib.rs:87-95`). The live node also has no canonical transaction decoder on the active `node.ShieldedTx` path enforcing proof, ciphertext, output, or total transaction byte limits before proof verification.

**Impact:** peers can force large proof/ciphertext allocation or parsing work once cheap anchor/nullifier checks pass. This is separate from normal proof-verification cost and should be bounded deterministically for mempool and block validation.

**Required remediation:**
- Add consensus constants for max proof bytes, ciphertext bytes, outputs/actions, and total transaction bytes.
- Reject oversize proofs/ciphertexts before calling `ffi.verifyJoinSplit`.
- Mirror limits in canonical transaction decoding and mempool admission.
- Add adversarial tests for oversize proof and ciphertext rejection before backend invocation.

#### M-06: Arbitrary issuance helper remains public in the live node module

**Severity:** Medium integration risk
**Area:** issuance API boundaries
**File:** `src/node.zig`

`Chain.mint` is a public helper that inserts shielded value and updates supply directly (`src/node.zig:305-315`). `verifyAndApply` correctly rejects nonzero `mint`, and `applyCoinbase` gates join-split issuance by a caller-provided reward. However, a production integration must ensure arbitrary helper minting is not reachable outside genesis/test/bootstrap code.

**Impact:** misuse by host-chain code, RPC, tests promoted into production, or migration tooling can bypass emission policy even though the join-split path is gated.

**Required remediation:**
- Move bootstrap minting behind a genesis/test-only API or rename/gate it so production consensus code cannot call it accidentally.
- Enforce all post-genesis issuance through block-level emission policy plus `applyCoinbase`.
- Add tests that production-mode APIs expose no direct arbitrary mint path.

#### M-07: Full-node consensus surface remains outside the live implementation

**Severity:** Medium/High production readiness
**Area:** canonical consensus integration
**Files/docs:** `src/protocol.zig`, `src/node.zig`, `docs/full-node-security-integration.md`

The live path is still an in-memory state machine. `src/protocol.zig` documents its `ShieldedTx` codec as reference/transitional while `node.ShieldedTx` is the active join-split object. There is no live block format, canonical transaction decoder for the active object, authenticated nullifier-set root, supply-root commitment, reorg undo log, snapshot verification, mempool proof cache, or independent replay interface.

**Impact:** the cryptographic transaction verifier can be sound while the production full node remains unable to provide reproducible supply audits, root-committed state, safe reorgs, or light-client/auditor verification.

**Required remediation:**
- Promote one canonical transaction/block encoding to the live path and make `txBinding`, FFI public inputs, transaction IDs, and state application derive from the same decoded bytes.
- Commit note root, nullifier-set root, supply root, event root, transaction root, and consensus-parameter hash in block headers.
- Implement reorg-safe undo records for nullifiers, note tree, supply, fees, and transmitted-note/event state.
- Keep `docs/full-node-security-integration.md` as the production checklist, but update its current-status section to reflect the Plonky3 join-split cutover and the H-03/H-04 blockers.

### Additional Areas Covered

- **AIR soundness:** reviewed public-input bindings, value/range accumulator, position accumulator, `RHO1` persistence, output commitment bindings, fee/mint rows, ZK randomness, and adversarial tests. No new AIR soundness bug was found in this pass. `tx_binding` remains bound through the proof transcript rather than an algebraic witness relation; this is documented and should remain a focused external-review item.
- **Cross-language consistency:** verified public input layout is `anchor || N nullifiers || M out_cm || tx_binding || fee || mint`; Poseidon2 KAT and real integration cover the Zig/Rust seam.
- **FFI safety:** null pointer remediation and panic isolation are in place. Remaining DoS work is explicit verifier-side size limits.
- **Codec/canonicalization:** `codec.Reader.getBytes` overflow remediation is in place. The active node transaction path still needs a canonical consensus decoder.
- **Keys/encryption:** note encryption binds `cm` as KDF input and AEAD associated data; decrypt verifies the recomputed commitment and recipient. Deterministic note encryption and deterministic output randomness are deliberate v1 sign-off items, not cleared as universally safe defaults.
- **Operations:** proof failure spikes, duplicate nullifier attempts, issuance attempts, supply invariant drift, root mismatches, snapshot validation, and verifier disagreement should be metrics/alerting requirements for production.

### Developer Remediation Response — Round 2 (new findings)

All new findings addressed on the audit branch. Re-validated: **30 Rust tests**, the **full Zig suite**
(now incl. supply-atomicity, rejected-tx-unchanged, chain-owned-ciphertext, and oversize-rejection
tests), and the **real integration** (ghost-coin rejected through the real verifier).

| Finding | Resolution | Where |
|---|---|---|
| **H-03** non-atomic state on error | `SupplyState.apply` computes the full candidate in locals and assigns `self.*` only after all checked arithmetic succeeds. `Chain.applyChecked` and `bootstrapMint` are now **two-phase**: candidate supply + capacity reservation (`MerkleTree.ensureUnusedCapacity`, map/list `ensureUnusedCapacity`) + chain-owned ciphertext copies happen first; the commit phase is **infallible** (`appendAssumeCapacity`/`putAssumeCapacity`). Tests: supply-unchanged-on-underflow (`protocol.zig`) and rejected-tx-leaves-state-unchanged (`node.zig`). | `src/protocol.zig`, `src/node.zig`, `src/tree.zig` |
| **H-04** transmitted-note ciphertext ownership | The chain **deep-copies** each output ciphertext into chain-owned memory before storing it; `Chain.deinit` frees every stored ciphertext. Test builds a tx with a temporary arena, frees it, and still decrypts from chain history (no dangling pointer / no leak). | `src/node.zig` |
| **M-05** no size limits before verify | `applyChecked` rejects `proof.len > ffi.MAX_PROOF_LEN` and any output `ciphertext.len > MAX_NOTE_CIPHERTEXT_LEN` *before* verification (new `OversizeProof`/`OversizeOutput`). Test covers both. | `src/node.zig` |
| **M-06** public arbitrary-mint helper | `Chain.mint` renamed to **`bootstrapMint`** with a GENESIS/TEST-ONLY doc contract (bypasses the proof); production issuance stays gated through `applyCoinbase`. | `src/node.zig` (+ call sites) |
| **M-07** full-node consensus surface | The lattica-layer pieces are in place (supply accumulator H-01, single output-commitment source L-02, atomic apply H-03). Block-level commitments (state/nullifier-set/event/tx roots, header), canonical block format, reorg undo logs, snapshots, and the mempool proof cache are **host-chain (`rubble-node-zig`) production scope** — tracked by `full-node-security-integration.md`, not built into the lattica PoC tx-validation layer. |
| **L-01/L-02** stale docs / divergent formats | Pre-Plonky3 docs now carry reference-only banners pointing to `AUDITORS.md`; `AUDITORS.md` §4 lists canonical vs historical docs; `protocol.zig` marks `SupplyState` live and its `ShieldedTx` codec reference-only. The live node has a single output-commitment source of truth (C-01 fix). |

**Scope note:** H-03/H-04 are remediated at the node tx-validation layer; the broader M-07 consensus
surface (block headers, committed roots, reorg undo, mempool cache) remains host-chain / production
scope by design (`docs/AUDITORS.md` §1).

## Original Audit Executive Summary (pre-remediation)

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
