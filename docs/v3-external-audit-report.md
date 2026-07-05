# Lattica — external-scope security audit report (v3 tip)

**Date:** 2026-07-05 · **Target:** the v3 production tip (`lattica-prover-p3` circuits + C-ABI, the Zig
protocol seam) · **Method:** five independent adversarial reviewers, each tasked to *break* the target,
reading the actual code and writing/running probe tests; prior internal audits were treated as prior art
to independently re-verify, not trust. Supplements `docs/AUDITORS.md`, `docs/v3-batch-audit-handoff.md`.

## Verdict

**No CRITICAL or HIGH severity issue.** The shielded-payment system is **sound** across the audited
surface: the join-split and HTLC spend circuits non-vacuously enforce their statements, the C-ABI verify
boundary is fail-closed and panic-isolated, the Zig node's tx-validation + atomic-apply is safe, and the
ZK/crypto/cross-language layer holds. **All prior remediations were verified holding** — the rho1
persistence gap, the ghost-coin (C-01), the H-1 deanonymization oracle (OVK fix), the M-1 zero-hashlock
bypass, and the fixed-seed ZK-RNG are all closed. The findings are one MEDIUM code defect (remediated
here), two MEDIUM assurance/robustness items, and low/informational trust-boundary notes.

## Scope

**In scope:** `joinsplit_air.rs`, `htlc_air.rs`, `poseidon2_air.rs`, `batch_{joinsplit,htlc}_air.rs`, the
10 frozen `lattica_*` C-ABI externs + (de)serialization (`lib.rs`, `config.rs`), and the Zig seam
(`node.zig`, `ffi.zig`, `tx.zig`, `tree.zig`, `primitives.zig`, `poseidon2.zig`). **Out of scope:** the
host chain `rubble-node-zig` (block consensus/mempool/reorg/emission), the cross-chain
`rubble-xchain-xfer`, and GPU/streaming/recursion (research, feature-gated OFF, prove-only, verified under
the unchanged verifier). The batch circuits were separately audited in `docs/v3-batch-internal-audit.md`.

## Findings

| ID | Sev | Component | Finding | Status |
|---|---|---|---|---|
| **M-EXT-1** | Medium | C-ABI / verify | **Proof malleability** — the four verify externs accepted `postcard(Proof) ‖ trailing bytes` (`postcard::from_bytes` does not reject an unread remainder), a non-canonical accept at the untrusted-network boundary. Not a soundness break (PIs still bound, no statement forgeable), but contradicts the stated wire contract and risks relay/dedup amplification. Empirically confirmed (valid proof + 64 junk bytes → accept). | **FIXED** — `verify_proof_bytes` now uses `postcard::take_from_bytes` and rejects a non-empty remainder; regression test `proof_with_trailing_bytes_is_rejected`. |
| **M-EXT-2** | Medium | ZK / docs | **No current written HVZK argument.** The only ZK argument of record (`soundness.md` §5) is for a *deleted* prover (`stark.zig`/`rescue.zig`); the production prover is p3 `HidingFriPcs` (is_zk double-degree trace + 4 random codewords + salted Merkle over 96 FRI queries), whose zero-knowledge is nowhere argued in-repo. No leak was demonstrated (public inputs expose only anchor/nf/out_cm/fee/mint/tx_binding). | **SIGN-OFF** — the auditor must independently confirm p3 0.6.1 `HidingFriPcs` is honest-verifier ZK at these params, or the team writes the argument. `soundness.md` is already banner'd historical (won't mislead). |
| **M-EXT-3** | Medium | Cross-language | **Single-hash KAT drift risk.** The single-hash lane layouts (`commit`/`recipient`/`nullifier`/`htlc_root`) are pinned **only Zig-side** (`poseidon2.zig`) against literals that appear in no Rust file; `dump_p2` is print-only. A *consistent* Rust-side lane change (oracle + AIR together) would pass every Rust test and the stale Zig KAT → silent node/circuit divergence (consensus split). Currently byte-identical (verified lane-for-lane). | **RECOMMENDED** — add a Rust `#[test]` asserting the native single-hash oracles equal the shared literals (two-sided KAT), or a build-step regen+diff. |
| **L-EXT-1** | Low | Node | **`mint` not range-bounded** node-side, unlike `fee` — a coinbase `mint = 2^52` passed every node check while the symmetric `fee` is rejected; if a host ever authorized `reward ≥ p` the u128 supply counters would diverge from the in-field note value. Not a spendable-inflation hole (`mint` is pinned to `reward` on coinbase). | **FIXED** — `statelessTxChecks` now rejects `mint ≥ MAX_RANGE_VALUE` (`TxError.OversizeMint`), parity with `fee`. |
| **L-EXT-2** | Low | Prover | **Seeded `stream_prove` footgun** — the out-of-core research fork seeds its ZK RNGs with a fixed `seed_from_u64`; if it were ever promoted to production it would reintroduce the fixed-seed ZK break. Not on any production path (proof_to_bytes always uses the fresh-CSPRNG `make_config`; `stream_prove` is test/`recursion`-only, excluded from the staticlib). | **NOTED** — gate: the streaming prover must draw its RNGs from OS entropy before it can be a production path. |

**Informational (trust-boundary / by-design, not defects):** intra-tx duplicate-nullifier distinctness is
a node duty (both `applyChecked` and `applyHtlc` carry the `seen` guard — correct stateless-circuit
boundary); `current_height` value is node-trusted (consensus-pinned via `applyHtlc` `HeightMismatch`);
`PI_HASHLOCK` is unconstrained on non-redeem txs (the node must not treat a stray value as authorizing);
the anchor set has no expiry (safe — double-spend rests on the monotonic nullifier set, not anchor
recency); the untagged Merkle `merge` (residual A4, sound under Poseidon2 second-preimage resistance);
`detect()` binds to `tn.cm` not on-chain presence (an exchange must feed it only chain-sourced notes).

## Per-dimension verdicts

- **Join-split circuit — SOUND.** No mint/steal/double-spend/membership-forgery/A1-break/vacuous-constraint
  path. Value balance `Σin+mint=Σout+fee` is exact and non-wrapping (`|Σ| ≤ 3·2^52 ≪ p`), each value
  range-checked `<2^52`, each value cell shared between commitment + balance + range; ownership↔nullifier
  key binding and A1 position binding are non-vacuous (verified in-circuit with a new position-forgery
  probe that correctly rejects). rho1 fix present.
- **HTLC circuit — SOUND.** The headline invariant holds: `nf = H(DOM_NF_HTLC‖owner‖rho‖pos)` is
  **mode/party-independent** (redeem and refund of one note emit byte-identical nullifiers ⇒ the node
  blocks the second) — no redeem-and-refund double-spend. The timeout compare is a range argument with no
  Goldilocks wrap and partitions cleanly at `height==timeout` (two mutually-unsatisfiable constraints for a
  wrong-time spend). Hashlock binding + the M-1 non-zero backstop, the mode/owner MUX + tag-match, the
  `note_type` boolean gate, and hidden-asset preservation are all non-vacuous.
- **C-ABI / verify boundary — FAIL-CLOSED** (after M-EXT-1). Canonical field parsing (non-canonical limb
  rejected), M-08 size bound before deref, `catch_unwind` panic isolation (confirmed `panic=unwind`),
  bounded allocation, the F1 height cap and the F2 `n_tx`-overflow guard, and Rust↔Zig wire parity all hold.
- **Zig node — SAFE.** Double-spend (nullifier set + within-batch `seen` + verify-before-commit),
  anti-inflation (`mint` pinned + checked u128 supply arithmetic), apply atomicity (two-phase: fallible
  work then infallible commit, deep-copied ciphertexts), HTLC height-pinning and mode-conflict, and
  admission caps are all enforced.
- **Crypto / ZK / cross-language — HOLDS** under the named assumptions. Fresh independent CSPRNG per proof
  verified; no hidden value/key/asset in public inputs; poseidon2.zig is byte-identical to the circuit
  lane-for-lane across all six domains + both batch folds; Poseidon2 is the standardized p3 0.6.1 instance
  (no fork); the ~103-bit proven floor is machine-checked (`proven_security_meets_production_floor`).

## Remediations landed with this report

- **M-EXT-1** (proof malleability) — `config::verify_proof_bytes` rejects trailing bytes; regression test.
- **L-EXT-1** (node mint parity) — `statelessTxChecks` bounds `mint`.

Both are ABI/verify/node-glue only — **no AIR constraint-set change** (constraint fingerprints unchanged),
**no wire-format change** (a valid `postcard(Proof)` still verifies; the 10 externs' signatures are frozen).

## Recommendations (team, before production)

1. **M-EXT-3** — a two-sided single-hash KAT (a Rust test pinning the native `commit`/`recipient`/
   `nullifier`/`htlc_root` oracles to the same literals `poseidon2.zig` asserts) or an automated regen+diff,
   to make cross-language drift a test failure.
2. **M-EXT-2** — a written HVZK argument for the production `HidingFriPcs` construction (or the auditor's
   independent confirmation), replacing the stale `soundness.md` §5.

## Sign-off items (the auditor / operator must explicitly accept)

- **~103-bit *proven* soundness** (~127 conjectured) — the Goldilocks `F_p²` ceiling (`soundness-budget.md`).
- **p3 `HidingFriPcs` honest-verifier ZK** at is_zk=1 / 4 random codewords / salt width / 96 queries (M-EXT-2).
- **Poseidon2 RO/CR** — the 256-bit (4-Goldilocks) digest as a 128-bit-collision random oracle.
- **ML-KEM IK-CCA** for exchange mode (shared-KEM deposit unlinkability); + the operator accepts that a
  leaked shared hot KEM secret deanonymizes that epoch's deposits (the spend key stays cold).
- **Node-side trust seam** (host chain, out of repo): consensus-pinned `current_height`; verify against a
  self-recomputed `batchRoot`; anchor-freshness window; one coinbase per block at the emission `reward`;
  block-committed state/nullifier/supply roots + reorg-safe undo. Detailed in `docs/v3-batch-internal-audit.md`
  and `docs/full-node-security-integration.md`.
