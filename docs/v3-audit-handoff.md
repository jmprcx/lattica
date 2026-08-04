# v3-audit — external audit handoff note

> **Frozen record:** Handoff for the `v3-audit` revision. The later batch baseline is documented in [`v3-batch-audit-handoff.md`](v3-batch-audit-handoff.md).

**This tag (`v3-audit`) is the v3 external-audit artifact.** Start with `docs/AUDITORS.md` (the
comprehensive entry point); this note is the short orientation for a reviewer who already audited v1.

## What v3 adds (the review delta)
v3 layers **shielded HTLC atomic swaps with the asset type hidden on-chain** onto the audited v1
join-split. Review the delta against the v1 baseline:

```sh
git diff audit-v1-remediated-3 v3-audit        # v1 baseline (9da86f5) → this artifact
```

New/changed surface (all in `docs/AUDITORS.md` §1):
- **Multi-asset substrate** — a hidden `asset` committed in every note (commitment lane 6) + a global
  `ASSET` column + `input.asset == output.asset`.
- **`lattica-prover-p3/src/htlc_air.rs`** — the v3 spend circuit: HTLC note type (lane 7), owner =
  `htlc_root`, redeem/refund modes, tag-match access control, the timeout time-lock, the redeem
  hashlock binding + the **hashlock-nonzero backstop** (`htlc-constraint-audit.md` §5a), and the
  **mode-independent owner-nullifier** (the no-double-spend property).
- **`src/node.zig`** — `ShieldedHtlcTx`, `Chain.applyHtlc`, the `buildHtlcLock`/`buildHtlcSpend` wallet
  flows; the C ABI (`lattica_htlc_*`) and the Zig seam (`ffi.verifyHtlc`/`proveHtlc`).
- **OVK note encryption** — the KEM encapsulation coins derive from the sender's outgoing-viewing key
  (`H(ovk ‖ cm)`), closing the v1 deterministic-encapsulation deanonymization oracle (H-1) while
  keeping seed-restorability.

## Internal pre-audit (three rounds — read before re-deriving)
All findings are **remediated**; the reports are the audit trail. Don't re-spend effort re-finding
these — extend past them.
- `docs/v3-internal-audit.md` (R1, 4 reviewers) — defense-in-depth at both solver + node layers.
- `docs/v3-internal-audit-round2.md` (R2, 8 reviewers + a refutation skeptic) — Poseidon2, FRI config,
  join-split-under-v3, memory, encryption, economic, tree/codec. Foundational layers sound; fixed 2
  leaks + M-3; found + fixed **H-1 (HIGH deanonymization)** via the OVK change.
- `docs/v3-internal-audit-round3.md` (R3, audit-the-fixes + executable evidence) — caught **M-1** (a
  bug in an R2 fix — non-canonical zero-hashlock bypass), fixed at both layers (wallet + the in-circuit
  backstop); otherwise *empirically* confirmed soundness (verifier fuzz; harness-validated exhaustive
  corrupted-trace 51/51 columns; differential native-vs-AIR; 6 forgery-rejection tests).

## Highest-value places to focus (independent review still wanted)
1. **`htlc_air` soundness** — read `docs/htlc-constraint-audit.md` (constraint-by-constraint, incl. the
   delta over join-split), then attack the corrupted-trace class. The exhaustive non-vacuity test was
   self-validated by reintroducing the rho1 bug; try to find a column/binding it misses.
2. **The mode-independent nullifier** (no redeem-and-refund double-spend) and the **timeout compare**
   (direction + no field-wrap) — the highest-stakes HTLC invariants.
3. **OVK encryption + the key hierarchy** (`src/tx.zig`, `src/primitives.zig`) — confirm the oracle is
   closed and `ovk` is not leaked via the address / viewing key.
4. **Cross-language consistency** — the Poseidon2 KATs and the witness / public-input byte layouts
   between `lib.rs` and `node.zig`/`ffi.zig` (a mismatch is silent without the real backend linked).

## Reproduce (all green at this tag)
```sh
cd lattica-prover-p3 && cargo test --release            # default circuit + ABI suite
cd lattica-prover-p3 && cargo test --release -- --ignored   # the EXHAUSTIVE corrupted-trace/differential audit suite
cd lattica-prover-p3 && cargo test --release --test fuzz_htlc   # verifier robustness fuzz
zig build test            # Zig protocol suite + Poseidon2 KATs (from repo root)
zig build check-production # production compile gate (no test-only APIs on the consensus path)
scripts/run-real-integration.sh   # REQUIRED: real cross-language prove→verify (join-split + HTLC lock→redeem)
```
Two gates beyond `cargo test`/`zig build test` are **required** for full coverage:
`scripts/run-real-integration.sh` (the only validation of the Zig↔Rust witness/PI byte-match) and
`cargo test --release -- --ignored` (the exhaustive corrupted-trace/differential suite, `#[ignore]`'d
for routine speed).

## Out of scope (NOT in this artifact)
- **Phase B — the cross-repo xchain swap stack** (`rubble-xchain-xfer`): the HTLC engine, the shielded
  backend, and especially `await_lock` (which must verify the communicated lock's asset / htlc_root /
  membership) + the height↔seconds timeout cushion. Documented in `v3-internal-audit-round2.md` §3.
- **Host chain** (`rubble-node-zig`): block consensus/PoW/mempool, committed roots, reorg-undo, a
  bounded anchor window, and the commitment→position index for watching HTLC notes.

Production use of v3 is gated on this external audit + the Phase-B work above.
