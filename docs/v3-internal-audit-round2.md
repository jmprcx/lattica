# v3 internal pre-audit — round 2 (expanded coverage & depth)

A second, deeper internal pass before the external Codex audit, expanding into the layers round 1
treated as trusted. Method: **eight** independent adversarial reviewers (one per dimension) plus a
**refutation skeptic** that tried to disprove the most serious findings before any code changed. Where
a fix could live at the solver or the node, it was applied at both.

**Headline:** the foundational layers are **sound** — the Poseidon2 permutation (AIR ≡ Zig ≡ p3
constants), the FRI/STARK soundness config (identical to the audited join-split, ~103-bit proven /
~127 conjectured), the join-split circuit under the v3 asset substrate, and the Merkle tree + codec all
passed with no soundness defects. The expanded scope surfaced issues only in the **v1 encryption
layer** and in **wallet-side resource handling** — most now fixed. **One HIGH finding (H-1, a
recipient-deanonymization oracle from deterministic ML-KEM encapsulation) requires a v1 encryption
design decision and is reported for sign-off, not silently changed.**

## 1. Dimensions reviewed & verdicts
| # | Dimension | Verdict |
|---|---|---|
| 1 | Poseidon2 permutation (poseidon2_air ↔ poseidon2.zig ↔ p3) | **Sound** — 91/91 constants + 36/36 KAT digits identical; round structure, Mat4/diagonal layers, x⁷, and full-range Goldilocks `mul`/`add` all match. KAT truth-source is the real p3 lib. |
| 2 | FRI/STARK soundness config for `htlc_air` | **Sound** — byte-identical `make_config` to join-split; HEIGHT stays 4096 (extra blocks fit the pow2 padding), max degree 8, F_p² challenges, fresh per-proof CSPRNG, all 31 public inputs FS-bound. ~103/127-bit. |
| 3 | `joinsplit_air` under the v3 asset substrate | **Sound** — `ASSET` global-persistence correctly **ungated** (constant across the whole trace, not region-freed), bound at every commit_b lane 6 in+out; lane 7 pinned 0 keeps join-split PLAIN-only (the htlc_air boundary holds); all v1 invariants intact. |
| 4 | Zig memory safety / resources | **2 leaks (fixed)** — F1 witness leak (all 3 builders, success path), F2 output-ciphertext leak (error path). Consensus-path two-phase apply / deinit / 0-length placeholders verified correct. |
| 5 | `buildHtlcLock` + lock→redeem lifecycle | **Sound core** — htlc_root byte-consistency, PLAIN-input lock, asset binding, watch-by-commitment all correct. Hardening: fail-fast guards (frozen-note prevention) + a CI-coverage gap (below). |
| 6 | Note encryption / key hierarchy / AEAD | **H-1 HIGH (deanon, decision pending)**, M-3 MEDIUM (fixed), M-2 refuted; spend/view separation, address unlinkability, domain separation, HTLC empty-ciphertext handling all verified correct. |
| 7 | End-to-end economic attacks | **No new on-chain break** — theft/impersonation/early-refund/front-running/inflation/double-spend all prevented. Residual risk is Phase B (cross-chain timeout, await_lock asset check) + privacy (below). |
| 8 | Merkle tree + codec | **Sound** — tree↔circuit membership/leaf/empty-padding/depth/bit-order/position-binding match exactly; codec fail-closed (I-01/M-02 intact); codec not even on the live path. |

## 2. Findings & disposition
| ID | Finding | Sev | Status |
|---|---|---|---|
| **H-1** | Deterministic ML-KEM encapsulation (`coins = expand(cm)`, public `kem_ek`) is a **recipient-deanonymization oracle**: anyone holding a (public, shareable) address can recompute `kem_ct` for every on-chain output and test equality, enumerating all payments to that address — defeating the viewing-key capability separation. **Confirmed by the refutation skeptic on every axis.** | **HIGH** | **Decision pending** (§3) — v1 encryption design change |
| M-3 | `tryDecrypt`/`detect` returned the wire `div`, which is AEAD-authed but **not cm-bound**; a hostile sender could ship a correct `recipient` + garbage `div` that bricks the default spend (recoverable). | Med | **Fixed** (`f22d38c`) — re-derive div from the matched index |
| F1 | Witness slice leaked on the success path of all three builders. | Med | **Fixed** (`f22d38c`) |
| F2 | Output ciphertexts leaked on the builder error path. | Low-Med | **Fixed** (`f22d38c`) |
| R5-guards | `buildHtlcLock` accepted an out-of-range timeout (proves at lock, **freezes the note** at spend), and `hashlock==0` (atomicity footgun). | Low | **Fixed** (`f22d38c`) — fail-fast guards |
| preimage-bind | HTLC `tx_binding` bound only the reduced-limb hashlock, not the raw preimage. | Low | **Fixed** (`f22d38c`) — bind the raw 32-byte preimage (defense-in-depth) |
| R2-gate | `measure()` computed proven bits but nothing asserted the floor. | Low | **Fixed** (`d0e67dc`) — `proven_security_bits()` + `proven_security_meets_production_floor` |
| docs | `soundness-budget.md` (height 2048→4096, dead module/test refs), `joinsplit-constraint-audit.md` (missing `ASSET`, WIDTH 18→19). | Info | **Fixed** (`d0e67dc`) |
| M-2 | `cm` is not injective over the AEAD plaintext (`div` + high-16 of rho/rcm unbound). | — | **REFUTED** (inert: only a malicious sender who already knows both plaintexts can trigger it; the unbound bytes are never read) → **doc-only**: correct the false "cm binds full note randomness" invariant |
| CI-gap | The Zig witness encoders' byte-match to the Rust parser is exercised only by `scripts/run-real-integration.sh` (the mock backends ignore layout); it isn't a `zig build test` step (the `.sframe` linker constraint). | Med (process) | **Documented** — `run-real-integration.sh` is a **required** gate for the cross-language seam (AUDITORS §3); the cross-language reviewer verified the layout field-for-field. |
| privacy | Redeem vs refund is **publicly distinguishable** (redeem carries a preimage + nonzero redeem_hashlock); the shared SHA256 links the two swap legs; HTLC txs form a distinct anonymity set (empty-ciphertext output). | Med | **Documented** (corrects round-1's A-F2/C-F8 framing) — partly inherent to HTLC |
| Phase B | Cross-chain height↔seconds timeout cushion (free-option/reorg race); `await_lock` must verify the communicated lock's **asset**/htlc_root/membership. | High/Med | **Documented** — `rubble-xchain-xfer` scope, not this branch |

## 3. H-1 — the one open decision (v1 encryption)
The deterministic encapsulation was a deliberate v1 choice for **seed-restorability** (a sender
reconstructs sent notes from a seed). But deriving the encaps coins from the *public* `cm` makes
`kem_ct` publicly recomputable from the recipient's *public* address, which deanonymizes recipients of
known addresses. Options:
- **(A) OVK-style (recommended):** derive the encaps coins from a sender-held outgoing-viewing secret
  (`coins = expand(ovk ‖ cm)`). Closes the oracle (a third party lacks `ovk`), **preserves
  seed-restorability** (the sender has `ovk`), recipient decryption unchanged. Cost: add an `ovk` to
  the key hierarchy, thread it through `encryptNote` + the builders, regenerate the encryption KATs.
- **(B) Randomized encapsulation:** simplest, closes the oracle, but **breaks** deterministic
  seed-restorability (the sender must store `kem_ct`).
- **(C) Document as a known limitation** and leave the v1 scheme for the external audit to rule on.
This changes audited v1 core crypto with a real tradeoff, so it is surfaced for sign-off rather than
changed unilaterally.

## 4. Validation
After the round-2 fixes: **74 Rust tests** (incl. the proven-security gate), the full **Zig** suite
(incl. the new M-3 test and a leak-checking-allocator build test that would fail pre-fix),
**`check-production`**, and **`run-real-integration.sh`** (real join-split + HTLC lock→redeem lifecycle)
all green. Round-2 commits: `d0e67dc` (Rust/doc), `f22d38c` (node/tx). This pass does not replace the
external Codex audit; H-1 in particular is flagged for sign-off.
