# v3 internal pre-audit — round 3 (audit the fixes + executable evidence)

A third internal pass, deliberately *not* a re-run. Rounds 1–2 read code and reasoned; round 3
raises the methodology on three axes:
1. **Audit the remediations.** Rounds 1–2 changed a lot of code (the OVK encryption rewrite,
   div-rederive, in-circuit `mint==0` + a new height-range selector, canonical checks, lock guards,
   preimage-binding) — fresh code that was never itself audited. Fixes are a classic source of new bugs.
2. **Executable evidence, not arguments.** Reviewers (and I) *wrote and ran* fuzzers, differential
   checks, and exhaustive corrupted-trace tests — and one reviewer first *validated its own harness* by
   reintroducing the historical rho1 bug and confirming the probes flip to failing.
3. **Exhaustive coverage** of the thin spots: every persistent column's non-vacuity, the
   selector/periodic construction (did inserting `P_HEIGHT_SEED` misalign indices?), `spend_air`, and
   malformed-proof/codec fuzzing.

**Headline:** round 3 found **one real bug — M-1, in a round-2 fix** (now fixed) — and otherwise
*empirically* confirmed soundness across the board. The payoff of "audit the fixes" is concrete: M-1
could not have been found in rounds 1–2 because it didn't exist yet.

## Method
Three reviewers + my own fuzz: **(A)** adversarially audit the round-1/2 remediations; **(B)** the
under-examined surface (`spend_air`, `lib.rs` robustness, the periodic/selector construction, constraint
degree); **(C)** in an isolated git **worktree**, build + run *exhaustive* corrupted-trace + differential
+ boundary + forgery tests. My fuzz: malformed-proof / tampered-public-input through the real C ABI.

## Findings & disposition
| ID | Finding | Sev | Status |
|---|---|---|---|
| **M-1** | `buildHtlcLock`'s round-2 zero-hashlock guard checked the **raw bytes** for all-zero, but the value entering `htlc_root` is the **field-reduced** digest. A hashlock whose 4 LE limbs each equal `p` (`01 00 00 00 FF FF FF FF ×4`, non-canonical) isn't zero in bytes (passed the guard) yet reduces to `[0,0,0,0]` — re-opening the atomicity footgun (a "redeem" with a null preimage that reveals no secret). | **MED** | **Fixed** (`a56ceea`) — also reject a non-canonical hashlock (`isCanonicalDigest`); new test. **Recommended further hardening:** an in-circuit `PI_HASHLOCK != 0` on the redeem path (consensus-level), since a tx crafted outside `buildHtlcLock` bypasses the wallet guard. Primary defense remains the Phase-B `await_lock` hashlock check. |
| spend_air | `spend_air.rs` is **dead code** — `nm` shows the only C-ABI symbols are the join-split + htlc verify/prove/demo; it's reachable only from the `main` demo binary + its own tests, and neither production circuit imports it. Doc-rot in `lib.rs:3`. | Low | **Doc fixed** (`11817e1`) — marked superseded/demo-only; **removal recommended** (not deleted unilaterally — it's pre-existing milestone code). |
| nit | The `"lattica:v1:kem-encaps"` domain tag (from the H-1 fix) is a bare literal, not registered in the `domain` struct convention. | Nit | Documented. |
| OVK rewrite | H-1 fix: `ovk` is domain-separated from nk/div/kem/ml-dsa, never leaked (absent from Address + IVK), coins injective in (ovk,cm); all callers pass the sender's ovk. | — | **Confirmed correct** (R-A). |
| M-3 / mint / height / canonical / leaks / preimage | The other round-1/2 fixes. | — | **Confirmed correct** (R-A): div-rederive in both decrypt paths; `P_HEIGHT_SEED` did NOT misalign any selector (1:1, `N_PERIODIC=43`); the height window is disjoint from all 10 other range windows; `isCanonicalDigest` has no false positives; the raw-preimage binding matches prover↔node for refund; the `defer`/`errdefer` leak fixes are safe. |
| periodic / degree | The selector construction + constraint degree. | — | **Confirmed correct with a harness** (R-B): 32 pushed selectors land 1:1 on their `P_*` index, the 11 REM windows are pairwise disjoint (min gap 12), the round schedule is clean across all 4096 rows incl. padding; max constraint degree 8 within the blowup. (Also flagged a misleading TODO in the p3 *dependency* — not our code.) |
| verifier robustness | C-ABI fail-closed / panic-isolation / non-malleability. | — | **Confirmed by fuzz** (mine, `6c9f5af`): 3000 proof mutations + 3000 PI byte-flips + garbage/wrong-length inputs all rejected, no panics. |
| circuit soundness | Every persistent column non-vacuous; native==AIR; boundaries; forgeries. | — | **Confirmed by execution** (R-C, `11817e1`): harness self-validated (rho1 reintroduction flips probes), then 51/51 column corruptions rejected, 16-sample differential agrees, 496 PI perturbations rejected, 6 forgery/theft attempts rejected, boundaries correct. **No soundness bug.** |

## New regression tests (permanent)
- `tests/fuzz_htlc.rs` — verifier-robustness fuzz (proof + PI mutation, garbage/wrong-length).
- `htlc_air.rs`: `persistent_columns_are_non_vacuous`, `differential_native_vs_air`,
  `boundary_redeem_refund_windows`, `boundary_range_values`, `two_htlc_input_tx_verifies`,
  `all_zero_hashlock_redeem`, and 6 `forge_*_rejected` tests. The three heaviest (50+ proofs each) are
  `#[ignore]`'d so the default `cargo test` stays ~39s; run the full audit suite with
  **`cargo test --release -- --ignored`**.

## Validation
After round 3: default Rust suite green (51 htlc + the rest), the exhaustive audit suite green via
`--ignored` (54 htlc total), the fuzz green, full Zig suite + `check-production` + the real
join-split/HTLC integration green. Round-3 commits: `6c9f5af` (fuzz), `a56ceea` (M-1 fix), `11817e1`
(regression tests + spend_air doc).

## Net across three rounds
Round 1 found defense-in-depth gaps; round 2 found a HIGH privacy break (H-1, fixed) + leaks + M-3;
round 3 audited the fixes themselves (catching M-1) and replaced argument with executable proof. The
remaining open items are all out of lattica's scope (Phase-B `await_lock`/timeout, host-chain
reorg/anchor-window/cm-index) or recommended hardening (in-circuit `PI_HASHLOCK != 0`, remove
`spend_air`). The lattica v3 surface has now been read, reasoned, *and executed against* adversarially.
