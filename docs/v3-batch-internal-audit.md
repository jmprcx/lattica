# v3 batch-delta — internal adversarial audit round (W5)

> **Frozen audit record:** Internal review evidence for the batch delta at its named revision.

Internal pre-audit of the **production delta since the `v3-audit` tag** — the batch-aggregation circuits
(`batch_joinsplit_air`, `batch_htlc_air`, `batch_common`), the shared refactor (`eval_spend`/config/ABI
dedup), and the batch C-ABI + node seam. Run before the external Codex audit to front-load fixes; it does
not replace that audit. Four independent adversarial lenses, each tasked to *break* the delta. Companion:
`docs/batch-constraint-audit.md` (the constraint accounting), `docs/audit-readiness-status.md`.

**Bottom line: no critical/high soundness break.** Cross-tile isolation holds (every key/value/randomness/
asset column is freed at the tile boundary or reset per tile); the tx-root fold is sound (every folded
field except `tx_binding` is bound by `eval_spend`, and every fold block is a fully-constrained Poseidon2
permutation); the A1–I8 refactor preserved the constraint set exactly (fingerprint-proven) and the ABI's
fail-closed properties (diff-verified). The findings are two robustness fixes at the C-ABI seam, one
audit-ergonomics fix, and doc/test-coverage hardening.

## Lenses

| # | Lens | Files | Verdict |
|---|---|---|---|
| L1 | Cross-tile leakage (value/key/rho/asset/nullifier) | `batch_*_air.rs`, `joinsplit_air.rs::eval_spend`, `batch_common.rs` | isolation holds; 2 LOW hardenings |
| L2 | tx-root fold forgery + padding substitution | `batch_common.rs::eval_txroot_fold`, `fold_chunks`, `batch_root`, `dummy_*` | fold sound; node obligations to disclose |
| L3 | Refactor regression (build/ABI/glue outside the pinned constraint set) | `eval_spend` call sites, `verify_abi`/`write_out2`, `build_batch_trace` | no regression; OBS-1 audit friction |
| L4 | Batch C-ABI + node trust seam | `lib.rs:559-682`, `verify_batch_bytes`, `node.zig` contract | 2 real seam gaps (F1, F2) |

## Findings

| ID | Sev | Finding | Status |
|---|---|---|---|
| **F1** | Medium | **`MAX_BATCH_TILES` not enforced on verify.** The 64-tile cap lives only on the prove path (`lib.rs:594-596,660-662`; `batch_joinsplit_air.rs:346-349`). `verify_batch_bytes` → `verify_proof_bytes` → p3 `verify` reads `degree_bits` from the attacker-supplied proof and bounds it only by `TWO_ADICITY=32`, so a K≫64 batch (K=128 already <100-bit, `batch_proven_security_floor`) verifies. Bounded in-repo because `node.zig` pre-caps + verifies against a self-recomputed ≤64-tile root — so the ≥100-bit floor is a **caller obligation, not a verify-seam property.** Any consumer that verifies before recomputing the root inherits below-floor soundness. | **fixed (W6)** — verify now rejects a trace above the 64-tile height |
| **F2** | Med-Low | **Prove-side cap bypass → UB + panic escaping `extern "C"`.** `padded_tiles(n) = n.max(1).next_power_of_two()` overflows to 0 for `n_tx ∈ (2⁶³,2⁶⁴)`, so `padded_tiles(n_tx) > 64` is `0 > 64` = false and the cap check is skipped; reaching it forces `witness_len == usize::MAX` (the `checked_mul` gate), after which `slice::from_raw_parts(ptr, usize::MAX)` is UB and `Vec::with_capacity(n_tx)` panics — **outside** the `catch_unwind`, breaching the documented "1 on panic" contract. Prove side (trusted), contrived input, but a real fail-closed/panic-isolation breach + latent UB. | **fixed (W6)** — reject `padded_tiles == 0`; move the unsafe slice + parse inside `catch_unwind` |
| **OBS-1** | Low | **Soundness tests panic under debug `cargo test`.** The 6 `wrong_*_rejected` tests (`joinsplit_air.rs:935-980`, htlc mirror) call `prove`, whose *debug-only* `check_constraints` panics on the deliberately-tampered public input instead of returning cleanly; they pass in **release** (verify → `Err`). An auditor running the standard (debug) `cargo test` sees red on security tests. Pre-existing, not a refactor regression. | **fixed (W6)** — wrapped in `catch_unwind` like `corrupt_trace_rejected` |
| **OBS-2** | Low | HTLC batch fold/ROOT threading has no *fast* oracle cross-check (join-split has `batch_dummy_padding_fold_matches_oracle`); HTLC's is only in `#[ignore]` slow tests. | fixed (W6) — added `htlc_batch_dummy_padding_fold_matches_oracle` |
| **D1** | Low | `docs/batch-constraint-audit.md` said the cap is "enforced in both provers **and** both ABI entry points" — those line refs are the *prove* entries only; verify enforced nothing (F1). | fixed (W6) — corrected + notes the F1 fix |
| **T1** | Low | No adversarial test pins cross-tile value conservation (all other isolation props have corrupted-trace tests). | fixed (W6) — added a below-floor / oversize verify-reject test |

## Confirmations (probed, sound — severity none)

- **Cross-tile isolation (L1).** `tile_last = one_hot(4095)` (verifier-fixed periodic column) frees `NK,NK1,RHO,RHO1,VAL,ASSET,POSACC` and every staged column at exactly each tile boundary; `VALACC` resets to 0 per tile via `P_ROW0`/`P_FINAL` with no `acc_delta` after the region end, so "imbalance tile A, compensate tile B" fails. `P_REGION_LAST` (≤2559) and `tile_last` (4095) are disjoint (no `−1` gate). Empirically: `batch_per_tile_asset_isolation`, `batch_within_tile_asset_tamper_is_rejected` pass.
- **Fold (L2).** Every folded chunk (`fold_chunks`) reads a staged column that `eval_spend` binds to a genuine spend value (anchor/nf/out_cm/fee/mint), tied to the fold injection by tile-persistence; the 8 `eval_txroot_fold` groups fire on exactly the right rows (no vacuity/off-by-one); fold blocks 120–127 ride the period-32 round constraints so each `s_k`/`root_k` is a genuine Poseidon2 output. Reorder/omit/add/padding-swap all change the node-recomputed root (`batch_root_is_order_sensitive`, `dummy_sk_is_deterministic_and_distinct_from_real`).
- **Refactor (L3).** Fingerprint oracle green (`(49,45,4,167,8,…)` js-batch, `(71,57,4,244,9,…)` htlc-batch); `eval_spend` degrades correctly to the pre-refactor form at `tile_last=0`; `verify_abi`/`write_out2`/`parse_root_digest` fail-closed on every path; `build_batch_trace` writes every column of every tile; no feature-gated (gpu/stream/recursion) type leaks into the production `MyConfig`/wire params.

## Node-side obligations (out-of-repo; the trust seam — for the auditor)

The circuit proves "the public root is the ordered fold of `padded_tiles(n)` valid spends" but does not publish n / the anchor / the real-vs-dummy split. The host chain (`rubble-node-zig`, per `docs/full-node-security-integration.md`) MUST:
1. **Pre-cap** the tile count (`paddedTiles(txs.len) ≤ MAX_BATCH_TILES`) and **verify against a self-recomputed** `batchRoot(txs)` over exactly its canonical tx set — never a root taken from untrusted block data. (F1 now makes the height cap intrinsic to the verifier as defense-in-depth, but the root-recompute is still the binding.)
2. Apply each tx against **its own** staged anchor and enforce the **anchor-freshness window** (`isKnownAnchor` is set-membership only — no expiry in-circuit or in the reference node).
3. Validate `tx_binding`'s meaning off-STARK (it is a free staged column, bound only via the recomputed root) — identical strength to the single-tx path.
4. Route join-split vs HTLC batch proofs to the matching verifier + recompute (roots share `DOM_TXROOT` and carry no self-describing type tag; separation is by distinct AIR shape + separate roots).
5. Bound aggregate block issuance (per-tile `mint` is range- + balance-checked, but the batch multiplies the surface).
