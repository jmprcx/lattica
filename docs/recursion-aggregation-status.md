# Recursion — recursive-aggregation status & review guide

**Status (2026-07-05): monolith BUILT + VALIDATED (R1–R5); the R4 flat aggregator is built + measured; R5 self-recursion is deferred behind a wrap.** RESEARCH — feature-gated behind `--features recursion` (`scripts/check-abi-symbols.sh` proves zero recursion symbols in the default staticlib), NOT on any production path, NOT externally audited. The node consensus seam is unchanged (the aggregate tx-root is byte-identical to `batch_joinsplit_air::batch_root`), so the **batch** path carries production.

This doc **consolidates** the recursion family for review and gives an explicit **improvement surface** (§5) — it does not restate the siblings. Read those for the primitives/soundness detail:

- `docs/recursion-design.md` — what recursion buys over the batch, the model, feasibility (§10 = build status).
- `docs/recursion-verifier-audit.md` — the built single-inner verifier's constraint self-audit (§0: soundness claim, the 7-row cross-region binding table §0.2, the two fixed bugs §0.3, R5 §0.5, audit posture §0.6).
- `docs/recursion-aggregation-params.md` — the aggregation-tree soundness parameters (§1 the ≥100-bit floor, §3.3 topology, §4 tests, §5 the R5 wrap).

Purpose: a single entry point for an external reviewer (**Codex**) to look for ways to **improve the implementation**. It does **not** pull recursion into the production audit gate — that remains the batch path (`docs/AUDITORS.md`).

## 1. The recursion family at a glance

| Milestone | Claim | Status | Authoritative source |
|---|---|---|---|
| **R1** | One AIR (`MonolithAir`) accepts **iff `p3::verify(inner)` accepts** — real `JoinSplitAir` inner, non-hiding + hiding (`is_zk=1`), via a data-driven symbolic epilogue | BUILT + VALIDATED | `recursion-verifier-audit.md` §0; `air.rs:1023` `MonolithAir::eval` |
| **R3** | Query-scaling / peak-RSS measurement + aggregation-level soundness parameters | MEASURED + SPEC'd | `recursion-aggregation-params.md` |
| **R4** | Aggregator verifies **K** inner join-split proofs (row-disjoint tiles) and folds them into a block tx-root **byte = `batch_root`** | BUILT + VALIDATED (flat, depth-1) | `tests.rs:1606` `run_symbolic_aggregator` (`root == batch_root` at `tests.rs:1700`) |
| **R5** | Self-recursion (a monolith verifying a monolith) | MEASURED — **size- and degree-explosive; DEFERRED behind a wrap** | `recursion-verifier-audit.md` §0.5; `recursion-aggregation-params.md` §5; `tests.rs:1919` `phase9_self_recursion_probe` |

R2 / R6 / R7 are not milestones in the code; "productionization" (a callable aggregator entry + the C-ABI/Zig seam) is **B5** in `recursion-design.md` and is unbuilt (§4, §5.6).

## 2. What is built + validated (pointers, not proofs)

- **The in-circuit verifier** — `MonolithAir::eval` (`src/recursion/monolith/air.rs:1023`): transcript region (in-circuit `DuplexChallenger` → α, ζ, β, indices) + one super-tile per replayed inner query (FRI fold + Merkle openings + DEEP) + the OOD epilogue (`eval_symbolic_circuit`, walks `get_symbolic_constraints(inner)`) + the aggregator tx-root fold. The soundness argument (accept ⇒ p3::verify) is `recursion-verifier-audit.md` §0.1–§0.2.
- **The aggregator** — `run_symbolic_aggregator` (`src/recursion/monolith/tests.rs:1606`) tiles K real join-split inners and asserts the emitted tx-root equals `batch_root` (`tests.rs:1700`, `tests.rs:1682` for the per-instance `tx_statement_digest`). `build_aggregator_trace` (`tests.rs:1296`) returns an instance provable under **any** outer config.
- **Always-on guards** (run in the fast suite under `--features recursion`): the two `MonolithAir` constraint-fingerprint pins (`src/constraint_fingerprint.rs:106-134`), the degree-budget regression guard (`src/recursion/native_verify.rs:2141-2151`), and the geometry pins (`tests.rs` `geometry_matches_milestone`, `phase0_geometry_pin_and_budget`).
- **Runnable end-to-end gates** (all `#[ignore]`, slow): `phase8_joinsplit_monolith`, `phase8_joinsplit_hiding_monolith` (`native_verify.rs`), `phase8_joinsplit_aggregator` + `phase8_joinsplit_aggregator_probe` (`tests.rs:1905`/`:1822`), `phase9_self_recursion_probe` (`tests.rs:1919`).

## 3. Measured cost & scaling (2026-07-05 benchmark)

The R4 aggregator is **flat, depth-1**: it tiles K inner verifications row-disjoint in one AIR, so `height() = k_instances · inst_h()` (`air.rs:604`) — trace height, and thus peak RAM, grows **linearly in K**. CPU-vs-GPU hiding-prove, **inner q=8** (a reduced milestone; see the caveat), production hiding config, 24-core Ultra 9 275HX / RTX 5080 / 62 GB:

| K (tx) | rows | CPU prove | GPU prove | peak RAM |
|--:|--:|--:|--:|--:|
| 2 | 2¹⁶ | 31 s | 12.1 s | 10.6 GB |
| 4 | 2¹⁷ | 62 s | 22.9 s | 21 GB |
| 8 | 2¹⁸ | 130 s | 48.9 s | 42 GB |
| 16 | 2¹⁹ | **1150 s** (swap-bound) | **OOM** (thrashes > 108 GB) | 48 GB (RAM-capped) |

≈ **5.3 GB per tx — ~20× the batch's ~0.27 GB/tx** (the batch reaches 64 tx in 17 GB). The aggregator hits this box's RAM wall at **K ≈ 12–16**; K = 64 projects to **~340 GB**. At the wall the GPU's compute advantage inverts — it holds *more* host RAM (LDE resident for the CPU quotient + GPU staging) and OOMs before the CPU.

**Caveat:** these numbers are at **inner q = 8**. Production verifies q96/lb4 inners (`recursion-aggregation-params.md` §1), whose `inst_h` is several× larger — so a production-parameter aggregator is *heavier* per tx than the table shows. This is the quantitative case for the params doc's §3.3 guidance ("keep K small (2–4), get width from **tree depth**, not wide tiling") — and therefore for the R5 wrap (§5, item 4), since a deeper tree at bounded per-proof RAM is exactly what self-recursion would buy and what currently does not converge.

## 4. Remaining to production (roadmap)

1. Raise the outer config from the dev-box milestone (arity-2 / 32-query) to the batch's **q96 / lb4** and enforce the ≥100-bit proven-security floor **per aggregation level** (`recursion-aggregation-params.md` §1, §4).
2. The **R5 wrap** — a fixed-size, low-degree re-proof per tree level so self-composition converges (`recursion-aggregation-params.md` §5). Blocks any tree deeper than depth-1.
3. Real **dummy-proof padding** for K′ < K blocks (today only zero-value fold tiles exist — §5 item 5).
4. The **B5 C-ABI / Zig node seam** — a callable aggregator that constructs/verifies an aggregate proof, mirroring the batch seam (`recursion-design.md` B4/B5).
5. Audit artifacts (extend the corrupted-trace suite to the HTLC-precedent bar; `recursion-verifier-audit.md` §0.6).

## 5. Improvement targets / review asks for Codex

Prioritized. Each item is the issue, why it matters, and where to look. Items 1–6 are correctness/soundness/architecture; 7–10 are code health.

1. **The ≥100-bit proven-security floor is unenforced for the aggregator.** The milestone runs arity-2 / 32-query (`monolith/mod.rs:198-205`, `tests.rs:139` `MILESTONE_QUERIES = 32`, `native_fri.rs:376`); production needs q96/lb4 at *every* tree level (`recursion-aggregation-params.md` §1). No `proven_security_bits` / floor assertion exists in `src/recursion/` (the batch has one via `soundness-budget.md`). **Ask:** add the aggregation-level floor assertion and wire the query-count lift; confirm the construction is query-count-agnostic as claimed (`native_fri.rs:377`).
2. **`MonolithAir::eval` is one ~750-line function** (`air.rs:1023` to end of file) holding the entire soundness surface — and it is the named audit target (`recursion-verifier-audit.md` §0.6). **Ask:** decompose into per-region functions (transcript / super-tile / OOD epilogue / fold) with region-level unit tests, so the §0.2 binding table can be checked region-by-region against small functions rather than one monolith.
3. **The degree ≤ 16 / `log_num_quotient_chunks ≤ log_blowup` budget is a silent-corruption cliff.** p3-0.6.1 silently produces unverifiable proofs above it (`air.rs:1578` "SILENTLY corrupts the quotient"; the always-on guard `native_verify.rs:2141-2151`). The `is_zk=0` merge-link was migrated from the product form to a disjoint-one-hot **sum** form to hold ≤ 16 at the real db=12 join-split shape; the **`is_zk=1` branch still uses the pre-fix product form** under a standing "LATENT DEGREE BUDGET" note. **Ask:** migrate `is_zk=1` to the sum form (or prove it never crosses 16 for any shippable config); keep the guard always-on.
4. **R5 self-recursion needs a wrap.** Verifying the smallest monolith (W=193, 384 constraints) yields an outer of W≈8520 (~44×), ~133 GB LDE, `log_nqc = 7 > 4` — size- and degree-explosive per level, so naive tree self-composition diverges (`tests.rs:1919`; `recursion-verifier-audit.md` §0.5; `recursion-aggregation-params.md` §5). This blocks any tree deeper than the flat depth-1 aggregator (see §3). **Ask:** design the fixed-size/low-degree wrap (uniform verifier at a canonical small shape), or evaluate a SNARK wrap; this is R5's open problem.
5. **Dummy-proof padding is noted but unimplemented.** `MAX_AGG_TILES = 64` and K must be a power of two (`mod.rs:198-205`); the fold gadget pads absent tiles with a **zero public value**, not a verifiable dummy proof (`gadgets.rs:490`, `gadgets.rs:635` `padding tiles fold pvs0 = 0`). A real aggregator folding K′ < K genuine inners up to a power of two needs synthesized *verifiable* dummy inner proofs (design intent), not zero-value fold tiles. **Ask:** implement/spec dummy-proof instances and their soundness (a padded slot must not stand in for a real tx).
6. **B5 C-ABI / Zig node seam is entirely unbuilt** and gated out of the shipped staticlib (`Cargo.toml` `recursion` feature; `scripts/check-abi-symbols.sh`). The aggregator emits a `batch_root`-compatible tx-root but no `extern "C"` entry constructs or verifies an aggregate proof (`recursion-design.md` B4/B5). **Ask:** the callable aggregator entry + the seam (needs items 1 and 4 first for a production-parameter, tree-scalable path).
7. **Duplication / structure.** Two parallel re-verifier stacks — `native_fri.rs` (non-hiding) and `native_verify.rs` (hiding) — repeat the `log_nqc` / `create_disjoint_domain` prologue ~8×; the `as_basis_coefficients_slice(…).try_into()` "c/cc/pair" closure is re-declared ~15× across the module; a compile-time geometry twin (`mod.rs` `commit_layout`) and a runtime twin (`MonolithAir` methods) must agree, guarded only by `geometry_matches_milestone`. File sizes: `tests.rs` 3132, `lineage.rs` 2764, `native_verify.rs` ~2200, `air.rs` 1771. **Ask:** shared helpers; unify the two verifier stacks where sound; consider whether the geometry twins can be a single source of truth.
8. **Debug scaffolding left in the tree.** `src/recursion/native_verify.rs:2081-2195` (`hiding_monolith_cap2_bisect`, `hiding_monolith_check_small`, `hiding_monolith_e2e_small`) document a since-fixed failure hunt (the small-cap / query-index-specific hiding failure that #86 hardening resolved). **Ask:** prune, or convert the useful ones into permanent guards.
9. **Two `panic!("preprocessed columns unsupported")`** in live code (`gadgets.rs:946`, `native_fri.rs:1005`) — the symbolic epilogue cannot handle preprocessed columns. Production circuits define none, but the limitation is silent. **Ask:** note it explicitly / handle gracefully (a clear error, or support).
10. **97 of ~115 recursion tests are `#[ignore]`d** — the overwhelming majority of the surface never runs in the fast suite, so a reviewer cannot cheaply exercise it and CI cannot regression-guard it. **Ask:** a fast, representative subset (a small-config accept-iff-verify + one aggregator + the corrupted-trace core) that runs by default under `--features recursion`.

**Do not duplicate (reference instead):** the single-inner soundness claim + the 7-row binding table + the two fixed bugs → `recursion-verifier-audit.md` §0; what recursion buys + the build log → `recursion-design.md` §10; the tree soundness parameters + the R5 divergence table → `recursion-aggregation-params.md`.

## 6. Scope & audit posture

RESEARCH, feature-gated (`--features recursion`), NOT on any production path, NOT externally audited. Zero of the frozen `lattica_*` externs reach it; the default staticlib is recursion-free (`scripts/check-abi-symbols.sh`). The node consensus seam is unchanged regardless — the aggregate tx-root byte-matches `batch_joinsplit_air::batch_root` — so the **batch** path (which *is* in the production audit) carries production.

`docs/AUDITORS.md` §7 and `docs/audit-scope-p3.md` point here and have been corrected — their earlier "the in-circuit recursive verifier is NOT built" wording was stale; it **is** built + validated (R1–R5), it simply remains research and out of the production audit gate. Reviewing this work for improvement (this doc's §5) is distinct from auditing it as production.

## 7. See also

- `docs/recursion-design.md` — feasibility + what recursion buys (client-side proving, distribution, tree scaling).
- `docs/recursion-verifier-audit.md` — the built verifier's constraint self-audit (§0).
- `docs/recursion-aggregation-params.md` — aggregation-tree soundness parameters + the R5 wrap (§5).
- `docs/soundness-budget.md` — the proven/conjectured floor the aggregation levels inherit.
- `docs/AUDITORS.md` — the production audit handoff (recursion is §7, out of the gate).
