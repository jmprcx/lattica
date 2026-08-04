# Recursion — recursive-aggregation status & review guide

> **Research status:** Active, feature-gated work. No recursion symbol is exposed through the production C ABI, and the production-scale proof gate remains resource-blocked.

## Latest continuation — 2026-07-07 owned trace-store stream proof path

The production stream aggregate prover now moves the natural aggregate
`MmapLdeStore` into `stream_prove_from_trace_store_owned` instead of borrowing
it for the whole proof. The stream prover still builds the same trace
commitment and proof bytes, but drops the natural aggregate trace store
immediately after the trace commitment phase. Existing borrowed entrypoint
remains available for tests and non-owning callers.

Coverage added: `stream_prove_owned_trace_store_matches_borrowed_small_air`
proves a small Poseidon2 AIR through both borrowed and owned trace-store
entrypoints under deterministic one-thread FRI grinding and asserts byte-identical
proofs plus verifier acceptance. Production row emission remains covered by
`production_store_instance_matches_resident_instance_small`.

The owned stream prover now also consumes the quotient-value store through
`stream_commit_quotient_store_owned`, dropping it after split/evaluation stores
are built instead of carrying it through the rest of proof construction. This is
small relative to the trace LDE blocker but keeps the production stream path
ownership-based throughout trace and quotient commits. Coverage now includes
`stream_commit_quotient_matches_pcs` parity for resident, borrowed-store, and
owned-store quotient commits.

Spill accounting is now explicit:
`ProductionAggregateResourcePlan::stream_spill_estimate()` reports natural trace,
randomized trace, committed trace LDE, and trace-commit peak bytes separately.
The ignored q96 K=2 stream gate now prints the breakdown before returning at the
spill preflight. Current local K=2 numbers:
`trace_bytes=98_733_916_160`,
`randomized_trace_bytes=197_602_050_048`,
`committed_trace_lde_bytes=3_161_632_800_768`,
`trace_commit_peak_bytes=3_359_234_850_816`. This reduces the preflight by one
natural aggregate trace store (`98_733_916_160` bytes) versus the previous
borrowed-path estimate. The next meaningful production reduction remains the
committed trace LDE store itself, not C-ABI/Zig work.

## Latest continuation — 2026-07-06 q96 stream spill gate verified

The production K=2 binary-recursion stream path now fails safely at admission
when the spill filesystem is too small, instead of entering the mmap-backed
proof path and risking `SIGBUS`. On this workstation the ignored
`production_binary_recursion_k2_stream_proves_and_verifies` gate builds the two
real q96 JoinSplit proofs, plans `inner_query=31_009_440`,
`aggregate_query=31_072_800`, `aggregate_trace=2_097_152x5_885`, then exits
cleanly on the stream spill preflight:
`required_bytes=3_457_968_766_976` versus about `33_244_065_792` available.

`production_binary_recursion_k2_trace_resource_gate` now reports the same spill
preflight while preserving the conservative in-memory full-trace rejection
(`6_158_286_848` felts versus the default `134_217_728`-felt cap). A full q96
K=2 aggregate proof now requires either a large enough `LATTICA_SPILL_DIR`
filesystem or further reduction/streaming of the aggregate LDE/spill footprint.
Until that full proof/verify gate runs on production spill capacity, recursive
aggregation stays Rust-only behind `--features recursion`; no C-ABI/Zig seam
should be exposed.

## Latest continuation — 2026-07-06 hidden-inner source-backed production build

Production recursive aggregation no longer materializes every q96 hidden inner
monolith trace before folding. `build_symbolic_hiding_inner_window_source`
constructs an owned hidden-window source descriptor (`MonolithTraceSource`
inputs plus selector-window metadata). `build_production_instance` validates
all hidden inner shapes, allocates only the final folded aggregate trace, then
emits each hidden inner row range into its aggregate slot. Selector-window
columns are applied per emitted range, preserving byte-for-byte row parity with
the previous resident `monolith_build_trace` path.

Resource admission is backend-aware. Conservative
`ProductionAggregateResourcePlan::check_limits()` still rejects oversized
full hidden-inner and aggregate traces for in-memory callers. Production
proving/verifying with `AggregationBackend::Stream` gates hidden inner work on
`inner_query_segment` and aggregate work on `aggregate_query_segment`.

The stream production branch uses `build_production_store_instance`: it emits
the folded aggregate trace directly into `MmapLdeStore` and calls
`stream_prove_from_trace_store`, while the in-memory branch keeps the resident
`build_production_instance` path. `stream_open` now interpolates low cosets
from the committed store, keeps inverse-denominator precomputation in
`ChallengeCodewordStore`, compresses matrix blocks in chunks, writes reduced
FRI input accumulators to `ChallengeCodewordStore`, and proves FRI through
`stream_prove_fri_from_input_stores`. FRI commit/fold rounds now operate from
mmap-backed extension-field codeword stores and materialize only the final
short polynomial.

Coverage added/updated:
- `symbolic_hiding_inner_window_source_matches_resident_trace` proves emitted
  hidden-source ranges plus selector columns equal direct resident
  `monolith_build_trace` on a small binary-FRI hiding JoinSplit proof.
- `production_resource_plan_checks_backend_limits` locks in-memory full-trace
gates and stream query-segment gate semantics.
- `production_store_instance_matches_resident_instance_small` proves the
  store-backed aggregate rows equal the resident aggregate builder on a small
  binary-FRI hiding JoinSplit proof.
- `stream_prove_fri_matches_p3` now also checks store-backed FRI input proofs
against the resident streamed proof.
- `stream_pcs_open_matches_pcs` covers store-backed trace commitment,
store-backed low-coset interpolation, block-wise reduced-opening compression,
store-backed inverse denominators, store-backed FRI inputs, and proof parity
against P3.

Measured hardening gate: `stream_prove_matches_p3` still passes after the
store-backed denominator change (`539.54s`, sampled process-tree peak
`MAX_TREE_RSS_KB=398652`, about 389 MiB). Remaining production hardening:
run the real q96 K=2 stream aggregate proof on a spill filesystem large
enough for the current aggregate LDE footprint, or reduce that footprint
before exposing any C-ABI/Zig seam.

## Latest continuation — 2026-07-06 quotient commit and opt-random stores

`stream_prove` now keeps the quotient value vector in `MmapLdeStore` base-coordinate form and commits
it through `stream_commit_quotient_store`. This bypasses the resident `RowMajorMatrix<Val>` built by
`RowMajorMatrix::new_col(quotient).flatten_to_base()` and bypasses P3's resident `split_evals` copy.
The store-backed commit splits rows with the same interleaving as P3 (`row i*num_chunks + chunk`),
draws random columns in `with_random_cols` order, stages quotient-mask randomizers in mmap stores,
and then runs the same column-tiled quotient LDE/vanishing-mask path. Coverage: the existing
`stream_commit_quotient_matches_pcs` now checks both the old resident wrapper and the new store-backed
wrapper against P3 `commit_quotient`.

The opt-random commitment no longer materializes `RowMajorMatrix::<Val>::rand(...)`. The new
`stream_commit_random_matrix` writes random rows to a natural-order mmap store, runs the same
column-tiled coset LDE into committed order, and hiding-commits that store. Coverage:
`stream_commit_random_matrix_matches_resident_commit` compares cap and sampled openings against the
old resident `stream_commit` path under identical matrix/salt seeds.

Full proof coverage: `stream_prove_matches_p3` now passes under `--features stream`
after quotient-store commit and opt-random store wiring, proving the full streamed
proof remains byte-identical to p3 on the deterministic JoinSplit fixture.

The production q96 binary-recursion stream gate now reaches production planning
without resident quotient-domain trace, quotient-value matrix, randomized
quotient chunk inputs, opt-random matrix, or full hidden-inner trace. On this
machine it exits cleanly at the aggregate stream spill preflight rather than
entering a SIGBUS-prone proof run; current K=2 spill estimate is about 3.46 TB.

## Previous continuation — 2026-07-06 store-backed quotient evaluator

`stream_prove` now computes quotient values with
`stream_quotient_values_from_store` instead of first rebuilding the resident
quotient-domain trace matrix. The evaluator mirrors p3's selector,
periodic-table, alpha-decomposition, and `ProverConstraintFolder` path, but
loads each packed local/next trace window directly from the committed
bit-reversed `MmapLdeStore` and truncates hiding-random columns at the AIR
width.

Coverage: `stream_quotient_values_from_store_matches_p3` builds a real
JoinSplit trace, commits it through the streamed hiding trace path, compares
the new store-backed quotient vector against p3's `quotient_values` fed by the
old resident materializer, and passes under `--features stream`.

This removes the immediate `qsize × trace_width` resident
trace-on-quotient-domain allocation from full `stream_prove`. The evaluator now
reads contiguous committed-store blocks keyed by `next_step`, so each block
contains both local and next rows for its packed lanes. Remaining production
work in this layer: stream or chunk the quotient vector/quotient commit path so
the prover is not still bounded by resident quotient values and randomized
quotient chunk inputs.

## Previous continuation — 2026-07-05 quotient-domain store view experiment

The stream prover now has `StoreBitrevPrefixMatrix`, a `Matrix<Val>` view
over a committed bit-reversed LDE `MmapLdeStore`: it exposes the first
quotient-domain row prefix as natural-order rows and truncates to the public
trace width, matching `stream_trace_on_quotient_domain` without allocating
the resident quotient-domain trace matrix. A focused test compares ordinary
rows and `vertically_packed_row` output against the existing resident
materializer.

This view is byte-correct but is not yet wired into the full `stream_prove`
quotient path. P3's current `quotient_values` runs a parallel packed-row loop
through generic `Matrix` row-slice access; the naive store view turns that
into random mmap row gathers and is too slow for the full proof regression.
The production-ready cut is therefore a row-block streaming quotient evaluator
that walks the LDE store sequentially, constructs the two packed row windows
needed by `ProverConstraintFolder`, and avoids both the resident
quotient-domain matrix and random store access.

## Latest continuation — 2026-07-05 source-driven hiding trace commit seam

The stream prover now exposes `stream_commit_store_hiding`, a lower commit
seam that accepts an already materialized bit-reversed LDE `MmapLdeStore`,
draws hiding salts in the same order as `ValMmcs`, and builds the same
`StreamCommitData` used by streamed openings. `MmapLdeStore` also gained
`write_row`, used only for row-order sources such as P3's hiding
randomization.

The monolith source now has `monolith_trace_hiding_coset_lde_store` and
`monolith_trace_hiding_commit`. These mirror P3's
`with_random_cols(w + 2*nrc)` then `width = w + nrc` reshape without
materializing the monolith trace: random tails are generated in P3 row order
into an mmap store, source rows fill even randomized rows, odd randomized rows
come from the random tail, and the resulting randomized trace LDE is written
to the store in committed bit-reversed order. The stream monolith guard now
checks this hiding store's sampled rows, commitment cap, and opened row
against the resident P3-equivalent randomized LDE path.

This removes the resident trace allocation from the trace-commit side of the
recursive monolith stream path. Quotient evaluation now reads trace windows from
the LDE store, so the remaining resident production blockers are the quotient
vector itself and randomized quotient chunk inputs during quotient commit.

## Latest continuation — 2026-07-05 PCS-boundary striped LDE + mmap row store

P3's current PCS boundary was confirmed resident at the transform layer:
`TwoAdicSubgroupDft::{coset_lde_batch,lde_batch}` consumes
`RowMajorMatrix`, and `TwoAdicFriPcs::commit` / `HidingFriPcs::commit`
still require resident evaluation matrices. The recursive monolith now has
a local adapter below that seam: `monolith_trace_coset_lde_stripes` streams
`MonolithTraceSource` into bounded column stripes, runs P3's exact coset
LDE for each stripe, applies the same bit-reversal that `TwoAdicFriPcs`
commits, and emits byte-identical LDE stripes.

With `--features recursion,stream`, `monolith_trace_coset_lde_store` writes
those stripes into the existing column-major `MmapLdeStore` from
`stream_prove`. The fast guard proves the store-backed `StoreMatrix` rows,
MMCS commitment, and MMCS opening match the resident P3 LDE for the
two-query monolith fixture. This keeps the trace source, LDE transform, and
Merkle leaf commitment on a non-resident path for the tested slice.
`MonolithTraceSource::emit_range` also now emits transcript rows directly
from recorded Poseidon2 block inputs, so stripe generation no longer builds
a temporary full-transcript matrix per stripe.

Remaining production work is still above this adapter: wire the same
store-backed matrix into a recursive PCS/prover path that can also compute
openings and quotient commitments without rebuilding full `RowMajorMatrix`
inputs, then re-run the q96 production resource gate.

## Latest continuation — 2026-07-05 chunked monolith row source + MMCS chunk consumer

The resident monolith trace builder now materializes through
`MonolithTraceSource`: the source exposes transcript/query/padding row ranges,
emits each range into caller-owned buffers with `emit_range`, and
`monolith_build_trace` is now only a resident wrapper over that chunk producer.
Query chunks are exactly `air.m_period() × air.fused_w()` felts and use the
shared `fill_monolith_query_segment` path, keeping the resource planner's
single hidden q96 query-segment estimate (`31_009_440` felts) aligned with the
emitted unit.

`MonolithTraceChunkMatrix` now adapts one emitted range to P3's generic
`Matrix` trait. The fast guard commits a query chunk through the crate's hiding
MMCS and compares the commitment/opening with the equivalent resident chunk,
which is the first real commitment-layer consumer of chunked monolith rows.
This still stops below the PCS/prover layer: P3's `HidingFriPcs` interface
currently takes resident `RowMajorMatrix` inputs for LDE construction.

Fast guard `monolith_query_segment_matches_resident_trace` now materializes a
two-query column-window ConstAir monolith range-by-range, checks contiguous
coverage of the full trace height, compares the chunked output with the
resident matrix, and still checks a standalone query segment against its
resident slice. This proves the trace producer no longer requires the full
monolith `Vec` internally. Remaining integration work is a PCS/prover adapter
that can LDE/commit/open from these chunks without first materializing a full
trace `RowMajorMatrix`.

## Latest continuation — 2026-07-05 resource gate

The binary-recursion K=2 production-hiding gate now has an explicit planner API, `plan_joinsplit_aggregate_production`, and an allocation preflight instead of attempting to materialize oversized traces. The planner performs structural parsing/shape checks without full STARK verification; production prove/verify paths still verify inputs before proving or verifying aggregates. `production_binary_recursion_k2_trace_resource_gate` proves/verifies q96 binary-profile inputs through admission, plans the aggregate, then stops at `ResourceLimit` for the first hidden inner monolith trace: `6_158_286_848` felts required versus the default `134_217_728`-felt cap. `LATTICA_RECURSION_AGG_MAX_TRACE_FELTS` can raise that cap only for intentional benches. The same plan shows a single hidden query segment is `31_009_440` felts and fits the default cap, which makes a segment/out-of-core trace emitter the next concrete implementation target.

This makes the current production blocker concrete: q96 recursive aggregation needs a non-materializing/out-of-core monolith trace path, a smaller wrap construction, or another design that avoids flat q96 hidden monolith materialization before any C-ABI/Zig seam.

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

## 3.5. 2026-07-05 implementation note — research R4 Rust API

Codex follow-up promoted the validated **non-hiding R4 flat JoinSplit aggregator** out of test-only scaffolding into `lattica-prover-p3/src/recursion/aggregation.rs`, still behind `--features recursion`. New Rust API:

- accepts power-of-two research JoinSplit inner proofs plus public values,
- verifies inner proof under explicit `native_fri` recursion parameters,
- builds same `MonolithAir { column_window, fold_txstmt }` aggregate trace used by R4 tests,
- folds statements with `tx_statement_digest` so aggregate tx-root remains byte-identical to `batch_joinsplit_air::batch_root`,
- proves outer aggregate under the normal production proof type, using the streaming CPU backend when `--features stream` is enabled.

This is **not** the final production-hiding recursive aggregator. The promoted API named `ResearchAggregationOptions` keeps the inner proof family explicit. Production-hiding q96/lb4 aggregation is partially wired through a Rust-only research path, but production FRI arity support, real dummy-proof padding, C-ABI/Zig seam, and R5 wrap remain roadmap items below.

Fast coverage added: `recursion::aggregation::tests::{research_aggregator_builds_k2_trace,research_aggregator_rejects_non_power_of_two}`. Slow manual gate added: ignored `research_aggregator_proves_and_verifies_k2`.

## 3.6. 2026-07-05 productionization plan + current execution

Production rollout is sequenced so each step has a verifier-facing acceptance gate before any C-ABI node integration:

1. **Production admission gate** — verify real `crate::config::MyConfig` JoinSplit proofs, require hiding proof structure, q96 query count, cap height 6, power-of-two fan-in, compute batch-identical tx-root. **Done:** `admit_joinsplit_aggregate_production` in `recursion/aggregation.rs`; it now also preflights the production JoinSplit quotient/degree shape before full verification. Fast fail-closed tests added.
2. **Production-hiding R4 trace builder** — promote validated `is_zk=1` witness extraction from `native_verify.rs` into reusable builder code constructing `MonolithAir { is_zk: 1, column_window: true, fold_txstmt: true }` aggregate traces, K=2 first. **Partially done:** `prove_joinsplit_aggregate_production_research` parses/verifies q96/cap6 hiding JoinSplit proofs, builds hidden column-window aggregate traces, folds `tx_statement_digest`, can prove through existing in-memory/stream backends, and `verify_joinsplit_aggregate_production_research` rebuilds the same instance before verifying the outer proof. Production prove/verify paths now preflight the final aggregate trace height, quotient chunks, and degree bits before invoking P3.
3. **FRI arity + soundness/degree gate** — current monolith query fold is one-bit-per-round, so the node production profile (`max_log_arity=4`) still rejects non-binary commit rounds with `UnsupportedFriArity`. **Partial mitigation:** `config::make_recursion_binary_config` pins a production-parameter recursion profile (q96/lb4/cap6/query-PoW16, binary FRI rounds). The ignored one-proof binary-recursion dummy smoke gate passes; the ignored K=2 trace gate now builds real q96 binary-profile inputs, reaches production planning, confirms stream query-segment gates fit, and reports the conservative in-memory full-trace rejection plus stream spill preflight. Remaining decision is either integrating general-arity folds into the fused AIR or accepting the binary recursion profile as the recursive-input proof family.
4. **Streaming proof gate** — ignored `production_binary_recursion_k2_stream_proves_and_verifies` now reaches the real q96 K=2 aggregate plan under `--features recursion,stream` and exits cleanly on spill capacity (`required_bytes≈3.46 TB`, about `33 GB` available here). Full proof/verify remains blocked until a production spill filesystem is provided or the aggregate LDE/spill footprint is reduced.
5. **Dummy-proof padding** — replace power-of-two-only admission with verifiable dummy inner proofs; do not use zero-value fold padding for production padding. **Partially done:** `pad_joinsplit_aggregate_production_inputs` validates the real inputs and dummy proof under the selected production input profile, requires the dummy public values to hash to `batch_joinsplit_air::dummy_sk()`, and `prove_joinsplit_aggregate_production_padded_research` pads before proving. Ignored `production_binary_recursion_dummy_proof_verifies` proves/verifies one binary-profile dummy proof and checks the dummy digest. Remaining work is generating/distributing the canonical dummy proof for the accepted production-recursion profile and measuring K=2/K=4 resource cost.
6. **R5 wrap** — design fixed-size/low-degree wrap before any recursive tree deeper than flat R4; direct monolith-over-monolith remains non-convergent.
7. **C-ABI/Zig seam + audit** — only after steps 1–6 pass gates; default staticlib remains recursion-free until explicitly moved into scope.

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
