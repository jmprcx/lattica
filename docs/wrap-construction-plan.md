# Wrap-AIR construction plan — the recursion fixed point

> **Research roadmap (branch `tree-tip5-research`, a worktree off `v3`) — NOT part of the v1 audit artifact
> and NOT on any production path.** The full construction plan for the deep-recursion wrap, spec'd for a
> specialist to execute. Companion: [`deep-tree-tip5-design.md`](deep-tree-tip5-design.md) (the architecture
> + Phase-0 feasibility). Start at [`AUDITORS.md`](AUDITORS.md) for the audited surface.

## Context

The recursion tree needs a **wrap**: a canonical, **fixed-size, low-degree (≤16), self-composing** in-circuit
STARK verifier, so tree levels stack at bounded cost. Today the "monolith" verifier **explodes** under
self-recursion — verifying a W=193 monolith yields W=8520 (~44×), `log_nqc=7 > log_blowup=4` (the hard
degree-16 cliff that silently corrupts). This roadmap builds the wrap that converges.

**Already de-risked + built (on `tree-tip5-research`, feature-gated, isolated):** measured GO (0a′: degree
91→`log_nqc 7` reproduced; deg 7 & lookup deg 3 clear the cliff); **real Tip5 constants** + a Tip5-committed
proof that verifies end-to-end; the **LogUp lookup argument** validated (constraint degree *measured* = 3;
aux-well-formedness validated) + a **working two-round prover skeleton** on the real config; the
**size-stability fixed-point model** (monolith `B≈48` diverges, lookups drive `B<1`).

**Design decisions:** wrap designed **K-ary / DAG-ready** — each wrap aggregates K children, aligning with a
block-DAG where each block wraps K parents (the existing flat aggregator is already K-ary).

## Status (built on `tree-tip5-research`; blow-by-blow lives in the commits + auto-memory — this doc is the forward spec)

- **W1 — DONE.** The forked lookup-capable prover (`src/lookup/prover.rs`) is complete end-to-end: combined
  AIR+lookup layout, the shared single-point constraint folder, quotient-over-domain, and the batched
  ζ-opening of trace + aux + quotient. A range-check lookup AIR round-trips; imbalance → `NonZeroTerminal`,
  tamper → `Pcs`/`OodMismatch`, forged aux → `OodMismatch`. 16/16 lookup tests.
- **W2 — IN PROGRESS; the DEGREE crux is measured GO, the full assembly remains.** The prover is generalized
  to arbitrary interaction AIRs (public values, multi-arity, periodic), and the three high-degree constructs
  **B / C / I** are each built + measured in `src/wrap/mod.rs`. The `log_nqc ≤ 4` degree crux (vs the
  monolith's 7) is measured **three independent ways** — synthetic 384-constraint models, the **real
  81-constraint `JoinSplitAir`** epilogue, and the accessible-region rollup (composed 3). **W2-super** then
  folded the reused `--features recursion` super-tile tiles into the rollup and measured them (D/E/F = 2/3/3),
  so classes A/D/E/F sit ≤ budget too. **Remaining = W2-assemble + W2-measure** — build the actual wrap AIR
  and measure the whole construction (incl. the G/H/J `monolith/air.rs` regions) — the actual gate.

## The load-bearing insight (from the grounded conversion map)

The degree explosion has **one source**: the **α_stark constraint-fold** (Horner over the inner's
constraints, `monolith/air.rs:1310-1331`, `FOLD_CHUNK` `:481`) + its **symbolic epilogue**
(`gadgets.rs:919-973`). The inner AIR is tuned to sit at *exactly* `maxd≤16`, so **any** α-Horner fold of it
(+1 for `·α`, +1 for the region gate) exceeds 16 → `log_nqc 7`. **No `FOLD_CHUNK` value escapes this.** Every
other gadget is already ≤16 and **reusable verbatim**. So the fix = express each inner verification relation
as a degree-≤3 **LogUp** — and it is **independent of Tip5** (Tip5 is the separate *size* lever). ⇒ gate the
**degree** crux first with the existing Poseidon2 gadgets, then do Tip5 + the fixed point.

## Conversion map — reuse vs replace (the wrap blueprint)

**REUSE verbatim (already ≤16; size-dominant; validated):**
- A Poseidon2 rounds — `air.rs:1056-1073`, `poseidon2_air.rs:36-47` · D FRI β-fold — `air.rs:1211-1230`,
  `fri_fold.rs:58-62` · E Merkle-opening + **SUM-form `not_term`** (load-bearing) — `fri_merkle.rs:81-162`,
  `air.rs:1569-1615` · F transcript sponge — `air.rs:1075-1103`, `transcript.rs:48-114` · G DEEP α_fri
  witnessed-`apow` batch — `air.rs:1144-1164` · H OOD selectors + z_h squaring — `air.rs:1247-1285` · J
  aggregator tx-root fold — `air.rs:1689-1768`.

**REPLACE with lookups (the high-degree constructs):**
- **B** α_stark fold (`air.rs:1310-1331`) → **one LogUp per inner constraint** (deg ≤3).
- **C** `eval_symbolic_circuit` (`gadgets.rs:919-973`) → table / running-sum; **never re-evaluate the tree**.
- **I** cap-mux product (`air.rs:1652-1664`; cap width `2^cap_height·4`) → **index→cap-entry lookup** (kills
  both the `cap_height`-degree product and the `2^cap_height` width).

**CANONICALIZE the inner-dependent dims to fixed constants** (so outer size is independent of the inner —
the defining wrap property): `nb→cm_rounds→lg`, `n_terms`→9-col tiles, `w_inner`, `nqc`, `cap_height`.

## Phases (gated). W2 and W5 are the make-or-break research gates; the rest is spec'd engineering.

**W1 — Complete the lookup-capable prover. — DONE.** `src/lookup/prover.rs`, forked over `p3-lookup` LogUp:
- **W1.1** — the **combined AIR+lookup constraint layout** + `log_nqc` (`combined_constraint_layout`; p3's own
  helper misses the lookup constraints, sizing the quotient domain too small).
- **W1.2** — `batched_constraints_at_point`, a single-point scalar folder via
  `VerifierConstraintFolderWithLookups` **deliberately shared by the prover quotient AND the verifier
  ζ-check**; plus `lookup_quotient_values` (fold ÷ Z_H over the quotient domain; aux reconstructed from the
  `flatten_to_base` layout, col `c*D+d`) and the 3-round `prove_lookup_with_quotient` (main → sample
  α_L/β → commit aux → sample fold-α → commit quotient → ζ).
- **W1.3** — the batched **ζ-opening** `prove_lookup` / `verify_lookup`: opens trace + aux at {ζ, ζ·g} and
  each quotient chunk at ζ in one FRI proof (aux round appended so trace/quotient indices are undisturbed);
  verify = `pcs.verify` + the OOD identity `folded(ζ)·Z_H(ζ)⁻¹ = Q(ζ)` (same folder) + the LogUp terminal.

*Milestone met:* a range-check lookup AIR round-trips; imbalance → `NonZeroTerminal`, tampered opening →
`Pcs`/`OodMismatch`, forged aux → `OodMismatch`. 16/16 lookup tests. (ZK caveat: the optional FRI-batch
randomization poly is omitted — ZK-only, not soundness; salted-Merkle + random-column hiding retained.)

**W2 — [GATE 1 · DEGREE]. — IN PROGRESS (degree crux measured GO; full assembly remains).** Build a wrap AIR
(`src/wrap/`) that verifies a **real join-split inner** (Poseidon2 hashing reused = class A) with **B/C/I
expressed as lookups / witnessed low-degree columns**, and measure `log_nqc ≤ 4` (vs the monolith's 7) on the
*real* construction (converting 0a′'s model to a measurement on the actual wrap).

*Delivered (each committed + measured in `src/wrap/mod.rs`, probe = `wrap_log_nqc` over p3's own
`get_log_num_quotient_chunks`):*
- **W2.0–2.2** — generalized the W1 prover from `RangeCheckAir` to any interaction AIR, threading public
  values, multi-arity lookups (2 challenges per lookup), and periodic columns. The fold now handles every AIR
  feature the wrap needs.
- **W2-B** (`FoldAir`) — the α_stark constraint-fold. **Witness** each inner-constraint value `c_k` in a
  degree-1 column and **chunk** the α-Horner (`FOLD_CHUNK`): at the 384-constraint join-split scale,
  `log_nqc 3`. Both levers are needed — inline deg-16 → 5, unchunked witnessed → 9.
- **W2-C** (`DagFoldAir` wide + `ChainEvalAir` narrow-tall) — evaluate each `c_k` at low degree *without* the
  inline degree-16 expression: either witnessed degree-2 steps (`t_i = t_{i−1}·x_{i+1}`, `c_k` degree-1, `2d−1`
  cols) or a running product down the rows (constant width — `d` rows not `2d` cols). Both `log_nqc ≤ 3`; the
  narrow-tall form also validates the prover's **transition** support end-to-end.
- **W2-I** (`CapMuxAir`) — the cap-mux as a single 2-element `(index, value)` LogUp with signed multiplicity:
  **width 3 (const, not `2^cap_height`), degree 3 (not `cap_height`)**. First wrap component to
  PROVE+VERIFY through the W1 prover; wrong selection → `NonZeroTerminal`.
- **W2-real** — grounded on the REAL inner: `get_symbolic_constraints(JoinSplitAir)` = 81 constraints, max
  degree 8, 214 unique Mul nodes (= the witnessed C columns with `Arc`-identity sharing). The witnessed
  epilogue over the real DAGs holds `log_nqc 3`.
- **W2-rollup** (`wrap_degree_budget_rollup`) — `log_nqc` composes as the MAX over regions, so rolled up the
  accessible real regions: epilogue B (real 81-constraint inner) = 3, real Poseidon2 hash (`Poseidon2RowsAir`,
  the super-tile Merkle/transcript hash) = 3, cap-mux I = 1, chain-eval C = 2 ⇒ **composed `log_nqc 3 ≤ 4`**.
- **W2-super** (`wrap_degree_budget_rollup` under `--features lookup,recursion`) — folded the reused
  super-tile verifier tiles into the rollup and MEASURED each ≤ budget: **D (FRI β-fold) = 2, E
  (Merkle-opening + SUM-form `not_term`) = 3, F (transcript sponge) = 3** (alongside A = 3, B over the real
  inner = 3, I = 1, C = 2) ⇒ composed `log_nqc 3 ≤ 4`. The plan's "every other gadget is already ≤16"
  premise is now a **measurement** for classes A/D/E/F (`FriFoldAir`/`FriMerkleAir`/`SpongeAir` are standalone
  AIRs faithful to the monolith's fused regions; each satisfies `wrap_log_nqc`'s `SymbolicAirBuilder` bound).

*Remaining — the full wrap assembly (the actual GATE; large, multi-session):*
- **W2-assemble — build the actual wrap AIR** in `src/wrap/` (extend `mod.rs` into `air.rs`/`gadgets.rs`):
  compose the transcript (F) + super-tile (A/D/E) regions over the real inner **on top of** the grounded
  B/C/I epilogue + the class-J tx-root fold, reusing the recursion gadgets **verbatim** per the conversion
  map. This is where the last unmeasured reuse-classes — **G (DEEP α_fri), H (OOD selectors + z_h squaring),
  J (tx-root fold)** — enter, as regions of `monolith/air.rs` (not standalone AIRs), measured once a
  `MonolithAir`-shaped instance exists. Like the monolith #86 build, this is *coupled* — no incremental
  validation until it proves end-to-end.
- **W2-measure — the GATE.** Measure `log_nqc ≤ 4` (via `wrap_log_nqc` / the native
  `get_log_num_quotient_chunks` guard) on the **whole assembled wrap** verifying a real join-split inner, and
  prove + verify + tamper-reject it. **GO/NO-GO:** the full construction holds ≤ 4 ⇒ degree solved; else the
  offending region (its measured `log_nqc`) points straight back to its lookup encoding.

The degree crux is already measured GO three independent ways (synthetic, real 81-constraint inner,
accessible-region rollup — all ≤ 4), so W2's residual risk has narrowed from *"does the lookup encoding
work"* to *"does the **assembled** composition stay ≤ 4"* — i.e. whether the remaining super-tile gadgets in
fact hold ≤ 16 (the plan's premise, which W2-super now measures).

**W3 — Canonicalize the shape.** Fix `nb/cm_rounds/n_terms/cap_height` to canonical constants; the cap-mux
lookup (I) removes the `2^cap_height` blow-up; a canonical FRI shape fixes `n_terms`. *Milestone:* the wrap's
width is **measured constant** across inner shapes (independent of the inner).

**W4 — Tip5 for size (the `B<1` lever).** Real Tip5 leaf Layer-A migration (config exists in
`tip5::proof_system`; do the leaf-circuit swap + native packed Tip5 + wire KATs) **and** swap the wrap's own
hashing to Tip5 (reuse the lookup S-box) → ~4.6× fewer hash rows. *Milestone:* the wrap's width **contracts**
(measured `B<1` on the hashing-dominated term).

**W5 — [GATE 2 · SIZE / FIXED POINT].** Make the wrap verify a **canonical** proof + re-emit the **same**
canonical shape; self-compose (wrap-verifies-wrap). Measure **`W_out ≤ W_in`** (the attracting fixed point —
converting 0a/P3's models to a measurement on the real wrap). **GO/NO-GO:** non-expansive self-composition ⇒
the tree converges; else redesign the canonical shape.

**W6 — K-ary tree / DAG aggregation.** Self-compose the wrap **K-ary** (each wrap aggregates K children —
DAG-ready); block tx-root **byte-identical** to `batch_joinsplit_air::batch_root` (reuse the class-J fold
seam). *Milestone:* aggregate K txs → one proof at bounded per-node RAM, parallelizable; a K-ary tree/DAG
converges.

**W7 — Integration + re-audit + soundness.** Feature-gate (`wrap`/`tree`, OFF by default, out of the audited
staticlib — `check-abi-symbols.sh`); new **soundness budget** (LogUp soundness + Tip5 cryptanalysis + a
per-tree-level proven-security floor); the wrap-verifier **constraint audit** (accept-iff-verify + a
corrupted-trace matrix). The **C-ABI/Zig seam stays DEFERRED** (research; a node-callable aggregator + a
≥128 GB server is premature until W5 lands).

## Files

- **New / extend:** `src/lookup/prover.rs` (W1 ✅ complete); `src/wrap/mod.rs` (the B/C/I constructs + the
  rollup probe ✅ — extend into `air.rs`/`gadgets.rs` for the W2-assemble wrap AIR); `src/tree/mod.rs` (the
  degree/size fixed-point models ✅ — extend for K-ary self-composition + the W5 probe); update
  `docs/deep-tree-tip5-design.md`.
- **Reuse (committed recursion gadgets):** `recursion/poseidon2_air.rs` (A), `fri_merkle.rs` (E),
  `fri_fold.rs` (D), `transcript.rs` (F), `monolith/air.rs` G/H/J patterns, `native_fri.rs`/`native_verify.rs`
  (the verification-algorithm spec + the always-on degree guards).
- **Replace with lookups:** `monolith/air.rs:1310-1331` (B), `gadgets.rs:919-973` (C), `air.rs:1652-1664` (I).
- **Do NOT touch:** the concurrent recursion work in flight (`aggregation.rs`, `native_verify.rs`,
  `monolith/{build,tests}.rs`, `native_fri.rs`, `config.rs`, `stream_prove.rs`); the v1 surface (10 frozen
  externs, `Proof<MyConfig>`, the note model).

## Verification / gates

- **W1 ✅:** `cargo test --features lookup` — the range-check (and cap-mux) lookup AIRs round-trip; imbalance
  → `NonZeroTerminal`; tamper → `Pcs`/`OodMismatch`; forged aux → `OodMismatch`. 16/16 lookup tests green.
- **W2 (GATE 1):** `wrap_degree_budget_rollup` measures **`log_nqc ≤ 4`** — ✅ on the accessible regions
  (composed 3) and, under `--features lookup,recursion` (W2-super ✅), with the reused super-tile tiles D/E/F
  folded in (2/3/3, still composed 3). The gate closes when the same probe, run over the fully-assembled wrap
  (W2-assemble, incl. the G/H/J monolith-air regions), still measures ≤ 4 verifying a real join-split inner.
- **W5 (GATE 2):** a self-verify probe measures **`W_out≤W_in`** — the size/fixed-point GO/NO-GO.
- **Throughout:** `check-abi-symbols.sh` green (feature-gated; 0 symbols in the default staticlib); each
  phase committed + pushed on `tree-tip5-research`.

## Honest risk framing

W2 and W5 are genuine **research gates**, not foregone — but the built measurements point hard to GO: **W1 is
DONE**, and W2's **degree crux is now measured GO three independent ways** (synthetic models, the real
81-constraint join-split inner, and the accessible-region rollup — all `log_nqc ≤ 4`), so its residual risk
has narrowed to whether the **assembled** construction (with the `--features recursion` super-tile gadgets)
holds ≤ 4. The size fix (W5) still rests on `B<1` (*modeled* from the measured monolith `B≈48` + lookups'
fixed per-column cost). Everything else is bounded engineering with precise file:line specs. Rough scale:
multi-month, one specialist; **the live front is the W2 full wrap assembly** (`src/wrap/`, large/multi-
session — W2-super → -assemble → -measure). A NO-GO at the W2 assembly or W5 would point back to the
encoding / canonical shape, not a fundamental barrier — the PQ mandate rules out the curve/SNARK-wrap
shortcut, so the lookup wrap is the path.
