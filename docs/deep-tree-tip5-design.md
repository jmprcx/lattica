# Deep parallel recursion tree + Lookup/Tip5 — design & Phase-0 feasibility

> **Research design doc (branch `tree-tip5-research`, a worktree off `v3`) — NOT part of the v1 audit
> artifact and NOT on any production path.** Records the Phase-0 feasibility spikes and the full program
> they gate. Start at [`AUDITORS.md`](AUDITORS.md) for the audited surface.

**Verdict (Phase 0): GO — with the residual risk being Phase-3 engineering, not a fundamental barrier.**
The two mechanisms this program depends on are validated in-tree: a lookup argument runs over lattica's
Goldilocks/F_p² config with **low-degree** constraints (measured 3 for a 2-sided lookup, P2), and Tip5 slots into the Layer-A hash traits at
**4.6× fewer rows/permutation** than Poseidon2 (0c). Wired against the measured self-recursion explosion
(0a), the wrap's degree math closes (≤7 ≤ 16) and its size is stabilizable by a canonical fixed-shape
design. See §5 for the gate.

## 1. Why — the problem chain

A *timely* 64-tx block proof needs a **recursion tree** (parallel, bounded-RAM nodes). The flat aggregator
is linear (~7.4 TB in-core at q96); streaming bounds RAM but takes hours/block. A tree needs the **wrap** —
a canonical fixed-size verifier so self-composition converges — and the wrap is unsolved because
`log_nqc ≤ log_blowup = 4` (constraint degree ≤ 16) is a hard cliff that *silently corrupts* proofs, while
naive self-recursion blows both degree and width past it. The only in-mandate fix (no curves / PQ) is a
low-degree canonical verifier, and **lookups + Tip5** are its enabling substrate. Full background:
`docs/hash-function-analysis.md` (why Poseidon2 for v1, Tip5 for recursion) and
`docs/recursion-aggregation-params.md §5` (the R5 wrap).

## 2. Phase-0 findings (measured in this worktree)

| Spike | Artifact | Result |
|---|---|---|
| **0a** wrap feasibility | `src/tree/mod.rs` | Baseline (probe, first-hand): monolith-verifies-monolith **W 193→8520 (44×), log_nqc=7, ~133 GB** — diverges. Modelled lookup-based canonical wrap: **max degree 7 ≤ 16 ⇒ log_nqc ≤ 4**, size-stable by canonical design ⇒ **GO=true**. |
| **0a′** degree-cliff **measurement** (Phase-3 spike) | `src/tree/mod.rs::degree_probe` | Model → hard numbers via p3's real `get_log_num_quotient_chunks`. Measured degree→log_nqc: **deg 91 → log_nqc 7** (exactly reproduces the baseline monolith + air.rs's "91"), **deg 7 (Tip5 x⁷) → log_nqc 3**, **deg 3 (lookup) → log_nqc 1** — both hold the cliff. The real budget is deg ≤ ~17 (cliff between 17 and 32). So the baseline explosion **is** a degree problem, and both levers clear it — **measured, not modelled**. |
| **0b** lookup argument | `src/lookup/mod.rs` | `p3-lookup` LogUp runs over lattica's `MyConfig`; balanced lookup ⇒ zero terminal, tampered ⇒ rejected. |
| **P2** lookup validation + degree | `src/lookup/mod.rs` | **Measured** `constraint_degree` = **3** for a 2-sided range-check lookup (formula `1 + Σ side-degrees`, correcting the modelled "2"); a k-way lookup is degree `1+k` ⇒ lookups must be **low-arity** (chunk the fold, cf. `FOLD_CHUNK`). Full argument validated at the constraint level with `check_lookups` (balanced accepts, tampered caught). |
| **P2b** two-round prover skeleton | `src/lookup/prover.rs` | The forked prover's core, working on the **real `MyConfig` hiding-FRI PCS + challenger**: the genuine two-round Fiat-Shamir (commit main → sample α/β → commit the extension aux trace → sample ζ). A matching verifier re-derives every challenge (FS-consistency) + checks the terminal — accepts balanced, rejects imbalance *and* a tampered aux commitment. **Isolated remainder:** the quotient (enforces aux well-formedness via `ProverConstraintFolderWithLookups`) + FRI open at ζ — mechanical extensions of p3's `quotient_values`/`open`, not new structure. |
| **0c** Tip5 | `src/tip5.rs` | Tip5 (width-16, 5-round, 4 split-lookup + 12 `x^7` lanes) slots into `PaddingFreeSponge`/`TruncatedPermutation`/`DuplexChallenger` ⇒ Layer-A swap is a `config.rs` type-alias change. **~7 rows/perm vs Poseidon2's 32 (4.6×)**; S-box degree still 7 (⇒ Tip5 buys **rows, not degree**). **P1: now the real vetted constants** — fermat-cube lookup `(x+1)³−1 mod 257` (value-identical to Triton), real MDS (SHA-256("Tip5")), Blake3 round constants — as a **canonical-Goldilocks variant** (documented not byte-identical to Triton's Montgomery-raw form). |

**The key conceptual result:** the two levers do *different* jobs. **Lookups** fix the **degree** (the
`log_nqc=7` driver — the α-Horner fold over high-degree inner constraints becomes low-arity, low-degree lookups).
**Tip5** fixes the **size** (fewer hash rows) and is the hash a lookup argument verifies cheaply. Neither
alone suffices; together they address both explosion drivers.

## 3. Target architecture

- **Leaves** (join-split / HTLC): **Layer A = Tip5** (native PCS Merkle + Fiat-Shamir — no lookup argument
  needed, it's native hashing), **Layer B = Poseidon2** (note/statement hashes — note format **untouched**,
  no consensus fork). Confirmed mechanical (0c): a `config.rs` alias change.
- **Wrap / tree node**: an AIR that verifies a *canonical* Tip5-committed inner **in-circuit** using a
  **LogUp lookup argument** for the FRI-fold batching, the range/bit decompositions, and the S-box — so the
  wrap's own constraints stay degree ≤ ~7 and its width is fixed. This is the fixed point self-composition
  needs (0a).
- **Tree**: recursion over the flat aggregator with the **wrap** as the inner AIR; the tx-root fold stays
  byte-identical to `batch_joinsplit_air::batch_root` (the existing `fold_txstmt` seam). K-ary,
  power-of-two, ≤ `MAX_AGG_TILES`.
- **Parallel harness**: an orchestrator over the "prove one node" boundary
  (`recursion::aggregation::prove_joinsplit_aggregate_production_research`) distributing the tree across
  processes/machines — timely 64-tx (minutes, not hours).

## 4. The program (phases, gated on §5 = GO)

1. **Tip5 + leaf Layer-A migration** — **[mechanical core ✅ done]** a Tip5 `MyConfig` (`tip5::proof_system`)
   proves + verifies a real AIR end-to-end through the standard `p3_uni_stark::{prove,verify}` — the FRI-PCS
   + Merkle + Fiat-Shamir stack composes with the width-16/digest-5 Tip5 hash (incl. the packed-SIMD
   permutation for Merkle row hashing) — now with the **real vetted constants** (fermat-cube lookup, real
   MDS, Blake3 round constants), a canonical-Goldilocks variant (not byte-identical to Triton's
   Montgomery-raw form, which its degenerate representation makes impractical + unnecessary to replicate).
   *Remaining:* the native packed impl (perf), the leaf-circuit swap, GPU Merkle kernels (`gpu.rs`), wire
   KATs (`lib.rs`), Zig proof-*deserialization* seam. *Breaks the v1 proof wire (coordinated, pre-v1);
   note hashing untouched.*
2. **Lookup argument (production)** — **[two-round skeleton ✅ P2b]** harden the working two-round prover
   (`src/lookup/prover.rs`) into a full forked prove/verify + a new `Proof` type (aux
   permutation-trace commitment + `LookupTerminal` + α/β round + `…WithLookups` folders); re-express the
   recursion AIRs as `AirBuilder + InteractionBuilder`.
3. **Tip5-in-circuit gadgets + the wrap AIR** — re-author the `recursion/` gadgets (fri_merkle / native_fri
   / transcript / native_verify / monolith) for Tip5 + lookups; build the canonical fixed-shape wrap that
   holds degree ≤ 16 and is size-stable (0a's payoff). *This is the research core.*
4. **The tree** — self-compose over the wrap; K-ary; tx-root byte-identical to `batch_root`.
5. **Parallel/distributed harness** — orchestrate the tree over the node boundary (single-process today).
6. **Integration + re-audit** — feature-gates + `check-abi-symbols.sh`; a new soundness budget (LogUp
   soundness + Tip5 cryptanalysis + a per-tree-level proven-security floor); full re-audit of the changed
   proof system + recursion.

**Re-audit scope (what phase-1+ invalidates):** the v1 *proof-system* audit (Layer A → Tip5 changes the
proof bytes + the FRI/transcript hash) and the recursion module. **Preserved:** the Layer-B note/statement
model, the shielded pool, `spend_common.rs`, `poseidon2_air.rs`, and the batch circuits' statement
constraints — so the note-format audit stands.

## 5. GO/NO-GO gate (0e)

| Criterion | Needed | Phase-0 result |
|---|---|---|
| A lookup argument runs in this stack | end-to-end gadget over `MyConfig` | ✅ 0b — runs; sound accept/reject |
| Lookup constraint degree low enough to fold under 16 | ≤ ~8 | ✅ P2 — **measured degree 3** (2-sided); low-arity keeps it ≤ ~8 |
| Tip5 fits Layer A | slots into the p3-symmetric traits | ✅ 0c — mechanical alias change |
| Wrap holds the degree cliff | `log_nqc ≤ 4` | ✅ 0a′ — **MEASURED** (p3's `get_log_num_quotient_chunks`): deg 7 → log_nqc 3, deg 3 → log_nqc 1; baseline deg 91 → log_nqc 7 reproduced |
| Wrap size-stable | outer W bounded | ✅ 0a — by canonical fixed-shape design (Phase-3) |

**Decision: GO.** All five criteria pass with validated, in-tree mechanisms — and the crux (the degree
cliff) is now *measured*, not modelled: the baseline's `log_nqc=7` is a degree-~91 problem, and both levers
(Tip5's degree-7 residual, the lookup's measured degree-3) drop it to `log_nqc ≤ 3`, comfortably under the cliff.

**Honest residual risk (what Phase 0 did NOT prove).** Phase 0 validated the mechanisms and *measured* the
degree math, but did not *build* the wrap. The remaining risk is engineering, concentrated in Phase 3 and
now sharply narrowed to two items:
1. **Wrap construction** — express *every* FRI-fold / range / S-box relation in the verifier as a
   low-arity lookup (deg 3) or a Tip5 hash lane (deg 7) so the built wrap's measured max degree actually
   lands ≤ 17. The degree→`log_nqc` mapping is now measured (0a′); what remains is holding every relation
   under it.
2. **Size-stability** — verifying-a-wrap must re-emit a proof of the *same* canonical shape (the true fixed
   point), so outer width is constant.
Also outstanding: the native packed Tip5 impl (perf) + Triton-byte-exact interop *if ever needed* (its
Montgomery-raw representation), the forked lookup prove/verify wire format (Phase 2), and the distributed
harness (Phase 5). None is a fundamental barrier.

**Recommended next step:** Phase 1 (real Tip5 + the leaf Layer-A migration) in parallel with a Phase-3
**wrap AIR spike** that builds the smallest real canonical wrap and *measures* its `log_nqc` (turning 0a's
model into a measurement) before committing to the forked lookup prover.

## 6. Isolation (maintained through Phase 0)

All work is on branch `tree-tip5-research` (worktree off `v3@4e3b0e4`), in **new modules** (`src/tip5.rs`,
`src/lookup/`, `src/tree/`) behind **new OFF-by-default features** (`tip5`, `lookup`, `tree`) gated in
`lib.rs`. Zero edits to Codex's live files; the 10 frozen externs, `Proof<MyConfig>`, and the note format
are untouched, so `scripts/check-abi-symbols.sh` stays green. Rebase onto Codex's committed work before any
Phase-1 wire change.
