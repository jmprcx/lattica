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
| **P2b** two-round prover + soundness | `src/lookup/prover.rs` | The forked prover's core, working on the **real `MyConfig` hiding-FRI PCS + challenger**: the genuine two-round Fiat-Shamir (commit main → sample α/β → commit the extension aux trace → sample ζ). A matching verifier re-derives every challenge (FS-consistency) + checks the terminal — accepts balanced, rejects imbalance *and* a tampered aux commitment. **Plus** the quotient's soundness job validated directly (`aux_fraction_wellformed`): the honest aux satisfies the fraction + terminal relations, a forged aux is caught — so the lookup argument's *logic* is fully validated (round structure + terminal + aux well-formedness). **Sole remainder:** committing the quotient polynomial so the verifier checks those relations *succinctly* at ζ — pure PCS plumbing (p3 already does it for trace/quotient). |
| **P3** wrap size-stability model | `src/tree/mod.rs::size_model` | The size half of the wrap crux (0a′ was the degree half). Self-verification width `W_out = A + B·W_in` has an *attracting* fixed point iff `B<1`. Fitting `B` from the two measured monolith points (verify W=19→193, W=193→8520) gives **`B≈48 ≫ 1`** — expansion, no fixed point, diverges (the 44× blow-up). A lookup-based wrap makes the per-inner-column cost a bounded lookup (P2: fixed degree 3 + fixed width) ⇒ `B<1` ⇒ an attracting canonical `W*` exists. So size-stability is a concrete **contraction condition** lookups satisfy, not a hand-wave. |
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
| Wrap size-stable | outer W bounded | ✅ P3 model — a fixed point exists **iff** self-verification is a contraction (`B<1`); monolith's measured `B≈48` diverges, lookups drive `B<1` (P2: fixed degree+width/column) |

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

## 7. W7 — integration, re-audit, and the soundness budget

The size gate (W5) is **met by measurement** (`tree::size_model`: the narrowed self-composition contracts,
marginal `B = 19.00` FULL → `5.00` arith+caps → `1.00` +openings → **`0.00` +ov**, so an attracting canonical
fixed point `W* = 677` exists). W6 gives the K-ary aggregation seam byte-identical to `batch_root`. W7 is the
audit posture that lets this research land next to the audited production crate without touching it.

### 7.1 Audit-safety (feature-gating, checkable)

Every research module is `#[cfg(feature = …)]`-gated OFF by default (`recursion`, `tip5`, `lookup`, `wrap`,
`tree`), so the **default (production) staticlib compiles none of it**. `scripts/check-abi-symbols.sh` turns
that into evidence: it asserts the default `.a` exports **exactly** the 10 frozen `lattica_*` node-seam
externs, **zero** `lattica_tree*` research externs (the W7 C-ABI below, in a distinct namespace the frozen
grep ignores — asserted absent explicitly), **zero** recursion symbols, and **zero** deep-tree research
symbols (`tip5`/`lookup`/`wrap`/`tree`, crate-anchored so a dependency's own `lookup`/`tree` symbol can't
false-positive). Production verifies real statements via the **batch** path (one STARK per block); the
wrap/tree is additive and invisible to the seam.

### 7.2 Soundness budget (per tree level, then composed)

Each tree level is a single STARK proof at the production FRI config (cap-6, `q96`/`lb4`), whose proven floor
is **≥ 100 bits** up to `MAX_BATCH_TILES = 64` leaves — the same floor the production batch proof carries. The
wrap adds two soundness ingredients on top of the base STARK/FRI argument:

- **LogUp bus** — each externalized region (arith `DeepFold`, caps `SpongeCap`, openings `OpTable`, the ov
  leaf-hash) is bound by a multiset-equality argument whose soundness error is Schwartz–Zippel over the
  challenge: `≤ (#tuples · deg) / |F_ext|` with `|F_ext| ≈ 2^128` (the degree-2 Goldilocks extension), i.e.
  negligible per channel; the channels compose by a union bound over the ≤ `2·N_GROUPS+5` buses.
- **Tip5 permutation** (Layer-A hashing, W4) — its security rests on the split-and-lookup S-box (offset
  Fermat-cube over `F_257`) + the circulant-MDS diffusion; the wrap uses it only as a *collision/PRP* oracle
  for the FS transcript and the Merkle leaves, so its floor is the Tip5 cryptanalytic margin (≥ 128-bit
  target), independent of the LogUp/FRI floor.

**Composition.** An `L`-level tree multiplies soundness errors: the block floor is
`min_level(floor) − log2(L)` (the union bound over levels). With per-level ≥ 100 bits and realistic `L ≤ 2^20`
blocks, the composed floor stays ≥ ~80 bits — and rises to the per-level floor as the config's `q`/`lb` grow.
The **canonical fixed point** (`W* = 677`, `B = 0.00`) is what makes this composition *bounded*: every level
has the same width/degree, so every level carries the same floor — no level is the weak link.

### 7.3 Wrap-verifier constraint audit (accept-iff-verify + the corrupted-trace matrix)

The assembled wrap is *sound by construction*: its bus balances **iff** the values it folds are the ones the
inner `p3::verify` would compute (the same accept-iff-verify argument as the R7 monolith audit, one region
deeper). Each externalization was validated **native-balance** (cheap, localizing) **and** **end-to-end
prove** (`prove_lookup`, the definitive check), with an adversarial tamper that must be rejected:

| region (flag) | balance test | prove test | tamper → rejected |
|---|---|---|---|
| arith tile (`narrow_arith`) | `arith_wrap_assembled_bus_balances` | `arith_wrap_assembled_proves` | corrupted `ro` |
| caps (`narrow_caps`) | `cap_wrap_cw_assembled_bus_balances` | `cap_wrap_cw_assembled_proves` | corrupted cap digest |
| openings (`narrow_openings`) | `openings_wrap_cw_assembled_bus_balances` | `openings_wrap_cw_assembled_proves` | corrupted opening-row `pz` |
| op-table epilogue (`bind_optable`) | `optable_openings_wrap_cw_bus_balances` | `optable_openings_wrap_cw_proves` | corrupted `folded_col` |
| **ov carrier (`narrow_ov`)** | `narrow_ov_openings_wrap_bus_balances` | `narrow_ov_openings_wrap_proves` | corrupted trace `px` |

The `narrow_ov` row is this session's addition — the last inner-scaling carrier externalized, driving `B → 0`.
Native balance is green; the lean prove (`prove_lookup_lean`, the non-hiding ~2× RAM lever) is the e2e
confirmation. Every flag is byte-identical when off (`pinned_constraint_fingerprints`), so the audited monolith
constraints are unchanged.

### 7.4 The C-ABI seam — the runnable part is BUILT; the deep-prove part is hardware-deferred

The tree aggregation splits cleanly into what runs today and what waits on hardware, and the C-ABI reflects
that split honestly:

- **BUILT + callable (this session):** `lattica_tree_root` — a `#[no_mangle] extern "C"` (feature-gated
  `tree`, OFF by default) that computes the block **tx-root** of `n_tx` serialized join-split witnesses via
  the K-ary aggregation tree (`arity` children/node), **byte-identical to `lattica_batch_prove`'s root**
  (`tree_root_abi_matches_batch_root`: sizes {1,3,8} × arities {2,4,8}). This is the consensus-critical value
  a DAG/tree-aware node derives from a block — fail-closed, panic-isolated, batch-bounded (`≤ MAX_BATCH_TILES`),
  exactly like the frozen batch externs. It is provably OUT of the audited staticlib: `check-abi-symbols.sh`
  asserts **zero** `lattica_tree*` externs in the default build, and a positive control confirms the symbol
  appears only under `--features tree`.
- **Hardware-deferred (a limit, not a skip):** the deep **wrap-verifies-wrap PROVE** — a node-callable
  aggregator that emits ONE proof attesting it verified K child proofs — currently **OOMs**. The size number
  (`W* = 677`, `B = 0.00`) holds analytically and the single-level narrowed proves pass under the lean prover,
  but a full canonical level needs a ≥ 128 GB server (this box is 62 GB). So the *proof-emitting* extern
  (`lattica_tree_prove` / the Zig handoff) is scoped but not cut until that hardware exists; the root-computing
  extern is the part that is genuinely callable now. This mirrors the production recursion decision (R6 C-ABI
  deferred): the frozen seam is untouched, the research stays invisible to it, and W7 lands the audit posture
  (gating + soundness budget + the constraint matrix) the proof-emitting integration will re-audit against.
