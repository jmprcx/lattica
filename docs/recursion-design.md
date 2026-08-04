# Recursion — trustless per-user proving + proof aggregation (design & feasibility)

> **Research design:** Motivation and architecture for recursive aggregation; not a production commitment.

**Status: design doc for deferred future work.** This is *not* implemented. The batch-aggregation
circuit (`batch_joinsplit_air` / `batch_htlc_air`, "one proof per block") is the implemented, validated
interim that already handles realistic block sizes; recursion is the scale-out beyond it. This document
records what recursion buys, why it is a large project (not a session task), the concrete design, the
feasibility on the current stack, and — importantly — why the work already done is **forward-compatible**
with it.

## 1. What recursion buys (over the batch)
The batch proves N transactions as one proof by tiling them in one trace, proven **monolithically by one
party that holds all N witnesses**. That has three real limits:
- **Witness custody / trust.** One prover (a sequencer/aggregator) needs every tx's private witness — it
  can't be trustless per-user. (`docs/multi-asset-exchanges-issuance-cto.md` and the batch commits flag
  this.)
- **Prove time ~linear in N**, single-threaded over the whole block (n=32 ≈ 70 s measured).
- **`MAX_BATCH_TILES = 64`** at the ≥100-bit proven floor — bigger blocks need multiple batch proofs.

**Recursion** removes all three: **each user proves their own spend** (the existing single-tx
join-split/HTLC proof, on their own hardware, revealing no witness), and a **recursive aggregation
circuit verifies K inner proofs and emits one outer proof**. Aggregation parallelizes (a tree of
aggregators), so block proving is `O(log N)` depth instead of `O(N)` serial, with no party holding all
witnesses and no per-proof soundness decay with N.

## 2. The model
- **Inner proof (per user):** exactly today's `lattica_joinsplit_prove` / `lattica_htlc_prove` single-tx
  proof. Unchanged.
- **Aggregation circuit (the new, hard part):** an AIR that, given K inner proofs + their public
  statements, (a) **verifies each inner proof in-circuit**, and (b) folds the K per-tx statement digests
  into one **block tx-root** — *the same `s_k = MD-chain(DOM_TXROOT ‖ statement)` and running root the
  batch already uses* (see `batch_joinsplit_air`). Output: one outer proof + the block tx-root.
- **Tree aggregation (large blocks):** aggregators compose — an outer proof can itself be an inner proof
  to the next level — giving a log-depth tree. The root proof attests the whole block.
- **Node side: unchanged.** The node still computes `batchRoot(txs)` from the block's statements and
  checks **one** proof (`verifyBatch`-shaped) against it. The proof system underneath changes; the
  consensus interface (the tx-root, the seam) does not. **This is why the batch work is not throwaway.**

## 3. The hard part — a recursive STARK verifier AIR
Recursion's cost is almost entirely the **in-circuit verifier**: an AIR that runs the FRI-STARK
verification algorithm on the inner proof. It must, in-circuit:
- Replay the **Fiat–Shamir transcript** (absorb commitments + public values, squeeze challenges) — our
  Poseidon2 sponge.
- Verify the **FRI query phase**: for each query, check Merkle openings of the committed polynomials and
  the folding relation across rounds, over the F_p² challenge field.
- Check the **constraint / quotient (DEEP) relation** at the out-of-domain point.

These are deep, but lattica already has **directly reusable in-circuit primitives** — a genuine head
start, not from scratch:
| Recursive-verifier need | Existing lattica gadget |
|---|---|
| In-circuit Fiat–Shamir transcript (absorb/squeeze) | `poseidon2_air` (the Poseidon2 permutation AIR) — the same hash the challenger uses |
| FRI query Merkle-path opening checks | the depth-`DEPTH` general-position membership fold in `joinsplit_air` (Merkle `merge` up a path) |
| Binding the aggregated statements | the `DOM_TXROOT` per-tx digest + running-root fold (`batch_*_air`) — reused verbatim |
| F_p² field model | the challenge field is already `BinomialExtensionField<Goldilocks, 2>` |
What remains genuinely new: the FRI **folding** arithmetic in-circuit, the **DFT/coset** evaluation
checks, and wiring the full transcript — i.e. the bulk of a STARK verifier, expressed as constraints.

## 4. Feasibility on the current stack
- **Plonky3 0.6.1 (pinned) has no recursion support**: no `p3-recursion` crate, no in-circuit verifier;
  `p3-uni-stark::verify` is a *native* Rust function. Confirmed against the lockfile + the registry
  sources. So recursion is not a matter of calling an API — the recursive verifier AIR must be built.
- **Two paths:**
  1. **Build the recursive verifier AIR on p3 primitives** (recommended). Preserves every v1/v3 invariant
     — transparent (no trusted setup), post-quantum (hash + lattice only, no curves/pairings), stable
     Rust — and reuses the gadgets in §3. Largest effort, but the only path that keeps the PQ/transparency
     guarantees that are lattica's whole point.
  2. **Adopt a recursion-capable framework** (e.g. a Plonky2/3 recursion stack, Halo2). Faster to a
     working recursive verifier, but most mature recursion stacks rely on curve-based commitments
     (**not** post-quantum) or a trusted setup — a direct conflict with the threat model. Would need a
     PQ-preserving recursion stack.
- **Effort:** a recursive STARK verifier is the single hardest component of any recursive proof system —
  a multi-month build + its own dedicated audit, comparable in scope to the original circuit. It is
  **not** a session-scale increment, which is why it is staged as future work rather than rushed (a wrong
  in-circuit verifier is a silent soundness hole).

## 5. Why this is staged, not done now
The batch ("one proof per block", implemented + real-prover-validated + now with the node batch-apply
path) already delivers the on-chain win — one verification per block, ~log-n proof size — for realistic
block sizes (≤64 txs/proof, multiple proofs/block for larger). Recursion is required only when you need
**trustless per-user proving** or **unbounded block size with parallel proving**. Building it correctly
is a project in its own right; doing it carelessly at the tail of the batch work would risk a soundness
bug in an audited consensus circuit. The interface is already in place (the tx-root + the verify seam),
so recursion can be slotted underneath without touching the node when it is built.

## 6. Concrete next steps (when this is picked up)
1. Spike: a minimal in-circuit FRI **query-path verifier** over F_p² reusing the membership gadget +
   `poseidon2_air` — the riskiest sub-component — and benchmark its trace size.
2. Decide path (1) vs (2) in §4 from the spike + a PQ-recursion-stack survey.
3. Design the aggregation circuit's public interface to **emit the existing block tx-root** (so the node
   is unchanged) and a fixed-size outer proof.
4. Treat it as a new audited circuit (its own constraint-audit doc + corrupted-trace suite), like
   `joinsplit_air`/`htlc_air`.

## 7. B1 spike result — **GO (on the p3 path)**
Built and validated `lattica-prover-p3/src/recursion/fri_merkle.rs` — an in-circuit FRI-query
Merkle-opening verifier (the dominant, most-repeated FRI operation). Findings:
- **Correctness / reuse proven.** `merge` is bit-identical to the FRI MMCS compression
  (`TruncatedPermutation<Perm,2,4,8>`); the AIR recomputes a Merkle root by bit-controlled `merge` up a
  path (each level = one `poseidon2_air` permutation block) and the in-circuit root **matches the native
  `merge`-tree opening** (differential test). Tampered sibling / wrong root are rejected
  (corrupted-trace). So the size-dominant FRI operation verifies in-circuit using gadgets lattica already
  proves at depth 32 (the membership fold).
- **Measured cost.** A depth-16 opening (a realistic FRI input-opening depth) = **512 rows (2⁹)**,
  32 rows per `merge`, proving in ~0.5 s (dominated by FRI fixed overhead at this tiny size).
- **Extrapolation (see `recursion-verifier-audit.md` §5).** A full single-inner-proof verifier ≈ 96
  queries × ~3 openings × ~16-level paths ≈ **~2^18 rows — batch-circuit scale**, which the existing
  prover already handles in tens of seconds. Size is therefore **not** the blocker.
- **Decision: proceed on the p3 path (§4 option 1).** No framework migration needed for feasibility.
  The residual risk is **correctness** of the in-circuit FRI *folding* (F_p² Lagrange) + the
  OOD/quotient/DEEP check — that is what B3 retires, not scale.

## 8. B2 result — in-circuit transcript validated
Built `lattica-prover-p3/src/recursion/transcript.rs` — the Fiat–Shamir transcript (`DuplexChallenger`
duplex sponge, Poseidon2 w8/rate4) as chained `poseidon2_air` blocks with the capacity carried + the
prefix-free count (`state[CAP_LANE] += RATE`) linked across blocks. Findings:
- **Model fidelity pinned (fast, no proving):** a native sponge over `native_permute` reproduces the real
  `DuplexChallenger`'s squeeze for the observe-(RATE·m)-then-sample case; `sample` pops from the back, so
  the F_p² challenge = `(rate[3], rate[2])`. Asserted for m∈{1,2,3}.
- **In-circuit validated:** the AIR's bound squeeze matches the native sponge (real prover); a tampered
  absorb / wrong squeeze is rejected.
- Scope: absorb-multiple-of-RATE-then-sample (the core mechanic); variable-length buffering +
  `sample_bits` (index sampling) are follow-ons folded into B3.

## 9. B3a/B3b result — in-circuit F_p² fold validated
Built `lattica-prover-p3/src/recursion/fri_fold.rs` — in-circuit F_p² arithmetic + the arity-2 FRI
commit-phase fold step (the residual-risk primitive from B1). Findings:
- **Field model confirmed:** `Challenge = BinomialExtensionField<Goldilocks,2>`, `X² = W = 7`; the
  in-circuit `mul = (a0·b0 + 7·a1·b1, a0·b1 + a1·b0)` (KAT: `X² == 7`).
- **Fold formula pinned to p3:** `folded = (e0+e1)/2 + (e0−e1)·β/(2s)` (from `p3_fri`'s
  `fold_matrix`/`lagrange_interpolate_at`); the in-circuit AIR supplies `inv2s = 1/(2s)` as witness +
  constrains `inv2s·2s = 1`, then checks the relation. The plain-Rust mirror equals `native_fold`, and
  the real prover accepts the correct fold + rejects a wrong claimed result.
- So the in-circuit FRI folding over F_p² is correct + cheap (arithmetic, not hashing).

## 10. Status — the three core primitives are built; integration remains
**Built + validated as standalone in-circuit spikes (all green, real-prover differential vs native):**
1. **Merkle openings** (`fri_merkle.rs`, B1) — the FRI query-path hashing.
2. **Fiat–Shamir transcript** (`transcript.rs`, B2) — the `DuplexChallenger` duplex sponge.
3. **F_p² arithmetic + the FRI fold** (`fri_fold.rs`, B3a/B3b) — the commit-phase folding.

These are the three operations a FRI-STARK verifier is made of; each is now proven to be in-circuit-ready
on the existing Plonky3 prover, reusing `poseidon2_air` + lattica's `merge`/membership gadgets.

**B3-wire native skeleton — DONE (`native_verify.rs`):** a from-scratch re-implementation of the
`p3-uni-stark::verify` orchestration — transcript replay (observe → sample α → observe → sample ζ), the
opening-rounds construction, quotient recomposition, and the constraint/OOD check — **validated to agree
with `p3::verify`** (accepts a valid proof, rejects a tampered public value) on a minimal `ConstAir`, now
under the **production hiding (ZK) FRI config** (the `is_zk=1` path: random commitment observed,
`init_trace_domain = degree >> is_zk`, quotient-chunk count `1 << (log + is_zk)`). The FRI low-degree test
is delegated to `pcs.verify` (its internals = the validated `fri_merkle`/`transcript`/`fri_fold`
primitives). This is the porting blueprint: each step maps to an in-circuit gadget. Remaining for B3-wire:
the actual in-circuit AIR port (replace `pcs.verify` with the primitives + the constraint folder as
constraints) + re-implementing the FRI query-loop orchestration in-circuit.

**In-circuit verifier — construction STARTED (`verifier_air.rs`), 2 of N components validated:**
- **Component 1 — in-circuit Fiat–Shamir transcript (`TranscriptAir`):** replays verify's two-phase
  transcript (absorb instance → squeeze **α** → absorb quotient+random commitments → squeeze **ζ**) as a
  Poseidon2 sponge AIR, binding α, ζ as public outputs. Validated: the in-circuit (α, ζ) equal the native
  `ModelChallenger`'s (which agrees with the real `DuplexChallenger`); wrong α / tampered absorb rejected.
- **Component 2 — in-circuit OOD/constraint check (`ConstraintCheckAir`):** evaluates the inner AIR's
  constraints at ζ in-circuit, combined with α (Horner), and checks `folded·inv_vanishing == quotient`.
  Validated to **agree with native `verify_constraints`** (correct quotient accepts, wrong rejects) for
  `ConstAir`. (The domain selectors at ζ are fed as witness here; computing them in-circuit is a separate
  sub-component, below.)

**Remaining — the large-scale integration (the genuine multi-month bulk):**
- **Component 3 — in-circuit FRI query loop (the middle, the biggest piece):**
  - **3a — FRI commit-phase challenge derivation: DONE + validated (`FriTranscriptAir`).** Extends the
    transcript past ζ to observe each FRI round commitment and squeeze every β_r (with α, ζ); the
    in-circuit challenges match the native `ModelChallenger` for R=4 rounds; tampered absorb rejected.
  - **3b-i — in-circuit MMCS leaf hash: DONE + validated (`LeafHashAir`).** Hashes a committed matrix row
    to a 4-felt leaf digest via the `PaddingFreeSponge` (rate-overwrite + capacity-carry, no prefix-free
    count) in-circuit; validated vs native `MyHash`. The leaf level beneath the `fri_merkle` path-merge.
  - **3b-ii — in-circuit reduced opening (DEEP): DONE + validated (`ReducedOpeningAir`).** Computes
    `(X−ζ)⁻¹·Σ_i α^i·(p_i−y_i)` (Horner over α, in-circuit inverse) for a single matrix/point; validated vs
    a native computation. (The multi-matrix α-offset + multi-point {ζ, ζ·g} accumulation is the wiring.)
  - **3b-iii — in-circuit `sample_bits` (query index): DONE + validated (`SampleBitsAir`).** Decomposes the
    squeezed challenge into 64 boolean bits, reconstructs `x = Σ b_i·2^i`, enforces CANONICAL (`< p`) via
    `q₃₁·lo == 0` (q₃₁ = Π high 32 bits, lo = low 32 bits), and outputs the low `bits` as the index.
    Validated vs the native challenger's `sample_bits` (canonical-boundary case included).
  - **3b — the query loop proper: WIRING COMPLETE + VALIDATED (native) (`native_fri.rs`).** All building
    blocks are built + individually validated — challenge derivation [3a], `sample_bits` [3b-iii], leaf
    hash [3b-i] → path merge [`fri_merkle`] → reduced opening [3b-ii] → fold/fold-chain [`fri_fold`]. The
    wiring re-implements `p3-fri::verify_fri` natively (the blueprint to port to the AIR): `open_input`
    (reduced openings — GENERATOR shift + bit-reversal + α-by-height accumulation + the input MMCS verify),
    `verify_query` (commit-phase fold loop — reconstruct the arity group, MMCS-verify, fold at β_r, roll in
    openings), the `verify_fri` driver (transcript → per-query open_input + verify_query + `final_poly`
    check), and a `verify_proof` STARK wrapper. **`verify_proof` runs the FULL FRI-STARK verify with NO
    `pcs.verify` delegation and agrees with `p3::verify`** (`native_fri_verify_agrees_with_p3`: accepts a
    real proof; rejects a tampered public value, a tampered commit-phase sibling, and a tampered
    `final_poly`). **Remaining: the AIR PORT** — turn this validated native algorithm into constraints
    using the in-circuit gadgets each step maps to (the heavy in-circuit engineering), then B4/B5.
- **Component 4 — in-circuit domain selectors at ζ: DONE + validated (`DomainSelectorsAir`).** Computes
  `z_h = ζ^(2^log_size)−1` (a squaring chain), `is_first = z_h/(ζ−1)`, `is_last = z_h/(ζ−g⁻¹)`,
  `is_transition = ζ−g⁻¹`, `inv_vanishing = z_h⁻¹` in-circuit (F_p², in-circuit inverses), validated to
  match the real `domain.selectors_at_point(ζ)`. Feeds component 2 (which currently takes selectors as
  witness) once wired.
- **Wiring:** compose components 1–4 into one AIR that verifies a real inner proof end-to-end (agrees with
  `p3::verify`); add the ZK/hiding in-circuit branches.
- **B4 — aggregation:** verify K inner proofs (the verifier AIR ×K, tiled) + fold their per-tx statement
  digests into the existing block tx-root (reuse the `DOM_TXROOT` fold), emitting the SAME tx-root so the
  node seam is unchanged. **B5 — tree aggregation + seam:** compose outer-as-inner + C ABI + Zig seam.

  (Original B3-wire description, retained:) one AIR that parses a real `p3` `Proof`, replays the EXACT `p3-uni-stark::verify`
  transcript order (observe degree bits → trace commit → public values → sample α → observe quotient
  commit → sample ζ → FRI commit-phase observes/`β_i` → query-index `sample_bits`), then runs all 96
  queries (input opening + per-round fold + Merkle openings + "roll in reduced openings") and the final
  `final_poly` check. Requires extending B2 with `sample_bits` (index sampling) and the variable-length
  absorb, and parsing p3's proof structures into trace columns. This is the bulk of the effort + its own
  audit.
- **B3-quotient (OOD/DEEP):** evaluate the INNER AIR's constraint polynomial at ζ in-circuit, combine
  with α, recompose the quotient from its chunks, and check `constraints(ζ) == Z_H(ζ)·quotient(ζ)`.
  Circuit-specific (depends on the inner AIR); substantial.
- **B4 — aggregation:** verify K inner proofs (B3-wire ×K, tiled) + fold their per-tx statement digests
  into the existing block tx-root (reuse the `DOM_TXROOT` fold), emitting the SAME tx-root so the node
  seam is unchanged.
- **B5 — tree aggregation + seam:** compose outer-as-inner (log-depth) + C ABI + Zig seam + real
  integration.

The honest read: the unknowns that could have killed the p3 path (in-circuit hashing scale, transcript
fidelity, F_p² folding correctness) are now **retired** — each primitive verifies in-circuit and matches
native. What remains is faithful, high-volume *wiring* against p3's exact proof format + the
circuit-specific quotient check — large and audit-bearing, but no longer a feasibility question.

**Update (2026-07-03): the in-circuit verifier now accept-iff-`p3::verify`s a REAL production
`JoinSplitAir` proof, both non-hiding and hiding (`is_zk=1`)** — the §3/§10 "remaining" in-circuit
verifier is built (`recursion/monolith`, `phase8_joinsplit_monolith` / `phase8_joinsplit_hiding_monolith`,
commits `165a577`/`7d6a5ad`). What remains is productionization (aggregator over K real inners → tx-root,
self-recursive tree, C-ABI/Zig seam, audit artifacts) + the **aggregation-level parameters**, now designed
+ measured in `docs/recursion-aggregation-params.md` (every level q96/lb4 for proven-100; a full 96-query
inner ≈ 2^20 rows / ~116 GB ⇒ a ≥128 GB production-server capability; the node seam is unchanged).

See also: `docs/recursion-aggregation-params.md` (R3 — the tree's soundness parameters + the measured
cost curve), `docs/recursion-verifier-audit.md` (the in-circuit verifier spec + constraint budget),
`docs/soundness-budget.md` (the batch measurements + the "batching → recursion" conclusion),
`batch_joinsplit_air` / `batch_htlc_air` (the implemented aggregation + the reusable tx-root fold).
