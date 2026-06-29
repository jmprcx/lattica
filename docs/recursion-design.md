# Recursion — trustless per-user proving + proof aggregation (design & feasibility)

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

See also: `docs/soundness-budget.md` (the batch measurements + the "batching → recursion" conclusion),
`batch_joinsplit_air` / `batch_htlc_air` (the implemented aggregation + the reusable tx-root fold).
