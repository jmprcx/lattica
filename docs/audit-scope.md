# Lattica — Audit Scope & Reviewer Guide

> **⚠ Historical / reference-only — not the v1 audit artifact.** Predates the Plonky3 join-split
> cutover (earlier Winterfell/Rescue stack). Start at [`AUDITORS.md`](AUDITORS.md); current scope is
> `audit-scope-p3.md`.

This is a from-scratch, **unaudited**, PoC-grade cryptosystem written in Zig. Tests cover
completeness and many soundness *rejections*, but cannot substitute for review. This document
tells a reviewer where the soundness-critical surface is, what to verify, and what is a known
limitation (not a bug) so effort goes where it matters.

## What "soundness" means here, and the threat model

The load-bearing claim is **proof soundness**: a prover who does *not* know a valid witness
cannot make `verify` return `true`, except with negligible probability. A bug here is
**catastrophic** (forged proofs ⇒ forged money). Secondary claims: **zero-knowledge** (a proof
leaks nothing about the witness) and **completeness** (honest proofs verify). Everything reduces,
by design, to SHA3 collision/preimage resistance + module-lattice hardness; **no group DL, no
trusted setup**. Fiat-Shamir is used in the random-oracle model.

Severity: **[C]** soundness (accepts false proofs), **[Z]** zero-knowledge (leaks witness),
**[L]** completeness/liveness (rejects honest proofs), **[I]** informational/hardening.

## Live vs. demonstration code

- **Live in the running protocol:** `field.zig`, `rescue.zig`, `stark.zig` (the
  authorization proof, used via `circuit.zig` by `node.zig`), and `primitives.zig`. The
  end-to-end `demo` exercises these; the node still does membership/nullifier/balance natively.
- **Standalone (not yet wired into the node):** `membership.zig`, `permutation.zig`, `spend.zig`
  (the R3 work — the full four-constraint ZK spend proof and its building blocks). Audit them as
  the intended direction, but note they don't yet gate the demo.

---

## Tier 1 — STARK soundness machinery (highest priority) [C]

These are shared (duplicated) across `stark.zig`, `membership.zig`, `permutation.zig`,
`spend.zig`. A flaw is a soundness hole in every proof.

1. **Fiat-Shamir transcript** (`Transcript` in each module). Verify: every challenge is squeezed
   **after** the values it must depend on are absorbed (trace root before the constraint
   challenges; `β,γ` for the grand product strictly after the trace commitment; the FRI-mask `ζ`
   after `g` is committed; FRI fold `β_k` after layer-`k` root; query indices after the final
   layer). Check the squeeze counter prevents challenge reuse, and that domain separation between
   absorb/squeeze is sound. **Failure mode:** a challenge drawn too early lets the prover rig
   commitments to it ⇒ unsound.
2. **FRI low-degree test** (`friFold`, `FriProver.commit`, `friCheckFinalLowDegree`, and the
   fold-consistency loop in each `verify`). Verify: the fold formula
   `next = even + β·odd` with `even=(a+b)/2`, `odd=(a−b)/(2x)`; the query "descent" indices
   (`ai = q0 % half_k`, pair at `ai+half_k`); the `expected = if (ai < half_next) a else b`
   sibling-selection; the final-layer low-degree check (iNTT then assert high coefficients zero);
   and that the **last fold's** value is checked against `fri_final`. **Failure mode:** a function
   far from low-degree passes ⇒ unsound.
3. **ALI binding** (the `compositionAt(...) == fri.layers[0].a/.b` checks in `verify`). Verify the
   verifier *recomputes* the composition from the opened trace/`Z`/`g` values and equates it to
   the FRI layer-0 opening (with `H = CP + ζ·g`). **Failure mode:** if FRI isn't bound to the
   committed trace, constraints aren't enforced ⇒ unsound.
4. **Merkle commitments** (`MerkleTree`, `verifyLeaf`/`verifyRow`). Verify leaf hashing
   (single value vs. WIDTH-row), node hashing, path length = `log2(n)`, index-bit traversal, and
   domain separation between leaf/row/node. **Failure mode:** second-preimage / index confusion ⇒
   openings not bound.

## Tier 1 — Grand-product copy constraint (highest priority) [C]

`permutation.zig` (multiset form) and `spend.zig` (the `rho` wire). This is the subtlest piece.

- The running product `Z[0]=1`, `Z[r+1]=Z[r]·Nu_r/D_r`, the **transition on all N rows** (vanishing
  `xᴺ−1`), and the boundary `Z(1)=1`. Verify the **cyclic wrap** (row `N-1 → 0`) is what forces
  the total product to 1, and that `Z(ωx)` at the last row evaluates `Z(ω⁰)=Z[0]` via the
  interpolated polynomial.
- The id/σ encoding: `id(c,r)=k_c·ωʳ`, `σ` a true permutation of the ids, a 2-cycle forcing two
  cells equal. In `spend.zig` it is single-column (`col1`, cycle `RHO_A ↔ RHO_B`); confirm `σ` is a
  genuine permutation and that fixed points contribute 1.
- **Failure mode:** if the product doesn't actually force the wired cells equal (e.g. wrong `σ`,
  missing wrap, `β`/`γ` drawn before the trace commit), the copy constraint is **vacuous** ⇒ a
  spender could use inconsistent `rho` in commitment vs. nullifier. The test
  "inconsistent rho … rejected" guards this — confirm it genuinely exercises the path.

---

## Tier 2 — Per-circuit AIR correctness [C/L]

For each circuit, verify the constraints both **hold for honest traces** (completeness) and
**force the intended relation** (soundness), and that the **vanishing polynomials cover exactly
the intended rows**.

- **`stark.zig` (authorization):** the transition constraint equals one `rescue.round`
  (`next_i − (Σ_j M[i][j]·cur_j⁷ + rc_i)`), periodic round constants via `RC_i(x^{N/BLOCK})`, the
  boundary asserting the output = public image, and `Z_trans` excluding the last row.
- **`membership.zig`:** `Z_round = (xᴺ−1)/((x−ω^{N-1})·Z_link)` enmeshes round vs. link rows;
  the link carries the compressed output to the next block's left input and resets capacity; the
  anchor boundary. (Leftmost path here; `spend.zig` generalizes.)
- **`spend.zig` (the full spend):** the enumerated row sets `ROUND_EXCLUDED`, `CARRY_ROWS`,
  `CAP_ROWS` — verify they list exactly the right block-boundary rows and that the three
  vanishing polynomials are mutually consistent (round enforced on all non-boundary rows; carry on
  chained boundaries; capacity at block starts). Verify:
  - the **degree-2 "one-of" carry** `(next₀−cur₀)(next₁−cur₀)=0` (general Merkle position) really
    forces the running hash to be one of the next inputs;
  - the **`cm→leaf` adjacency** (commitment block precedes membership block 0);
  - the **balance** `value=send+fee` at row 0 and the **output boundaries** (`anchor` at the
    membership-output row, `nf` at the nullifier-output row) bind the right cells;
  - the **two-region rho wiring** (single-column grand product) and that `cm` stays hidden.
  **Failure mode (key one to hunt):** a constraint that is satisfiable without the intended
  relation (e.g. capacity not actually pinned to 0, an off-by-one in a vanishing set leaving a row
  unconstrained, the one-of carry allowing the running hash to be dropped).

---

## Tier 3 — Field, NTT, hash [C]

- **`field.zig`:** Goldilocks `p = 2⁶⁴−2³²+1`. Verify `add/sub/mul/pow/inv` (mul via `u128 % p`),
  `rootOfUnity` (2-adicity, primitivity), and especially **`ntt`/`intt`** (iterative
  Cooley-Tukey + bit reversal) — a transform bug silently corrupts every commitment. KATs exist in
  `kat.zig`; consider differential testing against a reference.
- **`rescue.zig`:** the SPN (`x⁷` S-box — confirm `gcd(7,p−1)=1` so it's a permutation), the Cauchy
  **MDS** (confirm it is actually MDS / invertible), the SHA3-derived round constants, and the
  one-wayness argument for `ROUNDS=15`, `WIDTH=3`. **Known gap (not a bug):** these are *not*
  standardized/vetted constants (see Caveats).

## Tier 4 — Zero-knowledge [Z]

- Trace/`Z` blinding `T' = T + Z_H·b` (`valuesToBlindedLde`): verify `TRACE_BLIND` ≥ the number of
  per-column openings (4·`NUM_QUERIES`), so opened values are uniform (the Vandermonde argument in
  `soundness.md §5`), and that `Z_H` vanishing on H leaves constraints intact.
- Masked FRI `H = CP + ζ·g` with committed random `g`: verify the FRI/`g` openings reveal nothing.
- **Caveat:** ZK is **honest-verifier** (Fiat-Shamir), heuristic, no formal simulator. The
  standalone `permutation.zig` is intentionally non-ZK.

## Tier 5 — Protocol & primitives (lower risk) [C/I]

- **`primitives.zig`** wraps `std.crypto` (ML-KEM-768, ML-DSA-44, SHA3-256, ChaCha20-Poly1305) —
  low risk, but verify the **domain-separated `hashDomain` framing** (length-prefixing prevents
  concatenation ambiguity), deterministic seeded keygen, and the deterministic note-encryption
  encaps (a deliberate PoC choice — confirm it doesn't undermine confidentiality for the use).
- **`tree.zig`/`tx.zig`/`node.zig`:** SHA3-based, not in-circuit; standard. Verify the tx digest
  ordering, nullifier-set/double-spend logic, and value-balance check.

---

## Cross-cutting [I, but review]

- **Soundness bound:** the **64-bit base field** caps soundness at ≈ `deg/p ≈ 2⁻⁵⁰` regardless of
  query count (`parameters.md §1`). Production must draw challenges from a field **extension**.
  Confirm the analysis; this is the headline parameter gap.
- **PoC parameters:** FRI rate/queries/grinding (`parameters.md §2`) — conjectured ~50-bit.
- **Engine duplication:** `field`/Merkle/transcript/FRI are copied across modules. Check the
  copies have not **diverged** (a fix in one not propagated is a real risk).
- **Memory safety:** allocator discipline (arenas in tests; the per-module `*Free` / `defer`s).
- **No constant-time / side-channel review** has been done.

## Known limitations (NOT bugs — don't spend audit time here)

- Hash MDS/round constants are deterministically generated, **not** a standardized Poseidon2/
  Rescue-Prime instance; state width `m=3` is small. → swap for vetted constants + wider state.
- `spend.zig` commitment is simplified `H(value, rho)` (no `recipient`/`rcm`/owner binding).
- `spend.zig`/`membership.zig`/`permutation.zig` are **not node-integrated**; the protocol's
  cm/nullifier/Merkle still use SHA3, so the in-circuit field hash and the on-chain hash differ.
- Single-input/single-output transfers; no consensus/networking/persistence (by PoC scope).
- No proof recursion/aggregation; proofs are large.

## Suggested review order

1. Tier 1 transcript + FRI + grand product + ALI (the shared engine) — most leverage.
2. `spend.zig` AIR + vanishing sets + wiring (the most complex live-direction circuit).
3. `field.zig` NTT (differential test) and `rescue.zig` MDS/permutation.
4. ZK blinding sufficiency, then parameters/soundness-bound.
5. `primitives.zig` framing and the protocol layer.
