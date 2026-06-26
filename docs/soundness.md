# Lattica — Soundness Argument and Gap Analysis

**Status:** written argument for the *implemented* construction + design for the remaining work
**Scope:** the zero-knowledge FRI-STARK in `src/stark.zig` and its use in `src/circuit.zig`

This document gives a written soundness, completeness, and zero-knowledge argument for the proof
system as implemented, states its assumptions, and is explicit about what is **not** yet proven
or built (the R1/R3 gaps). It is an engineering argument, **not** a formal proof, and the system
has **not** been externally audited. See [`parameters.md`](./parameters.md) for the numeric
parameters referenced here.

---

## 1. The statement proved

`prove(secret)` produces, and `verify(image, π)` checks, a non-interactive argument of knowledge
for the relation:

> **R(image; secret):** the prover knows `s = secretToField(secret)` such that
> `rescue.hash(s) = image`, where `rescue.hash` is the arithmetization-friendly Poseidon-style
> SPN in `src/rescue.zig` (S-box `x^7`, MDS diffusion, `ROUNDS` full rounds).

Equivalently: the prover knows an execution trace of `WIDTH` columns × `N = ROUNDS+1` rows where
row 0 is `[s, 0, 0]`, each row is one SPN round of the previous, and the output row's first cell
equals `image`.

> **R1 closed.** The relation is now a real one-way hash (the SPN's S-box `x^7` is a permutation
> with no algebraic inverse shortcut, and full rounds with MDS diffusion put Gröbner-basis
> preimage attacks out of reach), so the proof is a meaningful spend authorization, not just an
> argument of knowledge of a trace. The remaining hash caveat is that the specific MDS/constants
> are deterministically generated rather than a standardized vetted instance (see §6).

---

## 2. Building blocks and assumptions

1. **SHA3-256 collision resistance** — for the binding of all Merkle commitments and the
   Fiat-Shamir transcript. Modelled as a random oracle for non-interactivity (Fiat-Shamir).
2. **Reed–Solomon proximity via FRI** — a function `Q`-query-close to the RS code of rate `ρ` is,
   except with the FRI soundness error, within list-decoding distance of a codeword (we rely on
   the list-decoding conjecture used by all production STARKs).
3. **Schwartz–Zippel over the field** — a nonzero polynomial of degree `d` vanishes at a random
   point with probability `≤ d/|F|`; this bounds the "bad challenge" terms (see `parameters.md §1`).

No assumption rests on a group discrete log, factoring, pairings, or a trusted setup.

---

## 3. Completeness

For an honest prover the trace satisfies the transition on `H \ {ω^{N-1}}` and the boundary
`T(ω^{N-1}) = image`, so:

- both constraint quotients `q_trans = (T³+C−T_next)/Z_trans` and `q_bound = (T−image)/(x−ω^{N-1})`
  are genuine low-degree polynomials (the numerators vanish where the denominators do);
- the composition `CP = α·q_trans + γ·q_bound` and the FRI input `H = CP + ζ·g` therefore have
  degree `< COMP_DEGREE_BOUND`, so FRI's final layer is low-degree and every fold-consistency and
  Merkle check holds. Verification accepts. The trace-blinding term `Z_H·b` vanishes on `H`, so it
  does not disturb completeness. *(Verified empirically: `prove → verify` over random secrets.)*

---

## 4. Soundness

Suppose `verify` accepts. We argue the prover knew a valid trace, except with small probability.

1. **Commitment binding.** `trace_root`, `g_root`, and the FRI-layer roots are SHA3 Merkle roots;
   by collision resistance the opened `(value, path)` pairs are bound to the committed vectors.
   The verifier checks every opening against the root (`merkleVerify`).
2. **FRI ⇒ `H` is low-degree.** The fold-consistency checks plus the final low-degree check mean,
   by FRI soundness, that the committed layer-0 vector `H` is (close to) a codeword of degree
   `< COMP_DEGREE_BOUND`, except with error `≈ ρ^Q` (conjectured) + commit-phase terms.
3. **ALI binds `H` to the trace.** At each query the verifier recomputes `CP` from the *opened
   trace values* via the public `compositionAt`, reads `g` from its own commitment, and checks
   `H = CP + ζ·g`. So the low-degree `H` equals `CP(trace) + ζ·g` at the query points.
4. **Constraints hold.** If the trace did **not** satisfy the constraints, `CP(trace)` would not
   be a polynomial of degree `< COMP_DEGREE_BOUND`. Then `H = CP + ζ·g` is low-degree only if
   `ζ·g` cancels `CP`'s high-degree part — but `g` is committed *before* `ζ` is drawn, so this
   happens with probability `≤ deg/|F|` over `ζ` (Schwartz–Zippel). Hence a cheating trace is
   caught by FRI or the ALI check, except with that probability.
5. **Non-interactivity.** All challenges (`α, γ, ζ`, the FRI `β`s, and the query indices) are
   squeezed from the SHA3 transcript after the relevant commitments are absorbed, so a prover
   cannot choose commitments to fit the challenges (Fiat-Shamir in the ROM).

**Combined error** ≈ `max(ρ^Q, deg/|F|)` + Merkle/RO terms. With the current 64-bit field this is
dominated by `deg/|F| ≈ 2^-52` (see `parameters.md §1`), so honest soundness is **~50-bit** —
PoC-grade. Empirically, every tampering we test (wrong image, mutated trace/mask/final-layer,
forged opening, any single flipped proof byte, random byte strings) is rejected.

---

## 5. Zero-knowledge

The argument is **honest-verifier zero-knowledge** (the standard notion for a Fiat-Shamir
non-interactive STARK). Two blindings make the transcript independent of the witness:

1. **Trace blinding.** The committed trace polynomial is `T'(x) = T(x) + Z_H(x)·b(x)` with `b`
   uniform of degree `< TRACE_BLIND ≥` (number of trace openings). The opened LDE values are
   `T'(x_j) = T(x_j) + (x_j^N − 1)·b(x_j)`. Over distinct points `x_j` the map
   `b ↦ (b(x_j))_j` is a Vandermonde bijection, and `x_j^N − 1 ≠ 0` on the coset, so the opened
   values are **uniform and independent of `T`** (hence of `s`). Because `Z_H` vanishes on `H`,
   the masked trace still satisfies every constraint (completeness, §3).
2. **Masked FRI.** FRI runs on `H = CP + ζ·g` for a uniformly random committed `g` of degree
   `< COMP_DEGREE_BOUND`. As `g`'s coefficients are uniform and independent of the witness, `H`
   is a uniform low-degree polynomial, so all FRI-layer openings (and the two `g` openings per
   query) reveal nothing about `CP` — and the verifier only ever recomputes the composition from
   values it already holds. Blinding randomness comes from the OS CSPRNG, so proofs are
   **randomized** (verified: two proofs of one statement differ and both verify).

> **Not claimed.** No explicit simulator is written, the ZK is honest-verifier only, and the
> bounds are heuristic. A formal ZK proof (and ideally a simulator) is future work.

---

## 6. Remaining gaps and their design (R1, R3)

The exit criterion — *a fully zero-knowledge, fully in-circuit spend proof with a written
soundness argument* — is **not yet fully met**. R2 (zero-knowledge) and **R1 (in-circuit hash)
are implemented** (§1, §5). R3 remains; this section records the realized R1 design and the R3
plan.

### R1 — arithmetization-friendly hash, in-circuit — **implemented**
The toy `x³ + C` is replaced by a Poseidon-style SPN (`src/rescue.zig`) proven by a multi-column
AIR (`src/stark.zig`):
- the trace is `WIDTH` columns (state width) × `N = ROUNDS+1` rows, one row per round;
- per-element transition constraints encode one round —
  `T_i(ωx) − (Σ_j M[i][j]·T_j(x)^7 + RC[r][i]) = 0` — degree `α = 7`; the round constants `RC`
  are supplied as **periodic low-degree columns** the verifier evaluates at the query points;
- boundary constraints fix the capacity cells to 0 at row 0 and the output to `image` at row N-1;
  the input rate cell (the secret) is never asserted.
- *Realized impact:* the degree-7 S-box raises the composition degree to `≈ α·(N+TRACE_BLIND)`,
  so `COMP_DEGREE_BOUND` and the LDE were sized up accordingly (see `src/stark.zig` parameters).
- **Caveat:** the MDS (a Cauchy matrix) and round constants are deterministically generated, not
  a standardized vetted Poseidon2/Rescue-Prime instance, and the state width `m = 3` is small.
  Production must adopt published constants, the spec's round count, and a wider state.

### R3 — fold all four constraints into one AIR (partial)

Constraint (3) authorization is in-circuit (R1). **Constraint (1) membership is now also
in-circuit**, as a standalone zero-knowledge proof (`src/membership.zig`): a multi-column AIR
that folds a leaf up `DEPTH` field-hash (`rescue`) 2:1 compressions to the public anchor. Its
trace is `DEPTH` blocks of one permutation each; the per-block transition is the Rescue round
(periodic round constants, evaluated as `RC_i(x^{N/BLOCK})`), the block-boundary transition is a
**link** (carry the compressed output into the next block's left input, reset the capacity), and
boundary constraints fix the capacity to 0 at row 0 and the output to the anchor at row N-1. The
round/link constraints are separated by **fixed enumerated vanishing polynomials**
(`Z_round = (x^N−1)/((x−ω^{N-1})·Z_link)`), avoiding a periodic selector column. It needs **no
permutation argument** because its wiring is a pure chain (adjacency). The path is leftmost-only;
general positions add one boolean ordering selector per level.

Still node-enforced (not yet in-circuit): **(2) nullifier**, **(4) balance**, and the
**commitment opening**.

**Wiring a *single* spend proof needs a copy-constraint / permutation argument.** Unlike
membership (a chain), a full spend reuses the same witness in several constraints — `value` in
both the commitment and balance, `ρ` in both the commitment and nullifier, `nk` in both the
nullifier and the owner binding. Proving those cells are equal across regions requires a
PLONK-style grand-product argument.

**The grand-product mechanism is now built and tested** (`src/permutation.zig`): a committed
running-product column `Z` with `Z[0]=1`, `Z[r+1]=Z[r]·(A[r]+γ)/(B[r]+γ)`, whose cyclic
transition telescopes to `∏(A+γ)=∏(B+γ)`, proving (over a Fiat-Shamir `γ` drawn *after* the
columns are committed) that two columns hold the same multiset. This validates the
soundness-critical parts: the running-product column and its transition/boundary (the wrap forces
the total product to 1), and the **two-round Fiat-Shamir flow** (commit → `γ` → commit `Z` →
constraint challenges → FRI). Tests cover completeness (reversal, cyclic shift, identity,
duplicate-swap) and soundness (a single changed element is rejected).

Progress:
1. ~~Implement the grand-product permutation argument.~~ **Done** (`src/permutation.zig`,
   multiset form). The copy-constraint specialization is the same `Z` with an id/σ encoding:
   `num=∏(v+β·id+γ)`, `den=∏(v+β·σ(id)+γ)`, `id(c,r)=k_c·ω^r`; a 2-cycle `σ` forces two cells equal.
2. ~~Assemble the four constraints + copy-constraint wiring into one proof.~~ **Done**
   (`src/spend.zig`): a single trace proving **all four constraints** for public
   `(anchor, nf, send, fee)` and hidden `(value, ρ, nk, siblings)` —
   (1) `cm = H(value, ρ)`, (2) `cm` folds up the path to `anchor` (DEPTH=6 levels),
   (3) `nf = H(nk, ρ)`, (4) `value = send + fee` — with `ρ` wired equal across the commitment and
   nullifier regions by the id/σ grand product, and `cm`→leaf wired by **adjacency** (the
   commitment block precedes the first membership block). `cm` is never revealed (ZK membership).
   Soundness tests: wrong anchor, wrong nf, unbalanced, tampered trace, a **wrong sibling/path**,
   and the decisive **inconsistent-`ρ`** case are all rejected; the two-round Fiat-Shamir
   (commit trace → β,γ → commit `Z` → constraint challenges → FRI) runs end-to-end.
3. ~~ZK on the spend circuit.~~ **Done** — `src/spend.zig` now blinds all four committed columns
   (the three trace columns and the grand-product `Z`) with `Z_H·b` and runs FRI on `CP + ζ·g`
   for a committed random `g`, so trace/`Z`/FRI openings are uniform and proofs are randomized
   (tested). The four-constraint fold is therefore both complete and zero-knowledge.
4. ~~General (non-leftmost) Merkle path positions.~~ **Done** — the carry constraint at each
   chained boundary is the degree-2 `(next₀−cur₀)·(next₁−cur₀)=0` ("the running hash is one of
   the two child inputs"), so the path may turn left or right at every level and the position
   stays hidden. Tested across all-left, all-right, and mixed patterns, with a wrong-position
   (different path shape) rejected.
5. **Remaining to harden/integrate R3:** widen the commitment to the real opening
   (`recipient`/`rcm`) + an owner binding (needs a fixed-carry sub-hash region distinct from the
   one-of Merkle carries, or the multi-column grand product for cross-column wiring); switch the
   protocol's commitment/nullifier/Merkle hashing to the field hash; node integration (verify the
   single proof instead of native checks); and a generic engine to replace the per-module
   duplication.

The four-constraint fold, its wiring, and ZK are now all demonstrated; what remains is hardening
and integration, not an unbuilt mechanism. `src/permutation.zig` is non-ZK and standalone (it
isolates the grand-product mechanism); `src/spend.zig` is the integrated, zero-knowledge one.

### Other gaps (carried from the assessment)
- **64-bit-field soundness bottleneck** → extension-field challenges (`parameters.md §1`).
- **PoC parameters** (rate, queries, grinding) → `parameters.md §2`.
- **Self-generated hash constants would not be "vetted"** → use published standard constants.
- **No formal proof, no external audit, no constant-time / side-channel review.**
- **Fiat-Shamir is a ROM heuristic.**

---

## 7. What the tests establish

`src/kat.zig` and the per-module tests provide: KAT vectors (SHA3-256 NIST, Goldilocks identities,
a known NTT, the `hashDomain` framing), property tests (field axioms, NTT round-trip at every
size, Merkle path verification/tampering, note serialization, STARK completeness+soundness over
random secrets), and a randomized robustness harness (the verifier rejects random and truncated
byte strings and every single-byte mutation of a valid proof, without crashing). These give
strong evidence of completeness and of the soundness *rejections*; they are **not** a substitute
for a formal soundness proof or an audit.
