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

> **R(image; secret):** the prover knows `s = secretToField(secret)` such that iterating the
> transition `x → x³ + C` over Goldilocks for `N-1` steps maps `s` to `image`.

Equivalently: the prover knows an execution trace `T[0..N]` with `T[0] = s`, `T[i+1] = T[i]³+C`,
and `T[N-1] = image`.

> **Caveat (R1).** `x → x³ + C` is a *permutation with an easy inverse* (cube roots exist over
> Goldilocks), so knowing `image` lets anyone compute a valid `s`. The proof is therefore a
> sound *argument of knowledge of a trace*, but the relation is **not a one-way authorization**.
> Replacing the transition with a vetted arithmetization-friendly hash (§6, R1) is what turns
> this into a meaningful spend authorization. Everything below concerns the soundness of the
> *proof system*, which is independent of this caveat.

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
soundness argument* — is **not yet met**. R2 (zero-knowledge) is implemented (§5). R1 and R3
remain; this section is the design to build them, incrementally and with review.

### R1 — vetted arithmetization-friendly hash, in-circuit
Replace `x³ + C` with **Poseidon2** or **Rescue-Prime** over Goldilocks (standard published
constants). AIR shape:
- trace widens to the hash state width `m` (one row per round); add **periodic columns** for the
  round constants (the current single-constraint AIR must generalize to multi-column with periodic
  values);
- transition constraints encode one round: S-box (degree `α`, e.g. 7), the MDS linear layer, and
  round-constant addition; Rescue's inverse S-box is expressed as a forward degree-`α` constraint;
- boundary asserts input = secret state, output = `image`.
- *Soundness impact:* the composition degree rises to `≈ α·(state rows)`; size `COMP_DEGREE_BOUND`
  and the LDE accordingly.

### R3 — fold all four constraints into one AIR
Today only constraint (3) is in-circuit; (1) membership, (2) nullifier, (4) balance are
node-enforced. To fold them in (which requires R1's in-circuit hash so commitments/nullifiers/
Merkle nodes are cheap in the field):
- **(4) Balance** — add columns for input/output values; a single linear constraint
  `Σ in = Σ out + fee`. (Easiest; no hashing.)
- **(2) Nullifier** — in-circuit hash rows computing `nf = H(nk, ρ, pos)`; boundary binds the
  output to the revealed nullifier.
- **(1) Membership** — `depth` in-circuit hash invocations folding the leaf up the authentication
  path; boundary binds the top to the public anchor; a **selector/periodic column** chooses
  left/right per level.
- **Wiring** — the note commitment recomputed in-circuit must equal the Merkle leaf, the spend's
  `nk/ρ` must be the ones used by both the nullifier and commitment, etc. This needs **copy
  constraints** (a permutation argument) or careful shared boundary cells — the main new soundness
  surface, and the part most needing review.

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
