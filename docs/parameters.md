# Lattica — Production Parameter Selection

**Status:** design guidance · **Audience:** protocol engineers / reviewers

This document records the cryptographic parameters of the Lattica reference and the values
recommended for a production deployment, with the rationale for each. It accompanies
[`soundness.md`](./soundness.md), which argues why the construction is sound at these parameters
and catalogues what remains before they can be trusted with value.

> **Headline:** the current PoC parameters give only **~50-bit conjectured soundness**, and the
> binding bottleneck is the **64-bit base field**, not the query count. Production must draw the
> Fiat-Shamir challenges from a field **extension** (≥128-bit) and raise the FRI rate/queries.

---

## 1. Proving field

| | Current | Recommended (production) |
|---|---|---|
| Base field | Goldilocks `p = 2^64 − 2^32 + 1` | Goldilocks (keep) |
| Challenge field | base field (64-bit) | **quadratic or cubic extension** (≥128-bit) |

**Rationale.** Goldilocks is an excellent *base* field: 64-bit limbs with fast reduction, and
2-adicity 32 (subgroups up to `2^32`, far above what the trace/LDE need). The problem is not the
trace — it is the **soundness terms that scale as `1/|F|`**. Two examples in the current design:

- the random linear-combination challenge `ζ` fails to expose a cheating composition with
  probability ≈ `deg / p ≈ 2^12 / 2^64 = 2^-52`;
- the FRI folding challenges have a similar `O(deg/|F|)` commit-phase error per round.

A union bound over these caps soundness at roughly **2^-50** regardless of how many queries are
made. The standard fix (ethSTARK, Plonky2, Winterfell) is to keep the trace in the base field
but **sample all verifier challenges from an extension field** `F_{p^2}` or `F_{p^3}`, raising
these terms to `2^-104` / `2^-156`. This is the single most important parameter change for
production and is a contained engineering task (an extension-field type used only for
challenges and the FRI/DEEP arithmetic).

---

## 2. FRI / STARK parameters

| Parameter | Current | Recommended | Effect |
|---|---|---|---|
| Trace length `N` | 1024 | application-driven | rows of the AIR |
| Blowup (inverse rate `1/ρ`) | 16 (ρ = 1/4 after blinding) | 8–16 → **target ρ ≤ 1/8** | larger ρ⁻¹ ⇒ smaller query-phase error |
| FRI queries `Q` | 32 | **≥ 64** (with extension field) | query-phase error ≈ `ρ^Q` (conjectured) |
| Grinding (PoW) bits | 0 | **20–32** | adds that many bits of soundness cheaply |
| Folding factor | 2 | 2–4 (or 8/16) | fewer layers, smaller proofs |
| Final-layer degree | 16 | small constant | end of folding |

**Soundness estimate.** Treating the list-decoding conjecture as standard practice, the
query-phase error is ≈ `ρ^Q`. With `ρ = 1/4, Q = 32` that is `2^-64`; with the 64-bit field
bottleneck above the *effective* figure today is ≈ **2^-50**. Recommended production
(`ρ = 1/8`, `Q = 64`, grinding 20, extension-field challenges) targets **> 2^-120**:
`(1/8)^64 = 2^-192` query-phase, `~2^-104` field terms in `F_{p^2}`, `+20` grinding.

A DEEP-FRI quotient (out-of-domain sampling) — not yet implemented — additionally makes the
soundness independent of the constraint degree and is the conventional next step.

---

## 3. Hash functions

| Use | Current | Recommended |
|---|---|---|
| Out-of-circuit (commitments, nullifiers, Merkle, KDF, transcript) | SHA3-256 | SHA3-256 (keep) |
| In-circuit (AIR) authorization relation | **Poseidon-style SPN** (`x^7`, MDS, full rounds), generated constants | **Poseidon2 or Rescue-Prime over Goldilocks**, standardized constants + spec round count |
| Proof-of-work (consensus, out of scope here) | — | hash with **doubled output width** (Grover margin) |

**Rationale.** SHA3-256 is conservative and standard for the out-of-circuit hashing; under
Grover its preimage/collision margins remain adequate for the protocol's use (and PoW, when
added, doubles the width). The in-circuit relation **(R1) is now a real arithmetization-friendly
hash** — a Poseidon-style SPN (`x^7` S-box, Cauchy MDS, full rounds) in `src/rescue.zig`, proven
by a multi-column AIR — replacing the trivially-invertible `x³ + C`. What remains for production
is to swap the deterministically-generated MDS/constants for a **vetted, standardized**
Poseidon2/Rescue-Prime instance (published constants, spec round count, margins for the recent
Poseidon cryptanalysis) and to widen the state from the PoC's `m = 3`.

---

## 4. Signatures (ML-DSA)

`std.crypto.sign.mldsa` provides all three FIPS-204 parameter sets, so the level is a one-line
change.

| Set | NIST category | Public key | Signature | Use |
|---|---|---|---|---|
| ML-DSA-44 (current) | 2 (~AES-128) | 1312 B | 2420 B | compact; fine for a PoC |
| **ML-DSA-65** (recommended) | 3 (~AES-192) | 1952 B | 3309 B | balanced production margin |
| ML-DSA-87 | 5 (~AES-256) | 2592 B | 4627 B | maximum margin |

**Recommendation:** **ML-DSA-65** for the transaction binding signature in production — a clear
post-quantum margin over the PoC's level-2 choice at a modest size increase. ML-KEM stays at
**ML-KEM-768** (NIST level 3), which is already an appropriate production choice.

---

## 5. Summary: change-list for production

1. **Extension-field challenges** (≥128-bit) — closes the dominant `1/|F|` soundness term. *(highest priority)*
2. **FRI:** rate ≤ 1/8, ≥ 64 queries, 20–32 grinding bits → > 120-bit soundness.
3. **In-circuit hash (R1):** done — Poseidon-style SPN in-circuit. Remaining: swap to standardized/vetted constants and a wider state.
4. **ML-DSA-65** for binding signatures.
5. (Architectural, see `soundness.md`) **DEEP-FRI** and **fold all four constraints into the AIR** (R3).
