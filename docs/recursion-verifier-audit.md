# Recursive STARK verifier — in-circuit spec & constraint budget (Phase B0)

**Status: spec for an in-development circuit (Phase B of `recursion-design.md`).** This pins down exactly
what an in-circuit Plonky3 verifier AIR must compute (so the work is auditable like
`joinsplit-constraint-audit.md`), and sizes it against lattica's existing gadgets. It is the spec the
B1 spike validates and the eventual full verifier (B3) implements. Numbers below are from a read of
Plonky3 0.6.1 (`p3-uni-stark`/`p3-fri`/`p3-challenger`) + lattica's config.

## 1. What the native verifier does (`p3-uni-stark::verify`)
The in-circuit verifier must replay, as constraints, the native algorithm:
1. **Init transcript** (`DuplexChallenger`, Poseidon2 w=8 / rate=4 / cap=4).
2. **Observe** degree bits, the trace commitment, preprocessed commitment (if any), and the public
   values.
3. **Sample α** (constraint-combination challenge, in the challenge field F_p²).
4. **Observe** the quotient-chunks commitment (and the ZK random commitment if present).
5. **Sample ζ** (out-of-domain point, F_p²); check ζ ∉ trace domain.
6. **Verify openings** at {ζ, ζ·g} via the PCS → **the FRI verifier** (§2).
7. **Recompose** the quotient from its chunks at ζ; **check the constraint relation**
   `combined_constraints(ζ) == Z_H(ζ) · quotient(ζ)` (Z_H = trace-domain vanishing poly).

`Proof` = { `commitments` {trace, quotient_chunks, random?}, `opened_values` {trace_local, trace_next,
quotient_chunks, preprocessed?, random?}, `opening_proof` (the FRI proof), `degree_bits` }.

## 2. The FRI verifier (`p3-fri`), the dominant cost
`FriProof` = { `commit_phase_commits[]` (one per round), `commit_pow_witnesses[]`, `query_proofs[]`,
`final_poly[]`, `query_pow_witness` }. Each `QueryProof` = { `input_proof` (batch Merkle opening at the
query index), `commit_phase_openings[]` } where each step = { `log_arity`, `sibling_values[]`,
`opening_proof` (Merkle) }.

Per query (×`num_queries`):
- Sample the query index (`log_global_max_height` bits) from the transcript.
- **Input opening:** verify a Merkle authentication path for the trace/quotient commitment at the index.
- **Per commit-phase round:** reconstruct the arity-`2^k` evaluation group from self + siblings,
  **verify the Merkle opening** of that group, **fold** via Lagrange interpolation at the round challenge
  β (in F_p²), and roll in any new reduced openings.
- Check the final folded value equals `final_poly` evaluated at the index point.

So a query = a chain of **Merkle-opening verifications** (Poseidon2 compressions up paths) + **F_p²
Lagrange folds**. Hashing dominates; folding is cheap field arithmetic.

## 3. Lattica's config (sets the workload)
`Val = Goldilocks`, `Challenge = BinomialExtensionField<Goldilocks,2>`; Poseidon2 width 8. FRI:
`log_blowup = 4`, `max_log_arity = 4`, `log_final_poly_len = 0`, `num_queries = 96`,
`query_proof_of_work_bits = 16`. MMCS: internal-node compression `MyCompress =
TruncatedPermutation<Perm,2,4,8>`, leaf hash `MyHash = PaddingFreeSponge<Perm,8,4,4>`, cap height 4.

## 4. The decisive reuse — lattica already proves the dominant operation
**`MyCompress`, the FRI Merkle internal-node compression, is bit-identical to lattica's `merge`:**
`merge(l,r) = native_permute(l‖r)[0..4]` = `TruncatedPermutation<Perm,2,4,8>(l,r)`. And lattica already
verifies **depth-32 `merge`-chains in-circuit** — the `joinsplit_air` membership fold (`P_MEM_LINK`,
bit-controlled merge up a path), proven + exhaustively corrupted-trace-tested. A FRI Merkle opening is the
*same* operation at depth ≈ `log_height`. So the per-query Merkle-opening cost is not speculative — it is
the membership-fold cost we already pay.

| Recursive-verifier need | Existing gadget (reused) |
|---|---|
| FRI Merkle-opening verification | `merge` + the `joinsplit_air` depth-`DEPTH` membership fold (bit-controlled merge up a path) |
| Poseidon2 permutation as constraints | `poseidon2_air` (`native_steps` for the trace, the period-32 round constraints; `BLOCK = 32` rows/perm) |
| In-circuit Fiat-Shamir transcript | `poseidon2_air` (the same Poseidon2 the `DuplexChallenger` uses) — Phase B2 |
| Aggregation binding (block tx-root) | the `DOM_TXROOT` MD-chain + running-root fold from `batch_*_air` (reused verbatim) — Phase B4 |
| F_p² arithmetic | `BinomialExtensionField<Goldilocks,2>` (mul = 1 base-mul + 2 dot products; inverse = 1 Frobenius + 1 base-inverse) |

## 5. Constraint budget (single inner proof)
For one inner spend proof: trace height `2^12`, blowup `2^4` ⇒ committed domain `2^16` ⇒ input-opening
path depth ≈ 16. Commit-phase: ≈ 4–16 rounds (arity 2..16) with progressively shorter openings; ballpark
Σ opening depths per query ≈ 30. So per query ≈ **~46 `merge` compressions**; × 96 queries ≈ **~4,400
merges**. At `BLOCK = 32` rows/merge that is ≈ **~140k rows** for query-phase hashing, plus the transcript
permutations (tens) and the F_p² folds (cheap). ⇒ a single-inner-proof recursive verifier is on the order
of **2^18 rows** — the *same order as lattica's batch circuits at n=64* — i.e. **tractable on the existing
prover**. Aggregating K inner proofs tiles to ≈ K·2^18 (recursion proper keeps the *outer* proof verifying
a constant number of inner proofs per tree level).

**Risk read:** the size-dominant part (Merkle/transcript hashing) is the operation lattica already proves,
so size is *not* the blocker. The residual risk is the **correctness** of the in-circuit FRI **folding**
(F_p² Lagrange) + the **OOD/quotient/DEEP** check — that is what B3 must retire, not feasibility of scale.

## 6. The B1 spike (what's being built now) + go/no-go
**Build:** a standalone in-circuit **FRI-query Merkle-opening verifier** — given a leaf digest, the
sibling digests along a path, and the index bits, recompute the root by bit-controlled `merge` up the
path and bind it to a public input — reusing `poseidon2_air`'s permutation block and the membership-fold
pattern. **Validate:** (a) **differential** — the in-circuit root equals the native MMCS/`merge` opening
root on a real path; (b) **corrupted-trace** — a tampered sibling/bit ⇒ wrong root ⇒ reject; (c)
**benchmark** one path and extrapolate ×(96 queries × rounds).

**Go/no-go (written into `recursion-design.md`):** GO on the p3 path if the measured per-merge in-circuit
cost matches the membership-fold cost (expected — same op) and the extrapolated single-inner-proof trace
is ≤ ~2^20. If hashing cost is unexpectedly high, escalate to the framework-migration path
(`recursion-design.md` §4 path 2) before building B3.

## 7. Audit posture
This is a **new audited circuit**, never folded into the frozen `joinsplit_air`/`htlc_air`/`batch_*`. It
gets its own corrupted-trace suite (mirroring the existing `forged_*` negatives) and this doc grows
constraint-by-constraint as B1→B5 land.

## 8. Built so far (the three core primitives — all validated)
The three operations a FRI-STARK verifier is composed of are each implemented as standalone, real-prover-
differential-tested in-circuit spikes in `lattica-prover-p3/src/recursion/`:
- **Merkle openings** — `fri_merkle.rs` (B1): in-circuit FRI query-path verification via bit-controlled
  `merge`; matches the native `merge`-tree root; tampered path rejected.
- **Fiat–Shamir transcript** — `transcript.rs` (B2): the `DuplexChallenger` duplex sponge; in-circuit
  squeeze validated. A faithful `ModelChallenger` (executable spec) is pinned equal to the real
  challenger across the full operation set the verify-replay needs — variable-length absorbs, interleaved
  observe/sample, `sample_algebra_element` (F_p² = `(rate[3], rate[2])`), and `sample_bits` (query-index
  sampling). This is the reference B3-wire's in-circuit transcript must reproduce.
- **F_p² arithmetic + the FRI fold** — `fri_fold.rs` (B3a/B3b): `X²=7`; the arity-2 fold
  `(e0+e1)/2 + (e0−e1)·β/(2s)` with an in-circuit `1/(2s)`; matches native; wrong fold rejected. Also
  the **commit-phase fold chain** (`FoldChainAir`): the running eval folded round-by-round with the FRI
  squaring point map `x→x²`, reaching the final-poly value; tampered sibling / wrong final rejected.

The remaining work is the **integration** (B3-wire + B3-quotient + B4 + B5) — see `recursion-design.md`
§10 for the precise roadmap. Feasibility unknowns (hashing scale, transcript fidelity, F_p² folding) are
retired; what's left is faithful high-volume wiring against p3's exact proof format + the circuit-specific
quotient/DEEP check.
