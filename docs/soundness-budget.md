# C-04 — soundness budget (Plonky3 spend circuit)

Resolves audit finding **C-04** ("~50-bit soundness on the 64-bit base field"). The production
spend proof (`lattica-prover-p3/`) operates over the **Goldilocks** base field but draws all
Fiat–Shamir / DEEP / FRI challenges from the **quadratic extension `F_p²`** (~127-bit), and uses FRI
parameters chosen for a ≥100-bit *proven* and ≥128-bit *conjectured* security level. The numbers
below are **machine-checked** by `full_spend_air::security_report()` and the
`production_security_budget` test (which asserts proven ≥ 100 and conjectured ≥ 128), computed with
Plonky3's own accounting (`StarkSecurityParams` / `ProvenSecurity` / `ConjecturedSecurity`,
cross-checked against Ethereum's `soundcalc`).

## Production parameters

| Parameter | Value | Notes |
|---|---|---|
| Base field | Goldilocks `p = 2^64 − 2^32 + 1` | values map 1:1 to `u64` |
| Challenge field | `F_p²` (BinomialExtensionField, 2) | ⌊log₂ p²⌋ = **127** bits |
| Commitment hash | Poseidon2, 4-Goldilocks digest | ~**128**-bit collision resistance (birthday) |
| FRI rate ρ | `2^-4` (`log_blowup = 4`) | blowup 16; bounds bits/query |
| FRI queries | **96** | |
| Query grinding | **16** bits | PoW before sampling queries |
| Commit grinding | 0 bits | |
| `log_final_poly_len` / `max_log_arity` | 0 / 1 | fold to a constant, arity 2 |
| Trace | height **2048** (`DEPTH=32`), width 17 | 62 constraints, max degree 8 |

`max_constraint_degree = 8 ≤ blowup + 1 = 17` (the Plonky3 quotient-fit requirement), with margin.

## Budget (machine-checked)

| Level | Bits | Basis |
|---|---|---|
| **Conjectured (FRI query)** | **400** | ethSTARK `log_blowup·num_queries + query_pow = 4·96 + 16`. |
| Conjectured (effective) | **~127** | capped by the challenge field (`F_p²`, 127) and commitment collision (128). |
| **Proven — unique-decoding** | **103** | round-by-round, [2024/1553] Thm 2. |
| Proven — list-decoding | 96 | [2024/1553] Thm 3 + [2025/2055] Thm 4.2 (improved LDR). |
| **Proven (reported)** | **103** | `max(UDR, LDR)`, capped by collision resistance. |

So the spend proof has **≈103-bit proven** and **≈127-bit conjectured** security — versus the audited
~50 bits. The query count (96) is what lifts the proven unique-decoding bound past 100; the LDR bound
plateaus near 96 for this rate, so UDR is the binding (and reported) regime.

## Performance (release, single core, `DEPTH=32`)

| | |
|---|---|
| Proof size | ~848 KB |
| Prove | ~2.2 s |
| Verify | ~14 ms |

Verify (the node-side cost) is ~14 ms; proving (~2 s, wallet-side) is acceptable. Proof size is
dominated by the 96 FRI query openings; it can be cut by raising `log_blowup` (fewer queries for the
same security, at a larger prover LDE) if proof size becomes the binding constraint.

## Parameter hardening (was demo-sized in M4c)

| Parameter | Demo | Production | Why |
|---|---|---|---|
| Merkle `DEPTH` | 4 | **32** | full note-commitment tree depth (block count padded to a power of two: 36 → 64). |
| `recipient` | 1 element | **4-element digest** | binds the full `H(nk)` address; input & output notes share the commitment layout. |
| value `BITS` | 32 | **52** | range bound; `value = out_value + fee` is a field equation, so all three < `2^52` keeps `2·2^52 < p` (no wraparound). |

## Caveats / residual work

- These bounds assume the FRI/DEEP analysis as implemented in `p3-uni-stark::security` (refs:
  ethSTARK 2021/582, 2020/654, 2024/1553, 2025/2055, 2025/2010). [2025/2010] recommends proven
  bounds for deployment — we report and gate on **proven** (103), not just conjectured.
- Collision resistance assumes the Poseidon2 4-Goldilocks digest behaves as a 256-bit random oracle
  (128-bit birthday bound). A dedicated Poseidon2 security review is part of the Phase-3 audit.
- `RoundConstants`/linear layers are the **vetted** `p3-goldilocks` Poseidon2 constants; the
  in-circuit hash equals the protocol's native `Poseidon2Goldilocks` (differential-tested).
- Final production parameters should be re-confirmed at audit time against the then-current
  `soundcalc` / literature, and against the deployed proof-size budget.
