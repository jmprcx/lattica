# C-04 — soundness budget (Plonky3 spend circuit)

Resolves audit finding **C-04** ("~50-bit soundness on the 64-bit base field"). The production
spend proof (`lattica-prover-p3/`) operates over the **Goldilocks** base field but draws all
Fiat–Shamir / DEEP / FRI challenges from the **quadratic extension `F_p²`** (~127-bit), and uses FRI
parameters chosen for a ≥100-bit *proven* and ≥128-bit *conjectured* security level. The proven level
is **machine-checked** per production circuit by `proven_security_bits()` + the
`proven_security_meets_production_floor` test (asserts proven ≥ 100) in both `joinsplit_air` and
`htlc_air`, and is reported (with prove/verify timings + proof size) by each circuit's `measure()`,
computed with Plonky3's own accounting (`StarkSecurityParams` / `ProvenSecurity`, cross-checked against
Ethereum's `soundcalc`). Both production circuits share one `make_config` and resolve to the same
budget. (The earlier `full_spend_air::security_report()` / `production_security_budget` names predate
the Plonky3 join-split cutover and no longer exist.)

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
| `log_final_poly_len` / `max_log_arity` | 0 / **4** | fold to a constant, arity 16 (proof-size lever) |
| Merkle cap height | **6** | 2⁶ cap ⇒ shorter query paths (proof-size lever) |
| Trace | height **4096** (`NUM_BLOCKS = next_pow2(USED_BLOCKS) = 128`, `BLOCK=32`, `DEPTH=32`); width **19** (join-split) / **31** (htlc) | max constraint degree 8 (Poseidon2 round); same height/degree both circuits |

The `max_log_arity` and `cap_height` values are FRI *encoding* choices — they shrink the proof with
**no** effect on the security level (see the sweep below). They were chosen by `cargo run --bin
sweep`.

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
| Proof size | **~421 KB** |
| Prove | ~2.05 s |
| Verify | ~8 ms |

## Proof-size parameter sweep

`cargo run --release --bin sweep` proves a real `DEPTH=32` spend at each FRI configuration and
measures proof size + timings next to the proven/conjectured bits. Headline rows (proven/conjectured
are bits; proof in KB):

| config | proven | conj | proof KB | prove ms | verify ms |
|---|---|---|---|---|---|
| `lb4 q96 ar1 cap0` (initial) | 103 | 127 | 828 | 2143 | 13 |
| `lb4 q96 ar3 cap0` | 103 | 127 | 539 | 2035 | 9 |
| `lb4 q96 ar3 cap4` | 103 | 127 | 443 | 2075 | 7 |
| **`lb4 q96 ar4 cap6`** (production) | **103** | **127** | **421** | 2019 | **7** |
| `lb4 q64 ar1 cap0` | 96 | 127 | 553 | 2091 | 9 |
| `lb5 q64 ar1 cap0` | 94 | 127 | 589 | 4373 | 9 |
| `lb6 q48 ar1 cap0` | 91 | 127 | 469 | 8568 | 8 |
| `lb4 q64 pow24` | 96 | 127 | 553 | **30710** | 9 |

What the data shows:
- **FRI folding arity is a (near-)free proof-size lever.** Arity 1→4 + a 2⁶ Merkle cap cut the proof
  **828 → 421 KB (−49%)** at the *same* 103-bit proven / 127-bit conjectured level, and verify ~halves
  (13 → 7 ms). Adopted as production. (Pushing further — `ar5 cap6` — regresses; the cap/arity
  overhead overtakes the path savings.)
- **Raising the blowup (lower rate) is counter-productive here:** `lb5`/`lb6` cost 2–4× prove time
  *and* give fewer proven bits at these query counts. `log_blowup=4` is best.
- **Query grinding is not a useful lever** for the proven bound: `q64 pow24` matches `q64 pow16`
  (96 bits) but proves 15× slower (~31 s). Proven security is gained by *queries*, not grinding.
- The proven floor for ≥100 bits is `num_queries = 96`; fewer queries (≤80) sit at the 96-bit LDR
  plateau. So the production choice is "96 queries at the smallest encoding."

## Two further levers, measured (and rejected)

### Trace height / padding (`DEPTH` recompiles)
> **Historical (pre-v3) figures.** This sweep predates the current layout and counts only one input
> span (36 blocks → 64). The current circuits use the **total** `USED_BLOCKS` (80 join-split / 88 htlc)
> padded to **128** ⇒ **height 4096**; the production proof is ~0.42–0.47 MB. The lever's *conclusion*
> (proof size ~logarithmic in height; padding is cheap) still holds. Re-measure before quoting absolute
> numbers.

`DEPTH=32` uses 36 blocks, padded to 64 (height 2048, ~44% "dead"). Measured at the production FRI
params:

| `DEPTH` | height | padding | proof | prove | verify |
|---|---|---|---|---|---|
| 28 | 1024 | none | 398 KB | 1.17 s | 6 ms |
| **32** (production) | 2048 | 44% | 421 KB | 2.05 s | 8 ms |
| 60 | 2048 | none (full use) | 431 KB | 2.10 s | 7 ms |

Takeaways: proof size is ~**logarithmic** in height — halving the trace (2048→1024) cuts prove time
~**43%** but proof size only ~**5%**. And the padding is **not wasted**: `DEPTH` up to 60 (a 2⁶⁰-leaf
tree) costs the same as 32 (2³² leaves), so the headroom is free depth. Trace tightening (incl. the
deferred lookup-based dense layout) is therefore a **prover-time/memory** lever, not a proof-size one.

### Base field — Goldilocks vs BabyBear (`cargo run --bin field_compare`)
Same logical work (128 Poseidon2 compressions), each field's native Poseidon2, matched FRI params,
algebraic commitments + `DuplexChallenger`:

| field | trace width | proof | prove | verify |
|---|---|---|---|---|
| Goldilocks (w8) | 180 | 643 KB | 189 ms | 9 ms |
| BabyBear (w16) | 298 | **616 KB** (−4%) | 225 ms | 13 ms |

The naive "31-bit field ⇒ 4-byte elements ⇒ half the proof" does **not** hold for this circuit. Two
effects cancel the smaller elements: (1) a ~256-bit digest needs **2× the BabyBear elements**, so its
Poseidon2 is **width 16** (298 cols vs 180); (2) the **extension field is ~16 bytes on both**
(`F_p⁴` vs `F_p²`), and the FRI-phase openings — which dominate the proof — live in the extension.
Net ~4% for a full circuit rewrite plus multi-limb `u64` value/range/balance arithmetic. **Not
worth it** — Goldilocks stays.

## Batch aggregation — one proof per block (implemented: `batch_joinsplit_air`)

The production batch circuit `lattica-prover-p3::batch_joinsplit_air` proves `n` **distinct** join-split
transactions as a **single** proof (the spend AIR tiled `n` times, per-tile self-contained, with an
in-circuit fold of each tile's statement into one **block tx-root** public input). The table below is
the original size/verify measurement (identical tiles, size-representative); the production circuit adds
the staging columns + the fold (a few extra columns + the trailing free padding blocks — the tile stays
2^12 rows, so the sizes are unchanged).

**Proven-soundness floor ⇒ `MAX_BATCH_TILES = 64`.** Recomputed at batch height (`batch_proven_security_bits`):
103 bits through n=8, 102 @ n=16, 101 @ n=32, **100 @ n=64 (height 2^18)**, 99 @ n=128. So one proof
covers up to **64** transactions at the ≥100-bit floor; a larger block emits **multiple** batch proofs of
≤64 tiles each (or a future config raises `num_queries`). Enforced by `prove_batch_to_bytes` + the
`batch_proven_security_floor` test.

`cargo run --release --bin batch` proves a batch of `n` spends as a **single** proof (the spend AIR
tiled `n` times in one trace) at the production FRI params:

| n | proven | proof KB | per-spend KB | vs n separate | prove ms | verify ms |
|---|---|---|---|---|---|---|
| 1 | 103 | 421 | 421 | 1× | 2067 | 7 |
| 2 | 103 | 446 | 223 | 1.9× | 4161 | 7 |
| 4 | 103 | 468 | 117 | 3.6× | 8380 | 8 |
| 8 | 103 | 497 | 62 | 6.8× | 16785 | 8 |
| 16 | 103 | 532 | 33 | 12.6× | 34194 | 9 |
| 32 | 102 | 560 | **17.5** | **24×** | 70025 | 9 |

- Proof size grows **~log n** (~+28 KB per doubling), so **per-spend bytes collapse**: 421 → 17.5 KB
  at n=32 (24×). Extrapolating (~+28 KB/doubling): a **1024-spend block ≈ ~700 KB** single proof vs
  ~431 MB as separate proofs (**~600×**).
- **Verify is ~constant** (7–9 ms) regardless of n — a validator checks **one** proof per block.
- Security holds (proven ≥ 102 through n=32).
- **Cost: proving is monolithic and ~linear in n** (n=32 ≈ 70 s) — the block producer proves the
  whole block. This is the batch AIR's limit vs *true recursion* (each user proves their own spend;
  the producer aggregates fixed-size proofs in parallel). The batch AIR needs **no recursive
  verifier**, so it's the pragmatic first step; recursion is the scale-out when monolithic / per-user
  independent proving becomes the constraint. (The `n` spans here are identical — size-representative;
  a production batch carries distinct spends bound by an aggregate public-input hash, same size.)

**Conclusion:** the realized per-proof win is the FRI encoding (arity + cap, −49%, adopted). The
field and trace levers don't help proof size (≤5% / ~4%). The structural lever — **batching toward
one proof per block** — is the real headroom: measured ~log(n) growth ⇒ ~600× smaller and constant
verify at block scale, at the cost of monolithic proving (which true recursion later removes). The
batch is implemented (`batch_joinsplit_air`/`batch_htlc_air`, + the node `applyBatch`/`applyHtlcBatch`
path); the trustless per-user-proving scale-out beyond it is designed in **`docs/recursion-design.md`**
(deferred — it requires a recursive STARK verifier circuit, which Plonky3 0.6.1 does not provide). The
chosen block cadence (one batch proof per 12-min transaction block ⇒ ~320 tx/hr baseline) and how
recursion is the scaling path beyond it are documented in **`docs/block-production-consensus.md`**.

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
