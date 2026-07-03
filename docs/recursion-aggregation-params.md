# Recursion — aggregation-level soundness parameters (R3)

**Status: design + measurement, on branch `v3`.** Companion to `docs/recursion-design.md` (what recursion
buys) and `docs/recursion-verifier-audit.md` (the in-circuit verifier spec). This doc fixes the
**parameters** of the recursive aggregation tree so its soundness clears the same **≥100-bit proven**
floor the batch path enforces (`docs/soundness-budget.md`), and records the measured feasibility curve
that constrains them.

Prerequisite achieved (2026-07-03, commits `165a577` + `7d6a5ad`): the monolith
(`recursion/monolith`) accept-iff-`p3::verify`s a **real production `JoinSplitAir` proof**, both
non-hiding and hiding (`is_zk=1`), through the data-driven symbolic epilogue. So the in-circuit verifier
is no longer the unknown; the aggregation **parameters** are.

## 1. The soundness identity for the tree

A recursive proof's soundness is **`min` over every level** of that level's FRI soundness
`f(num_queries, log_blowup)`. Why: a level's outer proof proves the statement "the level below verified"
only to the strength of its **own** FRI parameters; and preserving the level-below proof's
`f(q, lb)` requires the monolith to **replay all `q` of its queries in-circuit** (replaying only `q' < q`
re-establishes just `f(q', lb)`). There is **no soundness-preserving shortcut** that checks fewer queries.

Consequences, from `soundness-budget.md`'s accounting (`p3-uni-stark` / soundcalc):
- Proven unique-decoding ≥100 bits needs **`num_queries = 96` at `log_blowup = 4`**; `≤80` queries sit on
  the 96-bit list-decoding plateau. Grinding does **not** lift the *proven* bound (it lifts conjectured).
- Therefore **every level** of the tree — leaf user proofs, every aggregator, the root — must be a
  **q96 / lb4** proof to keep the whole chain at proven-100. Reduced-query configs (the phase-6/7
  monolith milestones) are correctness milestones only; they do **not** clear the floor (as flagged at
  `MAX_AGG_TILES`).

So the aggregation tree does **not** reduce per-proof cost: each aggregator must replay `K × 96` inner
queries (K inners × 96 each). What the tree buys is **parallelism** (independent aggregators on separate
machines) and **log-depth** composition + **trustless per-user proving** — not a smaller single proof.

## 2. The cost of replaying 96 queries in-circuit

The monolith lays out one **super-tile per replayed inner query** (a transcript region + `n_queries`
super-tiles), then the AIR height is padded to a power of two. Each super-tile for the real join-split
shape (W=19 → 5-block input leaf, degree-8 → nqc=8, db=12 → log_global=16 / cm_rounds=12) is large.
Measured curve (is_zk=0 — the recursion-path inner shape, since we control inner `is_zk`; width 773;
`phase8_joinsplit_query_curve`, this box: 62 GB RAM / 24-core Arrow Lake, AVX2+LTO):

| inner queries replayed | monolith rows | peak RSS | prove+verify |
|---|---|---|---|
| 4 | 2^16 | 7.1 GB | 17.7 s |
| 8 | 2^16 | 7.2 GB | 17.8 s |
| 12 | 2^17 | 14.5 GB | 35.6 s |
| 16 | 2^17 | 14.7 GB | 35.6 s |

**Rows quantize to powers of two**, so RSS/time track `next_pow2(tr + n_queries · m_period)` in
~2× steps, and there is **free headroom** up to each boundary (2^16 holds ~4–8 queries at ~7 GB; 2^17
holds ~12–16 at ~14.5 GB). `tr + n·m_period` implies `m_period ≈ 6.1k` rows and `tr ≈ 16k`. Extrapolating
by the power-of-two boundaries:

| rows | RSS | inner queries held | note |
|---|---|---|---|
| 2^18 | ~29 GB | ~24–40 | |
| 2^19 | ~58 GB | ~48–80 | **this box's ceiling** |
| 2^20 | ~116 GB | **96** (full wire proof) | production server |
| 2^21 | ~232 GB | ~192 (K=2 aggregator) | production server |

So a **single monolith verifying a full 96-query wire join-split ≈ 2^20 rows / ~116 GB / ~5 min** — a
production-prover (128 GB+) capability, just past this 62 GB dev box. The dev box validates the path at
reduced queries (the correctness milestone, done: `phase8_joinsplit_monolith` /
`phase8_joinsplit_hiding_monolith`); the ≥100-bit-proven full-query proof runs on a server.

## 3. Recommended architecture

1. **Every level is q96 / lb4** (proven-100), per §1 — no reduced-query intermediate levels. The
   reduced-query monoliths are correctness milestones only.
2. **Leaf level:** users prove their own single-tx join-split (today's `lattica_joinsplit_prove`,
   96q/lb4, ~2 s, ~0.4 MB) on their own hardware — *not* the aggregator's cost, and the trustless
   per-user-proving win over the batch (`recursion-design.md` §1).
3. **Aggregator level:** one aggregator instance verifies **K inner proofs** (the monolith tiled ×K,
   `fold` mode, shared transcript per inner) and folds each verified `pvs[0]` into the block tx-root
   (`DOM_TXROOT`, `merge`, IV=0, pow2 pad — byte-identical to `batch_joinsplit_air::batch_root`, so the
   node seam is unchanged). Cost ≈ **K · 2^20 rows** → K=2 ≈ 2^21 / ~232 GB / ~10 min on a 256 GB server.
   Keep K small (2–4) and get width from **tree depth**, not wide tiling, to bound per-proof RAM.
4. **Tree:** aggregator outputs compose as inners to the next level (`monolith-verifies-monolith`,
   self-recursion — R5). The open size-stability question: an aggregator proof is a q96 proof of a
   ~2^21-row AIR, so the level above it replays 96 queries of a *bigger* inner (more commit rounds → a
   bigger super-tile) — the per-level super-tile must not grow unboundedly. This is why K is kept small
   and why a fixed-size **wrap** (re-prove each aggregator output at a canonical small shape) is the
   likely stabilizer; R5 measures whether the monolith is size-stable under self-composition or needs a
   wrap circuit.
5. **`MAX_AGG_TILES`** mirrors `MAX_BATCH_TILES = 64` at the ≥100-bit floor; a block beyond one tree emits
   multiple roots (same as the batch's multiple-proof rule).

**Honest hardware requirement:** the recursive prover targets a **≥128 GB server** (256 GB for K≥2
aggregators). The node/consensus seam (the block tx-root + one `verifyBatch`-shaped check) is **unchanged**
— so the batch path (`batch_joinsplit_air`, proven-100, ≤64 tx/proof) carries production until the
recursive prover is deployed; recursion is the trustless-per-user / parallel-proving scale-out, slotted
underneath the same seam.

## 4. Verification

- Soundness: `proven_security_bits` gates each level's config at ≥100 (the same test the batch uses);
  the aggregator config reuses `production_fri` (q96/lb4/pow16/cap6). A `recursion_proven_security_floor`
  test (R4) asserts the aggregator level clears 100 bits at its height.
- Cost: `phase8_joinsplit_query_curve` (this doc's table) is the measured basis; re-run on the target
  server to confirm the 2^20 / ~116 GB single-inner point before deployment.
- The reduced-query milestones (`phase8_joinsplit_monolith` at 4q) stay as the always-runnable
  dev-box correctness gate; the full-query proof is a server-only `--ignored` measurement.
