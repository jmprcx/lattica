# Arithmetization-hash analysis — Poseidon2 vs Monolith vs Tip5

> **Pre-v1 forward-looking analysis — not part of the current audit artifact.** Evaluates whether to
> replace the in-circuit / on-chain hash before v1 freezes it. Start at [`AUDITORS.md`](AUDITORS.md).

**Decision: keep Poseidon2 for v1.** Poseidon2 is the only one of the three candidates that fits lattica's
proving stack *as it is today*. Monolith and Tip5 are faster designs, but both buy their in-circuit speed
with a **lookup argument** — and lattica's single-AIR `p3-uni-stark` prover has no lookup argument to run
against (§4). Adopting one is a larger, wire-breaking change than the hash swap it would enable, so it is a
**v-next prover-architecture** question, not a v1 hash question (§7). Separately, the dominant proving cost
is the depth-32 Merkle path, which is a **tree-geometry** lever largely independent of the hash family
(§8).

---

## 1. Why evaluate this now

We are **pre-v1**. The hash is wired into the note commitment, the nullifier, the note tree, and the block
tx-root — and mirrored byte-for-byte on-chain (`src/poseidon2.zig`) and pinned to consensus via
`postcard(Proof<MyConfig>)` (`lattica-prover-p3/src/config.rs`). Once v1 ships, changing it is a **consensus
hard fork** that re-hashes the entire shielded pool. Pre-v1 is the only cheap window to reconsider it, which
is why the "can we go faster / build a *poseidon3*" question is worth answering properly rather than
dismissing.

This is also not lattica's first arithmetization-hash decision: the project already migrated once, from
**Winterfell / Rescue-Prime `Rp64_256`** to **Plonky3 / Poseidon2** (`docs/framework-decision.md`,
`docs/protocol-v1-decisions.md §M6`). This document is the same shape of decision, made deliberately.

The bottom line up front: **don't hand-roll a "poseidon3"** — a novel permutation in a value-bearing
shielded system is the textbook roll-your-own-crypto trap, and Poseidon2 is *already* the vetted successor
to Poseidon (2019 → 2023). The real question is whether an existing, peer-reviewed alternative (Monolith or
Tip5) is worth adopting. The answer, for the current stack, is no — for a concrete structural reason, not a
conservative reflex.

## 2. How Poseidon2 is used here — the cost map

Poseidon2 (`Poseidon2Goldilocks<8>`) wears two hats, both over **Goldilocks** (p = 2⁶⁴ − 2³² + 1); the
digest is **4 field elements = 256 bits → 128-bit collision resistance**.

**Layer A — the proof system** (`config.rs`): `MyHash = PaddingFreeSponge<Perm,8,4,4>` hashes FRI/Merkle
leaves, `MyCompress = TruncatedPermutation<Perm,2,4,8>` compresses inner nodes, `Challenger =
DuplexChallenger<Val,Perm,8,4>` is the Fiat-Shamir transcript. These are wire-pinned to consensus.

**Layer B — the statement** (`spend_common.rs`, `poseidon2_air.rs`, `domains.rs`): every hash in a spend is
a domain-separated Poseidon2 — `recipient_of` (1 permutation), `commit` (2), `nullifier` (1), `merge` (1),
and the membership `fold` (DEPTH = 32 merges).

**Where the cost concentrates.** In the circuit, one permutation is **32 trace rows** (`poseidon2_air.rs`:
BLOCK = 32, width 8, 8 full + 22 partial rounds, x⁷ S-box). A single join-split runs ~**76 meaningful hash
permutations**, and the split is lopsided:

| Category | Perms | Share |
|---|---|---|
| **Merkle membership** (2 inputs × depth-32) | **64** | **84% of hashing, ~50% of the 2¹² trace** |
| Note commitments (in + out) | 8 | |
| Ownership / nullifiers | 4 | |

The join-split trace is **~95% Poseidon rows by used-block count** (80 used blocks → padded to 128 =
4096 = 2¹² rows; the non-hash logic — value balance, range, nullifier binding — is a thin wrapper on the
non-state columns). Two consequences frame everything below:

1. **A cheaper permutation *would* help — linearly.** Hashing is not a rounding error here; it is the trace.
2. **But the cost is the depth-32 Merkle authentication path, not the note/nullifier hashes.** That is a
   property of the *tree*, not the *hash family* (§8).

## 3. The candidates

**Poseidon2** (Grassi–Khovratovich–Schofnegger, 2023). A substitution-permutation network: external (full)
rounds with a light MDS built from 4×4 blocks + a circulant sum, internal (partial) rounds with a cheap
diagonal matrix, `x⁷` S-box over Goldilocks. **Purely algebraic** — every round is a polynomial constraint.
lattica uses the **standardized p3 instance** (`default_goldilocks_poseidon2_8`, published round constants),
so its parameters are vetted and widely deployed (Plonky3 and many downstream systems). Constraint degree is
~7, inside the documented ≤16 budget at `LOG_BLOWUP = 4`.

**Monolith** (Grassi–Khovratovich–Roy–Schofnegger, 2023). Designed for Goldilocks and Mersenne-31. Each
round is **Concrete** (MDS/circulant linear) + **Bricks** (a low-degree feed-forward) + **Bars** — the
nonlinear layer that decomposes selected state elements into small chunks and applies a fixed **lookup**
S-box per chunk. The Bars are constant-time and, crucially, **lookup-friendly**: Monolith is engineered to
be *both* very fast in plain (competitive with SHA-3, well ahead of Poseidon2, because it avoids a
high-degree S-box) *and* cheap in-circuit **on a proof system that supports lookups**. It is newer, with
correspondingly less deployment and third-party cryptanalysis than Poseidon2.

**Tip5** (Szepieniec, 2023; Triton VM / Neptune Cash). Goldilocks, **state width 16** (rate 10). Its S-box
layer is *split*: a few lanes go through **split-and-lookup** (decompose a 64-bit element into bytes, apply
an 8-bit lookup S-box per byte, recombine), the rest through `x⁷`. Like Monolith, the lookup lanes are the
whole point and assume a lookup-capable STARK (Triton has table lookups). Two fit notes for lattica: its
width-16 state is tuned for **sponge hashing of longer strings**, a **poorer fit for the 2-to-1 Merkle
compression** (4+4→4) that dominates our workload; and it is deployed but in a narrower ecosystem.

*Context (not scored):* **Rescue-Prime** — the conservative, high-margin algebraic hash and lattica's own
predecessor (`Rp64_256`); very few rounds but each is costly in plain (inverse S-box), no lookups.
**Anemoi / Griffin** — other purely-algebraic families; like Poseidon2 they fit an algebraic stack but offer
no lookup-driven speedup to justify a migration.

## 4. The decisive constraint — this stack has no lookup argument

Monolith and Tip5 are faster *because of their lookups*. lattica's prover cannot run a lookup argument, so
that speed is not available here. This is the linchpin, and it is a hard fact about the current stack, not a
judgement call:

- lattica proves on **single-AIR `p3-uni-stark` 0.6.1** (`config.rs` imports `prove`/`verify`;
  `Cargo.toml` pins the p3 0.6.1 family). Every circuit is one AIR, one trace.
- The `Proof` commits to **trace + quotient + optional ZK-mask only** — there is no permutation/multiplicity
  commitment and no lookup-challenge round. The prover samples exactly two challenges (α for constraint
  batching, ζ for the opening point).
- The constraint folders implement only `AirBuilder`/`ExtensionBuilder` — i.e. `assert_zero` /
  `assert_zero_ext`. A LogUp-style lookup needs a `PermutationAirBuilder`; that trait exists in `p3-air` but
  is **unused scaffolding** (only `FilteredAirBuilder` and the debug checker implement it), and the real FRI
  folders do not. An AIR literally cannot call `builder.permutation()` on the proving path — it would not
  type-check.
- A working LogUp implementation (`p3-lookup`) exists in the ecosystem but is **not a lattica dependency**
  (absent from `Cargo.toml` and `Cargo.lock`).

So a lookup-based hash has two — both losing — ways into this stack:

- **(a) Arithmetize the lookups as pure constraints.** A byte-decomposition S-box expressed algebraically is
  a very high-degree / range-decomposition constraint that blows past the documented **degree-≤16 budget**
  at `LOG_BLOWUP = 4`, forcing a larger blowup (bigger LDE, slower prover). This is exactly the cost Monolith
  and Tip5 were designed to *avoid* — their advantage evaporates and then some.
- **(b) Adopt a lookup-capable prover** (pull in `p3-lookup`/LogUp or a multi-table architecture). This adds
  a permutation-trace commitment, extra opened values, and a new challenge round — i.e. it **changes the
  `Proof` shape**, which is consensus- and wire-pinned (`config.rs`, the Zig node seam, `soundness-budget.md`).
  That is a **bigger, more invasive change than the hash swap it enables**.

By contrast, **Poseidon2's `x⁷` is a single `assert_zero` transition** — precisely what `p3-uni-stark`
provides, with nothing added. It is the natural fit for the stack, not a compromise.

## 5. Decision matrix

| Axis | **Poseidon2** | **Monolith** | **Tip5** |
|---|---|---|---|
| Needs a lookup argument? | ✅ No — purely algebraic | ❌ Yes — the Bars layer | ❌ Yes — split-and-lookup lanes |
| Fit with current `p3-uni-stark` | ✅ **Native** (`assert_zero` x⁷) | ❌ No lookup argument exists here | ❌ No lookup argument exists here |
| Plain / native speed (Zig node) | ⚠ Moderate (high-degree S-box) | ✅ Fastest (constant-time lookups)¹ | ✅ Fast (byte-lookup lanes)¹ |
| Constraint degree vs the ≤16 budget | ✅ deg-7, fits | ❌ lookups-as-constraints blow it | ⚠ x⁷ lanes fit; lookup lanes blow it |
| Goldilocks fit | ✅ native | ✅ native | ✅ native (designed for it) |
| State width & 2-to-1 Merkle fit | ✅ width-8, ideal for 4+4→4 | ✅ width-8 Goldilocks, good | ⚠ width-16, tuned for sponge, not 2:1 |
| Security maturity / cryptanalysis | ✅ most-analyzed, standardized | ⚠ newer, less third-party analysis | ⚠ newer, narrower deployment |
| Adoption | ✅ Plonky3 + broad | ⚠ limited | ⚠ Triton VM / Neptune |
| Migration blast radius from here | — (incumbent) | ❌ hash **+ lookup prover + wire fork** | ❌ hash **+ lookup prover + wire fork** |

¹ Plain-speed advantages are as **claimed in the literature**; they are not measured in this stack (neither
is implemented here), and — decisively — they are unrealizable in-circuit without a lookup argument.

## 6. Recommendation — keep Poseidon2 for v1

- **It fits the stack as-is.** Purely algebraic, degree-7, native to single-AIR `p3-uni-stark`. The
  alternatives require infrastructure lattica does not have and cannot get without breaking the wire format.
- **It is the vetted choice.** The standardized p3 Goldilocks-8 instance with published constants is the
  most-analyzed and most-deployed of the three — the right posture for a value-bearing shielded protocol
  heading into an external audit.
- **The blast radius of a swap is large and consensus-critical.** A hash change touches the permutation AIR
  and its round constraints re-inlined across **≥5 circuits**; **3 wire-pinned proof-system roles**
  (`MyHash`/`MyCompress`/`Challenger`) across **5 config builders**; a **full second implementation in Zig**
  (8 hash call sites + 5 KATs + `dump_p2` + 2 batch KAT dumps); the entire **11-file recursion verifier**
  (its transcript + FRI-Merkle gadgets must match the inner PCS hash); and **75 `native_permute` call sites
  across 16 files** — all behind a consensus hard fork. The bar for paying that is a *realized* win, and
  there is none here.

## 7. What would flip this — the forward path

The verdict is contingent on one thing: **the prover has no lookup argument.** If that changes, so does the
answer. Sequenced honestly:

1. **The circuit gates the hash — not the node.** The on-chain hash must match the circuit byte-for-byte, so
   the node can never adopt a faster hash on its own. Only the *circuit's* capability matters, and the
   circuit's capability is set by the prover.
2. **If a v-next prover gains a lookup argument** — by pulling in `p3-lookup`/LogUp or moving to a
   multi-table / interaction architecture — **then Monolith becomes the strongest candidate**: width-8
   Goldilocks (ideal for 2-to-1 Merkle compression), fastest plain, lookup-native. Tip5 is the weaker fit
   for lattica specifically (its width-16 targets sponge hashing, not our Merkle-dominated workload).
3. **Order of operations: decide the prover architecture first; the hash follows.** A lookup argument is a
   proof-system decision with its own soundness accounting and wire-format implications; the hash choice is
   downstream of it. The **recursion track** (`docs/recursion-aggregation-status.md`), which already reasons
   about tables and could motivate a lookup-capable prover, is the most plausible driver — but it is
   research, off the production path, and not a v1 input.

In short: revisiting the hash is a **v2+ prover-architecture** exercise, gated on adopting lookups, not a v1
task.

## 8. The bigger levers (hash-agnostic)

If the underlying goal is "prove faster," the hash family is not where the largest wins are — the
**depth-32 Merkle authentication path (64 of ~76 permutations, ~50% of the trace)** is. That cost is set by
tree geometry and compression width, both largely independent of which S-box family the hash uses:

- **Fewer / cheaper Merkle compressions.** The membership cost is `inputs × depth`. Reducing tree depth
  (fewer supported leaves, or higher arity) or folding more per permutation (a wider-state compression)
  attacks the 50% directly. Note the real trade-off: higher arity shortens the path but widens each node's
  compression, so it is not a free halving — and a *wider permutation state* is itself a hash-parameter
  change (this is the one place Tip5's width-16 could actually help, *if* the stack had lookups — full
  circle to §4).
- **Cross the power-of-two boundary.** The join-split trace is 80 used blocks padded to 128 = 2¹². Shaving
  below 64 used blocks (a real structural reduction, e.g. a shallower tree) halves `HEIGHT` to 2¹¹ — a ~2×
  prove win from geometry alone, no hash change.
- **GPU.** The prover already runs Poseidon2 on GPU at ~4× the AVX2 CPU path (`docs/gpu-acceleration.md`),
  entirely under the unchanged verifier. This is delivered, and orthogonal to the hash choice.

These are also pre-v1 decisions (any AIR change alters fingerprints and the wire format), but none requires
inventing or porting a new hash or a new proof system — a strictly smaller, lower-risk lever than a hash
migration.

## 9. See also

- `docs/soundness-budget.md` — the ~103-bit-proven / ~127-bit-conjectured accounting the hash feeds into.
- `docs/framework-decision.md`, `docs/protocol-v1-decisions.md §M6` — the prior Rescue-Prime → Poseidon2
  migration (the precedent for this decision).
- `lattica-prover-p3/src/config.rs`, `.../poseidon2_air.rs`, `.../spend_common.rs` — the incumbent
  implementation and its cost structure.
- Papers: *Poseidon2* (Grassi–Khovratovich–Schofnegger, 2023); *Monolith* (Grassi–Khovratovich–Roy–
  Schofnegger, 2023); *The Tip5 Hash Function for Recursive STARKs* (Szepieniec, 2023).
