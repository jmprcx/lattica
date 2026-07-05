# Batch circuit — constraint-accounting self-audit ("one proof per block")

A constraint-by-constraint review of `lattica-prover-p3::batch_joinsplit_air` and `batch_htlc_air` —
the **batch aggregation** circuits that prove *K* transactions as ONE block proof binding a single
32-byte block **tx-root**. This audits the **delta over the single-tx circuits**; the per-tile spend
body is *inherited verbatim* (§2), so read `docs/joinsplit-constraint-audit.md` and
`docs/htlc-constraint-audit.md` first — this doc argues the batch-specific surface (tiling isolation,
the tx-root fold, the public-input binding, and the one load-bearing trust seam) is sound and
non-vacuous. Self-audit feeding the external review, not a substitute for it. Companion:
`docs/audit-readiness-status.md`.

## 1. Layout — tiles, padding, the added columns

**A tile is one full single-tx trace, stacked vertically.** `TILE_HEIGHT = HEIGHT = 4096` rows
(join-split *and* HTLC — both `USED_BLOCKS.next_power_of_two() = 128` blocks × 32) — see
`batch_joinsplit_air.rs:135`, `joinsplit_air.rs:130-132`. `build_batch_trace` writes tile *t* at
row-offset `t·4096` (`batch_joinsplit_air.rs:301-341`), so **K scales rows, not columns**: K tiles =
`K·4096` rows at fixed width **49** (join-split) / **71** (HTLC). K = 64 ⇒ 2¹⁸ rows.

**Padding to a power of two.** `padded_tiles(n) = n.max(1).next_power_of_two()`
(`batch_common.rs:37-39`), capped at `MAX_BATCH_TILES = 64` (`batch_common.rs:34`) — the ≥100-bit
proven-soundness floor, enforced in both provers (`batch_joinsplit_air.rs:346-349`) **and** both ABI
entry points (`lib.rs:594-596, 660-662`). A **dummy/padding tile is a REAL balanced 0-value spend**
(`dummy_witness`, `batch_joinsplit_air.rs:79-99`: `nk=0`, `value=0`, `rho=rcm=0`, all-zero
membership), *not* a zeroed row-block — so it satisfies every per-tile constraint like a real tile and
needs no special-case gating (`batch_joinsplit_air.rs:75-78`). Its statement digest `dummy_sk` is a
fixed public constant (`:103-105`).

**Batch-added columns** (single-tx width, then per-tile staging, then one global ROOT chain —
`batch_joinsplit_air.rs:141-148`):

| col(s) | name | what determines it |
|---|---|---|
| `S_ANCHOR, S_NF, S_OUTCM, S_FEE, S_MINT` | staged statement fields | equal to the tile's genuinely-computed spend values (the `cur == statement[..]` equalities *inside* `eval_spend`: anchor `joinsplit_air.rs:464`, nf `:482`, out_cm `:495`, fee `:500`, mint `:503`), held tile-constant by tile-persistence (§3), read by the fold (§4). |
| `S_TXBIND` | staged `tx_binding` | **free** — `eval_spend` never constrains it; prover-chosen, bound *only* into the tx-root (§5 seam). |
| `ROOT` (4 lanes) | running block tx-root | global-persistent MD chain: 0 at the first row, updated once per tile, final == the public input (§4 groups 6–8). |

## 2. Per-tile spend soundness is *inherited verbatim*

Each tile reuses **`joinsplit_air::eval_spend` (resp. `htlc_air::eval_spend`) with no tile-edited
fork** — the single-tx AIR calls `eval_spend(builder, pis, ZERO)` (`joinsplit_air.rs:332-336`), the
batch calls the *same function* with the tile's staging columns and `tile_last` as the boundary
selector (`batch_joinsplit_air.rs:237-261`). This is mechanically guaranteed: the constraint-fingerprint
oracle pins JoinSplitAir at `(19,33,26,81,8,…)` and JoinSplitBatchAir at `(49,45,4,167,8,…)`
(`constraint_fingerprint.rs:120-124`) — the batch's 167 constraints are the 81 per-tile constraints
(unchanged) plus the tiling + fold. **So the whole per-tile argument of `joinsplit-constraint-audit.md`
/ `htlc-constraint-audit.md` carries over unchanged** (ownership, membership, nullifier + A1 position
binding, value balance A3, domain separation A2, one hidden asset per tx, the `rho1` persistence). The
audit's new obligations are only §3–§5 below.

## 3. Tiling isolation — no cross-tile leakage

`tile_last = p[P_TILE_LAST]` is a periodic one-hot at row `4095`, repeated every tile
(`batch_common.rs:94`). It appears in exactly the persistence gates that would otherwise let one tile's
secrets bleed into the next:

- **Local-persistent key/randomness/value** `NK, NK1, RHO, RHO1, VAL` are frozen by
  `1 − P_REGION_LAST − tile_last` (`joinsplit_air.rs:383-386`) and **`ASSET`** by `1 − tile_last`
  (`joinsplit_air.rs:390`). Because `tile_last` is in every one of these gates, the `4095→4096`
  transition into the next tile is *unconstrained* — tile *k*'s spend key, note randomness, value, and
  hidden asset cannot carry into tile *k+1*. (`P_REGION_LAST`'s last one-hot is row 2559, disjoint from
  `tile_last` at 4095, so the sum is a clean 0/1.) **Non-vacuous:** the `rho1` double-spend note of the
  single-tx audit still holds *within* a tile, and the boundary freeing means each tile is a
  self-contained spend — a prover cannot reuse tile *k*'s authenticated key to authorize tile *k+1*.
- **Staged statement columns** `{S_FEE,S_MINT}∪S_ANCHOR∪S_TXBIND∪S_NF∪S_OUTCM` are held tile-constant
  by `eval_tile_persistence` gated by `tile_persist = 1 − tile_last` (`batch_common.rs:108-118`,
  `batch_joinsplit_air.rs:268-287`) — constant across the tile so the fold reads a stable statement,
  free at the boundary so tiles differ.

## 4. The tx-root fold — the batch-specific soundness core

Each tile folds its statement into a global Merkle–Damgård **block tx-root**, in the tile's trailing
padding (fold blocks 120–127, rows 3840–4095; join-split uses blocks 0–79, so no overlap —
`batch_joinsplit_air.rs:152-155`). One shared emitter `eval_txroot_fold` (`batch_common.rs:131-190`)
enforces eight groups; the **Poseidon2 permutation of every fold block is enforced by the same audited
period-32 round constraints inside `eval_spend`** (`joinsplit_air.rs:363-376`, which apply to *every*
row including padding), so each in-circuit `s_k` and `root_k` is a genuine Poseidon2 output — the fold
emitter only pins the *input-lane injection* and the *chaining*:

1. **Chunk injection** — at each s_k block input, lanes `[DIGEST..2·DIGEST)` equal the staged chunk;
   a `None` lane is pinned to `0` (`batch_common.rs:144-152`). The chunk table `fold_chunks()`
   (`batch_joinsplit_air.rs:180-193`) is the in-circuit twin of native `statement_chunks`
   (`:60-73` = `anchor ‖ nf_i ‖ out_cm_j ‖ [fee,mint,0,0] ‖ tx_binding`, 7 chunks).
2. **Block-0 IV** — low lanes pinned to `[DOM_TXROOT,0,0,0]` (`batch_common.rs:153-158`).
3. **s_k MD link** — block output lanes `0..4` → next block input lanes `0..4` (`:159-163`).
4. **s_k → root handoff** — last s_k output → root-block input lanes `4..8` (`:164-168`).
5. **root-in bind** — root-block input lanes `0..4` == the running `ROOT` column `root_{k-1}` (`:169-173`).
6. **IV = 0** — `when_first_row`, `ROOT = 0` (`:174-177`).
7. **ROOT freeze/update** — `ROOT` constant except across the per-tile update transition, where it takes
   the root-block output; **ungated by `tile_last`**, so it carries across tile boundaries (`:178-185`).
8. **FINAL bind** — `when_last_row`, `cur[0..4] == pis[0..4]`: the last tile's root-block output row is
   exactly the global last row (`127·32+31 = 4095`), so this pins the final fold output to the single
   public tx-root (`:186-189`).

**Non-vacuous:** the periodic one-hots (`P_FOLD_IN+bi`, `P_SK_LINK`, `P_SK_TO_ROOT`, `P_ROOT_IN`,
`P_ROOT_UPDATE`) fire on exactly the intended rows (`append_batch_selectors`, `batch_common.rs:78-103`);
the emission order is the verifier's Horner-fold order (`batch_common.rs:126-130`); and the `None`-lane
must emit `sel·cur[DIGEST+k]` (not `…−0`) — a recorded landmine, since the fingerprint hashes the Debug
rendering (`batch_common.rs:25-26`).

## 5. Public-input binding + the one load-bearing trust seam

**The ONLY public input is the 32-byte block tx-root** (`num_public_values → DIGEST = 4`,
`batch_joinsplit_air.rs:216-218`; pinned publics = 4). Chain of custody: witness → `eval_spend` binds
`S_ANCHOR/S_NF/S_OUTCM/S_FEE/S_MINT` to computed spend values → tile-persistence holds them constant →
`eval_txroot_fold` group 1 injects them into the Poseidon2 MD chain → group 8 binds the final root to
the public input. The **node recomputes the same root purely from the block's declared transaction
statements** via `batch_root` (`batch_joinsplit_air.rs:107-121`) — no witnesses needed.

**What the proof certifies:** *"the public tx-root is the ordered Merkle–Damgård fold, from IV, of
`padded_tiles(n)` statements each of which satisfies the full single-tx spend relation."*

**The load-bearing trust seam (must be stated for the auditor):** the circuit does **not** itself label
which tiles are real vs dummy, nor does it publish *n*, the anchor, or the per-tx set — it folds
whatever staged statements the tiles carry, in trace order. The binding to **exactly the applied set**
comes from the **node** authoritatively recomputing `batch_root` over the block's canonical tx order +
the exact dummy count, and applying precisely those txs. Two consequences the review should confirm at
the node layer (`node.zig`, host-chain scope):
- `tx_binding` is a **free** staged column (`joinsplit_air.rs:505-506`) — bound only transitively via
  the node's root recompute, exactly as the single-tx `tx_binding` is a Fiat-Shamir public input. Its
  integrity is the node's root-recompute, not an in-circuit constraint.
- membership is per-tile against each tile's *own* staged `anchor` (there is no single block-level
  anchor public input); the node must apply each tx against the anchor it was proven under.

Everything the node needs to recompute the root is public (the declared statements); the proof adds
zero-knowledge over the hidden values/keys, exactly like the single-tx path.

## 6. Order / omission / swap resistance

- **Reorder** — `root_k = H(root_{k-1} ‖ s_k)` is order-committing; swapping tiles changes every
  downstream root (`batch_root_is_order_sensitive`, `batch_joinsplit_air.rs:514-519`).
- **Omit / add** — changes the fold length and `padded_tiles(n)`, hence the root; the node folds
  exactly its declared set + the right dummy count, so any mismatch rejects.
- **Padding ↔ real swap** — `dummy_sk` is a fixed public constant, and a real `s_k` cannot equal it
  (real anchors/nullifiers are non-zero); collision resistance rests on the 256-bit Poseidon2 chaining
  value / 128-bit collision resistance (`dummy_sk_is_deterministic_and_distinct_from_real`,
  `:508-512`; `spend_common.rs:48-50`).

## 7. HTLC batch — a mirror + two bound chunks

`batch_htlc_air` reuses the same `batch_common` machinery and reads its per-tile body from
`htlc_air::eval_spend` verbatim (`batch_htlc_air.rs:264`); width 71, pinned `(71,57,4,244,9,…)`. Deltas:
the HTLC statement is 31 elements (adds `PI_HEIGHT`, `PI_HASHLOCK`), so the fold absorbs **2 extra
chunks** `[current_height,0,0,0]` and `redeem_hashlock` (`batch_htlc_air.rs:47-62`, `FOLD_SK_BLOCKS=9`);
two extra staged columns `S_HEIGHT/S_HASHLOCK` join the tile-persistence set (`:244-260`). Crucially,
**unlike `tx_binding` these two are bound by the reused spend** — the hashlock at `htlc_air.rs:668,678`
and the range-checked height in the timeout compare at `:694-703` — so they are constrained both by the
spend and into the fold. The redeem/refund mode, owner MUX, tag-match, hashlock, and timeout live
entirely in `htlc_air::eval_spend` (audited by `htlc-constraint-audit.md`); the batch adds nothing
there. The HTLC boundary also frees `OWNER/NT/CLAIM/MODE/TIMEOUT` at `tile_last` (`htlc_air.rs:568-573`)
so mode/owner cannot leak across tiles. An HTLC `s_k` (9 blocks) cannot collide with a join-split `s_k`
(7 blocks), and the two batch circuits keep separate roots.

## 8. Evidence — what to run

- **Constraint-fingerprint pins** (`constraint_fingerprint.rs:120-124`) — any batch constraint-set drift
  trips the always-on `pinned_constraint_fingerprints` test.
- **Native-fold oracle** — `batch_dummy_padding_fold_matches_oracle` (`batch_joinsplit_air.rs:616-627`)
  builds a 3-real→4-padded trace and asserts the trace's final root-block output equals native
  `batch_root` limb-by-limb; `batch_root_folds_in_order_with_iv_and_padding` (`:484-495`).
- **Consensus KATs** — `batch_kat_dump` / `htlc_batch_kat_dump` pin `seq_statement_digest` + `dummy_sk`
  (the Zig node's `poseidon2.zig` must reproduce them or it is a chain fork).
- **Corrupted-trace / isolation** (`--ignored`) — `batch_corrupted_staged_{anchor,nullifier}_is_rejected`,
  `batch_within_tile_asset_tamper_is_rejected`, `batch_corrupted_fold_block_is_rejected`,
  `batch_per_tile_asset_isolation` (`batch_joinsplit_air.rs:637-691`); HTLC twins.
- **Security floor** — `batch_proven_security_floor` pins `proven_security_bits(1)=103`, ≥100 at 64,
  <100 at 128 (`:604-614`).
- **C-ABI** — `batch_c_abi_roundtrip` + `batch_abi_fail_closed` (`lib.rs:1154-1209`) and HTLC twins;
  and the **W2 verifier fuzz** `tests/fuzz_batch.rs` (2000-iter proof-byte + tx-root-byte mutation of a
  real 2-tile block through the C ABI, never-accept / never-panic).

**Residual for the external review:** the real/dummy tile split and the per-tile anchor application are
the **node's** responsibility (§5 seam) — confirm `node.zig`'s `applyBatch` recomputes `batch_root` over
its canonical set + exact dummy count and applies each tx against its proven anchor. The single deliberate
parameter (~103-bit proven soundness) and the requested Poseidon2 review apply to the batch exactly as to
the single-tx path (`docs/soundness-budget.md`).
