# HTLC circuit — constraint-accounting self-audit

A column-by-column and constraint-by-constraint review of `lattica-prover-p3::htlc_air`, the v3
shielded-HTLC spend circuit, arguing that **every HTLC-specific column is constrained** and **no new
binding is vacuous**. `htlc_air` is a superset of the audited `joinsplit_air`: it keeps the entire
join-split statement intact (read `docs/joinsplit-constraint-audit.md` first — ownership, the
two-permutation commitment, membership/root, balance/range, the PLAIN nullifier, fee, mint, and the
multi-asset substrate's hidden `asset` all carry over unchanged) and **adds** the machinery to spend an
HTLC note. This document covers only the **deltas**; everything not listed here is the join-split audit.

This is a self-audit to feed the v3 external review, not a substitute for it.

## What an HTLC note is (the new note shape)
A note's commitment is the same two-permutation chain as v1, with two committed lanes added by v3:
`cm = H₂(H₁(DOM_CM ‖ owner(4) ‖ value ‖ rho0 ‖ rho1) ‖ rcm0 ‖ rcm1 ‖ asset ‖ note_type)` — lane 6 =
`asset` (the substrate's hidden asset id), **lane 7 = `note_type` ∈ {PLAIN=0, HTLC=1}** (v3).
- For a **PLAIN** note, `owner = recipient = H(DOM_OWN ‖ nk0 ‖ nk1 ‖ div)` (exactly v1).
- For an **HTLC** note, `owner = htlc_root = MD-chain(DOM_HTLC ‖ redeem_tag ‖ refund_tag ‖ hashlock ‖
  timeout)` — a 4-block Merkle–Damgård chain committing the two party tags, the hashlock, and the
  timeout. The HTLC terms are thus bound into the commitment (and so into the anchor): they cannot be
  changed after the note is created.

The frozen `(N_IN, M_OUT) = (2, 2)` shape is unchanged; an HTLC spend uses one HTLC input + one PLAIN
dummy. Span layout: `SPAN_BLOCKS = 8 + DEPTH` (DEPTH = 32); the 4 `htlc_root` blocks sit at the **span
end** (blocks `4+DEPTH … 7+DEPTH`) so the recipient/chain/membership block-adjacency of the join-split
layout is untouched — the computed `htlc_root` is carried back into `commit_a` through the persistent
`OWNER` columns (see #2). `WIDTH = 31`.

## Columns — what determines each (delta over join-split)

| col | name | determined by |
|---|---|---|
| 18 | `ASSET` | (substrate) global-persistent hidden asset id; pinned at every `commit_b` lane 6 ⇒ one asset per tx. Carries over from the substrate audit. |
| 19–22 | `OWNER0..3` | the note owner digest (recipient for PLAIN, `htlc_root` for HTLC), local-persistent over the span. Pinned **(a)** at the recipient link for PLAIN (`OWNER == own.out`, gated `rl·(1−note_type)`), **(b)** at the `htlc_root` chain output for HTLC (`OWNER == htlc_out`, gated `hr·note_type`), and read into `commit_a.in[1..5]` (the owner MUX, #5). |
| 23 | `NT` | `note_type`; local-persistent; boolean (#1); pinned into `commit_b` lane 7 (#3) ⇒ the path is bound to the committed note type. Gates every HTLC-only constraint. |
| 24–27 | `CLAIM0..3` | the claiming party's tag = `own.out = H(DOM_OWN ‖ nk ‖ div)` of the spender; local-persistent; pinned `CLAIM == own.out` (all notes) and matched to the mode-selected HTLC tag (#7). |
| 28 | `MODE` | spend mode (1 = redeem, 0 = refund); local-persistent; boolean (#6); gates the tag-match, hashlock bind, and timeout direction. |
| 29 | `TIMEOUT` | the committed timeout; local-persistent; pinned `TIMEOUT == htlc block-3 input lane 4` (#9) and range-checked `< 2^BITS` (#10) ⇒ a sound comparison operand. |
| 30 | `DIFF` | the timeout-compare slack (`redeem: timeout−height−1`, `refund: height−timeout`); range-checked `≥ 0` (#10). Read only at its range seed. |

Intentionally-free witnesses (unchanged philosophy): `rcm0/rcm1`, output trapdoors, and — for a PLAIN
note — `redeem_tag/refund_tag/hashlock/timeout` (ignored; their constraints are `note_type`-gated off).
`div` is the spender's diversifier, free for the same 2¹²⁸-preimage reason as v1.

## Constraint families — what each enforces, why non-vacuous (delta over join-split)

All join-split families (round schedule, local-persistent constancy, `pos_acc`/A1, `val_acc`/balance,
range/A3, ownership, recipient link, commitment, membership, root, PLAIN nullifier, fee, mint, asset
equality) are **unchanged** and not repeated. New/changed:

1. **`note_type` (NT) boolean + commitment binding.** `NT·(1−NT)=0` (boolean) and `NT` is pinned into
   `commit_b` lane 7 for inputs and outputs ⇒ the committed note type equals the column that gates the
   spend logic. Non-vacuous: a prover cannot claim PLAIN-spend a note committed as HTLC (or vice
   versa) — the lane-7 binding + persistence forces `NT` to the committed value, and `NT` is the gate
   on every branch below.
2. **`htlc_root` chain (HTLC owner).** Four blocks at the span end: block 0 input =
   `[DOM_HTLC,0,0,0, redeem_tag]` (domain tag pinned, A2; capacity lanes pinned 0), blocks 1–3 are
   merge-shaped (`chain ‖ data`) absorbing `refund_tag`, `hashlock`, then `[timeout,0,0,0]`; the chain
   links pin each block's input `[0..4] = previous block's output`. Output of block 3 = `htlc_root`.
   Non-vacuous: `P_HTLC_IN0/_LINK/_IN1/_IN2/_IN3/_ROOT` fire on exactly those rows; the capacity-lane
   pins prevent absorbing extra data. ⇒ `htlc_root` is the real MD-chain over the four terms.
3. **Owner MUX → `commit_a`.** `commit_a.in[1..5] == OWNER` (always). `OWNER` is pinned to the
   recipient for PLAIN (`rl·(1−NT)·(OWNER − own.out) = 0`) and to `htlc_root` for HTLC
   (`hr·NT·(OWNER − htlc_out) = 0`). Non-vacuous + **mutually exclusive**: the two pins are gated by
   `(1−NT)` and `NT`, so exactly one is active; `OWNER` persistence carries the span-end `htlc_root`
   back to `commit_a` without violating block adjacency. ⇒ the commitment's owner slot is the recipient
   (PLAIN) or the term-committing `htlc_root` (HTLC).
4. **Tag-match = HTLC access control** (`CLAIM`). `CLAIM == own.out` (all notes) pins the claiming
   party's tag to `H(DOM_OWN ‖ nk ‖ div)` of the spender. Then, **gated by `NT` and `MODE`**:
   `h0·NT·MODE·(redeem_tag − CLAIM) = 0` (redeem ⇒ spender owns `redeem_tag`) and
   `h1·NT·(1−MODE)·(refund_tag − CLAIM) = 0` (refund ⇒ spender owns `refund_tag`). Non-vacuous: only a
   party whose `nk` reproduces the mode-selected tag can spend; since `redeem_tag/refund_tag` are
   committed in `htlc_root` (#2) and `CLAIM` is the real `own.out`, impersonation is a 2¹²⁸ preimage.
   This is the soundness of *who* may redeem vs refund.
5. **Redeem hashlock binding** (the cross-chain atomic link). Gated `h2·NT·MODE`: the HTLC note's
   committed `hashlock` (block-2 input lanes 4..8) `== pis[redeem_hashlock]`. Non-vacuous: on a redeem
   the public `redeem_hashlock` — which the node sets to `SHA256(revealed preimage)` — must equal the
   committed hashlock, so a redeem is valid **iff** the spender revealed a preimage hashing to the
   committed lock. (SHA256 itself is computed by the node from the publicly revealed preimage and bound
   as a public input; the circuit proves equality only — see Residuals.) Not bound on refund (`MODE=0`).
6. **Timeout compare** (the time-lock). `TIMEOUT == htlc block-3 lane 4` (#9 binds the operand to the
   committed timeout). `DIFF` is computed, gated by `NT`, as
   `DIFF = MODE·(TIMEOUT − height − 1) + (1−MODE)·(height − TIMEOUT)` where `height = pis[current_height]`,
   and **both `TIMEOUT` and `DIFF` are range-checked `< 2^BITS`** via the shared REM/RBIT machinery
   (windows placed in the otherwise-free span-end htlc region). With `TIMEOUT` range-bounded, `DIFF`
   range-bounded (`⇒ DIFF ≥ 0`, no field wrap), and `height` a node-pinned public input bounded
   `< 2^BITS`, the comparison is exact: `DIFF ≥ 0` holds **iff** redeem ⟺ `height < timeout`, refund ⟺
   `height ≥ timeout`. Non-vacuous: `P_TO_SEED/P_DIFF_SEED` seed the two range windows; the
   `MODE`-gated `DIFF` formula forbids using the wrong direction; range-checking `TIMEOUT` closes the
   wrap-around forgery (a near-`p` timeout that would otherwise make `DIFF` small).
7. **`note_type`-gated nullifier MUX** — *the critical v3 soundness property.* The nullifier input is
   selected by `NT`:
   - PLAIN (`NT=0`): `nf = H(DOM_NF ‖ nk0 ‖ nk1 ‖ rho0 ‖ rho1 ‖ pos)` — exactly the v1 (`nk`-based)
     nullifier, for cross-circuit consistency with `joinsplit_air`.
   - HTLC (`NT=1`): `nf = H(DOM_NF_HTLC ‖ owner(4) ‖ rho0 ‖ rho1 ‖ pos)` — **owner-based, NOT
     `nk`-based, and independent of `MODE`/party.**
   Why this matters: while an HTLC note sits in the tree, **both** spend windows are reachable (the
   redeem party before `timeout`, the refund party after). A `nk`- or `MODE`-dependent nullifier would
   yield a *different* `nf` for the redeem spend than the refund spend ⇒ the same note could be spent
   once in each window ⇒ **double-spend**. Binding `nf` to the `owner` (the `htlc_root`, identical in
   both modes) and `rho`/`pos` (identical for the one note) guarantees **one note ⇒ exactly one
   nullifier**, regardless of who spends it or how. Non-vacuous: the MUX is gated by `NT`/`(1−NT)` so
   exactly one nullifier shape is pinned into the public `nf_i`; `owner` is the persistent `OWNER`
   column tied to the committed note (#3), and `rho`/`pos` are tied as in v1.

## Public-output soundness chain (delta)
New public inputs `current_height` and `redeem_hashlock` (4 felts), appended after `tx_binding`:
- `redeem_hashlock` ← bound (redeem only) to the committed `hashlock` inside `htlc_root` (#5) ←
  `htlc_root` chain (#2) ← committed in `cm` via the owner MUX (#3). So the public hashlock equals what
  the note was locked with; the node ties it to `SHA256(preimage)` off-circuit.
- `current_height` ← read in the `DIFF` formula (#6); `DIFF`/`TIMEOUT` range-bounded ⇒ the timeout
  window is exactly decided. `current_height` is **not** prover-controlled (it is a public input the
  node pins to the consensus height; see Residuals).
- `nf_i` ← the `note_type`-gated MUX (#7): for an HTLC input, the owner-based `nf` over the committed
  `htlc_root`/`rho`/`pos`.
- Everything else (`anchor`, the other `nf`, `out_cm_j`, `fee`, `mint`, `tx_binding`) is the join-split
  chain, unchanged. `tx_binding` (Fiat–Shamir) covers the whole body incl. the revealed preimage on the
  node side, so the atomic-swap secret can't be swapped.

## Residuals / assumptions (for the auditor)
- **SHA256 is out-of-circuit (by design).** The hashlock is SHA256(preimage), shared with the BTC leg.
  The circuit does **not** compute SHA256; the node computes `redeem_hashlock = SHA256(revealed
  preimage)` and passes it as a public input, and the circuit proves only `committed_hashlock ==
  redeem_hashlock` (#5). The preimage rides the tx body and is bound by `tx_binding`. Trust: the node's
  SHA256 + the public-input binding. This is the deliberate v3 simplification (see the v3 plan).
- **`current_height` is a node-pinned public input**, not prover-controlled. The node sets it to the
  block height the tx is validated at (`Chain.applyHtlc` rejects any tx whose `current_height ≠` the
  consensus height), and it is bounded `< 2^BITS` by the node. The circuit's timeout soundness assumes
  this bound on `height` (it range-checks the prover-chosen `TIMEOUT` and the derived `DIFF`, but treats
  the public `height` as node-trusted — the same trust the node already places on `mint`/`anchor`).
- **Single hidden asset per swap leg** (substrate assumption): `input.asset == output.asset ==` the
  global `ASSET`; a leg is single-asset, so hiding the asset = commit it + prove equality. No partition
  gadget (out of v3 scope).
- **`htlc_root` MD-chain is structurally separated** from the 2-to-1 Merkle merge: the merge is
  untagged over digests, while `htlc_root` is `DOM_HTLC`-tagged at block 0 and absorbs fixed-shape data
  — a cross-structure collision needs a Poseidon2 collision (in scope of the Poseidon2 review).
- **`rho` uniqueness per note** is a note-creation invariant (protocol side), as in v1 — and is what
  makes the owner-based HTLC nullifier (#7) unique per note.
- **Padding / free cells** (`bit`, `rem`/`rbit` outside windows, `DIFF` outside its seed, PLAIN-note
  HTLC-term witnesses) are unconstrained junk that no active selector reads.
- Fixed `(N_IN, M_OUT) = (2, 2)`; an HTLC spend is one HTLC input + one PLAIN dummy (zero-value).
