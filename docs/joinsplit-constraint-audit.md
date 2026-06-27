# Join-split circuit — constraint-accounting self-audit

A column-by-column and constraint-by-constraint review of `lattica-prover-p3::joinsplit_air`, arguing
that **every witness column is constrained** and **no binding is vacuous** (the failure mode an
external audit hunts for). This is a self-audit to feed the Phase-3 review, not a substitute for it.

Layout: `N_IN` input spans + `M_OUT` output regions + a fee region + a **mint region** + padding,
each block = 32 rows (one Poseidon2 permutation). `WIDTH = 18`. Selectors are period-32 (round
schedule) or full-length one-hots (region boundaries / bindings). The nullifier key `nk` is **two
field elements** (128-bit spend authority): limb 0 in col 9 (`nk`), limb 1 in col 16 (`nk1`). Note
randomness `rho`/`rcm` are likewise **two elements each** (128-bit); the commitment is therefore a
**two-permutation** Merkle-Damgård chain `cm = H₂(H₁(DOM_CM ‖ recipient(4) ‖ value ‖ rho0 ‖ rho1) ‖
rcm0 ‖ rcm1)` (`commit_a` block then `commit_b` block), so each input/output commitment spans two
blocks.

## Columns — what determines each

| col | name | determined by |
|---|---|---|
| 0–7 | Poseidon2 state | round constraints chain each block input→output; input rows pinned by the region bindings (below); output rows pinned where public (root/nf/out_cm). |
| 8 | `bit` | boolean at each membership link; read only as `next.bit` at link rows. Elsewhere unread (free). |
| 9 | `nk` | nk limb 0; local-persistent (constant in span); pinned at the ownership input (lane 1) **and** the nullifier input (lane 1) ⇒ ties ownership↔nullifier key. |
| 16 | `nk1` | nk limb 1; local-persistent; pinned at the ownership input (lane 2) **and** the nullifier input (lane 2) — symmetric to col 9 (128-bit `nk`). |
| 10 | `rho` | rho limb 0; local-persistent; pinned at `commit_a` (lane 6) **and** the nullifier input (lane 3) ⇒ ties commitment↔nullifier. |
| 17 | `rho1` | rho limb 1; local-persistent; pinned at `commit_a` (lane 7) **and** the nullifier input (lane 4). **Must be persistent** — else a prover could use one rho1 in the commitment and another in the nullifier, forging a second nullifier for one note (double-spend). |
| 11 | `val` | local-persistent; pinned at `commit_a` (input value), `out_a` (out value), fee input (fee), **mint input (mint)**; consumed by the accumulator + range. |
| 12 | `pos_acc` | reset 0 at span start, `+= bit·2^d` at each link, constant else; pinned into the nullifier input (lane 5) ⇒ **A1**. |
| 13 | `val_acc` | 0 at row 0; `+val` at each commit, `+val` at the mint row, `−val` at each output, `−val` at the fee row; `=0` at the final row (after the mint contribution) ⇒ balance `Σin + mint = Σout + fee`. |
| 14–15 | `rem`,`rbit` | range running-remainder, seeded `=val` and closed `=0` per value; `rbit` boolean. Free (unread) outside the per-value windows. |

Intentionally-free witnesses (note trapdoors, never bound — by design): commitment `rcm0`/`rcm1`
(`commit_b` lanes 4,5), and each output note's `out_recipient`/`out_rho`/`out_rcm`. These are hidden
randomness; the proof binds only what the statement needs (the digests + values).

## Constraint families — what each enforces, why non-vacuous

1. **Round (period-32, `when_transition`).** Each block computes a correct Poseidon2 permutation
   (vetted constants/linear layers). Non-vacuous: `is_init/is_full/is_partial` are 1 on exactly the
   right rows of every block (incl. padding), so every block is a real permutation.
2. **Local-persistent constancy** (`nk/nk1/rho/rho1/val`, gated by `1 − region_last`; `pos_acc` has its
   own accumulation rule, #3). Forces each constant within its region; freed only at region-last rows.
   Non-vacuous: `region_last` is 1 only at the genuine last row of each region (incl. the mint
   region). **All four note-randomness/key limbs (`nk,nk1,rho,rho1`) are in this set** — a missing one
   would let that limb differ between the commitment and the nullifier (forgeable nullifier).
3. **`pos_acc` accumulation** (A1). `pos_acc' = pos_acc + bit·2^d` at links (coefficient column),
   `=0` at span start, pinned into the nullifier. Non-vacuous: `mem_link`=1 and `pos_coeff`=2^d at
   each link; `own_in`=1 forces the reset.
4. **`val_acc` balance** (A3). Accumulates `+in +mint −out −fee` and is asserted `0` at the final row
   (placed **after** the mint region, so the mint addend is included). With every addend range-bounded
   (#5), the field sum cannot wrap, so this is exact integer balance `Σin + mint = Σout + fee`.
   Non-vacuous: `row0`/`commit_in`/`mint_in`/`out_in`/`fee_in`/`final` selectors each fire.
5. **Range** (A3). `rem=val` at seed, `rem=2·rem'+rbit` (`rbit` boolean), `rem=0` at close ⇒
   `val < 2^BITS`. Applied to every input value, every output value, **the fee, and the mint** (so a
   wrapping mint cannot fake balance).
6. **Ownership input** = `[DOM_OWN, nk0, nk1, d, 0,0,0,0]`. Pins the domain tag (A2), both nk limbs,
   and lanes 4–7 = 0 ⇒ `recipient = H(DOM_OWN ‖ nk0 ‖ nk1 ‖ d)`. `d` (lane 3, the diversifier) is a
   **free** input: a spender must use the note's real `d` or the recomputed `cm` won't be in the tree,
   and mapping one's own `nk` onto another address's tag is a 2¹²⁸ preimage — so no extra constraint
   is needed. One `nk` thus spends notes to any of a wallet's diversified addresses.
7. **Recipient link.** `commit_a.in[1..5] = own.out[0..4]` ⇒ `recipient = H(DOM_OWN ‖ nk0 ‖ nk1)`
   flows into the commitment. Non-vacuous: gated by the boundary selector.
8. **Commitment (two permutations).**
   - `commit_a`: lane0=`DOM_CM`, lane5=`val`, lane6=`rho`(rho0), lane7=`rho1` (recipient via #7) ⇒
     `H1 = H(DOM_CM ‖ recipient ‖ value ‖ rho0 ‖ rho1)`.
   - **chain link**: `commit_b.in[0..4] = commit_a.out[0..4]` (same shape as the recipient link, at
     lane offset 0) — pins the chaining value; also applied to outputs (`out_b.in = out_a.out`).
   - `commit_b`: lanes 4,5 = `rcm0,rcm1` (free trapdoor), lanes 6,7 pinned `0` ⇒
     `cm = H(chain ‖ rcm0 ‖ rcm1 ‖ 0 ‖ 0)`. The 256-bit chain ⇒ 128-bit collision resistance.
9. **Membership link.** Places the running digest by `bit` (general position), `bit` boolean; the
   first link carries `commit_b`'s output (= `cm`) as the leaf. Folds to the root.
10. **Root.** Each input's root row `= public anchor` (all inputs under one anchor).
11. **Nullifier input** = `[DOM_NF, nk0, nk1, rho0, rho1, pos_acc, 0, 0]` ⇒
    `nf = H(DOM_NF ‖ nk0 ‖ nk1 ‖ rho0 ‖ rho1 ‖ pos)` with `pos` = the proven path (A1).
12. **Nullifier output.** input `i`'s null output `= public nf_i` (per-input one-hot).
13. **Output commitment.** `out_a`: lane0=`DOM_CM`, lane5=`out_value` (recipient/rho free); chained
    into `out_b` (chain link + pad-0, as #8); `out_cm_j` = `out_b` output (per-output one-hot).
14. **Output output.** output `j`'s out row `= public out_cm_j`.
15. **Fee.** fee region `val = public fee` (so the public fee is the value subtracted in #4 and
    range-checked in #5).
16. **tx_binding.** Bound by Fiat–Shamir (uni-stark observes all public values); no AIR constraint
    needed.
17. **Mint.** mint region `val = public mint` (so the public issuance is the `+mint` addend in #4 and
    is range-checked in #5). `mint > 0` authorization (only a coinbase may issue) is a consensus-layer
    check, **not** an AIR property — the AIR exposes mint as a bound, range-checked public value, and
    the node rejects `mint ≠ 0` for normal transactions.

## Public-output soundness chain (no vacuous public binding)
Each public value is bound to a trace cell that is **constrained to be the real computation**:
- `anchor` ← root row ← membership links (#9) over `cm` ← commitment (#8) over `recipient` (#7) ←
  ownership (#6). 
- `nf_i` ← null output (#12) ← Poseidon2 (#1) of `[DOM_NF, nk0, nk1, rho, pos_acc]` (#11), with
  `nk0`/`nk1`/`rho` tied to the spent note (cols 9/16/10) and `pos` to the path (#3).
- `out_cm_j` ← out output (#14) ← Poseidon2 of `[DOM_CM, …, out_value]` (#13), `out_value` in the
  balance (#4) + range (#5).
- `fee` ← fee region (#15), in the balance + range.

## Residuals / assumptions (for the auditor)
- The Merkle **merge is untagged** (8 lanes full); separated structurally (only ever a 2-to-1 over
  digests; the leaf is a `DOM_CM`-tagged commitment). A merge/data-hash collision needs a Poseidon2
  collision — in scope of the requested Poseidon2 review.
- **`rho` uniqueness per note** is a note-creation invariant (protocol side), assumed here.
- **Padding blocks** satisfy the round constraints (valid permutations) but no selector references
  them, so they bind nothing.
- `bit`/`rem`/`rbit` outside their active windows are unconstrained junk that no constraint reads.
- Fixed `(N_IN, M_OUT) = (2, 2)`; smaller transactions use dummy (zero-value) notes
  (see `docs/audit-scope-p3.md` §6 / the join-split variable-shape note).
