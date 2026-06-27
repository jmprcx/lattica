# Join-split circuit — constraint-accounting self-audit

A column-by-column and constraint-by-constraint review of `lattica-prover-p3::joinsplit_air`, arguing
that **every witness column is constrained** and **no binding is vacuous** (the failure mode an
external audit hunts for). This is a self-audit to feed the Phase-3 review, not a substitute for it.

Layout: `N_IN` input spans + `M_OUT` output regions + a fee region + a **mint region** + padding,
each block = 32 rows (one Poseidon2 permutation). `WIDTH = 17`. Selectors are period-32 (round
schedule) or full-length one-hots (region boundaries / bindings). The nullifier key `nk` is **two
field elements** (128-bit spend authority): limb 0 in col 9 (`nk`), limb 1 in col 16 (`nk1`).

## Columns — what determines each

| col | name | determined by |
|---|---|---|
| 0–7 | Poseidon2 state | round constraints chain each block input→output; input rows pinned by the region bindings (below); output rows pinned where public (root/nf/out_cm). |
| 8 | `bit` | boolean at each membership link; read only as `next.bit` at link rows. Elsewhere unread (free). |
| 9 | `nk` | nk limb 0; local-persistent (constant in span); pinned at the ownership input (lane 1) **and** the nullifier input (lane 1) ⇒ ties ownership↔nullifier key. |
| 16 | `nk1` | nk limb 1; local-persistent; pinned at the ownership input (lane 2) **and** the nullifier input (lane 2) — symmetric to col 9 (128-bit `nk`). |
| 10 | `rho` | local-persistent; pinned at the commitment input (lane 6) **and** the nullifier input (lane 3) ⇒ ties commitment↔nullifier. |
| 11 | `val` | local-persistent; pinned at the commitment input (input value), output input (out value), fee input (fee), **mint input (mint)**; consumed by the accumulator + range. |
| 12 | `pos_acc` | reset 0 at span start, `+= bit·2^d` at each link, constant else; pinned into the nullifier input (lane 4) ⇒ **A1**. |
| 13 | `val_acc` | 0 at row 0; `+val` at each commit, `+val` at the mint row, `−val` at each output, `−val` at the fee row; `=0` at the final row (after the mint contribution) ⇒ balance `Σin + mint = Σout + fee`. |
| 14–15 | `rem`,`rbit` | range running-remainder, seeded `=val` and closed `=0` per value; `rbit` boolean. Free (unread) outside the per-value windows. |

Intentionally-free witnesses (note trapdoors, never bound — by design): commitment `rcm` (lane 7),
and each output note's `out_recipient`/`out_rho`/`out_rcm`. These are hidden randomness; the proof
binds only what the statement needs (the digests + values).

## Constraint families — what each enforces, why non-vacuous

1. **Round (period-32, `when_transition`).** Each block computes a correct Poseidon2 permutation
   (vetted constants/linear layers). Non-vacuous: `is_init/is_full/is_partial` are 1 on exactly the
   right rows of every block (incl. padding), so every block is a real permutation.
2. **Local-persistent constancy** (`nk/nk1/rho/val/pos_acc`, gated by `1 − region_last`). Forces each
   constant within its region; freed only at region-last rows. Non-vacuous: `region_last` is 1 only
   at the genuine last row of each region (incl. the mint region's last row).
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
6. **Ownership input** = `[DOM_OWN, nk0, nk1, 0,0,0,0,0]`. Pins the domain tag (A2), both nk limbs,
   and the pad ⇒ `recipient = H(DOM_OWN ‖ nk0 ‖ nk1)`.
7. **Recipient link.** `commit.in[1..5] = own.out[0..4]` ⇒ `recipient = H(DOM_OWN ‖ nk)` flows into
   the commitment. Non-vacuous: gated by the boundary selector.
8. **Commitment input.** lane0=`DOM_CM`, lane5=`val`, lane6=`rho` (recipient via #7, `rcm` free) ⇒
   `cm = H(DOM_CM ‖ recipient ‖ value ‖ rho ‖ rcm)`.
9. **Membership link.** Places the running digest by `bit` (general position), `bit` boolean; the
   first link carries the commitment output (= `cm`) as the leaf. Folds to the root.
10. **Root.** Each input's root row `= public anchor` (all inputs under one anchor).
11. **Nullifier input** = `[DOM_NF, nk0, nk1, rho, pos_acc, 0,0,0]` ⇒ `nf = H(DOM_NF ‖ nk0 ‖ nk1 ‖ rho
    ‖ pos)` with `pos` = the proven path (A1).
12. **Nullifier output.** input `i`'s null output `= public nf_i` (per-input one-hot).
13. **Output input.** lane0=`DOM_CM`, lane5=`out_value` ⇒ `out_cm = H(DOM_CM ‖ … ‖ out_value ‖ …)`.
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
