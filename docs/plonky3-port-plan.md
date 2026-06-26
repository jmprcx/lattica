# Plonky3 production port plan

**Decision (see `docs/framework-decision.md`):** the production spend circuit is built on **Plonky3**
— transparent, FRI/post-quantum, **zero-knowledge** (hiding PCS), **stable** Rust, **proven-security**
accounting. Field = **Goldilocks** (64-bit, so `u64` note values fit directly — clean value-balance
and range). Hash = **Poseidon2** with the **vetted** `GOLDILOCKS_POSEIDON2_RC_8_*` constants via the
vetted `p3-poseidon2-air` AIR, so the in-circuit hash equals the protocol's native
`Poseidon2Goldilocks` (closes the C-03 hash-mismatch at the hash level). New crate:
`lattica-prover-p3/` (production); the Winterfell `lattica-prover/` is kept as a **differential
oracle**.

## Milestone 1 — done
`lattica-prover-p3/`: the vetted Poseidon2-Goldilocks permutation as an AIR
(`Poseidon2Air<GenericPoseidon2LinearLayersGoldilocks, 8, 7, 1, 4, 22>` with `RoundConstants::new`
from the vetted constants), proving + verifying in-repo on stable (two-adic FRI config, 2/2 tests).
Plus `native_permute` = `Poseidon2Goldilocks` (the protocol's hash; the AIR matches it by sharing
the vetted constants). ZK shown separately end-to-end in `plonky3-spike/` (hiding PCS).

## The key open architecture decision — how to compose the full statement

`p3-poseidon2-air` is a **standalone permutation chip**; its round-constraint helpers are private,
so it cannot be embedded inline in a larger single AIR. The spend statement needs **many** hashes
(commitment, DEPTH membership merges, nullifier, output commitment, ownership) plus linking
(merge[i].out → merge[i+1].in, cm = commitment region output, recipient = H(nk)) and the non-hash
constraints (value-balance, range, tx-binding). Options:

- **A. Multi-chip + lookups (recommended)** — a Poseidon2 chip proves *all* permutations; a "spend"
  chip carries the values/structure (balance, range, tx-binding, the path shape); a **lookup/bus
  argument (LogUp)** enforces that each `(input → output)` hash used by the spend chip appears in
  the Poseidon2 chip. This is the real Plonky3/SP1 pattern, reuses the vetted Poseidon2 chip, and
  scales to depth-32. Cost: `p3-uni-stark` is single-table, so this needs a **lookup framework** —
  investigate the p3 ecosystem (a multi-table prover / LogUp) or implement a minimal LogUp.
- **B. Single hand-rolled AIR** — reuse the vetted *constants* but re-implement the Poseidon2 round
  constraints inline (≈ what the Winterfell `lattica-prover` did), plus the wiring. Avoids the
  lookup machinery but re-hand-rolls the soundness-critical hash AIR (larger audit surface).

**Plan: pursue A.** Lower long-term audit surface (vetted hash chip) and the scalable architecture;
the lookup framework is the next investigation.

## Incremental milestones

- **M1 — done:** vetted Poseidon2-Goldilocks AIR proves/verifies in-repo (stable).
- **M2:** ZK swap — `HidingFriPcs` + extension-field challenges on M1; write the C-04 soundness
  budget (Plonky3 `security.rs` gives proven bounds). (ZK already shown in `plonky3-spike/`.)
- **M3:** lookup/bus decision + a minimal **two-hash linked** example (commitment → one membership
  merge) proving the linking via a lookup.
- **M4:** the **full spend statement** — ownership + commitment + depth-D membership + nullifier +
  output commitment + value-balance + range + tx-binding (the `lattica-prover` statement, now ZK).
- **M5:** native oracle + **differential tests** vs the Winterfell `lattica-prover`; canonical proof
  serialization; the `lattica_spend_verify` / `lattica_spend_prove` C ABI (matches `src/ffi.zig`).
- **M6:** Phase-4 node cutover — wire the verifier into `node.zig`, switch protocol hashing to
  Poseidon2-Goldilocks, demote native checks. Then the Phase-3 external audit gates value use.

## Notes
- Goldilocks Poseidon2: WIDTH 8, S-box degree 7, 8 full + 22 partial rounds (vetted Grain-LFSR
  constants). DEPTH/recipient-digest/value-bit-width are parameters to finalize in M4/M5.
- Toolchain: stable (no nightly). Keep `lattica-prover` (Winterfell) building as the oracle.
