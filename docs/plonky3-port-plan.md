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
  scales to depth-32. **`p3-lookup` 0.6.1 (LogUp) exists** on crates.io, so the lookup argument is a
  library, not a from-scratch build; `p3-uni-stark` is single-table, so M3 wires `p3-lookup` to a
  multi-table prover (investigate `p3-lookup`'s prover integration / `p3-air` interaction builder).
- **B. Single hand-rolled AIR** — reuse the vetted *constants* but re-implement the Poseidon2 round
  constraints inline (≈ what the Winterfell `lattica-prover` did), plus the wiring. Avoids the
  lookup machinery but re-hand-rolls the soundness-critical hash AIR (larger audit surface).

**M3 finding (investigated):** `p3-lookup` 0.6.1 gives the LogUp *gadget* (`LogUpGadget`,
`LookupBus`, `InteractionBuilder`) — **but Plonky3 0.6.1 ships no multi-table prover**
(`p3-machine`/`p3-stark`/`p3-multi-stark` do not exist; `p3-uni-stark` is single-table). So option
**A would require building the multi-table prover *orchestration*** (per-table commits, shared
lookup challenges, LogUp aux/permutation traces, cross-table linking) — itself large and
soundness-critical, and *not* vetted. Option **B reuses the vetted single-table `uni-stark` ZK
prover** (already working in M1/M2); its only hand-written soundness-critical piece is the Poseidon2
*round constraints*, which are well-understood and **validatable against the native
`Poseidon2Goldilocks`** (differential test) — a contained, testable surface.

**Revised plan: build the first full statement with B** (single `uni-stark` AIR; vetted Poseidon2
*constants* + hand-written round constraints, differential-tested vs native; multi-region trace like
the validated Winterfell `lattica-prover`). Keep **A as the scalable future** if/when a vetted
multi-table prover is adopted (or the orchestration is built + audited). Net: B trades a contained,
testable hand-rolled hash-AIR for avoiding an un-vetted multi-table prover build.

## Incremental milestones

- **M1 — done:** vetted Poseidon2-Goldilocks AIR proves/verifies in-repo (stable).
- **M2 — done:** ZK swap — the foundation now proves/verifies under the **hiding FRI PCS**
  (`HidingFriPcs` + salted `MerkleTreeHidingMmcs`) with a Goldilocks-native `DuplexChallenger` and
  `F_p²` challenges. Still owed: the written C-04 soundness budget (Plonky3 `security.rs` gives
  proven bounds to anchor it).
- **M3 — done (investigation + decision):** no multi-table prover in p3 0.6.1; **chose option B**
  (single `uni-stark` AIR, vetted Poseidon2 constants + hand-written round constraints) for the
  first full statement (see the architecture section above).
- **M4:** the **full spend statement** as a single multi-region `uni-stark` AIR — Poseidon2 rounds
  (vetted constants, differential-tested vs `Poseidon2Goldilocks`) for the commitment / depth-D
  membership / nullifier / output / ownership hashes, plus the wiring (link region outputs→inputs),
  value-balance, range, and tx-binding — under the hiding (ZK) PCS. This is the analogue of the
  validated Winterfell `lattica-prover` statement; build it incrementally (one hash region →
  membership chain → + nullifier/output → + balance/range/ownership/tx-binding), each
  differential-tested against the Winterfell oracle.
  - **M4 de-risked:** `GenericPoseidon2LinearLayers::{external,internal}_linear_layer<R:
    PrimeCharacteristicRing>` is generic over the algebra, and the AIR builder's `AB::Expr`
    implements `PrimeCharacteristicRing` — so the custom AIR can **call the vetted linear layers
    directly** on the symbolic state. The hand-written surface is then only: the `x⁷` S-box, adding
    the vetted round constants, the full/partial round sequencing, and the spend wiring. The vetted
    constants + linear algebra are reused; correctness of the round structure is pinned by the
    differential test against native `Poseidon2Goldilocks`.
- **M5:** native oracle + **differential tests** vs the Winterfell `lattica-prover`; canonical proof
  serialization; the `lattica_spend_verify` / `lattica_spend_prove` C ABI (matches `src/ffi.zig`).
- **M6:** Phase-4 node cutover — wire the verifier into `node.zig`, switch protocol hashing to
  Poseidon2-Goldilocks, demote native checks. Then the Phase-3 external audit gates value use.

## Notes
- Goldilocks Poseidon2: WIDTH 8, S-box degree 7, 8 full + 22 partial rounds (vetted Grain-LFSR
  constants). DEPTH/recipient-digest/value-bit-width are parameters to finalize in M4/M5.
- Toolchain: stable (no nightly). Keep `lattica-prover` (Winterfell) building as the oracle.
