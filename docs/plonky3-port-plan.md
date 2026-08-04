# Plonky3 production port plan

> **Historical plan:** The port is complete and Plonky3 is now the live proof stack. Retained as implementation history.

> **⚠ Historical / reference-only — not the v1 audit artifact.** The port (M1–M6) is complete; this is
> the milestone record. Start at [`AUDITORS.md`](AUDITORS.md); current state is `remediation-status.md`.

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
- **M4 — done:** the **full spend statement** as a single multi-region `uni-stark` AIR under the
  hiding (ZK) PCS, built incrementally and each step differential-tested against an **independent
  native `Poseidon2Goldilocks` oracle** (note: a *proof-level* differential vs Winterfell is not
  meaningful — Winterfell uses Rescue, Plonky3 uses Poseidon2; Winterfell remains a *structural*
  reference for the statement shape):
  - **M4a** (`poseidon2_air.rs`): the across-rows Poseidon2-Goldilocks permutation AIR (vetted
    constants/layers; hand-written S-box + RC + sequencing), output == native. 3 tests.
  - **M4b** (`spend_air.rs`): commitment + general-position Merkle membership (block-boundary links,
    boolean position bit), root == native fold. 4 tests.
  - **M4c** (`full_spend_air.rs`): ownership + commitment + membership + nullifier + output +
    value-balance + range + tx-binding, with cross-region binding via **persistent columns**
    (nk, rho, value, out_value) and **period-256 per-boundary selectors** + the period-32 round
    schedule. A negative test for every binding (wrong root/nf/out_cm, unbalanced, out-of-range,
    wrong tx-binding via prove-real/verify-other, forged nk). 9 tests.
  - **M4 de-risked:** `GenericPoseidon2LinearLayers::{external,internal}_linear_layer<R:
    PrimeCharacteristicRing>` is generic over the algebra, and the AIR builder's `AB::Expr`
    implements `PrimeCharacteristicRing` — so the custom AIR can **call the vetted linear layers
    directly** on the symbolic state. The hand-written surface is then only: the `x⁷` S-box, adding
    the vetted round constants, the full/partial round sequencing, and the spend wiring. The vetted
    constants + linear algebra are reused; correctness of the round structure is pinned by the
    differential test against native `Poseidon2Goldilocks`.
- **M5 — done** (`lib.rs`): canonical **proof serialization** (postcard; round-trip + tamper +
  malformed-fail-closed tests) and the **`lattica_spend_verify` C ABI** matching `src/ffi.zig`'s
  136-byte `SpendPublicInputs` layout (anchor‖nullifier‖out_cm‖tx_binding‖fee), with canonical
  field-element parsing — fail-closed on null pointers, wrong length, non-canonical limbs, or
  malformed proof bytes. The crate now builds a `staticlib` exporting `lattica_spend_verify`.
  Differential = the independent native Poseidon2 oracle (per-region `native_*` tests). 21 tests.
- **M6:** Phase-4 node cutover — wire the verifier into `node.zig` (via `ffi.setBackend`), add
  `lattica_spend_prove` (wallet side), link the staticlib, switch protocol hashing to
  Poseidon2-Goldilocks, demote native checks. Then the Phase-3 external audit gates value use.

## Status: M1–M5 complete + C-04 + parameter hardening done
The production spend circuit exists, is zero-knowledge, builds on stable, exposes the C ABI the node
calls, runs at **production parameters**, and carries a **machine-checked soundness budget**.
- **C-04 — done** (`docs/soundness-budget.md`): challenges in `F_p²` (~127-bit) + FRI `log_blowup=4`,
  `num_queries=96`, `query_pow=16` ⇒ **≈103-bit proven** / **≈127-bit conjectured** (vs the audited
  ~50). `full_spend_air::security_report()` computes it via Plonky3's `ProvenSecurity`/
  `ConjecturedSecurity`; the `production_security_budget` test gates proven ≥ 100, conjectured ≥ 128.
- **Parameter hardening — done**: `DEPTH 4→32` (block count padded 36→64), `recipient` 1→**4-element
  digest** (input & output notes share the commitment layout), value `BITS 32→52` (wraparound-safe).
- **Proof-size tuning — done** (`cargo run --bin sweep`, table in `docs/soundness-budget.md`): FRI
  folding arity 1→4 + a 2⁶ Merkle cap cut the proof **828→421 KB (−49%)** at the *same* 103/127-bit
  security (verify 13→8 ms). Raising the blowup or grinding were shown counter-productive.
  Production (`DEPTH=32`): proof **~421 KB**, prove ~2.05 s, verify ~8 ms. 22 tests pass.

**Remaining before production** (scope + threat model in `docs/audit-scope-p3.md`):
- ✅ **Pre-audit circuit work done:** the **join-split (N-in/M-out)** circuit `joinsplit_air` (fixed
  2-in/2-out, `DEPTH=32`, ~444 KB / 8.3 s / 24 ms, proven 103-bit, 12/12) with the soundness fixes
  baked in — A1 position-consistency, A2 domain separation, A3 fee+value range, A4 nullifier
  argument. The 1-in/1-out `full_spend_air` stays as the reference.
- **Protocol seam (C-03):** switch `tx.zig`/`primitives.zig` hashing to the exact in-circuit
  Poseidon2-Goldilocks layouts (+ domain tags) with shared known-answer vectors; the join-split C ABI
  + byte layout; an end-to-end FFI integration test (mint → prove → in-node verify → double-spend).
- **Constraint-accounting self-audit**; variable `(N,M)` if the protocol needs it.
- **M6** node cutover + `lattica_spend_prove`; then **Phase-3 external audit** (incl. a Poseidon2
  review).

## Notes
- Goldilocks Poseidon2: WIDTH 8, S-box degree 7, 8 full + 22 partial rounds (vetted Grain-LFSR
  constants). DEPTH/recipient-digest/value-bit-width are parameters (small here; widened for prod).
- Toolchain: stable (no nightly). Keep `lattica-prover` (Winterfell) building as a structural
  reference.
