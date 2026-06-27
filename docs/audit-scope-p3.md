# Lattica spend circuit — external audit scope, threat model & readiness (Plonky3 stack)

Auditor handoff for the **production** proving stack (`lattica-prover-p3/`). It defines what is in
scope, the trust/threat model, the frozen parameters, known limitations, and the pre-audit readiness
checklist. Companion docs: `docs/soundness-budget.md` (C-04), `docs/plonky3-port-plan.md` (how the
circuit was built), `docs/remediation-status.md` (audit-finding tracker), `docs/audit-scope.md` (the
older *Winterfell* reviewer guide — reference only; superseded by this for production).

> **Status: ready for external review; one deliberate-parameter sign-off remains (not a bug).** The
> production circuit is the **join-split N-in/M-out** (`joinsplit_air`, §6), with the soundness fixes
> applied (A1–A4, 128-bit `nk`, **128-bit `rho`/`rcm`**) and the live protocol fully cut over to it:
> Poseidon2 on-chain hashing == circuit; hidden-value node tx model; fail-closed, panic-isolated
> verifier; validated coinbase issuance (`mint` is impossible except via the consensus-authorized
> path). Four adversarial recheck passes hardened it: they found + fixed real bugs — the ZK-blinding
> RNG, a node-layer `mint` inflation hole, and (after the `rho`/`rcm` widening) a missing `rho1`
> persistence constraint that would have allowed a forged second nullifier per note — plus added
> verifier panic isolation.
>
> **The in-node real prove→verify path executes green** (`scripts/run-real-integration.sh`:
> the Zig node builds the witness → real Rust prover → Zig reconstructs the public inputs → real Rust
> verifier → accept; replay + tamper rejected). It is built as an object linked with the system
> toolchain because this host's Zig linker can't link the Rust staticlib.
>
> **Remaining before value-bearing use** — one *deliberate parameter* needing explicit auditor
> sign-off (see §5 / `docs/protocol-v1-decisions.md`), not a defect: proven soundness is ~103-bit
> (≈127-bit conjectured), which is the ceiling for Goldilocks F_p² — raising it further requires a
> larger field. (`rho`/`rcm` are now 128-bit — the two-permutation commitment — so the note-randomness
> sign-off is resolved.) Out of lattica's scope by design: block
> consensus / PoW / mempool / networking / the emission schedule belong to the host chain
> (`rubble-node-zig`); lattica provides the shielded-tx + issuance *mechanisms* it drives.

## 1. Scope

**In scope (to be audited):**
- The circuit: `lattica-prover-p3/src/{joinsplit_air,poseidon2_air,spend_air}.rs` — the AIR
  constraints, trace generation, periodic columns, and the cross-region binding (`joinsplit_air` is
  the production circuit; `poseidon2_air`/`spend_air` are its building blocks).
- The verifier/prover boundary: `lattica-prover-p3/src/lib.rs` — `lattica_joinsplit_verify` /
  `lattica_joinsplit_prove` C ABI, the `JoinSplitPublicInputs` + witness parsing, canonical
  field-element checks, fail-closed + panic-isolated behavior, proof (de)serialization.
- The Zig protocol seam: `src/ffi.zig` (ABI shape), `src/protocol.zig` (tx encoding, supply model,
  tx-binding digest), `src/codec.zig` (canonical encoding) — **specifically the requirement that the
  on-chain hashes equal the in-circuit hashes** (see §5 / C-03).
- The frozen parameter set and proof format (§4).

**Out of scope (this round):**
- Recursive / batch aggregation (`batch_measure` is a measurement prototype, not production).
- The live consensus node (`rubble-node-zig`) beyond the verify seam; networking; mempool; P2P.
- The wallet/prover key management and note-discovery.
- Performance (covered by `docs/soundness-budget.md`; not a security gate).

**Reference only (not audited as production):** the Winterfell `lattica-prover/` crate — kept as a
differential oracle for the hashes, not a production artifact.

## 2. Trust model & assumptions

- **Roles.** The **prover** (wallet) is fully untrusted. The **verifier** (node, via
  `lattica_spend_verify`) is the security boundary. A spend proof is a *validity witness*; the node
  enforces the stateful checks the proof does not (nullifier-set non-membership = double-spend
  prevention; anchor is a known tree root; fee policy).
- **Cryptographic assumptions.**
  - **Poseidon2-Goldilocks** (vetted `p3-goldilocks` constants) modeled as collision-resistant /
    random-oracle-like. *A dedicated Poseidon2 parameter & algebraic-attack review is explicitly
    requested as part of this audit.*
  - **FRI / STARK soundness** per ethSTARK (2021/582) and the proven bounds (2024/1553, 2025/2055);
    Fiat–Shamir in the ROM. Soundness level **≈103-bit proven / ~127-bit conjectured**, machine-
    checked (`docs/soundness-budget.md`, `production_security_budget` test).
  - **Transparency:** no trusted setup. **Post-quantum:** no elliptic curves / pairings. Stable Rust.
- **What the proof guarantees** (for one spend, current 1-in/1-out — generalized in §6): there exist
  hidden `(nk, value, rho, rcm, path)` such that the spent note `cm = H(recipient,value,rho,rcm)`
  with `recipient = H(nk)` is a leaf at the proven path under the public `anchor`; the revealed `nf`
  is its nullifier; the public `out_cm` commits to `out_value`; `value = out_value + fee`;
  `value, out_value < 2^BITS`; and the proof is bound to the public `tx_binding`.
- **What the proof does NOT guarantee (node's responsibility):** `nf` not already spent; `anchor` is
  a valid historical root; `fee` matches policy; transaction-level authorization/signatures outside
  the shielded statement.

## 3. The statement under audit (current artifact)

Eight Poseidon2 blocks, height 2048, hiding (ZK) FRI PCS. Public inputs (17 field elements):
`root(4) ‖ nf(4) ‖ out_cm(4) ‖ fee(1) ‖ tx_binding(4)`.

| # | Region | Constraint |
|---|---|---|
| 0 | ownership | `recipient = H(nk)` (4-element digest) |
| 1 | commitment | `cm = H(recipient, value, rho, rcm)` |
| 2..5 | membership | `cm` folds up a **general-position** depth-`DEPTH` path to the public `root` |
| 6 | nullifier | `nf = H(nk, rho, pos)` (public) |
| 7 | output | `out_cm = H(out_recipient, out_value, out_rho, out_rcm)` (public) |
| — | balance | `value = out_value + fee` |
| — | range | `value, out_value < 2^BITS` (running-remainder; no wraparound mod p) |
| — | tx-binding | bound via Fiat–Shamir (public input) |

Cross-region binding uses **persistent columns** (`nk, rho, value, out_value`, constant across the
trace, pinned per block) and **period-256 one-hot boundary selectors**; within-block Poseidon2 rounds
use the period-32 round schedule. Hash inputs use the **vetted** Poseidon2-Goldilocks constants, so
the in-circuit hash equals the protocol's native `Poseidon2Goldilocks` (differential-tested).

## 4. Frozen parameters & proof format

| Item | Value |
|---|---|
| Base field | Goldilocks `p = 2^64 − 2^32 + 1` |
| Challenge field | `F_p²` (BinomialExtensionField, degree 2) |
| Hash | Poseidon2, width 8, S-box `x^7`, 8 full + 22 partial rounds, vetted `GOLDILOCKS_POSEIDON2_RC_8_*` |
| Merkle/leaf hash | Poseidon2 sponge/compression, 4-Goldilocks digest |
| FRI | `log_blowup=4`, `num_queries=96`, `query_pow=16`, `commit_pow=0`, `max_log_arity=4`, `cap_height=6` |
| Soundness | ≈103-bit proven / ~127-bit conjectured |
| Circuit params | `DEPTH=32`, `BITS=52`, `recipient`=4-element digest |
| Proof serialization | postcard; `SpendPublicInputs` = `anchor‖nullifier‖out_cm‖tx_binding (4×32) ‖ fee(8 LE)` = 136 bytes |
| Proof size / verify | ~421 KB / ~8 ms (single spend, `DEPTH=32`) |

These freeze for the audited artifact. Join-split (§6) adds `N` (inputs) and `M` (outputs)
parameters and widens the public inputs accordingly; the freeze is re-confirmed once §6 lands.

## 5. Known limitations & open items (must close before audit)

Tracked in detail in `docs/remediation-status.md`. The soundness-relevant ones:

- **A1 — position-consistency. ✅ Closed** in the join-split circuit (`joinsplit_air`): `pos = Σ_d
  bits_d·2^d` is accumulated from the membership path (a `pos_acc` column updated at each link with a
  `2^d` coefficient) and bound into the nullifier input, so a note has exactly one nullifier tied to
  its tree position. Validated natively (distinct positions ⇒ distinct nullifiers) and in-circuit
  (the `pos_acc`→nullifier binding).
- **A2 — domain separation. ✅ Closed**: ownership/commitment/nullifier carry distinct lane-0 tags
  `DOM_OWN/DOM_CM/DOM_NF`; the Merkle merge is untagged but structurally separated (only ever a
  2-to-1 over digests; the tree leaf is a `DOM_CM`-tagged commitment). See the A4 argument below.
  Validated (same field input, different domain ⇒ different digest).
- **A3 — fee soundness. ✅ Closed**: every input value, output value, **and the fee** are
  range-checked (`< 2^BITS`, running-remainder) and the value balance is a global accumulator
  `Σin − Σout − fee = 0`; all addends bounded ⇒ no field wraparound. Validated (out-of-range and
  wrong-fee rejected).
- **A4 — nullifier-derivation argument. ✅ Written** (see "A4 — nullifier-derivation" below).
- **C-03 — protocol/circuit hash match. 🟡 Hash matched; protocol swap = M6.** `src/poseidon2.zig`
  is a Zig Poseidon2-Goldilocks that reproduces the circuit's permutation **and** the domain-tagged
  `recipient`/`commit`/`nullifier`/`merge` hashes **byte-for-byte** — pinned by known-answer vectors
  generated from the circuit (`dump_p2`) and asserted in `poseidon2.zig`'s KAT tests. The remaining
  step is the **coordinated protocol swap**: migrate the `Note` model (`tx.zig`) + Merkle tree
  (`tree.zig`) off SHA3 onto these functions (note fields become Goldilocks elements). Because that
  swap is protocol-wide (touches note encryption/wallet) it lands with the **M6 node cutover**; the
  end-to-end FFI test (below) demonstrates the protocol-side `poseidon2.zig` hashes equal the
  circuit's via a real proof verifying.
- Single-asset; no memo field; coinbase/mint/burn not yet modeled.

### A4 — nullifier-derivation argument
The nullifier is `nf = H(DOM_NF ‖ nk ‖ rho ‖ pos)` with `H` = Poseidon2-Goldilocks (vetted constants),
modeled as a random oracle. Properties:
- **Uniqueness / no double-spend.** `pos` is bound (A1) to the note's tree position and `rho` is the
  note's per-note randomness; together with `nk` they fix a single `nf` per (note, position). A note
  occupies one position, so it has exactly one nullifier — re-spending yields the same `nf`, caught by
  the node's nullifier set.
- **Binding / unforgeability.** Computing `nf` requires `nk` (the nullifier key, never revealed) and
  the note opening; in the ROM, `nf` reveals nothing about `nk`/`rho` and cannot be produced without
  them. Ownership binds `recipient = H(DOM_OWN ‖ nk)` into the spent commitment, so the same `nk`
  that authorizes the spend derives the nullifier (no nullifier/authority split).
- **No faerie-gold / cross-context collision.** Domain separation (A2) prevents an `nf` from
  coinciding with a commitment, ownership digest, or Merkle node. `rho` must be unique per note
  (a protocol-level invariant on note creation — flagged for the auditor as an assumption); given
  that, `H`'s collision resistance gives distinct `nf` for distinct notes.
- **Residual to audit:** the untagged merge (collision between a merge node and a data hash would
  require a Poseidon2 preimage/collision — out of scope of the statement, in scope of the requested
  Poseidon2 review), and the `rho`-uniqueness invariant on the note-creation side.

## 6. Join-split (N-in / M-out) — **landed** *(decision 2026-06-26; built)*

`joinsplit_air` implements the audit-target shape (the 1-in/1-out `full_spend_air` is kept as the
simpler reference):
- **N input notes** (`N_IN`), each: ownership `recipient = H(DOM_OWN ‖ nk)`, commitment
  `cm = H(DOM_CM ‖ recipient ‖ value ‖ rho ‖ rcm)`, general-position membership to a **shared public
  `anchor`**, and a revealed nullifier `nf_i = H(DOM_NF ‖ nk ‖ rho ‖ pos)` (A1).
- **M output notes** (`M_OUT`), each a published `out_cm_j` binding `out_value_j`.
- **Value balance:** a global accumulator `Σ in − Σ out − fee = 0`, with every value + the fee
  range-checked `< 2^BITS` (A3) ⇒ no wraparound.
- **One `tx_binding`** bound by Fiat–Shamir.
- Cross-region binding via local-persistent columns (`nk`/`rho`/`value`, constant within an input
  span, freed at region boundaries).

**Parameters & numbers (current):** `N_IN=2, M_OUT=2, DEPTH=32, BITS=52`; production FRI params;
proof ~**444 KB**, prove ~**8.3 s**, verify ~**24 ms**, **proven 103-bit**. Validated 12/12
(valid; wrong anchor / nullifier / out_cm / fee; out-of-range; wrong tx_binding; native
domain-separation / pos-from-bits / balance).

**Design choices made:** fixed `(N, M)` as compile-time constants (2,2 now); per-instance public
inputs `anchor ‖ N·nf ‖ M·out_cm ‖ fee ‖ tx_binding` with per-input/output one-hot bindings (not an
aggregate hash — that is the future batching path); per-input distinct `nk`/`rho` via the
local-persistent columns.

**Variable `(N, M)`** is supported by the standard **dummy-note convention**: a smaller transaction
pads to the fixed 2-in/2-out shape with zero-value notes (a dummy input is a zero-value note the
spender owns; balance and range are unaffected). Tested (`dummy_notes_pad_smaller_transactions`). A
variable-shape circuit is only needed if more than 2-in/2-out is required.

**Remaining for the audited artifact:** only the **C-03 protocol note-model swap** (migrate the
`Note` model + Merkle tree off SHA3 onto `poseidon2.zig` — protocol-wide, lands with the M6 node
cutover; §5). Everything else is done: join-split **C ABI + byte layout**
(`lattica_joinsplit_verify`, round-trip tested), the **shared KATs** + Zig hash match
(`poseidon2.zig`), the **end-to-end FFI test** (`tests/ffi_integration.c`: prove→verify→tamper→
double-spend, verified), and the **constraint self-audit** (`docs/joinsplit-constraint-audit.md`).

## 7. Pre-audit readiness checklist

| Item | Status |
|---|---|
| Full spend statement, ZK, on stable (M1–M5) | ✅ |
| C-04 soundness budget (machine-checked) | ✅ |
| Production parameters + proof-size tuning | ✅ |
| Differential vs native Poseidon2 oracle | ✅ (per-region) |
| Verifier ABI fail-closed tests | ✅ (basic) |
| **A1 position-consistency** | ✅ (join-split) |
| **A2 domain separation** | ✅ (join-split) |
| **A3 fee soundness** | ✅ (join-split) |
| **A4 nullifier-derivation argument** | ✅ (§5) |
| **B — join-split (N-in/M-out) circuit** | ✅ (`joinsplit_air`, fixed 2-in/2-out, 12/12) |
| **Join-split C ABI + byte layout** | ✅ (`lattica_joinsplit_verify` + `ffi.zig::JoinSplitPublicInputs`) |
| **C-03 hash match: Zig Poseidon2 == circuit + KATs** | ✅ (`src/poseidon2.zig`) |
| **C-03 protocol note-model swap (tx/tree off SHA3)** | ⏳ M6 cutover (protocol-wide) |
| **End-to-end FFI integration test** (prove→verify→tamper→double-spend) | ✅ (`tests/ffi_integration.c`, verified; Zig `test-ffi` ready) |
| **Constraint-accounting self-audit** (every column/constraint, no vacuous binding) | ✅ (`docs/joinsplit-constraint-audit.md`) |
| **Variable (N,M) via dummy notes** | ✅ (tested) |
| ABI fuzz / adversarial tests (beyond fail-closed) | ❌ |
| Threat model + scope + frozen params (this doc) | ✅ |
| ZK blinding from a CSPRNG, fresh per proof | ✅ (`ChaCha20Rng`; re-randomization tested) |
| Consolidate to ONE production circuit (`full_spend_air` + spend ABI + bins removed) | ✅ joinsplit_air only |
| Protocol completeness decisions (asset/keys/randomness/issuance) | ✅ (`docs/protocol-v1-decisions.md`) |
| Mint (shielded issuance) in the circuit | ✅ (`Σin + mint = Σout + fee`, range-checked, ABI+ffi) |
| 128-bit spend authority (`nk` = 2 field elements) | ✅ (M6 §2a; found+fixed during cutover) |
| C-03 live: on-chain hashing → Poseidon2 (== circuit) | ✅ (`tx`/`tree`/`primitives` → `poseidon2.zig`) |
| Hidden-value join-split node tx model (revealed values + ML-DSA binding removed) | ✅ (`node.zig`; `verifyAndApply` = proof + anchor + nullifier; `tx_binding` binds the body) |
| `lattica_joinsplit_prove` wallet-side prover ABI + wallet witness glue | ✅ (Rust + Zig `buildTransfer`) |
| Real **in-node** prove→verify executed (not mocks) | ✅ (`scripts/run-real-integration.sh` / `src/integration_node.zig`: Zig witness→Rust prove→Zig pi→Rust verify→accept; replay+tamper reject) |
| Verifier ABI panic-isolated against malformed proofs | ✅ (`catch_unwind`; tampered+garbage-proof tests) |
| Validated coinbase issuance (`mint` only via consensus-authorized reward) | ✅ (`Chain.applyCoinbase`; normal path requires `mint == 0`) |
| Constraint self-audit current (covers `mint`, 128-bit `nk`) | ✅ (`docs/joinsplit-constraint-audit.md`; re-audited pass 3, no gaps) |
| ≥128-bit note randomness (`rho`/`rcm`) | ✅ two-permutation commitment (128-bit; rho1-persistence soundness fix + regression test) |
| ≥128-bit *proven* soundness | ⏳ ~103 proven / ~127 conjectured = Goldilocks ceiling (larger field needed) — auditor sign-off |

> **Self-review note (2026-06-26):** a recheck found the prover was seeding the hiding-PCS / Merkle
> salt RNG with a *fixed* non-cryptographic `SmallRng` — so the "zero-knowledge" proofs were not
> re-randomized (identical blinding every proof), defeating privacy. Fixed in `joinsplit_air` to a
> ChaCha20 CSPRNG seeded from the OS per proof, with a `zk_blinding_is_fresh_per_proof` test. The
> reference `full_spend_air` still uses the dev RNG and should be dropped or gated before audit.

## 8. Reproduce / verify

- `cd lattica-prover-p3 && cargo test --release` — 22 tests (circuit, ABI, security budget).
- `cargo run --release --bin lattica-prover-p3` — end-to-end demo (M1/M2 + M4a/b/c + C-04 report).
- `cargo run --release --bin sweep` / `--bin batch` / `--bin field_compare` — parameter / batch /
  field measurements behind `docs/soundness-budget.md`.
- `production_security_budget` test gates proven ≥ 100, conjectured ≥ 128.
- Native-hash differential checks: the `native_*` tests in each circuit module.
