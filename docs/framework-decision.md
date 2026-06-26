# Phase-0 framework decision

**Decision:** adopt **Winterfell** (v0.13.1) as the production proving framework.

## Why Winterfell

The plan's hard constraint is a **transparent, post-quantum** proof system (no trusted setup, no
elliptic curves) — anything curve-based (halo2, Groth16) is excluded because it would forfeit
Lattica's reason for existing. Winterfell is a FRI/hash-based STARK system and satisfies this.
Among the transparent-PQ candidates it is the strongest fit here because:

- **Prior art.** The original Lattica Rust prototype used Winterfell; the hand-rolled Zig STARK was
  a re-implementation of that design. Returning to Winterfell for production is the intended arc.
- **Same field.** It ships the **Goldilocks `f64`** field (p = 2⁶⁴−2³²+1) we prototyped on, so the
  arithmetization carries over directly.
- **Addresses the audit's crypto findings out of the box:**
  - **C-05 (vetted hash):** ships `Rp64_256`, a published Rescue-Prime instance (vetted MDS/round
    constants), replacing our project-local SPN.
  - **C-04 (soundness):** supports **extension-field challenges** (`FieldExtension::Quadratic`/
    `Cubic`), lifting soundness off the ~50-bit base-field bound.
  - **I-02/I-03 (RNG / engine duplication):** the framework owns the prover RNG and is a single,
    vetted engine — our duplicated hand-rolled engines leave the production path.
- **Integration fit.** Pure Rust, integrates via C ABI exactly like rubble's existing
  `tools/rubble-crypto-ffi`. Already cached locally → reproducible, offline-buildable.

Alternatives: **Plonky3** (modern, modular, also transparent-PQ — viable, but Winterfell is prior
art and a simpler AIR API for our needs); **plonky2** (predecessor of Plonky3); **RISC0/SP1**
(FRI zkVMs — more general but heavier than a hand-written AIR needs). All curve SNARKs excluded.

## Evidence — the spike (`framework-spike/`)

Re-expresses the **core of the authorization proof** (`stark.zig`): knowledge of a secret `seed`
with `seed^(7^(N-1)) = result`, enforced by the degree-7 transition `next = cur^7` — the same
S-box nonlinearity as our hash. Built on Winterfell with `f64` + `Rp64_256` + **F_p² challenges**.

```
trace length      : 1024
proof size        : 75067 bytes (~73 KB)
conjectured sec   : 127 bits        (vs. the ~50-bit hand-rolled base-field bound)
verify            : ACCEPTED
tests             : valid verifies · wrong public result rejected · matches native oracle (3/3)
```

Run: `cd framework-spike && cargo run --release` / `cargo test --release`.

## Scope & caveats

- This spike is the **x⁷ core**, not the full statement. **Phase 2** grows it into (a) the full
  Rescue-Prime *sponge* AIR and (b) the four-constraint spend — commitment opening + depth-32
  membership + nullifier + balance + a transaction-binding public input + ownership binding
  (closing C-01/C-02/C-03) — in a `lattica-prover` crate exposing prove/verify over a C ABI.
- Winterfell itself is vetted, but **our circuit is not** — Phase 3 (external audit) reviews the
  circuit + the protocol layer + the FFI glue.
- The spike's parameters (96 queries, blowup 8, grinding 16, F_p²) yield 127-bit conjectured
  security; production parameters and a written soundness budget are finalized in Phase 5.

## Next

- **Phase 1:** finalize the `lattica` Zig protocol package (note/commitment/nullifier formats,
  unified shielded tx + canonical serialization, sighash, the `verify()` FFI boundary), with the
  hand-rolled STARK retained as a differential-test oracle.
- **Phase 2:** the full spend circuit in Winterfell (`lattica-prover` crate).

---

## ZK reassessment (ZK-01) — Winterfell does **not** provide zero-knowledge

**Found in the remediation review.** This decision selected Winterfell for *transparency +
post-quantum + soundness* — but **zero-knowledge was not a selection criterion**, and a *shielded*
spend proof fundamentally requires it: a non-ZK FRI-STARK reveals trace cells at the query points
and the queried Merkle rows, leaking the hidden witness (value, recipient, `rho`, `nk`, and which
leaf/note is spent — breaking unlinkability). Note encryption hides note *contents* from third
parties; it does **not** hide the witness from the validator that checks the proof.

Investigation of the cached `winterfell-0.13.1` (the latest published version):
- `ProofOptions` has no ZK/salt toggle (only queries, blowup, grinding, field-extension, FRI, batching).
- No `salt` / `blind` / `hiding` / `zero-knowledge` in `winter-prover`; the trace/constraint
  commitments are plain Merkle trees over the LDE (no salting), and the DEEP-composition invariant
  (`poly_size−2 == degree`) assumes a non-randomized trace.
- The README does not mention zero-knowledge. Winterfell is an *integrity* STARK, not a ZK system.

So the current `lattica-prover` spend proof is **sound but not zero-knowledge** — a blocking gap.
(The hand-rolled `spend.zig` *did* implement ZK: trace blinding `T'=T+Z_H·b` + masked FRI; the
Winterfell port dropped it.)

### Options
- **A. Manual ZK on Winterfell** — add blinding columns/rows + salted commitments + masked FRI as a
  custom layer. *Re-introduces hand-rolled, soundness-critical ZK crypto and fights Winterfell's
  non-ZK assumptions — partly defeats the "use a vetted framework" rationale.*
- **B. Switch to a ZK-capable transparent-PQ FRI framework — `plonky2` (1.1.0 on crates.io, FRI over
  Goldilocks, ships a `zero_knowledge` config).** *ZK by construction from a vetted framework;
  keeps transparent + FRI/PQ. Re-expresses the circuit in plonky2's gate API; revisits this Phase-0
  decision. The circuit **design** (and the differential oracle) carries over.* **Recommended.**
- **C. Plonky3** (`p3-*`, modular; ZK story varies by component) — more assembly.
- **D. A FRI zkVM (`risc0-zkvm`, SP1)** — ZK by construction, prove the spend as a program; heaviest.

**Recommendation:** treat ZK-01 as reopening this framework choice. Because the entire product is a
*shielded* (ZK) protocol and Winterfell cannot provide ZK without substantial hand-rolled additions,
evaluate **plonky2** (option B) against the validated circuit design before further hardening. This
is a decision to make with the user / pre-audit, not a mechanical change.

### ZK-01 spike result (`plonky2-spike/`)

Built the **full spend-core statement** on plonky2 with zero-knowledge enabled
(`standard_recursion_zk_config`): ownership `recipient=Poseidon(nk)[0]`, commitment, general-position
2-level membership, nullifier, output commitment, value-balance, 32-bit range, and a tx-binding
public input. **Prove→verify ACCEPTED; `ZK re-randomized: true`** (two proofs of the same statement
differ — blinding confirmed); public inputs cross-check the native Poseidon oracle; 5/5 tests
(valid+native-match, unbalanced-fails-to-prove, out-of-range-fails-to-prove, tampered-root-rejected,
ZK-randomized).

| | Winterfell (`lattica-prover`) | **plonky2** (`plonky2-spike`) |
|---|---|---|
| Zero-knowledge | ❌ none (ZK-01) | ✅ built-in, validated |
| Field | Goldilocks 64-bit | Goldilocks 64-bit (same) |
| Transparent + post-quantum (FRI) | ✅ | ✅ |
| In-circuit hash | vetted Rescue-Prime `Rp64_256` | vetted Poseidon (gadget) |
| Arithmetization | **hand-written AIR** (periodic selectors, `rem` columns, round constraints) | **PLONKish gadgets** (hash / `range_check` / `select` built-in) |
| Hand-written soundness-critical code | high (the whole spend AIR) | low (compose gadgets) — **smaller audit surface** |
| Toolchain | **stable** | **nightly required** (`#![feature]`) |
| Proof size | ~73 KB (x⁷ core) | ~149 KB (full spend core) |
| Prove / verify | fast | ~0.9 s / ~5 ms (depth-2, demo params) |
| Maturity | Polygon Miden | Polygon zkEVM |

### ZK-01 further evaluation — Plonky3 and zkVM

To avoid plonky2's **nightly** requirement, also evaluated **Plonky3** (`p3-*` 0.6.1) and a
**zkVM** (SP1 6.3.1 / RISC0 5.0):

- **Plonky3** — *empirically builds on **stable*** (verified: `p3-field`/`p3-goldilocks`/
  `p3-uni-stark`/`p3-fri`/`p3-poseidon2` all compile on the stable toolchain). **Supports ZK**: the
  PCS carries `ZK` — enabled via `HidingFriPcs` + `MerkleTreeHidingMmcs` (hiding/salted
  commitments) — and the framework's own `fib_air` test runs both a ZK and a non-ZK config. Ships
  **`p3-goldilocks`** (our field) and **Poseidon2**, and a `security.rs` giving **proven *and*
  conjectured** soundness bounds (round-by-round, per 2024/1553) — a direct **C-04** advantage over
  Winterfell/plonky2's conjectured-only. Style is **AIR** (`impl Air` + `prove(&config, air, trace,
  pis)` / `verify`), so the existing `lattica-prover` AIR logic ports relatively directly. Cost:
  verbose config assembly (the `Val/Perm/Mmcs/Challenge/Pcs/Challenger` type stack) and hand-written
  AIR (larger audit surface than plonky2 gadgets); newer, faster-moving API. *(Confirmed via build +
  source/test inspection; a full prove-spike with the ZK PCS was not run here — fast follow-up.)*
- **zkVM (SP1 / RISC0)** — ZK by construction; the spend statement is written as an ordinary Rust
  program (no hand-written constraints → smallest *application* code/audit surface). Stable *host*
  toolchain, but needs a special *guest* toolchain (RISC-V) — **not installable in this sandbox**
  (`cargo-prove`/`sp1up`/`rzup`/`r0vm` absent, no `riscv` target), so no prove-spike. Tradeoffs:
  heaviest proving and largest proofs (compressible via their wrap/recursion), and the **largest
  trusted base** — you trust the entire (vetted) VM circuit, not just your statement.

### Decision matrix

| | Winterfell | plonky2 | **Plonky3** | zkVM (SP1/RISC0) |
|---|---|---|---|---|
| Zero-knowledge | ❌ | ✅ (spiked) | ✅ (framework-tested; not spiked here) | ✅ by construction |
| Toolchain | **stable** | **nightly** | **stable** | stable host + RISC-V guest |
| Field | Goldilocks | Goldilocks | Goldilocks (or BabyBear/Koala) | RISC-V VM |
| In-circuit hash | Rescue-Prime | Poseidon | Poseidon2 | VM-internal |
| Soundness accounting | conjectured | conjectured | **proven + conjectured** | VM's |
| Statement style | hand-AIR | **gadgets (small surface)** | hand-AIR (ports from our work) | plain Rust program |
| App audit surface | high | low | high (but reuses validated AIR) | tiny app / huge VM TCB |
| Proof size (spiked) | ~73 KB | ~149 KB | STARK-range (not spiked) | large, compressible |
| Maturity | Polygon Miden | Polygon zkEVM | SP1/Valida; newer | RISC0/SP1 production |

### Recommendation (updated)

**Plonky3 is the front-runner:** it is the only option giving **ZK + stable toolchain +
proven-security**, on our field, and our existing AIR work ports to it. **plonky2** is the strong
alternative when the smallest hand-written audit surface (gadgets) matters more than avoiding
nightly. A **zkVM** is the right call only if developer velocity / protocol-agility outweighs proof
size and a large trusted base. Suggested next step: a short **Plonky3 ZK prove-spike** (port the
spend core, enable `HidingFriPcs`) to confirm end-to-end parity with the plonky2 result before
committing. This is the user's design decision; C-04 (final FRI/PQ params + soundness budget) is
owed for whichever framework is chosen.
