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
