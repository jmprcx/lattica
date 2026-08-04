# Prover ↔ node wire formats (normative)

> **Document role:** Normative byte-level contract between Rust proof code and Zig consumers.

The Zig node and the Rust prover (`lattica-prover-p3`) exchange bytes across the C ABI declared in
`lattica-prover-p3/include/lattica_prover_p3.h` (mirrored by `src/ffi_integration.zig`,
`src/integration_node.zig`, `lattica-prover-p3/tests/ffi_integration.c`). Everything on this page is
**frozen**: a change is a node-seam break, and for the starred (★) items a consensus break.

## Proof bytes

`postcard::to_allocvec(p3_uni_stark::Proof<MyConfig>)` — **no version prefix**. Pinned to:

- p3-* **0.6.1** struct definitions (serde derives), postcard 1.x;
- the production config `MyConfig` in `lattica-prover-p3/src/config.rs` ★: Goldilocks, F_p²
  challenges, Poseidon2-8 sponge/compress, salted `MerkleTreeHidingMmcs` (ChaCha20, 2/4/4),
  `HidingFriPcs` with 4 random codewords, FRI `{log_blowup: 4, num_queries: 96, query_pow: 16 bits,
  arity ≤ 2⁴, cap height 6}` (≈103-bit proven / ~127-bit conjectured).

Verifiers reject `proof_len > MAX_PROOF_LEN = 1 << 21` (audit M-08; `src/ffi.zig` mirrors the bound).

## Digests

32 bytes = 4 Goldilocks limbs, **little-endian u64 each, canonical** (< p); non-canonical limbs fail
closed on every parse path.

## Public inputs (little-endian, byte-exact)

| circuit | bytes | layout |
|---|---|---|
| join-split | 208 | `anchor(32) ‖ nf₀(32) ‖ nf₁(32) ‖ out_cm₀(32) ‖ out_cm₁(32) ‖ tx_binding(32) ‖ fee(u64) ‖ mint(u64)` |
| HTLC | 248 | join-split layout ‖ `current_height(u64) ‖ redeem_hashlock(32)` |

Note the wire order differs from the in-circuit `PI_*` order (`lib.rs` re-orders on parse/encode);
`PI_*` in `joinsplit_air.rs`/`htlc_air.rs` is the in-circuit layout.

## Witness records (wallet → prover)

Fixed-length concatenated records; the normative field order is `lib.rs` (`js_witness_len` /
`htlc_witness_len`). `JS_WITNESS_LEN = 2464`, `HTLC_WITNESS_LEN = 2728`. The **join-split** record,
per input: `nk0,nk1 (u64) ‖ diversifier ‖ asset ‖ value ‖ rho0,rho1 ‖ rcm0,rcm1 ‖ 32×sibling(32) ‖
32×path-bit (1 byte each, strictly 0/1)`. The **HTLC** record extends it per `lib.rs`'s
`parse_htlc_witness` (note_type, mode, redeem/refund tags, hashlock, timeout, current_height —
do not infer the layout from this page). Batch proving: `witness_len == n_tx × record_len`, and
`padded_tiles(n_tx) ≤ MAX_BATCH_TILES = 64` ★.

## Batch tx-root ★

The batch proof's only public input: the block tx-root digest (32-byte wire form above). Defined as
the `DOM_TXROOT`-tagged Merkle–Damgård fold over per-tx statement digests (chunk order: `[dom‖anchor]`,
each nullifier, each out_cm, `[fee, mint, 0, 0]`, `tx_binding`, and for HTLC additionally
`[current_height,0,0,0]` + hashlock). The node recomputes it natively (`src/poseidon2.zig`
`txStatementDigest`/`batchRoot`, KAT-pinned by `dump_p2`); the circuits reproduce the same chain
in-circuit (`batch_joinsplit_air.rs` / `batch_htlc_air.rs`).

## Hash / domain constants ★

Poseidon2-Goldilocks W=8 with the vetted `GOLDILOCKS_POSEIDON2_RC_8_*` constants; domain-separation
tags per `lattica-prover-p3/src/domains.rs` (the normative table): `DOM_OWN=1, DOM_CM=2, DOM_NF=3,
DOM_HTLC=4, DOM_NF_HTLC=5, DOM_TXROOT=6`; note types `NOTE_PLAIN=0, NOTE_HTLC=1` (commitment lane 7);
asset id in commitment lane 6. Cross-language equality is KAT-pinned (`dump_p2` → `src/poseidon2.zig`).

## Return codes

- verify: `0` accept, nonzero reject (fail-closed; never unwinds across the ABI).
- prove: `0` ok; `1` malformed/invalid input or internal failure; `2` output buffer too small —
  on rc=2 the `*_len` outputs are **not** written (caps are checked before any store); size buffers
  from `MAX_PROOF_LEN` / the fixed PI widths. `*_len` are written only on rc=0.
