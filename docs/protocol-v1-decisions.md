# Lattica protocol v1 — completeness decisions

> **Decision record:** Protocol choices that complement the normative [`../SPEC.md`](../SPEC.md).

Resolves the protocol-completeness items the audit-scope flagged (`docs/audit-scope-p3.md` §5/§6).
These are deliberate v1 scoping decisions with rationale + the limitations an auditor should weigh.
They fix the note/circuit shape that the M6 live cutover migrates to.

## 1. Asset model — **single-asset (v1)**
One native shielded asset. The join-split balance (`Σin + mint = Σout + fee`) is single-asset; notes
carry no asset field. Rationale: matches Zcash's launch; multi-asset (per-asset balance + asset
commitments, ZSA-style) is a major addition. **Future:** add an `asset_id` lane to the note
commitment and make the balance per-asset.

## 2. Keys / addresses — **diversified addresses + incoming viewing key** *(implemented)*
- `seed → nk` (the 128-bit spend / nullifier key; §2a), `div_master`, `kem_master`, `sig` (ML-DSA).
- **Diversified address** at index `i`: `(d_i, recipientId = H(DOM_OWN ‖ nk0 ‖ nk1 ‖ d_i), ek_i)` where
  `d_i` is a per-address diversifier and `ek_i` a per-address ML-KEM key. The sender encrypts the note
  to `ek_i` and sets `note.recipient = recipientId`, `note.div = d_i`. One `nk` spends notes to **any**
  of a wallet's addresses; the circuit's ownership input takes `d` as a free lane (a spender must use
  the note's real `d` or the recomputed `cm` won't be in the tree). Different addresses are
  **unlinkable** (no shared tag / KEM key).
- **Incoming viewing key** = `(div_master, kem_master)`: derives every address's diversifier + KEM
  keypair, so it **detects and decrypts** incoming notes for all of a wallet's addresses **without**
  `nk` — delegatable (watch-only / auditor) and cannot spend. (ML-KEM has no "one secret, many public
  keys" structure, so the KEM key is per-diversifier rather than shared as in Sapling's `ivk·g_d`;
  detection scans the wallet's diversifiers.)
- **Authorization** = the join-split proof (knowledge of `nk`); the tx-binding replaces a signature.
- **Residual / future:** an **outgoing** viewing key (decrypt one's own sends) and a wider diversifier
  search window are simple follow-ups; `nk` is still the single spend authority (no ask/nsk split).

## 2a. Spend authority `nk` — **128-bit (two field elements)** *(fixed during M6)*
Starting the M6 cutover surfaced that a single-element `nk` gives only **~64-bit spend authority**
(`recipient = H(nk)` is brute-forceable in ~2⁶⁴ hashes ⇒ note theft). **Fixed:** `nk` is now **two
Goldilocks elements (128-bit)**; ownership `recipient = H(DOM_OWN ‖ nk0 ‖ nk1)` and `nf = H(DOM_NF ‖
nk0 ‖ nk1 ‖ rho ‖ pos)` (both fit the width-8 hash without touching the commitment's lane budget).
Implemented in `joinsplit_air` + `poseidon2.zig` (KAT-matched); 37 Rust + full Zig suite pass.

## 3. Note randomness `rho`, `rcm` — **128-bit (two field elements each)** *(done)*
Originally 1 field element each (~64-bit, forced by the 8-lane single-permutation commitment). **Now
widened to 128-bit**: the commitment is a two-permutation Merkle-Damgård chain
`cm = H₂(H₁(DOM_CM ‖ recipient(4) ‖ value ‖ rho0 ‖ rho1) ‖ rcm0 ‖ rcm1)`, so `rho`/`rcm` are each two
Goldilocks elements while `recipient` stays a 256-bit digest. The 256-bit chaining value gives 128-bit
collision resistance. `rho` uniqueness (now 128-bit) gives nullifier uniqueness; the birthday bound
moves from ~2³² to ~2⁶⁴ notes. Implemented in `joinsplit_air` + `poseidon2.zig` (KAT-matched);
validated by the full suite + the real in-node prove→verify.

**Interaction with deterministic note encryption.** Note encryption is deterministic — the ML-KEM
encapsulation coins are `expand(cm, "kem-encaps")` and the AEAD key+nonce are `H(ss ‖ kem_ct ‖ cm ‖ …)`
(`primitives.deriveNoteKey`), all derived from `cm` (chosen for seed-restorability, no stored `esk`).
The AEAD `(key,nonce)` is therefore unique up to a `cm` collision.

> **Corrections (v3 round-2 internal audit).** Two claims here were imprecise:
> 1. **`cm` does NOT bind the *full* plaintext** (finding M-2). It binds `recipient`, `value`,
>    `rho[0..16]`, `rcm[0..16]`, `asset`, `note_type` — but **not** the wire `div`, nor the high 16
>    bytes of `rho`/`rcm`. So distinct plaintexts can share a `cm` (hence a `(key,nonce)`) **without**
>    a hash collision. This was assessed **inert** (only a malicious sender, who already knows both
>    plaintexts, can trigger it; the unbound bytes are never read) — but the invariant as written is
>    false. The `div` half is what enabled the **M-3** griefing (fixed: decryption now re-derives `div`
>    from the matched address index).
> 2. **The determinism is not merely a stylistic difference** — deriving the encaps coins from the
>    *public* `cm` makes `kem_ct` publicly recomputable from the recipient's *public* address, a
>    **recipient-deanonymization oracle** (finding **H-1**, HIGH). See `v3-internal-audit-round2.md` §3
>    for the fix options (OVK-derived coins preserve restorability while closing the oracle).

This differs from a randomized scheme (Zcash uses a fresh `esk` per note + an OVK so the sender can
still recover sent notes without leaking recipient anonymity); the H-1 fix adopts the OVK part.

## 4. Issuance — **mint (v1); burn deferred**
Shielded issuance via a **public `mint` amount** in the join-split balance:
`Σ in_value + mint = Σ out_value + fee`. `mint` is a public input, range-checked like any value, and
**consensus enforces** the issuance rules (block-reward / supply schedule) on it. A coinbase
transaction sets `mint > 0` with all-dummy inputs; a normal transaction sets `mint = 0`.
- **Burn:** deferred for v1; modeled later as a public burn amount or a canonical unspendable
  `recipientId`.
- **Impact:** a contained join-split change — the value accumulator starts at `mint` and `mint` is a
  public input (range-checked). Implemented in `joinsplit_air` (see the mint commit).

## 5. Transaction shape — **fixed 2-in/2-out + dummy notes** (recap)
Already decided/built: fixed `(N_IN, M_OUT) = (2, 2)`; smaller transactions pad with zero-value dummy
notes. A variable-shape circuit is only needed beyond 2-in/2-out.

## M6 live cutover — sequence (status: COMPLETE)
The decisions above fixed the target shape; the live cutover landed incrementally, suite green at
each step:
1. ✅ **Mint** in the circuit (per §4) — public issuance in the balance.
2a. ✅ **128-bit spend authority** (`nk` → 2 field elements) — found + fixed during the cutover.
2. ✅ **On-chain hashing → Poseidon2 (C-03):** `Address.recipientId = H(nk)`, `Note.commitment`,
   `Note.nullifier`, and the Merkle node hash use `poseidon2.zig` (KAT-equal to the circuit), so the
   node-reconstructed public inputs equal the proof's. Note wire format kept; fields reduce to field
   elements canonically.
3. ✅ **`lattica_joinsplit_prove`** wallet-side prover ABI (canonical witness layout, fail-closed).
4. ✅ **Hidden-value node tx model:** `ShieldedTx` is now the join-split statement (anchor, N
   nullifiers, M output commitments, fee, mint, proof, output ciphertexts) — revealed values, native
   membership/balance, and the ML-DSA binding signature are **removed**. `verifyAndApply` authorizes
   via `ffi.verifyJoinSplit` alone (fail-closed); a canonical `tx_binding` digest of the body binds
   the proof to the tx (replacing the binding signature). `buildTransfer` builds the witness
   (siblings + position bits + reduced felts) and proves via the prover backend.
5. ✅ **Consolidate:** the single production circuit is `joinsplit_air` (`full_spend_air` + spend ABI
   removed); `node.zig` no longer uses `circuit.zig` (it remains only for `wallet bench` / `kat`).

**Backend seam.** The node calls the Rust `lattica_joinsplit_verify` (and the wallet
`lattica_joinsplit_prove`) via `ffi.set*Backend`, installed at startup. On hosts whose linker can't
link the Rust staticlib (this one — see `ffi_integration.zig`), tests + the `wallet demo` install
mock backends that model the proof's tx-binding; the real prove→verify is covered by the Rust tests +
`lattica-prover-p3/tests/ffi_integration.c`.
