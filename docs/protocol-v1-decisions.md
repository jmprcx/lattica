# Lattica protocol v1 — completeness decisions

Resolves the protocol-completeness items the audit-scope flagged (`docs/audit-scope-p3.md` §5/§6).
These are deliberate v1 scoping decisions with rationale + the limitations an auditor should weigh.
They fix the note/circuit shape that the M6 live cutover migrates to.

## 1. Asset model — **single-asset (v1)**
One native shielded asset. The join-split balance (`Σin + mint = Σout + fee`) is single-asset; notes
carry no asset field. Rationale: matches Zcash's launch; multi-asset (per-asset balance + asset
commitments, ZSA-style) is a major addition. **Future:** add an `asset_id` lane to the note
commitment and make the balance per-asset.

## 2. Keys / addresses — **minimal model (v1)**
- `seed → nk` (the spend authority / nullifier key, one Goldilocks element). The circuit binds
  ownership `recipient = H(DOM_OWN ‖ nk)` and derives `nf = H(DOM_NF ‖ nk ‖ rho ‖ pos)`.
- **Address** = (`recipientId = poseidon2.recipient(nk)` digest, `ML-KEM` encapsulation key). The
  sender encrypts the note to the ML-KEM key and sets `note.recipient = recipientId`.
- **Detection** = ML-KEM trial-decryption (the recipient decrypts candidate notes).
- **Authorization** = ML-DSA signature over the tx-binding (sighash).
- **Limitations (threat model):** no **diversified addresses** — repeated payments to one address
  share `recipientId`, so they are protocol-linkable (mitigated only by using fresh addresses); no
  separate **incoming-viewing key** — detection needs the ML-KEM secret, so viewing can't be
  delegated without the spend-adjacent secret; `nk` is the single spend authority (no ask/nsk split).
- **Future:** diversified addresses (per-payment `recipientId`) and an `ivk`/`ovk` viewing hierarchy.
- **Cutover requirement:** `Address.recipientId` must equal `poseidon2.recipient(nk)` so the on-chain
  commitment equals the circuit's.

## 2a. Spend authority `nk` — **128-bit (two field elements)** *(fixed during M6)*
Starting the M6 cutover surfaced that a single-element `nk` gives only **~64-bit spend authority**
(`recipient = H(nk)` is brute-forceable in ~2⁶⁴ hashes ⇒ note theft). **Fixed:** `nk` is now **two
Goldilocks elements (128-bit)**; ownership `recipient = H(DOM_OWN ‖ nk0 ‖ nk1)` and `nf = H(DOM_NF ‖
nk0 ‖ nk1 ‖ rho ‖ pos)` (both fit the width-8 hash without touching the commitment's lane budget).
Implemented in `joinsplit_air` + `poseidon2.zig` (KAT-matched); 37 Rust + full Zig suite pass.

## 3. Note randomness `rho`, `rcm` — **one field element each (~64-bit) in v1**
The width-8 Poseidon2 commitment input is `[DOM_CM, recipient(4), value, rho, rcm]` — 8 lanes, full —
so `rho` and `rcm` are single Goldilocks elements (~64-bit). `rho` uniqueness gives nullifier
uniqueness. **Limitation:** 64-bit per-note randomness; the birthday bound on `rho` becomes a concern
around `2^32` notes. **Decision:** accept 64-bit for v1 launch parameters and flag for the audit;
**future:** widen via a two-permutation (sponge) commitment or a wider permutation, which lifts `rho`
to ≥128-bit. (An auditor should explicitly sign off on the launch `rho` width.)

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
