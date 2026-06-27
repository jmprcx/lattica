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

## M6 live cutover — sequence (status: staged)
The decisions above fix the target shape. The live cutover (`node.zig` still runs the old
`circuit.zig` generic-preimage proof) is sequenced as:
1. **Mint** in the circuit (per §4) — *done* (contained; ABI/public-inputs updated).
2. **On-chain hashing → Poseidon2 (C-03):** `Address.recipientId`, `Note.commitment`,
   `Note.nullifier`, and the Merkle node hash (`tree.zig`) switch from SHA3 to `poseidon2.zig`, so the
   node-reconstructed public inputs equal the proof's. Keep the note wire format; reduce note fields
   to field elements canonically.
3. **`lattica_joinsplit_prove`** (wallet-side prover ABI) so the wallet produces real proofs.
4. **Node verify swap:** `ShieldedTx` carries a join-split proof; `verifyAndApply` calls
   `ffi.verifyJoinSplit` (backend = `lattica_joinsplit_verify`) and reconstructs `JoinSplitPublicInputs`
   from the tx; demote the native membership/nullifier/balance checks to consistency.
5. **Consolidate:** drop `circuit.zig` (old proof) and the reference `full_spend_air` + its ABI.
This is a broad refactor of the live path + the test suite; it lands incrementally, each step
keeping the suite green.
