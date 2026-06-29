# Multi-Asset, Exchanges & Issuance/Bridging — Architecture Decision Memo

**Audience:** CTO / technical leadership. **Status:** decision memo (no code committed).
**Scope:** the rubble shielded chain (lattica protocol layer) + the cross-chain stack
(`rubble-xchain-xfer`). Frames the design space, trade-offs, effort/risk, and a recommended
sequence for (1) multi-asset support, (2) exchange integration, (3) issuance & bridging.

---

## 0. TL;DR for the CTO

- **Where we are:** a feature-complete, validated **single-asset, shielded-only** payment protocol
  (Plonky3 join-split, Poseidon2, 128-bit security throughout, ZK, diversified addresses + an
  incoming viewing key). The remaining gate is an external audit.
- **The defining constraint:** we are **post-quantum and hash-based — there are no homomorphic value
  commitments.** Zcash's multi-asset (ZSA) and its O(1) exchange detection both *rely* on elliptic-curve
  homomorphism. We cannot port those for free; this shapes every decision below.
- **Three independent decisions**, each with a "cheap/standard" and an "expensive/ambitious" path:
  1. **Multi-asset** — *revealed* asset type (tractable) vs *hidden* asset type (research-grade).
  2. **Exchanges** — *shared-KEM deposit addresses* (scales, Monero-style) vs *per-diversifier* (private, doesn't scale).
  3. **Bridging** — federated lock-and-mint (ship now) → SPV → ZK (trust-minimized, later).
- **Recommendation:** treat single-asset payments as v1 and **audit it now**. Pursue multi-asset only
  if the product needs tokens; if so, ship **revealed-asset-type** multi-asset + **federated bridges**
  + **shared-KEM exchange addresses** as v2, and hold *hidden* asset type and *trust-minimized*
  bridges as v3 research tracks.

---

## 1. Current architecture (baseline)

- **lattica** = the shielded transaction layer (replaces Zcash Sapling/Orchard): a Plonky3
  N-in/M-out **join-split** circuit; Poseidon2-Goldilocks hashing on-chain == in-circuit; 128-bit
  spend key, 128-bit note randomness, ZK blinding; **diversified addresses** + a delegatable
  **incoming viewing key**; validated end-to-end (real prove→verify in-node). Value model is
  **shielded-only** and **single-asset**. Proven soundness ~103-bit (~127 conjectured) — the
  Goldilocks ceiling.
- **rubble-node** = the host chain (consensus, blocks, the transparent layer, RPC). Kept minimally
  changed by policy.
- **rubble-xchain-xfer** = a noncustodial **P2P atomic-swap** stack (BTC/XMR/ZEC/**fork=rubble**).
  Swaps the rubble side via **transparent P2SH HTLC** (ZIP-300 style). Crucially: **chain ≡ asset**
  everywhere (`Chain={Btc,Zec,Fork}`, `Amount=u64`, no asset id).

---

## 2. Multi-asset

### 2.1 What it provides
Many distinct asset types (native coin + tokens/stablecoins/wrapped assets) in **one** shielded pool,
all with identical privacy; per-asset balance conservation (`Σin_a + mint_a = Σout_a + fee_a`);
cross-asset transactions (move several assets in one tx — prerequisite for shielded DEX, fee
abstraction). See §5 for how an asset is *born*.

### 2.2 Why it's hard for us (the homomorphism gap)
Zcash ZSA gets per-asset balance *and* asset-type privacy almost free: value commitments are
homomorphic (Pedersen with an asset-specific generator), so summing commitments enforces per-asset
balance on the curve and hides the asset. **We have no homomorphic commitments** — balance is an
explicit in-circuit accumulator over values the circuit sees. So per-asset balance must be enforced
by circuit logic, and hiding the asset type is genuinely hard.

### 2.3 Options

| | **M1 — Revealed asset type** | **M2 — Hidden asset type** |
|---|---|---|
| Note | `cm = H(recipient, asset_id, value, rho, rcm)` | same |
| Balance | per-asset accumulator over a small fixed set of asset "slots" declared by the tx (asset id revealed in-circuit/public per slot) | prove the per-asset partition in-circuit without revealing which assets — needs a new gadget |
| Privacy | amounts hidden; **asset type visible** | amounts **and** asset type hidden |
| Effort | **Moderate** — core balance redesign + note/witness/ABI (akin to the rho-widening) | **Research-grade** — the hardest item on the roadmap for a hash-based system |
| Risk | contained; auditable | high; novel cryptography |

### 2.4 Recommendation
If multi-asset is in scope, ship **M1 (revealed asset type)**: amounts stay private, the asset type
is public (acceptable for most token/stablecoin use; it's what most non-ZSA chains do). Keep **M2** as
a research track only if asset-type privacy is a product requirement (e.g., confidential DeFi).

---

## 3. Exchanges on a shielded chain

### 3.1 The core problem
No transparent address to "watch." Deposits are encrypted notes (`cm, kem_ct, ciphertext`); the
exchange must **scan every block and trial-decrypt** to find them. This is the whole integration cost
(same reality as Zcash/Monero).

### 3.2 The primitives already exist
- **Per-user deposit address** = a diversified address from one wallet (no N keypairs to manage).
- **Hot deposit scanner** = the **incoming viewing key** — detects + decrypts all users' incoming
  notes, **cannot spend** → safe online.
- **Cold spend key** = offline; only for withdrawals.

**Deposit flow:** user gets deposit address `i` → sends a note → scanner decrypts → recovers
`(value, asset, recipient)` → the cm-bound **`recipient` (= H(nk‖dᵢ))** identifies user `i` (NOT the
malleable wire `dᵢ` — see below) → credit after N confirmations.

**Withdrawal flow:** spend the exchange's notes with the cold key → a join-split paying users. Proving
needs the spend key (offline/HSM proving step, not the hot scanner) and costs ~seconds + ~0.5 MB/proof
→ high volume wants **batched proving** and a wider-than-2-in/2-out shape.

### 3.3 The scaling decision (important)
Our diversified addresses derive a **separate ML-KEM keypair per address**, so detection is
**O(users) decaps per output** — fine for a personal wallet, **does not scale** to exchange user
counts (100k users ⇒ 100k decaps per note). The PQ tax: Zcash's `ivk` is O(1) per note via
`pk_d = ivk·g_d`; ML-KEM has no analog.

| | **Per-diversifier KEM (wallet mode)** | **Shared-KEM exchange mode** |
|---|---|---|
| Detection | O(users) decaps/output — wallet-scale only | **O(1)** decap/output, then route by the cm-bound recipient |
| Unlinkability | full + unconditional (distinct KEM key per address) | exchange's deposit addresses share `kem_ek` (never on-chain; `cm` still hiding) — rests on ML-KEM **ciphertext anonymity (IK-CCA)** |
| Pattern | privacy-max personal wallet | Monero integrated-address / payment-ID |

**Status: IMPLEMENTED — both modes coexist in `src/tx.zig`.** Wallet mode is `addressAt` /
`IncomingViewingKey`; exchange mode is `exchangeAddressAt(index, epoch)` + `ExchangeViewingKey`
(`FullKey.exchangeViewingKey(allocator, n_users, epoch)` to build it; `addRecipient` for nk-free
onboarding; `detect` for O(1) scanning). Same `nk`/`div`/circuit — only the KEM key is shared, off-chain.
The scanner routes by the **cm-bound `recipient_id`** (re-deriving `dᵢ` from the matched index), *not*
the wire diversifier, so a hostile sender cannot misattribute or brick a deposit (audit M-3). The
`detect` path's `note.commitment() == cm` check is load-bearing — it binds the credited value/asset to
what is actually committed on-chain (AEAD success alone proves nothing, since anyone can encapsulate to
the public shared `ek`). A note **memo** field would serve the same routing role; the diversifier already
does. Demo: `zig build run -- exchange`. Threat model is recorded in `docs/audit-scope-p3.md` §2.

This same shared-KEM scheme is **also reused for mining-reward payouts** (a pool/exchange detects its
many small reward notes in O(1)) in the heartbeat block-production design — see
`docs/block-production-consensus.md` §6.

### 3.4 Multi-asset interaction
With M1/M2 the note carries `asset_id`; deposit detection credits `(asset, value, user)`; withdrawals
select notes of the requested asset. Flow shape unchanged — gains an asset dimension.

---

## 4. xchain (cross-chain swap) impact

xchain swaps the fork's **transparent** coin via P2SH HTLC; multi-asset is a **shielded** feature, so
the impact is governed by how a swappable rubble asset is represented:

- **A — Native-only:** tokens aren't swappable via this stack; xchain ~unchanged.
- **B — Transparent asset-tagged HTLC:** thread an `AssetId` through the whole stack (core types,
  `htlc-engine`; per-asset UTXO scan/coin-select + asset-committing HTLC in `chains/zec`; the
  **versioned wire protocol** — offers/quotes/setup-PoW/trade-records → protocol-version bump;
  orderbook pair space, admission caps, CLI, rubbled RPC). Broad but mechanical — **but it requires
  multi-asset in rubble's *transparent consensus*, contradicting shielded-only.**
- **C — Shielded HTLC:** add a hash+time-locked spend mode to **lattica's circuit** and rewrite
  xchain's fork backend to a shielded-note HTLC. Biggest change, touches both repos; the only option
  consistent with shielded-only multi-asset.

Recommendation: keep xchain **native-only (A)** for v2; revisit **C** if shielded tokens must be
cross-chain-swappable noncustodially.

---

## 5. Issuance & bridging (how an asset is born on rubble)

### 5.1 Native issuance (built)
The validated **coinbase/issuance** path: `mint` is a public, range-checked input to the join-split
balance, gated by consensus (`applyCoinbase(tx, reward)`); normal txs require `mint = 0`. Covers the
base coin's emission + fee collection. **Generalizes to per-asset issuance** under M1/M2.

### 5.2 Issuer-authorized assets (user-issued tokens)
For tokens/stablecoins minted by a designated issuer: bind an **issuance authorization** to each
`asset_id` (an issuer key whose signature/proof authorizes a per-asset mint), with auditable supply.
Requires multi-asset (M1/M2) + an issuance-key binding in the circuit/consensus. Variants: capped vs
uncapped supply; single issuer vs governance/multisig issuer.

### 5.3 Bridges (assets that exist elsewhere, represented on rubble)
A bridge mints a **wrapped** shielded asset on rubble against value locked on a source chain (and
burns to unlock). All sit on a **trust-minimization vs complexity** spectrum:

| Design | Trust assumption | Complexity | Notes |
|---|---|---|---|
| **P2P atomic swap (xchain)** | none (noncustodial) | exists today | *Not a bridge* — swaps native coin ↔ BTC; creates **no** wrapped asset on rubble. The trustless way to *trade*, not to *represent*. |
| **Custodial lock-and-mint** | a single custodian | low | Fastest to ship; weakest trust. Mints a wrapped `asset_id` (issuer-authorized, §5.2). |
| **Federated / MPC (n-of-m)** | honest threshold of signers | medium | Distributed custody; standard for early bridges. Pairs with §5.2 issuer = the federation key. |
| **Light-client / SPV** | source chain's consensus (e.g. PoW) | high | Rubble verifies source-chain headers/SPV proofs to authorize mint; trust-minimized; heavy (header sync, reorg handling). |
| **ZK bridge** | cryptographic only | very high | A SNARK proves the source-chain lock event; strongest. Hard here: verifying foreign signature/hash schemes (e.g. Bitcoin ECDSA/secp, SHA-2) inside a PQ-friendly proof system is a major build. |

**Interaction with the shielded pool:** a bridged asset is just another `asset_id` in the shielded
pool — it inherits full shielding; bridge mint/burn are issuance ops authorized per §5.1/§5.2 (issuer
key for custodial/federated; an on-chain proof for SPV/ZK). Anchoring infrastructure already used by
xchain (`anchor-rubble`) is a precedent for posting bridge state to the chain.

### 5.4 Recommendation
Ship **federated lock-and-mint** first (fastest path to tokens/wrapped assets, well-understood trust
model), explicitly documenting the trust assumption. Treat **SPV** and especially **ZK** bridges as
later trust-minimization upgrades, not v2.

---

## 6. Cross-repo blast radius

| Workstream | lattica | rubble-node | rubble-xchain-xfer |
|---|---|---|---|
| M1 multi-asset | circuit balance redesign + note/witness/ABI | per-asset balance/supply consensus + RPC asset fields | only if xchain option B/C (else none) |
| Exchange shared-KEM addresses | small `tx.zig` addition | optional deposit-scan RPC helpers | n/a |
| Native/issuer issuance | mint generalization + issuer-auth binding | issuance policy/consensus | n/a |
| Federated bridge | wrapped-asset issuance hook | bridge contract/consensus + federation verification | optional (P2P swap already exists) |
| Trust-minimized bridge | (ZK) cross-chain proof verification | SPV/proof verification consensus | n/a |

---

## 7. Sequencing & recommendation

1. **Now:** external audit of the single-asset v1 (the gate). No new scope.
2. **v2 (if tokens are a product goal):** M1 revealed-asset multi-asset → issuer-authorized issuance →
   federated lock-and-mint bridge → shared-KEM exchange addresses. Each is contained + auditable.
3. **v3 (research):** hidden-asset-type (M2), SPV/ZK bridges, shielded-HTLC cross-chain swaps (xchain C),
   higher proven soundness via a larger field.

**Decisions the CTO must make:** (a) is this a payments chain or a token platform? (drives whether v2
happens at all); (b) if tokens — is **asset-type privacy** required? (M1 vs M2); (c) bridge **trust
model** acceptable for launch (custodial/federated vs trust-minimized); (d) target **exchange scale**
(personal-wallet privacy vs CEX-scale detection).

---

*Sources: this analysis is grounded in the current lattica implementation (built + validated) and a
read of `rubble-xchain-xfer` (htlc-engine, chains/zec, p2p, market, daemon, anchor-rubble). It is a
decision memo, not an implementation plan.*
