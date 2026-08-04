# Lattica's Post-Quantum Zero-Knowledge Transaction Stack

> **Technical overview:** An explanatory tour of the cryptographic stack. The normative protocol is [`SPEC.md`](SPEC.md), and current assurance claims are indexed in [`docs/README.md`](docs/README.md).

Lattica is a shielded-payment design that avoids elliptic curves, pairings, and discrete-log assumptions. Its core is a hash-based Plonky3 FRI-STARK, surrounded by lattice-based note encryption and symmetric cryptography.

The project is a working, audited proof-of-concept baseline rather than a deployment-ready cryptocurrency.

## Stack overview

| Layer | Construction | Purpose |
|---|---|---|
| Zero-knowledge proof | Plonky3 FRI-STARK | Proves transaction validity without revealing notes, values, owners, or Merkle paths |
| Arithmetic field | Goldilocks base field with quadratic-extension challenges | Efficient computation with an approximately 127-bit Fiat-Shamir challenge space |
| Circuit and protocol hash | Poseidon2-Goldilocks | Commitments, ownership, nullifiers, Merkle nodes, and STARK commitments |
| Recipient encryption | ML-KEM-768 | Post-quantum encapsulation of note-encryption secrets |
| Payload encryption | ChaCha20-Poly1305 | Confidentiality and integrity for note plaintexts |
| External hashing and KDF | SHA3-256 | Domain-separated digests, key derivation, and transaction framing |
| Wallet signatures | ML-DSA-44 | Key-hierarchy and transparent-signature functionality; shielded spends are authorized by the proof itself |

## What the STARK proves

The production join-split has two inputs and two outputs. Smaller transactions are represented using dummy zero-value notes.

Its public statement contains:

- a historical Merkle anchor;
- input nullifiers;
- output note commitments;
- fee and mint amounts;
- a canonical `tx_binding` digest.

The private witness contains:

- the spend/nullifier key;
- input and output values;
- note randomness and commitment trapdoors;
- recipients and diversifiers;
- Merkle authentication paths and positions.

The arithmetic circuit proves all of the following simultaneously:

1. Each input commitment is present beneath the public Merkle anchor.
2. The prover knows the 128-bit spending key corresponding to each input recipient.
3. Each public nullifier was correctly derived from that key, the note randomness, and its hidden tree position.
4. Each output commitment was correctly formed.
5. Values are range-constrained and satisfy:

   ```text
   sum(inputs) + mint = sum(outputs) + fee
   ```

6. All public transaction fields, including `tx_binding`, are bound to the proof through Fiat-Shamir.

The node therefore learns that the transaction conserves value and spends genuine, authorized notes, but it does not learn which leaves were spent or what the private input and output values are.

## Commitments and ownership

Notes use a two-permutation Poseidon2 commitment. Conceptually:

```text
recipient = Poseidon2(DOM_OWN, nk₀, nk₁, diversifier)

h₁ = Poseidon2(DOM_CM, recipient, value, rho₀, rho₁)

cm = Poseidon2(h₁, rcm₀, rcm₁, asset, note_type)
```

The random `rcm` trapdoor hides the note contents, while Poseidon2 collision resistance supplies binding.

Spend authorization is proven inside the STARK: the spender demonstrates knowledge of `nk₀` and `nk₁` without revealing them. This replaces the elliptic-curve spend-authorization signatures normally used by shielded-payment systems.

## Nullifiers and double-spend prevention

A spend publishes a nullifier derived as follows:

```text
nf = Poseidon2(DOM_NF, nk₀, nk₁, rho₀, rho₁, position)
```

The circuit proves that this is the correct nullifier for the committed note. The node rejects a nullifier if it has appeared before, preventing double spends without revealing the corresponding note commitment.

Including the Merkle-tree position binds the nullifier to the note's actual location in the commitment tree.

## How zero knowledge is achieved

The production proof uses Plonky3's hiding polynomial-commitment configuration. Witness columns are randomized before their low-degree extensions are committed, so queried openings do not directly expose private trace values. The Fiat-Shamir transcript then converts the interactive STARK protocol into a randomized, non-interactive proof.

Privacy therefore comes from a combination of:

- hiding commitments to witness traces;
- randomized proofs;
- exposing only constrained public digests;
- proving membership, ownership, nullifier derivation, commitments, and balance inside one circuit.

The proof system is transparent: it requires no trusted setup or toxic-waste ceremony.

## Post-quantum security basis

The principal security assumptions are:

- FRI proximity-testing soundness;
- collision and preimage resistance of Poseidon2 and SHA3;
- the random-oracle model for Fiat-Shamir;
- module-lattice security for ML-KEM and ML-DSA;
- symmetric security of ChaCha20-Poly1305.

These primitives are believed to resist known quantum attacks. Because Grover's algorithm reduces generic hash-search security, the stack uses approximately 256-bit hashes or four-Goldilocks-element digests to retain roughly a 128-bit generic security margin where required.

The configured STARK uses:

- the Goldilocks base field;
- quadratic-extension challenges of approximately 127 bits;
- FRI blowup 16;
- 96 FRI queries;
- 16 bits of query grinding;
- four-element Poseidon2 commitments.

The repository reports approximately **103-bit proven soundness** and **127-bit conjectured effective soundness**, with machine-checked gates requiring at least 100 bits for the production circuits.

## Note encryption

The zero-knowledge proof hides the transaction witness, while a separate encryption layer lets recipients discover and recover output notes:

1. ML-KEM-768 encapsulates a shared secret to the recipient's public encryption key.
2. A key and nonce are derived for the note.
3. ChaCha20-Poly1305 encrypts and authenticates the note plaintext.
4. The recipient decapsulates, decrypts, and verifies that the recovered note recreates its public commitment.

This encryption layer is complementary to the STARK. ML-KEM protects note delivery; the STARK proves that the hidden transaction is valid.

## Transaction lifecycle

```text
Wallet scans ML-KEM-encrypted notes
        ↓
Selects notes and constructs a private witness
        ↓
Generates the hiding FRI-STARK join-split proof
        ↓
Publishes the anchor, nullifiers, output commitments,
fee/mint, ciphertexts, tx_binding, and proof
        ↓
Node checks canonical encoding, the known anchor,
fresh nullifiers, issuance rules, and STARK validity
        ↓
Node atomically records nullifiers and appends outputs
```

One important distinction is that the current shielded transaction does not depend on an ML-DSA binding signature. Spend authorization is knowledge of the spending key inside the STARK, while the public `tx_binding` value binds the proof to the exact canonical transaction body.

## Current limitations

Lattica demonstrates a complete post-quantum shielded transaction path, but its production claim does not cover every component needed for a live cryptocurrency. Remaining areas include:

- networking and mempool policy;
- reorganization handling and complete consensus integration;
- operational wallet and prover-key management;
- production recursive proof aggregation;
- final independent review of the documented cryptographic assumptions.

In short, Lattica obtains post-quantum zero-knowledge transactions by combining a transparent, hash-based FRI-STARK with Poseidon2 commitments and Merkle trees, ML-KEM note delivery, SHA3 key derivation, and ChaCha20-Poly1305 payload encryption. Authorization, membership, double-spend prevention, and value conservation are all tied together inside the zero-knowledge statement.
