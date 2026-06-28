# Lattica Transaction Stack Production Audit

> **⚠ Historical / reference-only — not the v1 audit artifact.** This is the earlier (2026-06-26)
> pre-Plonky3 audit; its findings are tracked as closed/superseded in `remediation-status.md`. The
> current implementation audit is `lattica-implementation-audit.md`. Start at [`AUDITORS.md`](AUDITORS.md).

**Date:** 2026-06-26  
**Basepoint:** `docs/audit-scope.md`  
**Scope:** transaction validation, note/key primitives, Merkle state, live authorization STARK, and the standalone full-spend AIR direction.

## Executive Summary

The current transaction stack is a strong proof of concept, but it is not production-ready for value-bearing deployment. The main blocker is not a broken hash or signature primitive; it is that the live node still accepts transactions whose authorization proof is not bound to the note being spent, the revealed nullifier, the transaction binding key, or the transaction body beyond carrying the proof bytes in the digest.

The older trivially invertible authorization relation has been replaced by a Rescue-style preimage proof, which is a material improvement. However, the live protocol still enforces membership, nullifier uniqueness, and value balance natively in `node.zig`, while the full in-circuit spend proof remains standalone in `spend.zig` and is not wired into validation. Current STARK parameters are also explicitly PoC-grade, with about 50-bit conjectured soundness due to base-field challenges.

Result: **not suitable for production use without remediation of the critical findings below.**

## Severity Legend

- **[C] Soundness:** accepts false proofs or forged spends.
- **[Z] Zero-knowledge:** leaks witness data.
- **[L] Liveness/completeness:** rejects honest transactions or can be crashed/DoSed.
- **[I] Hardening/informational:** production hygiene, parameter, or maintainability issue.

## Critical Findings

### [C-01] Live authorization proof is not bound to spend authority

**Affected code:** `src/node.zig`, `src/circuit.zig`, `src/stark.zig`

`verifyAndApply` checks only that each spend carries a valid standalone authorization proof:

- binding signature over the transaction body: `node.zig`
- Merkle membership and nullifier set checks: `node.zig`
- `circuit.verifyAuthorization(s.auth)`: `node.zig`

The authorization proof's public input is `auth.image`, and that image is carried inside the transaction digest. But the verifier never checks that `auth.image` corresponds to anything in the note commitment, recipient, nullifier key, binding public key, or spend witness. A valid proof of knowledge of some Rescue preimage is therefore not a proof of authority over the note being spent.

**Impact:** an attacker who can construct a syntactically valid transaction with an existing note commitment/path and balance data is not forced by the authorization proof to know the note owner's spend secret. The current proof is a generic preimage proof, not a spend authorization proof.

**Required fix:** bind spend authority into the spend statement. Production validation should require a proof whose public inputs include, or are cryptographically tied to, the note commitment, nullifier, authorization key/image, and transaction-binding context. The preferred direction is to wire the full spend AIR into node validation and include ownership/nullifier wiring in the same proof.

### [C-02] Full spend constraints are not live in node validation

**Affected code:** `src/node.zig`, `src/spend.zig`, `src/membership.zig`, `src/permutation.zig`

The live node still verifies membership, nullifier uniqueness, and balance outside the STARK. The standalone R3 work in `spend.zig` demonstrates the intended direction: commitment opening, membership, nullifier, balance, and `rho` copy wiring in one proof. That proof is not used by `verifyAndApply`.

**Impact:** the deployed/live transaction stack is not the private spend protocol described by the future AIR. It exposes clear values to the validator and relies on native checks rather than a complete zero-knowledge spend statement.

**Required fix:** integrate a production version of `spend.zig` into the transaction type and node verifier, then remove or demote native membership/value checks to consistency checks over public inputs only.

### [C-03] Standalone full-spend proof is demo-depth and not production-wired

**Affected code:** `src/spend.zig`

`spend.zig` is explicitly standalone and uses `DEPTH = 6`, while the live commitment tree uses depth 32. Its header also documents non-production limitations: not node-integrated, not formally audited, commitment omits `recipient`/`rcm`, and owner binding is incomplete.

**Impact:** even if the standalone proof verifies in tests, it cannot be treated as production spend validation.

**Required fix:** lift the standalone proof into a production-depth, protocol-complete spend proof. The proof statement must match the real note commitment format and nullifier derivation used by `tx.zig`/`primitives.zig`.

## High Findings

### [C-04] PoC soundness parameters are below production target

**Affected code/docs:** `src/stark.zig`, `src/spend.zig`, `docs/parameters.md`, `docs/soundness.md`

The current STARKs draw challenges from the 64-bit Goldilocks base field. The project documentation correctly states that this caps effective soundness around 50 bits regardless of query count.

**Impact:** this is below any reasonable production target for a payment system.

**Required fix:** use extension-field challenges, revisit FRI rate/query/grinding parameters, and document a concrete end-to-end soundness budget before production.

### [C-05] Rescue-style hash is not a vetted production instance

**Affected code:** `src/rescue.zig`, `src/stark.zig`, `src/spend.zig`

The current Rescue/Poseidon-style SPN closes the old `x^3 + C` invertibility issue. The implementation uses a standard-looking construction, but its MDS matrix, round constants, and round count are project-local choices and explicitly not an externally reviewed Poseidon2/Rescue-Prime parameter set.

**Impact:** spend authorization and future in-circuit note/nullifier hashing would depend on unreviewed hash parameters.

**Required fix:** replace with a published arithmetization-friendly hash instance with reviewed constants and a clear security target.

## Medium Findings

### [I-01] STARK deserialization accepts malleable encodings

**Affected code:** `src/stark.zig`

The proof reader accepts raw `u64` values as field elements without rejecting values `>= field.P`. It also returns a parsed proof without checking that all input bytes were consumed.

**Impact:** proof encodings are malleable. This is not currently shown to create a direct soundness break, but production consensus formats should be canonical.

**Required fix:** reject non-canonical field encodings and reject trailing bytes. Add tests that append bytes to a valid proof and encode `field.P` as an opened field element.

### [L-01] Value arithmetic can overflow

**Affected code:** `src/node.zig`

Wallet construction checks `send_value + fee != spend_note.value`, and node validation sums `u64` inputs and outputs with unchecked addition.

**Impact:** in safe builds this can become a validation panic/DoS. In optimized builds or future code paths, modulo arithmetic could create balance-validation ambiguity.

**Required fix:** use checked addition for all value sums and reject overflow with `TxError.Unbalanced` or a dedicated `TxError.ValueOverflow`.

### [I-02] STARK blinding RNG failure handling relies on debug assertions

**Affected code:** `src/stark.zig`, duplicated STARK engines in standalone proof modules

The prover RNG calls Linux `getrandom` directly and uses `std.debug.assert` to handle non-progress/error returns.

**Impact:** optimized builds should not rely on debug assertions for cryptographic randomness failure handling.

**Required fix:** use a fallible OS RNG API or propagate `getrandom` errors explicitly. Keep prover failure fail-closed.

### [I-03] STARK engine duplication increases audit risk

**Affected code:** `src/stark.zig`, `src/membership.zig`, `src/permutation.zig`, `src/spend.zig`

Merkle commitment code, transcript code, FRI folding, query logic, RNG, and serialization-like routines are duplicated across multiple modules.

**Impact:** fixes and hardening may land in one engine but not the others. This is already visible in repeated RNG and field-encoding concerns.

**Required fix:** extract a shared audited STARK engine or enforce cross-module differential tests for transcript, Merkle, FRI, and parser behavior.

## Positive Findings

- The live authorization relation now uses `rescue.hash(s) = image` rather than the prior trivially invertible algebraic chain.
- The transaction digest includes spend ordering, output ordering, values, nullifiers, authorization image, proof bytes, output commitment, KEM ciphertext, encrypted note, and fee.
- ML-KEM, ML-DSA, SHA3-256, and ChaCha20-Poly1305 are sourced from `std.crypto`; protocol code mostly adds domain separation and framing.
- `hashDomain` length-prefixes fields, avoiding concatenation ambiguity.
- Note encryption binds AEAD associated data to the note commitment, and decryption recomputes the commitment and recipient id.
- Merkle path verification uses the path position bits to order siblings.
- The nullifier set rejects already-seen nullifiers and duplicate nullifiers inside one transaction.

## Component Review

### Live Node Validation

`node.zig` validates binding signatures, anchors, Merkle paths, nullifier uniqueness, authorization proofs, and cleartext balance. The digest coverage is broad, but the binding public key is not tied to the note owner, and the authorization proof is not tied to the spend.

Production node validation should accept a single spend proof that proves all private spend facts, with public inputs limited to the anchor, nullifier, value commitments or public value deltas, and transaction-binding digest as appropriate.

### Notes, Keys, and Encryption

`tx.zig` and `primitives.zig` are structurally sound for a PoC:

- note commitment includes recipient, value, `rho`, and `rcm`;
- nullifier derives from `nk`, `rho`, and position;
- wallet keys derive deterministically from seed;
- note encryption uses ML-KEM shared secret, commitment-bound KDF, and AEAD.

Production review should revisit deterministic encapsulation. It appears deliberate and commitment-derived, but randomized encapsulation is the default conservative choice unless reproducibility is required and carefully justified.

### Merkle State

`tree.zig` implements a conventional append-only Merkle tree with empty subtree roots and position-aware authentication paths. The main production gap is not the tree logic itself; it is that live membership is checked natively instead of inside the spend proof.

### Live Authorization STARK

`stark.zig` implements the live Rescue preimage proof. The major prior cryptographic issue, the invertible toy relation, has been addressed. Remaining production issues are parameter strength, canonical proof encoding, RNG error handling, and the fact that the proven relation is not linked to note ownership.

### Standalone Full-Spend AIR

`spend.zig` is the right architectural direction but remains a demo artifact. Before production it needs:

- depth 32 membership;
- the real note commitment shape including recipient and `rcm`;
- exact nullifier derivation compatibility with `primitives.zig`;
- transaction-binding public input;
- audited copy/permutation constraints;
- canonical serialization;
- integration into `node.zig`.

## Recommended Release Gates

Production use should be blocked until all of the following are complete:

1. Replace live `AuthProof` validation with a full spend proof that binds ownership, note commitment, nullifier, membership, value balance, and transaction context.
2. Use production STARK parameters with extension-field challenges and a documented soundness budget above 120 bits.
3. Replace local Rescue-style constants/round choices with a vetted arithmetization-friendly hash instance.
4. Canonicalize proof serialization and reject trailing bytes.
5. Make all value arithmetic checked.
6. Make prover randomness failures explicit and fail-closed.
7. Deduplicate or centrally audit the STARK engine.
8. Add adversarial tests for replayed auth proofs, malformed proof encodings, value overflow, wrong transaction binding digest, wrong nullifier witness, and wrong Merkle position.

## Verification Performed

Command run:

```sh
zig build test
```

Result: passed with no failure output.

Passing tests are useful regression coverage, but they do not establish production soundness for the transaction stack.
