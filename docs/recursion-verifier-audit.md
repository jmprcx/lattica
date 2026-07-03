# Recursive STARK verifier — in-circuit constraint audit + spec

**Status (2026-07-03): BUILT + VALIDATED (R1–R5).** The in-circuit verifier ("the monolith", `MonolithAir` in
`lattica-prover-p3/src/recursion/monolith`) is ONE AIR, proven by the audited `p3_uni_stark::prove`/`verify`,
that **accepts iff `p3::verify(inner_proof)` accepts** — validated on a REAL production `JoinSplitAir` proof,
both non-hiding and hiding (`is_zk=1`), through a data-driven symbolic epilogue; and the aggregator verifies K
real join-split inners and folds them to a block tx-root **byte-identical to `batch_joinsplit_air::batch_root`**.
RESEARCH — feature-gated behind `--features recursion` (`scripts/check-abi-symbols.sh` proves zero recursion
symbols in the default staticlib), NOT on any production path, NOT externally audited. §0 below is this crate's
own constraint self-audit (the artifact this doc's §7 promised to grow); §1–§10 are the original B0 design spec,
kept as history.

## 0. Constraint audit of the built verifier

### 0.1 The soundness claim and its shape

`MonolithAir` lays out, in ONE trace proven at `p3` FRI params: a **transcript region** (rows `0..tr`) that
replays the inner proof's Fiat–Shamir sponge; then one **super-tile per replayed inner query** (each a full
in-circuit FRI + Merkle + DEEP re-verification of that query); then the **OOD epilogue** (at the terminal-fold
row `tf`) that checks the inner's constraint relation at `ζ`; and — in the aggregator — a **fold region** that
folds each verified inner's statement into the single public tx-root. Soundness = **accept ⇒ p3::verify**: every
value `p3::verify` derives is either (a) RE-DERIVED in-circuit from the transcript (all Fiat–Shamir challenges +
query indices) or (b) AUTHENTICATED in-circuit (every opening → its committed cap; every query → the FRI
final-poly; the constraints → the quotient at `ζ`). A prover feeding a proof `p3::verify` would REJECT cannot
satisfy all the cross-region binds below at once. The proof is itself an audited-`p3` STARK, so the outer
soundness is the batch path's (q96/lb4 for proven-100 — `soundness-budget.md` + `recursion-aggregation-params.md`
§1; the reduced-query dev-box milestones are CORRECTNESS gates only, flagged where they run).

### 0.2 Cross-region binding table (the soundness backbone)

Every row is the mechanism by which a region's data is pinned so it cannot be forged, plus the corrupted-trace
negative that exercises it. All tests are in `recursion/monolith/tests.rs` (+ `native_verify.rs` for hiding).

| # | Binding | What it pins | In-circuit mechanism | Corrupted-trace negative(s) |
|---|---|---|---|---|
| 1 | transcript → challenges | `α_stark, ζ, α_fri, β_r` are the REAL FS challenges | in-circuit `DuplexChallenger` duplex sponge replayed over the observed commitments; each squeeze bound to its downstream use — or, in column-window mode, to the held pi window | `tampered α_fri ⇒ reject`; `wrong α ⇒ reject`; `wrong transcript output ⇒ reject`; `tampered pis window ⇒ internal bind fails ⇒ reject` |
| 2 | transcript → query index | each query index is the REAL `sample_bits` output | `sample_bits` from the sponge; a canonical 64-bit decomposition (`SB`) bound to the index felt (`sb_x == Σ b_i 2^i`, bits boolean, canonical `< p`) | `tampered index felt ⇒ reject (canonical index binding)`; `wrong index felt ⇒ reject`; `wrong high index bit ⇒ wrong cap entry ⇒ reject` |
| 3 | openings → committed caps | each opened row authenticates to the committed Merkle cap at `index >> shift` | leaf-hash (multi-block PaddingFree sponge) → `input_depth` path-fold (bit-ordered `merge`) → **cap-mux** selects `cap[index>>shift]` and binds it to the folded terminal (`shift = input_depth`, cap-height RUNTIME) | `tampered leaf ⇒ reject`; `tampered selected trace cap ⇒ cap-mux reject`; `tampered commit-phase cap ⇒ reject`; `wrong cap entry ⇒ reject` |
| 4 | openings → DEEP reduced opening → FRI fold chain | the query's codeword folds to `final_poly[0]` | `ro = Σ_k α_fri^k (pz_k − px_k)·inv(z_k − x)` seeds `E_0`; round-by-round arity-2 fold `(e0+e1)/2 + sign·(e0−e1)·β·inv(2s)` with the squaring point map reaches the final poly | `wrong ro ⇒ reject`; `tampered β_0 ⇒ reject (fold binding)`; `tampered folded ⇒ reject`; `wrong s_r ⇒ reject`; `tampered final_poly ⇒ reject`; `wrong final_poly target ⇒ reject` |
| 5 | px-sharing | one authenticated opened value feeds BOTH its `ζ` and `ζ_next` DEEP terms AND the Merkle leaf | `px(c) == px(W+c) == opened_row[c]` (one committed value → two reduced-opening terms + the leaf preimage) | `tampered opened value ⇒ reject` (breaks both terms + the leaf simultaneously) |
| 6 | OOD constraint relation | the inner AIR's constraints hold at `ζ` | the symbolic epilogue walks `get_symbolic_constraints(inner)` (`eval_symbolic_circuit`) with witnessed Lagrange selectors bound to their ζ-defs, α-folds them, and checks `folded·inv_van == quot(ζ)` recomposed from the nqc chunk-openings — exactly `p3::verify_constraints` | `tampered inner pub ⇒ symbolic epilogue rejects`; `tampered quotient ⇒ reject` |
| 7 | (aggregator) statement fold → block tx-root | each verified inner's statement folds into the ONLY public input, byte-matching `batch_root` | per instance, the `tx_statement_digest` MD-chain (`merge([DOM_TXROOT,0,0,0],anchor)…tx_binding` from the pi window) → `merge(root, s_k)` into the global-persistent root; final row == the public tx-root | `tampered tx-root ⇒ reject`; `corrupted instance 1 ⇒ reject` |

### 0.3 Two soundness/correctness bugs found + fixed while landing the real-inner path (audit-relevant)

Both were LATENT in the cap<6 column-window path — unreachable until a real join-split was proven in
column-window mode (which the degree bug blocked), so neither ever produced a wrong ACCEPT in a shipped test;
both were caught by in-tree guards before the path was declared working.

- **Degree-91 fold (soundness).** In column-window mode `α_stark` is a degree-1 witness column (the pi window),
  so folding all 81 inner constraints inline made the OOD check degree 91 ⇒ `log_nqc = 7 > log_blowup 4` — the
  quotient could not be committed at blowup 4 (silently unsound) and p3 evaluated it on a 2^23 domain (~90 GB).
  FIX: chunk the α-Horner (`FOLD_CHUNK`), witnessing each chunk boundary's running fold, capping the degree at
  ≤16. Guard: `phase8_joinsplit_aggregator_probe` now asserts `log_nqc ≤ log_blowup` for EVERY monolith shape
  (the check the original probe lacked — it only built `column_window=false`).
- **Cap-6 hardcode (correctness).** `native_fri::query_quotient_merkle` computed the quotient-cap index
  reduction as `log_global − 6`, assuming `cap_height=6`; at cap<6 it selected the WRONG quotient cap entry,
  and the cap-mux (row 3) rejected. FIX: derive the cap height at runtime (regression-safe — reduces to 6 at
  cap-6, so the committed cap-6 tests are unchanged). Guard: `phase8_window_discriminator` verifies the cap-2
  column-window monolith across inner shapes (degree 1..4, nqc 1/2/4, periodic, W=8 leaf, db 6/12).

### 0.4 Constraint fingerprints + geometry pins

`constraint_fingerprint.rs::pinned_constraint_fingerprints` pins `MonolithAir` at its two canonical shapes
(`is_zk=0,db=6` and `is_zk=1,hiding`) — `(width, periodic, publics, n_constraints, max_degree, fnv)` — so any
unintended constraint-set drift is a test failure; a deliberate change re-pins in the same commit (the doc-block
policy). Under `--features recursion` these 2 pins run alongside the 5 production-AIR pins. `geometry_matches_
milestone` pins the runtime super-tile geometry (block layout / periods) at the db=6 ConstAir shape.

### 0.5 Self-recursion (R5) — measured, does not converge without a wrap

`phase9_self_recursion_probe` confirms the verifier is genuinely AIR-generic (it builds + self-validates a
witness for verifying ANOTHER monolith), but verifying the SMALLEST monolith (W=193, 384 constraints) yields an
outer of W≈8520 (~44×), ~133 GB LDE, `log_nqc=7` — both size- and degree-explosive per level. So naive tree
self-recursion diverges; a fixed-size wrap (or a different outer proof system) is required — `recursion-
aggregation-params.md` §5. The production scale-out is the flat depth-1 aggregation tree (R4), which needs no
self-recursion.

### 0.6 Audit posture

RESEARCH, feature-gated, NOT externally audited. If recursion is ever slated for deployment, the audit surface
is: this constraint table (§0.2) verified region-by-region against `air.rs::eval`; the corrupted-trace suite
extended to a per-column exhaustive sweep at the HTLC-precedent bar; the transcript replay's fidelity to the
real `DuplexChallenger` (the `ModelChallenger` executable spec, §8); and the two fixes in §0.3 re-derived. The
node consensus seam is UNCHANGED regardless (aggregate root byte-matches `batch_root`), so the batch path — which
IS in the production audit — carries production until then.

## 1. What the native verifier does (`p3-uni-stark::verify`)
The in-circuit verifier must replay, as constraints, the native algorithm:
1. **Init transcript** (`DuplexChallenger`, Poseidon2 w=8 / rate=4 / cap=4).
2. **Observe** degree bits, the trace commitment, preprocessed commitment (if any), and the public
   values.
3. **Sample α** (constraint-combination challenge, in the challenge field F_p²).
4. **Observe** the quotient-chunks commitment (and the ZK random commitment if present).
5. **Sample ζ** (out-of-domain point, F_p²); check ζ ∉ trace domain.
6. **Verify openings** at {ζ, ζ·g} via the PCS → **the FRI verifier** (§2).
7. **Recompose** the quotient from its chunks at ζ; **check the constraint relation**
   `combined_constraints(ζ) == Z_H(ζ) · quotient(ζ)` (Z_H = trace-domain vanishing poly).

`Proof` = { `commitments` {trace, quotient_chunks, random?}, `opened_values` {trace_local, trace_next,
quotient_chunks, preprocessed?, random?}, `opening_proof` (the FRI proof), `degree_bits` }.

## 2. The FRI verifier (`p3-fri`), the dominant cost
`FriProof` = { `commit_phase_commits[]` (one per round), `commit_pow_witnesses[]`, `query_proofs[]`,
`final_poly[]`, `query_pow_witness` }. Each `QueryProof` = { `input_proof` (batch Merkle opening at the
query index), `commit_phase_openings[]` } where each step = { `log_arity`, `sibling_values[]`,
`opening_proof` (Merkle) }.

Per query (×`num_queries`):
- Sample the query index (`log_global_max_height` bits) from the transcript.
- **Input opening:** verify a Merkle authentication path for the trace/quotient commitment at the index.
- **Per commit-phase round:** reconstruct the arity-`2^k` evaluation group from self + siblings,
  **verify the Merkle opening** of that group, **fold** via Lagrange interpolation at the round challenge
  β (in F_p²), and roll in any new reduced openings.
- Check the final folded value equals `final_poly` evaluated at the index point.

So a query = a chain of **Merkle-opening verifications** (Poseidon2 compressions up paths) + **F_p²
Lagrange folds**. Hashing dominates; folding is cheap field arithmetic.

## 3. Lattica's config (sets the workload)
`Val = Goldilocks`, `Challenge = BinomialExtensionField<Goldilocks,2>`; Poseidon2 width 8. FRI:
`log_blowup = 4`, `max_log_arity = 4`, `log_final_poly_len = 0`, `num_queries = 96`,
`query_proof_of_work_bits = 16`. MMCS: internal-node compression `MyCompress =
TruncatedPermutation<Perm,2,4,8>`, leaf hash `MyHash = PaddingFreeSponge<Perm,8,4,4>`, cap height 4.

## 4. The decisive reuse — lattica already proves the dominant operation
**`MyCompress`, the FRI Merkle internal-node compression, is bit-identical to lattica's `merge`:**
`merge(l,r) = native_permute(l‖r)[0..4]` = `TruncatedPermutation<Perm,2,4,8>(l,r)`. And lattica already
verifies **depth-32 `merge`-chains in-circuit** — the `joinsplit_air` membership fold (`P_MEM_LINK`,
bit-controlled merge up a path), proven + exhaustively corrupted-trace-tested. A FRI Merkle opening is the
*same* operation at depth ≈ `log_height`. So the per-query Merkle-opening cost is not speculative — it is
the membership-fold cost we already pay.

| Recursive-verifier need | Existing gadget (reused) |
|---|---|
| FRI Merkle-opening verification | `merge` + the `joinsplit_air` depth-`DEPTH` membership fold (bit-controlled merge up a path) |
| Poseidon2 permutation as constraints | `poseidon2_air` (`native_steps` for the trace, the period-32 round constraints; `BLOCK = 32` rows/perm) |
| In-circuit Fiat-Shamir transcript | `poseidon2_air` (the same Poseidon2 the `DuplexChallenger` uses) — Phase B2 |
| Aggregation binding (block tx-root) | the `DOM_TXROOT` MD-chain + running-root fold from `batch_*_air` (reused verbatim) — Phase B4 |
| F_p² arithmetic | `BinomialExtensionField<Goldilocks,2>` (mul = 1 base-mul + 2 dot products; inverse = 1 Frobenius + 1 base-inverse) |

## 5. Constraint budget (single inner proof)
For one inner spend proof: trace height `2^12`, blowup `2^4` ⇒ committed domain `2^16` ⇒ input-opening
path depth ≈ 16. Commit-phase: ≈ 4–16 rounds (arity 2..16) with progressively shorter openings; ballpark
Σ opening depths per query ≈ 30. So per query ≈ **~46 `merge` compressions**; × 96 queries ≈ **~4,400
merges**. At `BLOCK = 32` rows/merge that is ≈ **~140k rows** for query-phase hashing, plus the transcript
permutations (tens) and the F_p² folds (cheap). ⇒ a single-inner-proof recursive verifier is on the order
of **2^18 rows** — the *same order as lattica's batch circuits at n=64* — i.e. **tractable on the existing
prover**. Aggregating K inner proofs tiles to ≈ K·2^18 (recursion proper keeps the *outer* proof verifying
a constant number of inner proofs per tree level).

**Risk read:** the size-dominant part (Merkle/transcript hashing) is the operation lattica already proves,
so size is *not* the blocker. The residual risk is the **correctness** of the in-circuit FRI **folding**
(F_p² Lagrange) + the **OOD/quotient/DEEP** check — that is what B3 must retire, not feasibility of scale.

## 6. The B1 spike (what's being built now) + go/no-go
**Build:** a standalone in-circuit **FRI-query Merkle-opening verifier** — given a leaf digest, the
sibling digests along a path, and the index bits, recompute the root by bit-controlled `merge` up the
path and bind it to a public input — reusing `poseidon2_air`'s permutation block and the membership-fold
pattern. **Validate:** (a) **differential** — the in-circuit root equals the native MMCS/`merge` opening
root on a real path; (b) **corrupted-trace** — a tampered sibling/bit ⇒ wrong root ⇒ reject; (c)
**benchmark** one path and extrapolate ×(96 queries × rounds).

**Go/no-go (written into `recursion-design.md`):** GO on the p3 path if the measured per-merge in-circuit
cost matches the membership-fold cost (expected — same op) and the extrapolated single-inner-proof trace
is ≤ ~2^20. If hashing cost is unexpectedly high, escalate to the framework-migration path
(`recursion-design.md` §4 path 2) before building B3.

## 7. Audit posture
This is a **new audited circuit**, never folded into the frozen `joinsplit_air`/`htlc_air`/`batch_*`. It
gets its own corrupted-trace suite (mirroring the existing `forged_*` negatives) and this doc grows
constraint-by-constraint as B1→B5 land.

## 8. Built so far (the three core primitives — all validated)
The three operations a FRI-STARK verifier is composed of are each implemented as standalone, real-prover-
differential-tested in-circuit spikes in `lattica-prover-p3/src/recursion/`:
- **Merkle openings** — `fri_merkle.rs` (B1): in-circuit FRI query-path verification via bit-controlled
  `merge`; matches the native `merge`-tree root; tampered path rejected.
- **Fiat–Shamir transcript** — `transcript.rs` (B2): the `DuplexChallenger` duplex sponge; in-circuit
  squeeze validated. A faithful `ModelChallenger` (executable spec) is pinned equal to the real
  challenger across the full operation set the verify-replay needs — variable-length absorbs, interleaved
  observe/sample, `sample_algebra_element` (F_p² = `(rate[3], rate[2])`), and `sample_bits` (query-index
  sampling). This is the reference B3-wire's in-circuit transcript must reproduce.
- **F_p² arithmetic + the FRI fold** — `fri_fold.rs` (B3a/B3b): `X²=7`; the arity-2 fold
  `(e0+e1)/2 + (e0−e1)·β/(2s)` with an in-circuit `1/(2s)`, validated **against p3's actual
  `TwoAdicFriFolding::fold_row`** (using p3's own point derivation) across multiple indices/heights, not
  just the documented formula; wrong fold rejected. Also the **commit-phase fold chain**
  (`FoldChainAir`): the running eval folded round-by-round with the FRI squaring point map `x→x²`,
  reaching the final-poly value; tampered sibling / wrong final rejected.

- **Native re-verifier (B3-wire skeleton)** — `native_verify.rs`: a from-scratch re-implementation of the
  `p3-uni-stark::verify` orchestration (transcript replay → opening rounds → quotient recomposition →
  constraint/OOD check), **validated to agree with `p3::verify`** (accepts valid, rejects a tampered
  public value) on a minimal `ConstAir` under the **production hiding (ZK) config** (the `is_zk=1` path:
  random commitment, `degree >> is_zk` domain, quotient-chunk count `1 << (log + is_zk)`). The FRI test is
  delegated to `pcs.verify` (= the validated primitives). This is the §9 plan, executed natively — the
  porting blueprint for the in-circuit verifier.

> **Superseded by §0 (2026-07-03): this "remaining work" is DONE.** The in-circuit integration (the AIR port,
> the ZK/hiding branches, B4 aggregation, and B5's determination) all landed — see §0 for the built + validated
> state. The paragraph below is the B0 forecast, kept as history.

The remaining work is the **in-circuit integration** (port the native skeleton to an AIR: replace
`pcs.verify` with the `fri_merkle`/`transcript`/`fri_fold` gadgets + the constraint folder as
constraints; add the ZK/hiding branches; B4 aggregation; B5 seam) — see `recursion-design.md`
§10 for the roadmap. Feasibility unknowns (hashing scale, transcript fidelity, F_p² folding) are retired;
what's left is faithful high-volume wiring against p3's exact proof format + the circuit-specific
quotient/DEEP check. §9 below specifies that wiring concretely.

## 9. B3-wire — the integration plan (how to build the full verifier AIR)
The recommended order is **native re-verifier first, then port to an AIR** — build a from-scratch
verifier composed ONLY from the validated primitives' native sides (`merge`-tree opening, `ModelChallenger`,
`native_fold`/`native_fold_chain`, the quotient check), confirm it **accepts real p3 proofs and rejects
tampered ones**, then translate each native step into the constraints already prototyped (B1/B2/B3b).
Porting is mechanical once the native composition is proven correct; debugging native is far cheaper than
debugging a circuit.

### 9.1 Proof → trace columns  ✓ groundwork validated
Parse a `p3_uni_stark::Proof` into witness columns: `commitments{trace, quotient_chunks, random?}` (each a
4-felt MerkleCap), `opened_values{trace_local, trace_next, quotient_chunks, …}` (F_p² vectors),
`opening_proof = (OpenedValues, FriProof)` where the `FriProof` carries `commit_phase_commits[]`,
`query_proofs[]` (each `{input_proof, commit_phase_openings[{log_arity, sibling_values, opening_proof}]}`),
`final_poly[]`, PoW witnesses; plus `degree_bits`. **Validated against a real proof** (`fri_merkle.rs`
`proof_structure_introspection`): under lattica's config a proof has 96 query proofs, one
`commit_phase_openings` entry per commit round, and a length-1 `final_poly` (`log_final_poly_len = 0`).

### 9.2 Transcript replay (use `ModelChallenger` as the executable spec — §8)
Replay EXACTLY the native order (from `p3-uni-stark::verify`): observe degree bits + base degree bits +
preprocessed width → observe trace commit → (observe preprocessed commit) → observe public values →
**sample α** → observe quotient commit → (observe random commit) → **sample ζ** → for each FRI commit
round: observe `commit_phase_commits[r]`, verify the commit PoW, **sample β_r** → **sample query indices**
via `sample_bits(log_global_max_height)` (×`num_queries`), verify the query PoW. Every challenge the
verifier uses is derived here; the in-circuit transcript (B2) must produce bit-identical values, which
`ModelChallenger` pins.

### 9.3 Per-query FRI check (compose B1 + the fold chain)
For each of the 96 queries: (a) open the input (trace/quotient) commitment at the index — a Merkle-opening
verification (**B1**); (b) run the commit-phase rounds — reconstruct each round's arity-`2^k` group from
`sibling_values` + the running eval, verify the group's Merkle opening (**B1**) against
`commit_phase_commits[r]`, and fold at β_r (**fold chain**, generalized to `max_log_arity = 4` via the
documented arity-`2^k` = k sequential arity-2 folds with β, β², …); roll in reduced openings at matching
heights; (c) evaluate `final_poly` at the final index point (Horner) and assert it equals the folded
result.

### 9.4 OOD / quotient (DEEP) check — the circuit-specific piece
Recompose the quotient at ζ from its chunks (Lagrange), evaluate the INNER AIR's constraints at ζ using
`trace_local`/`trace_next`/public values (combined with α), and assert
`combined_constraints(ζ) == Z_H(ζ)·quotient(ζ)` (`Z_H` = trace-domain vanishing poly). This depends on the
inner AIR's constraint set; for aggregating lattica spends the inner AIR is fixed
(`joinsplit_air`/`htlc_air`), so its symbolic constraints can be compiled into the verifier once.

### 9.5 Aggregation (B4) + tree (B5)
Wrap B3-wire ×K (tiled) and fold each inner proof's per-tx statement digest into the block tx-root with
the **existing `DOM_TXROOT` MD-chain** (`batch_*_air`) — emitting the SAME tx-root, so the node's
`verifyBatch`/`batchRoot` seam is unchanged. Compose outer-as-inner for a log-depth tree; add the C ABI +
Zig seam mirroring the batch seam; real cross-language integration.

### 9.6 Effort + audit
This is multi-month and audit-bearing (its own corrupted-trace suite + a constraint-by-constraint audit
here). But every sub-operation is now a validated, real-prover-tested primitive; B3-wire is composition +
faithful proof parsing, not new cryptography.

## 10. The AIR port — concrete construction plan (the remaining multi-month build)

The native verify (`native_fri.rs::verify_proof`) is COMPLETE + validated vs `p3::verify` and is now the
exact algorithm to port. The port turns that native Rust into ONE verifier AIR whose trace, when the inner
proof verifies, satisfies the constraints — and is satisfiable **iff `p3::verify` accepts** (the only
end-state validation; there is no sound partial-accept). Status + the construction:

**Done — port step 1 (`ConstraintCheckWithSelectorsAir`, validated):** the first *wired multi-gadget
fragment* — component 4 (in-circuit domain selectors at ζ) composed INTO component 2 (the constraint
folder), so the constraint/OOD region derives `is_first`/`is_transition`/`inv_vanishing` from ζ in-circuit
and folds with α, checking `folded·inv_van == quotient`. Validated vs the real `selectors_at_point(ζ)` +
the folded relation. This is the constraint-check half of `verify_proof`'s tail, as one AIR.

**The monolithic verifier AIR — region layout** (trace ≈ 2²⁰ rows; the inner proof is laid into columns):
1. **Transcript region** — the full Fiat-Shamir sponge (component 1 generalized): absorb degree bits, the
   trace/quotient commitments, the public values, the FRI batch α, each round's commit + β_r, the
   `final_poly`, the opened evaluations — producing α (constraint), ζ, the FRI α, the β_r, and the query
   indices via `SampleBitsAir` (3b-iii). Variable-length absorbs ⇒ a long sponge sub-trace.
2. **Per-query regions × num_queries(96)** — each unrolls `open_input` + `verify_query` for one query:
   `LeafHashAir` (3b-i, the MMCS leaf) → `fri_merkle` path-merge (the input opening) → `ReducedOpeningAir`
   (3b-ii, the DEEP reduce, accumulated by height) → the commit-phase `fri_fold` chain with per-round
   `fri_merkle` openings → the `final_poly` Horner check. ~50k+ rows (96 × path-depth × Poseidon2 width).
3. **Constraint region** — port step 1 above (`ConstraintCheckWithSelectorsAir`) over the recomposed
   quotient + the opened trace values.
The hard part is the **column plumbing** between regions (the transcript outputs feed the query/constraint
regions; the query indices feed the Merkle paths) wired via periodic/selector columns — this is the bulk,
and it is validatable only once whole.

**Validation strategy:** prove the verifier AIR over a real inner proof's columns; it must accept iff
`p3::verify` accepts, and reject every tampered inner proof (mirror `native_fri_verify_agrees_with_p3`).
Plus its own corrupted-trace suite (each region's constraints).

**B4 (aggregation) — sits on top of the finished port:** the verifier AIR ×K (tiled, like `batch_*_air`),
folding each inner proof's per-tx statement digest into the block tx-root via the existing `DOM_TXROOT`
MD-chain — emitting the SAME tx-root, so the node's `verifyBatch`/`batchRoot` seam is unchanged.
**B5:** compose outer-as-inner (log-depth tree) + the C ABI/Zig seam mirroring the batch seam + a real
cross-language integration. B4/B5 cannot be built or validated until the port (above) exists.
