# GPU-accelerated proving (opt-in)

`lattica-prover-p3` can offload the two heaviest proving steps — the low-degree extension (LDE) and the
Merkle tree build — to a GPU via OpenCL, for a **measured 2.12× speedup on the production (hiding)
config**, with the GPU proof **verifying under the existing production verifier unchanged**. It is
**opt-in and prove-only**: the default CPU proving path, the byte-exact wire format, and the C-ABI
verifier are untouched. Both GPU paths — `GpuDft` (LDE) and `GpuHidingMerkleMmcs` (Merkle) — are
byte-compatible with the production `HidingFriPcs` + `MerkleTreeHidingMmcs`, so a GPU-produced proof
deserializes and verifies exactly like a CPU one (accepted by `verify_bytes` / the C-ABI / the node).

## Enabling it

```bash
cargo build   --release --features gpu      # pulls the optional `ocl` dep + the GPU kernels
cargo test    --release --features gpu -- --ignored gpu_   # the GPU tests (need an OpenCL runtime + GPU)
```

Without `--features gpu`, nothing changes — `ocl` isn't even in the dependency tree.

**Runtime requirement:** an OpenCL 1.2+ runtime and a GPU (validated on an NVIDIA RTX 5080 via the
NVIDIA CUDA OpenCL platform; portable to AMD/Intel).

## What it does

`crate::gpu::GpuDft` implements p3's `TwoAdicSubgroupDft<Goldilocks>` with an OpenCL radix-2 DIT NTT.
p3 composes the whole coset-LDE from `dft_batch`, so dropping `GpuDft` into the PCS's `Dft` slot moves
the LDE onto the GPU. `crate::config::gpu::proof_to_bytes` proves with it:

```rust
#[cfg(feature = "gpu")]
let proof_bytes = lattica_prover_p3::config::gpu::proof_to_bytes(&JoinSplitAir, trace, &pis);
// verify with the STANDARD verifier — unchanged:
assert!(joinsplit_air::verify_bytes(&proof_bytes, &pis));
```

## Why it's safe (consensus)

- **The DFT is not in the wire or the verifier.** The `Dft` type never appears in `verify` or in the
  serialized `Proof`, so swapping `Radix2DitParallel → GpuDft` cannot change the wire.
- **The GPU MMCS is byte-compatible, not a new wire type.** `GpuHidingMerkleMmcs`'s `Commitment`
  (`MerkleCap<Val,[Val;4]>`) and `Proof` (`(salts, siblings)`) are the *identical* types as
  `MerkleTreeHidingMmcs`, and its GPU tree reproduces p3's tree bit-for-bit — so `Proof<GpuConfig>`
  serializes exactly like `Proof<MyConfig>` and the CPU verifier reconstructs the same caps/paths. GPU
  proofs are therefore accepted by the existing verifier and the Zig node unchanged.
- **Bit-exact kernels.** Every GPU primitive is validated bit-for-bit against p3: Goldilocks field, the
  NTT/coset-LDE (`GpuDft` matches `Radix2DitParallel` up to the real 2¹⁶ LDE), Poseidon2-8, the Merkle
  cap + sibling paths (`gpu_merkle_cap_matches_p3`, `gpu_hiding_mmcs_matches_p3`), F_p², the quotient
  selectors, and the FRI fold. The kernels reproduce p3's exact roots (`two_adic_generator`) and
  reduction; the serde encoding is canonical, so intermediate representation is irrelevant.
- **The correctness gate:**
  - *non-hiding* (deterministic) → a GPU proof is **byte-identical** to the CPU proof;
  - *production (hiding)* → salts are a fresh CSPRNG per proof, so full proofs differ CPU-vs-CPU too;
    the criterion is **"the standard verifier accepts it"** — the LDE-only path
    (`gpu_{joinsplit,htlc}_proof_verifies`) and the full LDE+Merkle path
    (`gpu_{joinsplit,htlc}_proof_verifies_hiding`).

## Status & performance

Two heavy proving steps run on the GPU: the **LDE** (`GpuDft`) and the **Merkle tree build**. Both are
byte-compatible with the production **hiding** config, so GPU proofs verify under the standard verifier.

### The 2.12× on the production (hiding) config (`gpu_hiding_benchmark`, join-split, best of 5)

Production `HidingFriPcs` + `is_zk` + salts + `CAP_HEIGHT = 6`, GPU vs CPU, **both verified under the
production `verify_bytes`**:

| config | LDE | Merkle | join-split prove |
|---|---|---|---:|
| CPU (production) | `Radix2DitParallel` | `MerkleTreeHidingMmcs` | **955.9 ms** |
| GPU | `GpuDft` | `GpuHidingMerkleMmcs` | **450.6 ms** (**2.12×**) |

Of the GPU run, ~80 ms is NTT + ~116 ms is Merkle per proof; the rest (quotient constraint-eval, FRI,
challenger) is still CPU. The killer test `gpu_{joinsplit,htlc}_proof_verifies_hiding` proves a circuit
with the GPU hiding config and asserts the **standard production verifier accepts it** — the whole FRI
query/open/verify path over the salted GPU tree round-trips.

(An isolated non-hiding micro-benchmark, `gpu_merkle_benchmark`, measures the same two offloads at 2.42×
on a small 141 ms → 58.2 ms workload; the production number above is the one that matters.)

### How the Merkle offload works

`crate::gpu::GpuHidingMerkleMmcs` is a custom `p3_commit::Mmcs` byte-compatible with
`MerkleTreeHidingMmcs<…, 2, 4, 4>`: `commit` appends 4 salt columns per matrix (the exact p3 draw) and
runs the whole salted tree on the GPU (Poseidon2 `leaf_hash` → pairwise `compress_layer`, extracting the
`cap_height = 6` `MerkleCap`), while `open_batch`/`verify_batch` stay on the CPU using the **same**
exported Poseidon2 constants. Its `Commitment` (`MerkleCap<Val,[Val;4]>`) and `Proof`
(`(salts, siblings)`) are the *identical* types p3 uses, so a `Proof<GpuConfig>` serializes byte-for-byte
like `Proof<MyConfig>`. Validated at three levels: the GPU cap matches CPU `MerkleTreeMmcs` byte-for-byte
(`gpu_merkle_cap_matches_p3`); seeding both MMCS the same reproduces p3's salts and cap exactly and the
CPU verifier accepts the GPU opening (`gpu_hiding_mmcs_matches_p3`); and the full GPU-hiding proof
verifies under production `verify_bytes`. A custom MMCS was necessary because p3's `MerkleTree` internals
are `pub(crate)` and can't be reused. (`GpuMerkleMmcs`, the non-hiding `cap_height 0` variant, remains for
the isolated benchmark.)

### Quotient offload (done, but net-neutral)

The quotient evaluation is not behind a trait seam (it is inline in p3's `prove`), so it is offloaded by
`crate::quotient_gpu::prove_gpu` — a faithful fork of `prove` (preprocessed = None) that reuses every p3
public function and swaps only `quotient_values` for a GPU evaluator. The evaluator (`gpu_quotient_values`
+ the `quotient` kernel) flattens each AIR's `get_symbolic_constraints` DAG (~800–1300 nodes, `Arc`-CSE)
into an instruction stream and interprets it one-row-per-thread, folding the constraints with the F_p²
alpha powers × `inv_vanishing`. It is correct and **verifies under the production verifier** (all three
heavy steps now on GPU; `gpu_{joinsplit,htlc}_proof_verifies_hiding` + `gpu_quotient_verifies`).

**But it is net-neutral.** The kernel is fast (~10 ms/proof), yet marshalling the trace to `u64` buffers
on the CPU (~50 ms) offsets it — the quotient's cost is *data movement*, not arithmetic. Profiling the
~443 ms GPU hiding proof: ~109 ms Merkle + ~84 ms NTT + ~10 ms quotient are on GPU; the remaining ~180 ms
CPU is **FRI + commit glue** — that is the real next lever, not the quotient. The fork + interpreters are
kept as validated infrastructure: a real quotient win needs the trace kept **on-GPU across LDE→quotient**
(a deeper PCS integration that avoids the round-trip).

### What's next

- **FRI + commit glue** (~180 ms CPU, the new dominant remainder) — the next real lever.
- On-GPU trace persistence across LDE→quotient (would make the quotient offload pay off).
- Shared-memory NTT butterflies; a `_prove_gpu` C-ABI entry for the node.
