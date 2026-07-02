# GPU-accelerated proving (opt-in)

`lattica-prover-p3` can offload the two heaviest proving steps — the low-degree extension (LDE) and the
Merkle tree build — to a GPU via OpenCL, for a **measured 2.42× speedup** on the real join-split circuit.
It is **opt-in and prove-only**: the default CPU proving path, the byte-exact wire format, and the C-ABI
verifier are untouched. The LDE path (`GpuDft`) is wire-compatible with the production hiding config; the
Merkle path (`GpuMerkleMmcs`) currently runs under a non-hiding benchmark config (see *What's next*).

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

- **The DFT is not in the wire or the verifier.** A GPU-produced `Proof` serializes to the same bytes a
  CPU proof would and deserializes/verifies under the standard `MyConfig` — the `Dft` type never appears
  in `verify` or in the serialized `Proof`. So GPU proofs are accepted by the existing verifier and the
  Zig node unchanged.
- **Bit-exact kernels.** Every GPU primitive is validated bit-for-bit against p3: Goldilocks field, the
  NTT/coset-LDE (`GpuDft` matches `Radix2DitParallel` up to the real 2¹⁶ LDE), Poseidon2-8, the Merkle
  root, F_p², the quotient selectors, and the FRI fold. The kernels reproduce p3's exact roots
  (`two_adic_generator`) and reduction; the serde encoding is canonical, so intermediate representation
  is irrelevant.
- **The correctness gate:**
  - *non-hiding* (deterministic) → a GPU proof is **byte-identical** to the CPU proof;
  - *production (hiding)* → salts are a fresh CSPRNG per proof, so full proofs differ CPU-vs-CPU too;
    the criterion is **"the standard verifier accepts it"** (`gpu_{joinsplit,htlc}_proof_verifies`).

## Status & performance

Two heavy proving steps run on the GPU today: the **LDE** (`GpuDft`) and the **Merkle tree build**
(`GpuMerkleMmcs`). Together they deliver a **measured 2.42× over CPU** on the real join-split circuit.

### The 2.42× (measured, `gpu_merkle_benchmark`, join-split, best of 5)

Apples-to-apples, non-hiding configs with identical FRI params:

| config | LDE | Merkle | join-split prove |
|---|---|---|---:|
| CPU baseline | `Radix2DitParallel` | `MerkleTreeMmcs` | **141.0 ms** |
| GPU | `GpuDft` | `GpuMerkleMmcs` | **58.2 ms** (**2.42×**) |

Of the GPU run, ~18 ms is NTT + ~10 ms is Merkle; the rest (quotient constraint-eval, FRI, challenger)
is still CPU. Each proof **verifies under its own config** (self-consistent) — and the GPU Merkle commit
was validated bit-exact against the CPU p3 hasher standalone (`gpu_merkle_mmcs_self_consistent`: GPU
commit ↔ CPU verify agree across 2¹–2¹²; tampered values / wrong indices rejected).

### How the Merkle offload works

`crate::gpu::GpuMerkleMmcs` is a custom `p3_commit::Mmcs`: `commit` runs the whole tree on the GPU
(Poseidon2 `leaf_hash` over concatenated rows → pairwise `compress_layer` up to the root), while
`open_batch`/`verify_batch` stay on the CPU (cheap, per-query) using the **same** exported Poseidon2
constants — so a GPU-built root verifies against the CPU hasher bit-for-bit. The kernels
(`perm8`/`leaf_hash`/`compress_layer`) match `default_goldilocks_poseidon2_8` exactly. This was
necessary because p3's `MerkleTree` internals are `pub(crate)` and can't be reused.

### What's next

- **Production (hiding) integration.** The 2.42× is measured on a *non-hiding* config (`GpuMerkleMmcs`
  has no salts, `cap_height 0`, a `[Val;4]` root). Folding it into the production **hiding** wire format
  means a salted variant whose `Commitment`/`Proof` are byte-compatible with `MerkleTreeHidingMmcs`
  (`MerkleCap` + `(salts, siblings)`), so proofs still verify under the standard verifier / the node.
- **Quotient constraint-eval** (`quotient_values`, the next ~17% CPU slice) — a codegen pass emitting a
  GPU kernel from each AIR's `SymbolicExpression` DAG.
- Shared-memory NTT butterflies; a `_prove_gpu` C-ABI entry for the node.
