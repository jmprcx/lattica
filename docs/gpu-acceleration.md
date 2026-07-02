# GPU-accelerated proving (opt-in)

`lattica-prover-p3` can offload the low-degree extension (LDE) — the single heaviest step of proving —
to a GPU via OpenCL. It is **opt-in, prove-only, and wire-compatible**: the default CPU proving path,
the byte-exact wire format, and the C-ABI verifier are untouched.

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

Working today: real join-split and HTLC proofs run with GPU LDE and verify. On the reference machine,
join-split proving is **CPU ~829 ms → GPU-LDE ~707 ms** (~15% faster end-to-end). `coset_lde_batch` is
overridden to run the entire LDE device-side (iDFT → coset-scale → forward NTT, one upload + one
download), so the LDE is fully offloaded.

### Where the time goes (measured, p3 tracing spans, join-split)

| phase | CPU time | on GPU? |
|---|---:|---|
| commit quotient chunks — **Merkle hashing** | ~365 ms | ✗ (next lever) |
| commit quotient chunks — LDE | ~322 ms | ✓ |
| `quotient_values` (constraint eval) | ~170 ms | ✗ |
| commit trace — **Merkle hashing** | ~71 ms | ✗ |
| open / FRI | ~42 ms | partial |

**Merkle hashing is ~45% of a proof** — and it's exactly the Poseidon2 workload the GPU crushes
(validated bit-exact in the pipeline: 500K permutations, Merkle roots to the limb). It is the single
biggest remaining win, but it requires a **custom GPU `Mmcs`** (the tree build on GPU) that is
byte-compatible with `MerkleTreeHidingMmcs` so proofs still verify — a substantial, carefully-tested
piece (p3's `MerkleTree` internals are `pub(crate)`, so it can't be reused; the whole commit/open/verify
must be reimplemented). The `quotient_values` constraint-eval (~17%) is the other lever and needs a
codegen pass (emit a GPU kernel from each AIR's `SymbolicExpression` DAG).

**Roadmap to ~2×:** GPU Merkle `Mmcs` (kernels validated, ready) → quotient constraint-eval codegen →
shared-memory NTT butterflies → a `_prove_gpu` C-ABI entry for the node. The LDE slice is done; the next
increment is the Merkle `Mmcs`, and it earns its own careful pass because it must verify.
