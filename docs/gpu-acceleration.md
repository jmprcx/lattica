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
join-split proving is **CPU 844 ms → GPU-LDE 757 ms** (~10% faster end-to-end, with the un-optimized
default coset-LDE composition).

Follow-on wins (the LDE offload is the first slice): a GPU `coset_lde_batch` override (coset
decomposition device-side), offloading Merkle / quotient / FRI (needs a constraint-eval codegen pass for
the quotient), shared-memory NTT butterflies, and a `_prove_gpu` C-ABI entry for the node.
