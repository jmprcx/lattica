# GPU-accelerated proving (opt-in)

> **Research status:** Feature-gated, prove-only, and outside the production audit. The CPU verifier and proof format remain authoritative.

`lattica-prover-p3` can offload the heavy proving steps — the low-degree extension (LDE), the Merkle
tree build, and the hiding PCS's quotient-randomization pipeline — to a GPU via OpenCL, for a
**measured ~4.6× speedup over an AVX2-optimized CPU** on the production (hiding) config, with the GPU
proof **verifying under the existing production verifier unchanged**. (The CPU baseline uses p3's
packed-Goldilocks SIMD — see *CPU SIMD* below.) It is
**opt-in and prove-only**: the default CPU proving path, the byte-exact wire format, and the C-ABI
verifier are untouched. All three GPU paths — `GpuDft` (LDE), `GpuHidingMerkleMmcs` (Merkle), and
`GpuHidingPcs` (quotient randomization) — are byte-compatible with the production `HidingFriPcs` +
`MerkleTreeHidingMmcs` stack, so a GPU-produced proof deserializes and verifies exactly like a CPU one
(accepted by `verify_bytes` / the C-ABI / the node).

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

Three heavy proving steps run on the GPU: the **LDE** (`GpuDft`), the **Merkle tree build**
(`GpuHidingMerkleMmcs`), and the hiding PCS's **quotient-randomization pipeline** (`GpuHidingPcs`). All
are byte-compatible with the production **hiding** config, so GPU proofs verify under the standard
verifier.

### The 4.6× on the production (hiding) config (`gpu_hiding_benchmark`, join-split, best of 5)

Production `HidingFriPcs` + `is_zk` + salts + `CAP_HEIGHT = 6`, GPU vs CPU, **both verified under the
production `verify_bytes`**:

| config | LDE | Merkle | quotient LDEs | join-split prove |
|---|---|---|---|---:|
| CPU (AVX2 + LTO, production) | `Radix2DitParallel` | `MerkleTreeHidingMmcs` | CPU | **~785 ms** |
| GPU | `GpuDft` | `GpuHidingMerkleMmcs` | `GpuHidingPcs` | **~172 ms** (**~4.6×**) |

The killer test `gpu_{joinsplit,htlc}_proof_verifies_hiding` proves a circuit with the GPU hiding config
and asserts the **standard production verifier accepts it** — the whole FRI query/open/verify path over
the salted GPU tree round-trips. Of the ~172 ms: ~39 ms GPU NTT (51 calls), ~52 ms GPU Merkle
(7 commits), the rest CPU (FRI fold, challenger, opens, glue).

The 2.1× → 4.6× step came from three findings (2026-07-03):

1. **The NTT was launch- and transfer-bound, not butterfly-bound.** The per-stage kernel did `log h + 1`
   full global-memory round-trips; the `ntt_tile` kernel now runs ~8–12 stages per launch in a 32 KiB
   local-memory tile (rows `hi<<(s0+lt) | t<<s0 | lo` × up to 16 columns), with the stage-`s` twiddle
   split as `w_s^lo · w_k^(t mod 2^(k-1))` off p3's generator squaring chain — no twiddle tables. The
   bit-reversal is fused into the first group's load, the `1/h`/coset-shift/canonicalize tails into the
   last group's store, and the last group can emit rows **bit-reversed (p3's storage order) directly**,
   deleting the CPU `reverse_matrix_index_bits` pass per LDE. Stage generators are cached per
   `(log_h, inverse)`.
2. **Transfers ran at pageable speed (~3–6 GB/s) on a PCIe5 ×16 link that does 38–54 GB/s pinned.**
   `GpuCtx` now keeps pooled device scratch buffers and a persistently-mapped pinned
   (`CL_MEM_ALLOC_HOST_PTR`) staging window; every upload/download memcpys through it with the host-side
   copy parallelized (a fresh `Vec`'s cold-page single-threaded memcpy costs more than the DMA). Merkle
   commits marshal leaf rows **directly into the window** (`upload_rows`) instead of materializing the
   combined leaf matrix host-side — the 16-chunk quotient commit moves ~170 MB/proof through that path.
3. **p3's hiding quotient randomization was doing 16 full-size mostly-zero DFTs + ~48 host permutation
   passes per proof.** `HidingFriPcs::get_quotient_ldes` randomizes each quotient chunk with a coset-LDE
   plus a **full-size `dft_batch` whose input is ~94% zero rows**, materializes both natural-order on the
   host, adds them on the CPU, and re-bit-reverses. `get_quotient_ldes` is a `Pcs` *trait* method, so
   `gpu_pcs::GpuHidingPcs` wraps the production stack, delegates everything else (associated types are
   the inner's — the wire is untouched), and overrides just that one: same randomization math (draws,
   `get_zp_cis`, last-chunk adjustment), but per chunk the coset-LDE, the vanishing-poly NTT (only the
   `2h`-row nonzero coefficient prefix is uploaded; the GPU zero-pads), the elementwise add
   (`add_canon`), and the bit-reversed store run device-side with ONE download. **Gold gate**
   `gpu_quotient_ldes_match_p3`: with the same seed, the returned chunk LDEs are byte-identical to p3's.

(An isolated non-hiding micro-benchmark, `gpu_merkle_benchmark`, measures the LDE+Merkle offloads on a
small workload; the production number above is the one that matters.)

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
on the CPU (~50 ms) offsets it — the quotient *constraint evaluation*'s cost is *data movement*, not
arithmetic. The fork + interpreters are kept as validated infrastructure, not wired into the default
path: a real win here needs the trace kept **on-GPU across LDE→quotient**. (Distinct from this, the
quotient *randomization/commit* pipeline — which profiling showed was the actual dominant cost — DID
move to the GPU via `GpuHidingPcs`; see above.)

### CPU SIMD (AVX2)

Rust's default `x86-64` target is SSE2-only, so p3-goldilocks's `target_feature`-gated AVX2 packed-field
module compiled out and all CPU field arithmetic ran scalar. `.cargo/config.toml` now pins
`target-cpu=x86-64-v3` (AVX2 + BMI2 + FMA; portable to all Haswell+/Zen+ CPUs, scoped to `x86_64` so
aarch64 NEON builds are unaffected). Measured **~10% faster CPU proving** (~940 → ~845 ms) — bit-identical
(packed field arithmetic equals scalar; fingerprints + verifier unchanged). The gain is modest because
p3 has **no hand-vectorized Poseidon2** (the speedup is from packed field ops only, capped by Poseidon2's
round dependencies and the NTT's memory-bound nature); a server with AVX-512 would additionally use p3's
8-lane `x86_64_avx512` path. **Runtime requirement:** x86_64 binaries now need a v3 CPU (2013+).

### GPU kernel tuning (done + learned)

- **NTT shared-memory tiling** (done, see above): the definitive fix for the per-stage global
  round-trips; superseded the earlier coalescing-only `ntt_stage` kernel.
- **Pinned staging** (done, see above): measure transfer paths before kernels — the "slow NTT" was
  mostly the driver staging pageable memory (probe: `gpu-smoke/xfer` in the session scratchpad).
- **Twiddle precompute in global memory** (tried, *reverted*): replacing the per-butterfly `gl_pow`
  with a master-table lookup made the NTT *slower*. `gl_pow` (pure compute) hides behind memory
  latency; a table adds global reads. The tiled kernel keeps computing twiddles.
- Parallelizing the host-side `u64` conversion is size-thresholded (`to_u64s`, ≥ 4 MiB): per-matrix
  `rayon` overhead loses on the many small quotient-chunk / FRI-layer matrices.

### What's next

- The Merkle **leaf-hashing** (~52 ms, the dominant GPU cost now) is *compute*-bound (~40 Poseidon2
  perms per wide quotient leaf) and near-optimal per-kernel; the remaining waste is re-uploading LDEs
  the GPU just produced — on-GPU LDE persistence across LDE→Merkle (device-resident matrix handles in
  the PCS) is the structural fix.
- The residual ~80 ms CPU tail is the FRI commit phase (ext-field folds + challenger) and the opens —
  p3's FRI prover is not behind a trait seam, so offloading it means forking `commit_phase` (the
  validated S4 fold kernel exists).
- A `_prove_gpu` C-ABI entry (or runtime GPU/CPU switch) + Zig-node wiring, once the node wants it.
