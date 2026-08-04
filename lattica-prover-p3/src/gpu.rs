//! GPU (OpenCL) acceleration of the low-degree extension — **opt-in** via `--features gpu`.
//!
//! `GpuDft` implements p3's `TwoAdicSubgroupDft<Goldilocks>` by computing the DFT on the GPU; p3
//! composes the whole coset-LDE (the single heaviest proving step) from `dft_batch`. It is a drop-in
//! for `Radix2DitParallel` in the PCS's `Dft` slot, so it is **additive and prove-only**: the wire
//! format, the C-ABI verifier, and the default CPU proving path are untouched. A GPU-produced proof
//! deserializes and verifies under the standard config exactly like a CPU one — the DFT never appears
//! in `verify` or in the serialized `Proof`.
//!
//! Correctness is validated bit-for-bit against p3 (see `gpu_dft_matches_p3` /
//! `gpu_coset_lde_matches_p3`): a radix-2 DIT NTT over Goldilocks, twiddle base per stage =
//! `Goldilocks::two_adic_generator(s)` — p3's exact roots, so the evaluations are identical. The NTT is
//! memory-bound, so stages run tiled in local memory (`ntt_tile`): ~8–11 stages per launch with the
//! bit-reversal fused into the first load and the scale/canonicalize tails fused into the last store —
//! 2–3 global round-trips total instead of one per stage. Field arithmetic matches p3's
//! `reduce128`/`add` (canonical only at the boundary; the serde encoding is canonical, so intermediate
//! representation is irrelevant).
//!
//! Runtime requirement: an OpenCL runtime + a GPU. The kernel program is compiled once per thread
//! (cached), so per-DFT cost is just buffer transfer + the butterfly launches.

use crate::config::{MyCompress, MyHash};
use ocl::ProQue;
use p3_commit::{BatchOpening, BatchOpeningRef, Mmcs};
use p3_dft::TwoAdicSubgroupDft;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField64, TwoAdicField};
use p3_goldilocks::{
    default_goldilocks_poseidon2_8, Goldilocks, GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_FINAL,
    GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_INITIAL, GOLDILOCKS_POSEIDON2_RC_8_INTERNAL,
    MATRIX_DIAG_8_GOLDILOCKS,
};
use p3_matrix::bitrev::{BitReversalPerm, BitReversedMatrixView};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::{Dimensions, Matrix};
use p3_symmetric::{CryptographicHasher, MerkleCap, PseudoCompressionFunction};
use rand_chacha::ChaCha20Rng;
use rayon::prelude::*;
use std::cell::RefCell;
use std::sync::atomic::{AtomicU64, Ordering};

/// Lightweight profiling counters (GPU NTT wall-time + call count), for the benchmark to attribute
/// how much of a proof is spent in the accelerated LDE. Reset/read via `prof_reset`/`prof_report`.
pub static NTT_NANOS: AtomicU64 = AtomicU64::new(0);
pub static NTT_CALLS: AtomicU64 = AtomicU64::new(0);
pub static MERKLE_NANOS: AtomicU64 = AtomicU64::new(0);
pub static MERKLE_CALLS: AtomicU64 = AtomicU64::new(0);
pub static QUOTIENT_NANOS: AtomicU64 = AtomicU64::new(0);
pub static QUOTIENT_CALLS: AtomicU64 = AtomicU64::new(0);
/// Reset the GPU profiling counters.
pub fn prof_reset() {
    NTT_NANOS.store(0, Ordering::Relaxed);
    NTT_CALLS.store(0, Ordering::Relaxed);
    MERKLE_NANOS.store(0, Ordering::Relaxed);
    MERKLE_CALLS.store(0, Ordering::Relaxed);
    QUOTIENT_NANOS.store(0, Ordering::Relaxed);
    QUOTIENT_CALLS.store(0, Ordering::Relaxed);
}
/// `(GPU-quotient ms, quotient calls)` since the last reset.
pub fn prof_report_quotient() -> (f64, u64) {
    (
        QUOTIENT_NANOS.load(Ordering::Relaxed) as f64 / 1e6,
        QUOTIENT_CALLS.load(Ordering::Relaxed),
    )
}
/// `(GPU-NTT ms, dft_batch calls, GPU-Merkle ms, commit calls)` since the last reset.
pub fn prof_report() -> (f64, u64, f64, u64) {
    (
        NTT_NANOS.load(Ordering::Relaxed) as f64 / 1e6,
        NTT_CALLS.load(Ordering::Relaxed),
        MERKLE_NANOS.load(Ordering::Relaxed) as f64 / 1e6,
        MERKLE_CALLS.load(Ordering::Relaxed),
    )
}

/// OpenCL C: Goldilocks field ops (matching p3's reduce128/add) + a radix-2 DIT NTT.
const KERNEL_SRC: &str = r#"
#define NEG_ORDER 0xFFFFFFFFUL
#define GP        0xFFFFFFFF00000001UL
inline ulong gl_reduce128(ulong lo,ulong hi){ uint hh=(uint)(hi>>32),hl=(uint)(hi&0xFFFFFFFFUL);
 ulong t0=lo-(ulong)hh; if(lo<(ulong)hh)t0-=NEG_ORDER; ulong t1=(ulong)hl*NEG_ORDER; ulong t2=t0+t1; if(t2<t0)t2+=NEG_ORDER; return t2; }
inline ulong gl_mul(ulong a,ulong b){ return gl_reduce128(a*b, mul_hi(a,b)); }
inline ulong gl_add(ulong a,ulong b){ ulong s=a+b; ulong o1=(s<a)?NEG_ORDER:0UL; ulong s2=s+o1; ulong o2=(s2<s)?NEG_ORDER:0UL; return s2+o2; }
inline ulong gl_neg(ulong b){ ulong c=(b>=GP)?(b-GP):b; return c==0UL?0UL:(GP-c); }
inline ulong gl_sub(ulong a,ulong b){ return gl_add(a, gl_neg(b)); }
inline ulong gl_canon(ulong c){ return (c>=GP)?(c-GP):c; }
inline ulong gl_pow(ulong b,ulong e){ ulong r=1UL; while(e){ if(e&1UL)r=gl_mul(r,b); b=gl_mul(b,b); e>>=1;} return r; }
inline uint brev(uint x, uint bits){ uint r=0; for(uint i=0;i<bits;i++){ r=(r<<1)|(x&1u); x>>=1; } return r; }

// ---- tiled NTT: radix-2 DIT, `lt` stages per kernel launch in local memory ----
// The NTT is MEMORY-bound: one butterfly stage per launch means a full global round-trip per stage.
// Here one workgroup owns a TILE=2^lt-row × C=2^log_c-column tile — rows r(t) = hi<<(s0+lt) | t<<s0 | lo
// (t = 0..TILE) are exactly the rows whose stage-(s0+1 ..= s0+lt) butterflies interconnect (those stages
// pair rows differing in bits [s0, s0+lt)) — for C consecutive columns (coalesced global runs). It loads
// the tile once, runs the `lt` stages against local memory (barrier between stages), and stores once:
// ONE global round-trip for `lt` stages. The twiddle for stage s = s0+k at row r, j = r mod 2^(s-1),
// splits as w_s^j = w_s^lo · w_k^(t mod 2^(k-1)) — p3's generators form one squaring chain
// (gen(s)^(2^s0) = gen(s-s0), forward and inverse alike), so the per-stage generators `wlens` suffice;
// no twiddle table (a table would ADD memory traffic; gl_pow is compute, hidden behind the loads).
// fuse_bitrev (first group only, s0 = 0): load from bit-reversed source rows, fusing the bit-reversal
// pass — requires in != out. store_brev (last group of a forward NTT): store row r to row brev(r),
// emitting the matrix directly in p3's bit-reversed storage order (kills the CPU re-permutation pass);
// scattered stores land outside the workgroup's own rows, so it too requires in != out. Groups with
// neither flag pass in == out (in-place is safe: a workgroup touches only its own rows). The store also
// fuses the elementwise tails so they cost no extra pass:
//   out = canon?(x · post_c · post_b^row)   — post_c = post_b = 1, do_canon = 0 for a plain store;
// the iDFT's last group passes post_c = 1/h, post_b = coset shift; a forward NTT's last group canons.
__kernel void ntt_tile(__global const ulong* in,__global ulong* out,const uint w,const uint h,
                       const uint s0,const uint lt,const uint log_c,const uint fuse_bitrev,
                       const uint log_h,const uint do_canon,const uint store_brev,
                       const ulong post_c,const ulong post_b,
                       __global const ulong* wlens,__local ulong* tile){
  const uint C=1u<<log_c, lid=get_local_id(0), wg=get_local_size(0);
  const uint tiles=h>>lt, g=(uint)get_group_id(0);
  const uint tidx=g%tiles, cg=g/tiles;
  const uint lo=tidx&((1u<<s0)-1u), hi=tidx>>s0;
  const uint row0=(hi<<(s0+lt))|lo, col0=cg<<log_c;
  const uint n_el=(1u<<lt)<<log_c;
  for(uint e=lid;e<n_el;e+=wg){
    uint t=e>>log_c, col=col0+(e&(C-1u));
    uint r=row0+(t<<s0);
    uint sr=fuse_bitrev?brev(r,log_h):r;
    tile[e]=(col<w)?in[(size_t)sr*w+col]:0UL;
  }
  barrier(CLK_LOCAL_MEM_FENCE);
  for(uint k=1;k<=lt;k++){
    uint hl=1u<<(k-1u);
    ulong outer=gl_pow(wlens[s0+k-1u],(ulong)lo);
    for(uint b=lid;b<(n_el>>1);b+=wg){
      uint t2=b>>log_c, lc=b&(C-1u);
      uint j=t2&(hl-1u);
      uint tl=((((t2>>(k-1u))<<k)|j)<<log_c)|lc, th=tl+(hl<<log_c);
      ulong tw=gl_mul(outer,gl_pow(wlens[k-1u],(ulong)j));
      ulong u=tile[tl], v=gl_mul(tile[th],tw);
      tile[tl]=gl_add(u,v); tile[th]=gl_sub(u,v);
    }
    barrier(CLK_LOCAL_MEM_FENCE);
  }
  for(uint e=lid;e<n_el;e+=wg){
    uint t=e>>log_c, col=col0+(e&(C-1u));
    if(col<w){
      uint r=row0+(t<<s0);
      ulong x=tile[e];
      if(post_c!=1UL||post_b!=1UL) x=gl_mul(x,gl_mul(post_c,gl_pow(post_b,(ulong)r)));
      uint orow=store_brev?brev(r,log_h):r;
      out[(size_t)orow*w+col]=do_canon?gl_canon(x):x;
    }
  }
}
// ---- Poseidon2-Goldilocks width-8 (matches p3 `default_goldilocks_poseidon2_8`) ----
inline ulong gl_pow7(ulong x){ ulong x2=gl_mul(x,x); ulong x3=gl_mul(x2,x); ulong x4=gl_mul(x2,x2); return gl_mul(x4,x3); }
// apply_mat4 on x[0..4] (p3 external.rs; order matters — overwrite 0/2 after 1/3).
inline void mat4(ulong* x){
  ulong t01=gl_add(x[0],x[1]); ulong t23=gl_add(x[2],x[3]);
  ulong t0123=gl_add(t01,t23); ulong t01123=gl_add(t0123,x[1]); ulong t01233=gl_add(t0123,x[3]);
  x[3]=gl_add(t01233,gl_add(x[0],x[0]));
  x[1]=gl_add(t01123,gl_add(x[2],x[2]));
  x[0]=gl_add(t01123,t01);
  x[2]=gl_add(t01233,t23);
}
// external linear layer (mds_light_permutation, WIDTH 8): M4 per chunk, then outer circulant sums.
inline void extl(ulong* s){
  mat4(s); mat4(s+4);
  ulong z0=gl_add(s[0],s[4]),z1=gl_add(s[1],s[5]),z2=gl_add(s[2],s[6]),z3=gl_add(s[3],s[7]);
  s[0]=gl_add(s[0],z0); s[1]=gl_add(s[1],z1); s[2]=gl_add(s[2],z2); s[3]=gl_add(s[3],z3);
  s[4]=gl_add(s[4],z0); s[5]=gl_add(s[5],z1); s[6]=gl_add(s[6],z2); s[7]=gl_add(s[7],z3);
}
// internal linear layer (matmul_internal): s[i] = s[i]*diag[i] + sum(s).
inline void intl(ulong* s,__global const ulong* diag){
  ulong sum=0UL; for(int i=0;i<8;i++) sum=gl_add(sum,s[i]);
  for(int i=0;i<8;i++) s[i]=gl_add(gl_mul(s[i],diag[i]),sum);
}
// full permutation: extl; 4 full (rc+x^7 all lanes, extl); 22 partial (rc+x^7 lane0, intl); 4 full.
inline void perm8(ulong* s,__global const ulong* rci,__global const ulong* rcp,__global const ulong* rcf,__global const ulong* diag){
  extl(s);
  for(int r=0;r<4;r++){ for(int i=0;i<8;i++) s[i]=gl_pow7(gl_add(s[i],rci[r*8+i])); extl(s); }
  for(int r=0;r<22;r++){ s[0]=gl_pow7(gl_add(s[0],rcp[r])); intl(s,diag); }
  for(int r=0;r<4;r++){ for(int i=0;i<8;i++) s[i]=gl_pow7(gl_add(s[i],rcf[r*8+i])); extl(s); }
}
// leaf hash (PaddingFreeSponge<8,4,4>): one thread per row, sponge over `w` elems, out[row*4..].
// Padding-free: overwrite state[0..4] with each block, permute after any absorbed block.
// Row-banded: `in` is a band of `band_h` rows (band-local), `out` is the full leaf-digest buffer;
// thread g hashes band row g into digest `row0+g`. Row-independent, so banding is bit-transparent.
__kernel void leaf_hash(__global const ulong* in,__global ulong* out,const uint row0,const uint band_h,const uint w,
                        __global const ulong* rci,__global const ulong* rcp,__global const ulong* rcf,__global const ulong* diag){
  size_t g=get_global_id(0); if(g>=band_h) return;
  ulong s[8]; for(int i=0;i<8;i++) s[i]=0UL;
  __global const ulong* r=in+(size_t)g*w;
  uint i=0;
  while(i<w){ for(uint k=0;k<4 && i<w;k++){ s[k]=r[i]; i++; } perm8(s,rci,rcp,rcf,diag); }
  for(int k=0;k<4;k++) out[(size_t)(row0+g)*4+k]=gl_canon(s[k]);
}
// compress one tree layer (TruncatedPermutation<2,4,8>): out[j] = trunc(perm(in[2j] || in[2j+1])).
__kernel void compress_layer(__global const ulong* in,__global ulong* out,const uint n_out,
                             __global const ulong* rci,__global const ulong* rcp,__global const ulong* rcf,__global const ulong* diag){
  size_t j=get_global_id(0); if(j>=n_out) return;
  ulong s[8]; for(int k=0;k<4;k++){ s[k]=in[(size_t)(2*j)*4+k]; s[4+k]=in[(size_t)(2*j+1)*4+k]; }
  perm8(s,rci,rcp,rcf,diag);
  for(int k=0;k<4;k++) out[(size_t)j*4+k]=gl_canon(s[k]);
}
// elementwise dst[i] = canon(dst[i] + src[i]) — the hiding-quotient "add the vanishing randomizer"
// step, fused with the final canonicalization (both NTT results arrive uncanonicalized).
__kernel void add_canon(__global ulong* dst,__global const ulong* src,const uint n){
  size_t i=get_global_id(0); if(i<n) dst[i]=gl_canon(gl_add(dst[i],src[i]));
}
// Quotient evaluator: one thread per row (grid-stride over `qsize`). Interpret the flattened constraint
// DAG (`op_*`/`consts`/`roots`) into per-node scratch `v`, then fold the constraint roots with the F_p^2
// alpha powers (`alpha0`/`alpha1`) and scale by inv_vanishing → the two base coeffs of the F_p^2 quotient.
__kernel void quotient(
    __global const uint* op_code,__global const uint* op_a,__global const uint* op_b,
    __global const ulong* consts,__global const uint* roots,const uint n_ops,const uint n_roots,
    __global const ulong* trace,const uint width,const uint qsize,const uint next_step,
    __global const ulong* periodic,const uint n_periodic,__global const ulong* pub_vals,
    __global const ulong* is_first,__global const ulong* is_last,__global const ulong* is_trans,__global const ulong* inv_van,
    __global const ulong* alpha0,__global const ulong* alpha1,
    __global ulong* scratch,const uint n_threads,__global ulong* out)
{
  uint tid=get_global_id(0);
  __global ulong* v=scratch+(size_t)tid*n_ops;
  for(uint row=tid; row<qsize; row+=n_threads){
    uint nrow=(row+next_step)%qsize;
    for(uint i=0;i<n_ops;i++){
      uint oc=op_code[i],a=op_a[i],b=op_b[i]; ulong r;
      switch(oc){
        case 0: r=trace[(size_t)row*width+a]; break;
        case 1: r=trace[(size_t)nrow*width+a]; break;
        case 2: r=periodic[(size_t)row*n_periodic+a]; break;
        case 3: r=pub_vals[a]; break;
        case 4: r=is_first[row]; break;
        case 5: r=is_last[row]; break;
        case 6: r=is_trans[row]; break;
        case 7: r=consts[a]; break;
        case 8: r=gl_add(v[a],v[b]); break;
        case 9: r=gl_sub(v[a],v[b]); break;
        case 10: r=gl_mul(v[a],v[b]); break;
        default: r=gl_neg(v[a]); break;
      }
      v[i]=r;
    }
    ulong c0=0UL,c1=0UL;
    for(uint k=0;k<n_roots;k++){ ulong cv=v[roots[k]]; c0=gl_add(c0,gl_mul(cv,alpha0[k])); c1=gl_add(c1,gl_mul(cv,alpha1[k])); }
    ulong iv=inv_van[row];
    out[(size_t)row*2+0]=gl_canon(gl_mul(c0,iv));
    out[(size_t)row*2+1]=gl_canon(gl_mul(c1,iv));
  }
}
"#;

/// Pinned staging window size in u64 elements (8 Mi × 8 B = 64 MiB). Transfers chunk through it.
const STAGING_LEN: usize = 8 << 20;

/// Thread-local GPU state: the compiled program (compilation is the expensive part) plus reusable
/// buffers — two device scratch buffers grown to the largest size seen, and a persistently mapped
/// **pinned** host staging window (`CL_MEM_ALLOC_HOST_PTR` + map, the standard OpenCL pinned-transfer
/// pattern). Every upload/download memcpys through the window so the PCIe DMA runs at full speed;
/// transferring straight to/from pageable `Vec` memory makes the driver stage it internally at
/// ~3–6 GB/s, which profiling showed was the dominant cost of the GPU NTT path (~47 of ~79 ms/proof).
struct GpuCtx {
    pq: ProQue,
    dev: [Option<ocl::Buffer<u64>>; 3],
    /// Kept alive so the mapping stays valid for `staging_map`'s lifetime.
    _staging_buf: Option<ocl::Buffer<u64>>,
    staging_map: Option<ocl::MemMap<u64>>,
    /// Stage-generator buffers keyed by `(log_h, inverse)` — tiny but rebuilt on every NTT call
    /// otherwise (~100 host-pointer buffer creations per proof).
    wlens: std::collections::HashMap<(usize, bool), ocl::Buffer<u64>>,
    /// The device's per-allocation cap (`CL_DEVICE_MAX_MEM_ALLOC_SIZE`) in u64 elements, queried once.
    /// Column-tiling keeps every `dev_buf` under it (see `col_block`).
    max_alloc: Option<usize>,
}

thread_local! {
    static GPU_CTX: RefCell<Option<GpuCtx>> = const { RefCell::new(None) };
}

fn with_ctx<R>(f: impl FnOnce(&mut GpuCtx) -> R) -> R {
    GPU_CTX.with(|cell| {
        let mut opt = cell.borrow_mut();
        let ctx = opt.get_or_insert_with(|| {
            let pq = ProQue::builder().src(KERNEL_SRC).dims(1).build().expect(
                "GpuDft: OpenCL program build failed (is an OpenCL runtime + GPU present?)",
            );
            GpuCtx {
                pq,
                dev: [None, None, None],
                _staging_buf: None,
                staging_map: None,
                wlens: Default::default(),
                max_alloc: None,
            }
        });
        f(ctx)
    })
}

/// Compatibility shim for call sites that only need the compiled program.
fn with_proque<R>(f: impl FnOnce(&ProQue) -> R) -> R {
    with_ctx(|ctx| f(&ctx.pq))
}

impl GpuCtx {
    /// Device scratch buffer for `slot`, at least `n` elements — grown geometrically, reused across
    /// calls (buffer churn is avoidable overhead on every NTT/commit).
    fn dev_buf(&mut self, slot: usize, n: usize) -> ocl::Buffer<u64> {
        if self.dev[slot].as_ref().is_none_or(|b| b.len() < n) {
            // Round up to a power of two for geometric reuse, but never past the per-allocation cap: a
            // column-tiled remainder block can be a non-power-of-two size whose `next_power_of_two`
            // would exceed the cap even though its exact size fits (the tiled callers keep `n` legal).
            let want = n.next_power_of_two();
            let len = if want <= self.max_alloc_u64s() {
                want
            } else {
                n.max(1)
            };
            self.dev[slot] = Some(
                ocl::Buffer::<u64>::builder()
                    .queue(self.pq.queue().clone())
                    .flags(ocl::flags::MEM_READ_WRITE)
                    .len(len)
                    .build()
                    .unwrap(),
            );
        }
        self.dev[slot].as_ref().unwrap().clone()
    }

    /// The device's per-allocation cap (`CL_DEVICE_MAX_MEM_ALLOC_SIZE`), in u64 elements — queried
    /// once and cached. A single OpenCL buffer larger than this fails with `CL_INVALID_BUFFER_SIZE`,
    /// regardless of free global memory; `col_block` uses it to bound every `dev_buf`.
    fn max_alloc_u64s(&mut self) -> usize {
        if let Some(m) = self.max_alloc {
            return m;
        }
        let bytes = self
            .pq
            .queue()
            .device()
            .info(ocl::core::DeviceInfo::MaxMemAllocSize)
            .ok()
            .and_then(|r| match r {
                ocl::core::DeviceInfoResult::MaxMemAllocSize(s) => Some(s as usize),
                _ => None,
            })
            .filter(|&b| b >= (1 << 20))
            .unwrap_or(1 << 30); // 1 GiB fallback if the driver won't report a sane cap
        let m = bytes / 8;
        self.max_alloc = Some(m);
        m
    }

    /// Largest power-of-two column count `C` whose `big × C` u64 device buffer fits under ~7/8 of the
    /// per-allocation cap, capped at `w`. Tiling every LDE/NTT into `C`-column blocks keeps each
    /// `dev_buf` legal, so a wide trace (the batch at ≥16 tx, the aggregator at width ~1291) no longer
    /// trips `CL_INVALID_BUFFER_SIZE`. The blocks are independent-column polynomials, so the stitched
    /// output is bit-identical regardless of `C` — only the tile shape (`log_c`) changes, never the
    /// butterfly values. `LATTICA_GPU_COL_BLOCK` caps `C` (forces multi-block tiling on small test inputs).
    fn col_block(&mut self, big: usize, w: usize) -> usize {
        let budget = self.max_alloc_u64s() / 8 * 7; // 7/8 headroom (fill/upload also touch the buffer)
        let fit = (budget / big.max(1)).max(1);
        // floor to a power of two so `big·C` is itself a power of two (no `dev_buf` next_pow2 inflation)
        let mut c = 1usize << (usize::BITS - 1 - fit.leading_zeros());
        if let Ok(v) = std::env::var("LATTICA_GPU_COL_BLOCK") {
            if let Ok(cap) = v.parse::<usize>() {
                c = c.min(cap.max(1));
            }
        }
        c.min(w.max(1))
    }

    /// Rows per band such that a `rows × w` u64 leaf-input buffer fits under ~7/8 of the per-allocation
    /// cap, capped at `h`. Row-banding the (wide) Merkle leaf input keeps its device buffer legal while
    /// the per-row leaf hash is unchanged — each row maps to one digest, band-independent. `LATTICA_GPU_COL_BLOCK`
    /// also caps the band (× w) so the tiling tests exercise multi-band leaf hashing.
    fn row_block(&mut self, w: usize, h: usize) -> usize {
        let budget = self.max_alloc_u64s() / 8 * 7;
        let mut rows = (budget / w.max(1)).max(1);
        if let Ok(v) = std::env::var("LATTICA_GPU_COL_BLOCK") {
            if let Ok(cap) = v.parse::<usize>() {
                rows = rows.min(cap.max(1));
            }
        }
        rows.min(h.max(1))
    }

    /// The persistently mapped pinned staging window.
    fn staging(&mut self) -> &mut ocl::MemMap<u64> {
        if self.staging_map.is_none() {
            let buf = ocl::Buffer::<u64>::builder()
                .queue(self.pq.queue().clone())
                .flags(ocl::flags::MEM_ALLOC_HOST_PTR | ocl::flags::MEM_READ_WRITE)
                .len(STAGING_LEN)
                .build()
                .unwrap();
            // SAFETY: the single persistent mapping per thread-local context; access is serialized by
            // the in-order queue and the blocking transfer calls below.
            let map = unsafe {
                buf.map()
                    .flags(ocl::flags::MAP_READ | ocl::flags::MAP_WRITE)
                    .len(STAGING_LEN)
                    .enq()
                    .unwrap()
            };
            self._staging_buf = Some(buf);
            self.staging_map = Some(map);
        }
        self.staging_map.as_mut().unwrap()
    }

    /// Blocking upload of `rows` logical rows (`row_w` u64s each) into `dst`, marshalling each row
    /// directly into the pinned window via `fill(row, buf)` — parallel over rows, no intermediate
    /// host-side Vec. This is the Merkle leaf-buffer path (its input is the widest data we move).
    fn upload_rows(
        &mut self,
        dst: &ocl::Buffer<u64>,
        rows: usize,
        row_w: usize,
        fill: impl Fn(usize, &mut [u64]) + Sync,
    ) {
        let rows_per_chunk = (STAGING_LEN / row_w).max(1);
        let map = self.staging();
        let mut r0 = 0usize;
        while r0 < rows {
            let nr = rows_per_chunk.min(rows - r0);
            map[..nr * row_w]
                .par_chunks_mut(row_w)
                .enumerate()
                .for_each(|(i, buf)| fill(r0 + i, buf));
            dst.cmd()
                .offset(r0 * row_w)
                .write(&map[..nr * row_w])
                .enq()
                .unwrap();
            r0 += nr;
        }
    }

    /// The `(1..=log_h)` stage-generator buffer (`wlens[s-1]` = `two_adic_generator(s)`, inverted
    /// for iDFTs), cached per `(log_h, inv)`.
    fn wlens_buf(&mut self, log_h: usize, inv: bool) -> ocl::Buffer<u64> {
        if !self.wlens.contains_key(&(log_h, inv)) {
            let gens: Vec<u64> = (1..=log_h)
                .map(|s| {
                    let g = Goldilocks::two_adic_generator(s);
                    (if inv { g.inverse() } else { g }).as_canonical_u64()
                })
                .collect();
            let buf = ocl::Buffer::<u64>::builder()
                .queue(self.pq.queue().clone())
                .flags(ocl::flags::MEM_READ_ONLY | ocl::flags::MEM_COPY_HOST_PTR)
                .len(gens.len())
                .copy_host_slice(&gens)
                .build()
                .unwrap();
            self.wlens.insert((log_h, inv), buf);
        }
        self.wlens[&(log_h, inv)].clone()
    }

    /// Blocking download of `src[0..n]` into a fresh Vec, chunked through the pinned window. The
    /// copy out of the window is parallel (rayon writes the uninitialized spare directly): the fresh
    /// Vec's pages are cold, and single-threaded fault-and-copy costs several × the DMA itself.
    fn download(&mut self, src: &ocl::Buffer<u64>, n: usize) -> Vec<u64> {
        let mut out = Vec::<u64>::with_capacity(n);
        let map = self.staging();
        let mut off = 0usize;
        while off < n {
            let len = STAGING_LEN.min(n - off);
            src.cmd().offset(off).read(&mut map[..len]).enq().unwrap();
            out.par_extend(map[..len].par_iter().copied());
            off += len;
        }
        out
    }

    /// Blocking download of a `rows × cw` device block (row-major, in the buffer's stored order) and
    /// scatter into `out` (row-major `rows × out_w`) at column offset `c0` — the column-tiling
    /// counterpart of `upload_rows`. Rows stream through the pinned window; the per-row scatter is parallel.
    fn download_cols_into(
        &mut self,
        src: &ocl::Buffer<u64>,
        rows: usize,
        cw: usize,
        out: &mut [u64],
        out_w: usize,
        c0: usize,
    ) {
        let rows_per_chunk = (STAGING_LEN / cw.max(1)).max(1);
        let map = self.staging();
        let mut r0 = 0usize;
        while r0 < rows {
            let nr = rows_per_chunk.min(rows - r0);
            src.cmd()
                .offset(r0 * cw)
                .read(&mut map[..nr * cw])
                .enq()
                .unwrap();
            out[r0 * out_w..(r0 + nr) * out_w]
                .par_chunks_mut(out_w)
                .zip(map[..nr * cw].par_chunks(cw))
                .for_each(|(orow, blk)| orow[c0..c0 + cw].copy_from_slice(blk));
            r0 += nr;
        }
    }
}

/// Enqueue a full tiled NTT (see the `ntt_tile` kernel): even-split the `log_h = wlens.len()` stages
/// into groups of ≤ `12 − log_c` stages (tile = 2^lt rows × 2^log_c columns ≤ 32 KiB local memory).
/// Group 1 loads via fused bit-reversal from `src` into `dst` (distinct buffers required); middle
/// groups run in-place on `dst`. The last group fuses the elementwise tail `x · post_c · post_b^row`
/// (pass 1, 1 for none) and, if `do_canon`, canonicalization. With `store_brev` the last group also
/// stores rows bit-reversed — p3's storage order — which forces it out-of-place: it then writes back
/// into `src`, and the function returns the buffer holding the result (`true` = `dst`).
/// The transform size is `2^log_h = h`; `inv` selects the inverse stage generators (iDFT).
#[allow(clippy::too_many_arguments)]
fn enqueue_tiled_ntt(
    ctx: &mut GpuCtx,
    src: &ocl::Buffer<u64>,
    dst: &ocl::Buffer<u64>,
    h: usize,
    w: usize,
    log_h: usize,
    inv: bool,
    post_c: u64,
    post_b: u64,
    do_canon: bool,
    store_brev: bool,
) -> bool {
    debug_assert_eq!(1usize << log_h, h, "log_h must match the transform size");
    let wlens_buf = ctx.wlens_buf(log_h, inv);
    let pq = &ctx.pq;
    // C = columns per tile: wide enough for coalesced runs, capped by the matrix width (w=2 quotient
    // chunks waste no lanes) and at 16 (128-byte runs). Tile budget: 2^(lt+log_c) u64 = 32 KiB.
    let log_c = (w.next_power_of_two().trailing_zeros() as usize).min(4);
    let lt_cap = (12 - log_c).min(log_h);
    let n_groups = log_h.div_ceil(lt_cap);
    let (base, rem) = (log_h / n_groups, log_h % n_groups);
    let mut s0 = 0usize;
    let mut result_in_dst = true;
    for gi in 0..n_groups {
        let lt = base + usize::from(gi < rem);
        let n_el = 1usize << (lt + log_c);
        let wg = (n_el / 2).clamp(32, 256);
        let n_wgs = (h >> lt) * w.div_ceil(1 << log_c);
        let last = gi + 1 == n_groups;
        // Buffer choreography: group 1 reads `src` (fused bit-reversal ⇒ out-of-place); a store_brev
        // last group scatters rows ⇒ out-of-place too, bouncing back into `src` unless it IS group 1.
        let (inb, outb) = match (gi == 0, last && store_brev) {
            (true, _) => (src, dst),
            (false, true) => (dst, src),
            (false, false) => (dst, dst),
        };
        if last {
            result_in_dst = std::ptr::eq(outb, dst);
        }
        unsafe {
            pq.kernel_builder("ntt_tile")
                .arg(inb)
                .arg(outb)
                .arg(w as u32)
                .arg(h as u32)
                .arg(s0 as u32)
                .arg(lt as u32)
                .arg(log_c as u32)
                .arg(u32::from(gi == 0))
                .arg(log_h as u32)
                .arg(u32::from(last && do_canon))
                .arg(u32::from(last && store_brev))
                .arg(if last { post_c } else { 1u64 })
                .arg(if last { post_b } else { 1u64 })
                .arg(&wlens_buf)
                .arg_local::<u64>(n_el)
                .global_work_size(n_wgs * wg)
                .local_work_size(wg)
                .build()
                .unwrap()
                .enq()
                .unwrap();
        }
        s0 += lt;
    }
    result_in_dst
}

/// Run the radix-2 DIT NTT on the GPU (tiled; bit-reversal fused into the first group's load,
/// canonicalization into the last group's store). Returns evaluations in **bit-reversed** row order —
/// p3's storage order, ready to wrap in `BitReversalPerm::new_view` with no CPU re-permutation.
fn gpu_ntt(coeffs: &[u64], h: usize, w: usize, log_h: usize) -> Vec<u64> {
    let _t0 = std::time::Instant::now();
    let mut out = vec![0u64; h * w];
    with_ctx(|ctx| {
        // Column-tile so each `h × cw` device buffer stays under the per-allocation cap. Columns are
        // independent transforms, so the stitched result is bit-identical to a single whole-width pass.
        let c_block = ctx.col_block(h, w);
        let mut c0 = 0usize;
        while c0 < w {
            let cw = c_block.min(w - c0);
            let n = h * cw;
            let cb = ctx.dev_buf(0, n);
            let ab = ctx.dev_buf(1, n);
            ctx.upload_rows(&cb, h, cw, |r, buf| {
                buf.copy_from_slice(&coeffs[r * w + c0..r * w + c0 + cw])
            });
            let in_dst = enqueue_tiled_ntt(ctx, &cb, &ab, h, cw, log_h, false, 1, 1, true, true);
            ctx.download_cols_into(if in_dst { &ab } else { &cb }, h, cw, &mut out, w, c0);
            c0 += cw;
        }
    });
    if std::env::var_os("LATTICA_GPU_PROF").is_some() {
        eprintln!(
            "ntt h={h} w={w}: total {:.3}ms",
            _t0.elapsed().as_secs_f64() * 1e3
        );
    }
    NTT_NANOS.fetch_add(_t0.elapsed().as_nanos() as u64, Ordering::Relaxed);
    NTT_CALLS.fetch_add(1, Ordering::Relaxed);
    out
}

/// Full coset-LDE on the GPU, **device-side** (one upload + one download): iDFT → coset-scale +
/// zero-pad → forward NTT on `shift·K` (|K| = `h << added_bits`). Returns evaluations in
/// **bit-reversed** row order — p3's storage order, ready to wrap in `BitReversalPerm::new_view`.
/// This is what `TwoAdicFriPcs` actually calls; keeping the two NTTs + the coset shift on-device
/// eliminates the host round-trips (and the CPU reverse/scale/coset-shift) of the trait's default
/// composition — the LDE's dominant overhead.
fn gpu_coset_lde_bitrev(
    evals: &[u64],
    h: usize,
    w: usize,
    added_bits: usize,
    shift: u64,
) -> Vec<u64> {
    let _t0 = std::time::Instant::now();
    let log_h = h.trailing_zeros() as usize;
    let big = h << added_bits;
    let log_big = log_h + added_bits;
    let h_inv = Goldilocks::from_u64(h as u64).inverse().as_canonical_u64();
    let prof = std::env::var_os("LATTICA_GPU_PROF").is_some();
    let mut out = vec![0u64; big * w];
    with_ctx(|ctx| {
        // Column-tile so each `big × cw` device buffer stays under the per-allocation cap: the columns
        // are independent LDEs, so the stitched result is bit-identical to a single whole-width pass
        // (only the tile shape `log_c` differs, never the butterfly values). This is what lets a wide
        // trace (the batch at ≥16 tx, the aggregator at width ~1291) LDE on-device at all.
        let c_block = ctx.col_block(big, w);
        let mut c0 = 0usize;
        while c0 < w {
            let cw = c_block.min(w - c0);
            let n_big = big * cw;
            let a = ctx.dev_buf(0, n_big);
            let b = ctx.dev_buf(1, n_big);
            // Only `b` needs zeroing (rows h..big are the forward NTT's zero-pad, read at its fused
            // bit-reversal); `a`'s first h·cw elements are overwritten by the upload below.
            b.cmd().fill(0u64, Some(n_big)).enq().unwrap();
            // gather this block's columns [c0, c0+cw) of the row-major h×w input into a[0..h·cw]
            ctx.upload_rows(&a, h, cw, |r, buf| {
                buf.copy_from_slice(&evals[r * w + c0..r * w + c0 + cw])
            });
            // iDFT on the first h rows (a → b), the last group fusing scale-by-1/h + coset shift^row;
            // rows ≥ h of `b` stay 0 (the zero-pad).
            enqueue_tiled_ntt(ctx, &a, &b, h, cw, log_h, true, h_inv, shift, false, false);
            // forward NTT of size `big` (b → a…, reading the zero-pad through the fused bit-reversal),
            // canonicalized + stored bit-reversed by the last group (which bounces back into `b` when
            // there are ≥ 2 groups).
            let in_dst = enqueue_tiled_ntt(ctx, &b, &a, big, cw, log_big, false, 1, 1, true, true);
            ctx.download_cols_into(if in_dst { &a } else { &b }, big, cw, &mut out, w, c0);
            c0 += cw;
        }
    });
    if prof {
        eprintln!(
            "lde h={h} w={w} big={big}: total {:.3}ms",
            _t0.elapsed().as_secs_f64() * 1e3
        );
    }
    NTT_NANOS.fetch_add(_t0.elapsed().as_nanos() as u64, Ordering::Relaxed);
    NTT_CALLS.fetch_add(1, Ordering::Relaxed);
    out
}

/// One hiding-PCS quotient chunk, fully device-side (see `gpu_pcs::GpuHidingPcs::get_quotient_ldes`):
/// the coset-LDE of the randomized chunk evals (iDFT → fused 1/h·shift^k scale → forward NTT) PLUS the
/// forward NTT of the vanishing-poly randomizer `v_H·r` — whose coefficients are nonzero only in the
/// first `2h` rows, so only that prefix is uploaded and the GPU zero-pads — summed elementwise and
/// canonicalized on device. ONE download, in p3's bit-reversed storage order. Replaces, per chunk:
/// p3's coset_lde_batch + a full-size mostly-zeros dft_batch + three host bit-reversal
/// materializations + a host-side add.
pub(crate) fn gpu_quotient_chunk_lde(
    evals: &[u64],
    van_prefix: &[u64],
    h: usize,
    w: usize,
    added_bits: usize,
    shift: u64,
) -> Vec<u64> {
    let _t0 = std::time::Instant::now();
    assert!(
        h >= 2 && h.is_power_of_two(),
        "quotient chunk height must be a power of two ≥ 2"
    );
    assert_eq!(
        van_prefix.len(),
        2 * h * w,
        "vanishing randomizer prefix is 2h rows"
    );
    let log_h = h.trailing_zeros() as usize;
    let big = h << added_bits;
    let log_big = log_h + added_bits;
    let h_inv = Goldilocks::from_u64(h as u64).inverse().as_canonical_u64();
    let mut out = vec![0u64; big * w];
    with_ctx(|ctx| {
        // Column-tile the chunk evals AND the vanishing-randomizer prefix in lockstep so each `big × cw`
        // device buffer stays under the per-allocation cap; independent columns ⇒ bit-identical output.
        let c_block = ctx.col_block(big, w);
        let mut c0 = 0usize;
        while c0 < w {
            let cw = c_block.min(w - c0);
            let n_big = big * cw;
            let a = ctx.dev_buf(0, n_big);
            let b = ctx.dev_buf(1, n_big);
            let c = ctx.dev_buf(2, n_big);
            // coset-LDE of the chunk (as in gpu_coset_lde_bitrev, but NOT canonicalized — the final
            // add_canon canonicalizes the sum).
            b.cmd().fill(0u64, Some(n_big)).enq().unwrap();
            ctx.upload_rows(&a, h, cw, |r, buf| {
                buf.copy_from_slice(&evals[r * w + c0..r * w + c0 + cw])
            });
            enqueue_tiled_ntt(ctx, &a, &b, h, cw, log_h, true, h_inv, shift, false, false);
            let in_dst = enqueue_tiled_ntt(ctx, &b, &a, big, cw, log_big, false, 1, 1, false, true);
            let (r, s) = if in_dst { (a, b) } else { (b, a) };
            // v_H·r: zero-pad the freed scratch buffer, upload this block's 2h-row prefix columns, forward NTT.
            // (The in-order queue sequences the fill after the LDE kernels that read `s`.)
            s.cmd().fill(0u64, Some(n_big)).enq().unwrap();
            ctx.upload_rows(&s, 2 * h, cw, |r2, buf| {
                buf.copy_from_slice(&van_prefix[r2 * w + c0..r2 * w + c0 + cw])
            });
            let v_in_dst =
                enqueue_tiled_ntt(ctx, &s, &c, big, cw, log_big, false, 1, 1, false, true);
            let v = if v_in_dst { c } else { s };
            // sum + canonicalize this block.
            unsafe {
                ctx.pq
                    .kernel_builder("add_canon")
                    .arg(&r)
                    .arg(&v)
                    .arg(n_big as u32)
                    .global_work_size(n_big)
                    .build()
                    .unwrap()
                    .enq()
                    .unwrap();
            }
            ctx.download_cols_into(&r, big, cw, &mut out, w, c0);
            c0 += cw;
        }
    });
    NTT_NANOS.fetch_add(_t0.elapsed().as_nanos() as u64, Ordering::Relaxed);
    NTT_CALLS.fetch_add(1, Ordering::Relaxed);
    out
}

/// ONE column-tile `[c0, c0+cw)` of a hiding-PCS quotient chunk LDE, computed fully device-side — the
/// per-tile core of `gpu_quotient_chunk_lde`, exposed so the STREAMING prover can compute a chunk one
/// `big × cw` tile at a time and spill each straight to its on-disk store, never holding the whole
/// `big × w` chunk resident (that whole-chunk buffer is the aggregator's quotient RAM floor, which the
/// CPU streaming path already tiles away — this keeps the property when the compute moves to the GPU).
/// `evals` (h×w) and `van_prefix` (2h×w) are the FULL chunk inputs; only columns `[c0, c0+cw)` are read.
/// Output is `big × cw` in p3's bit-reversed row order, canonical u64 — bit-identical to the same columns
/// of `gpu_quotient_chunk_lde` (independent-column polynomials; only the tile `log_c` differs). The caller's
/// `cw` must keep `big·cw` under the device per-allocation cap (the streaming `c_block` guarantees it).
#[cfg(feature = "stream")] // only the streaming quotient path calls this; avoids dead-code under `gpu`-only
pub(crate) fn gpu_quotient_chunk_lde_tile(
    evals: &[u64],
    van_prefix: &[u64],
    h: usize,
    w: usize,
    c0: usize,
    cw: usize,
    added_bits: usize,
    shift: u64,
) -> Vec<u64> {
    let _t0 = std::time::Instant::now();
    assert!(
        h >= 2 && h.is_power_of_two(),
        "quotient chunk height must be a power of two ≥ 2"
    );
    assert_eq!(
        van_prefix.len(),
        2 * h * w,
        "vanishing randomizer prefix is 2h rows"
    );
    let log_h = h.trailing_zeros() as usize;
    let big = h << added_bits;
    let log_big = log_h + added_bits;
    let h_inv = Goldilocks::from_u64(h as u64).inverse().as_canonical_u64();
    let mut out = vec![0u64; big * cw];
    with_ctx(|ctx| {
        let n_big = big * cw;
        let a = ctx.dev_buf(0, n_big);
        let b = ctx.dev_buf(1, n_big);
        let c = ctx.dev_buf(2, n_big);
        // coset-LDE of the chunk (not canonicalized — the final add_canon canonicalizes the sum).
        b.cmd().fill(0u64, Some(n_big)).enq().unwrap();
        ctx.upload_rows(&a, h, cw, |r, buf| {
            buf.copy_from_slice(&evals[r * w + c0..r * w + c0 + cw])
        });
        enqueue_tiled_ntt(ctx, &a, &b, h, cw, log_h, true, h_inv, shift, false, false);
        let in_dst = enqueue_tiled_ntt(ctx, &b, &a, big, cw, log_big, false, 1, 1, false, true);
        let (r, s) = if in_dst { (a, b) } else { (b, a) };
        // v_H·r: zero-pad the freed scratch, upload this tile's 2h-row prefix columns, forward NTT.
        s.cmd().fill(0u64, Some(n_big)).enq().unwrap();
        ctx.upload_rows(&s, 2 * h, cw, |r2, buf| {
            buf.copy_from_slice(&van_prefix[r2 * w + c0..r2 * w + c0 + cw])
        });
        let v_in_dst = enqueue_tiled_ntt(ctx, &s, &c, big, cw, log_big, false, 1, 1, false, true);
        let v = if v_in_dst { c } else { s };
        // sum + canonicalize this tile.
        unsafe {
            ctx.pq
                .kernel_builder("add_canon")
                .arg(&r)
                .arg(&v)
                .arg(n_big as u32)
                .global_work_size(n_big)
                .build()
                .unwrap()
                .enq()
                .unwrap();
        }
        // the tile IS the whole output here (out is `big × cw`, out_w = cw, c0 = 0).
        ctx.download_cols_into(&r, big, cw, &mut out, cw, 0);
    });
    NTT_NANOS.fetch_add(_t0.elapsed().as_nanos() as u64, Ordering::Relaxed);
    NTT_CALLS.fetch_add(1, Ordering::Relaxed);
    out
}

/// Canonical-u64 conversion of a field slice — parallel above ~4 MiB (the per-matrix rayon overhead
/// loses on the many small quotient-chunk/FRI-layer matrices, but the full-size randomization
/// matrices the hiding PCS feeds `dft_batch` are 6+ MiB of mostly-cold pages).
fn to_u64s(vals: &[Goldilocks]) -> Vec<u64> {
    if vals.len() >= (1 << 19) {
        vals.par_iter().map(|f| f.as_canonical_u64()).collect()
    } else {
        vals.iter().map(|f| f.as_canonical_u64()).collect()
    }
}

/// A GPU-backed two-adic DFT: a drop-in for `Radix2DitParallel` in the PCS's `Dft` slot.
#[derive(Clone, Copy, Default, Debug)]
pub struct GpuDft;

impl TwoAdicSubgroupDft<Goldilocks> for GpuDft {
    type Evaluations = BitReversedMatrixView<RowMajorMatrix<Goldilocks>>;

    fn dft_batch(&self, mat: RowMajorMatrix<Goldilocks>) -> Self::Evaluations {
        let (h, w) = (mat.height(), mat.width());
        // Match Radix2DitParallel::dft_batch: logical order = natural DFT, stored = bit-reversed.
        // The GPU emits the bit-reversed storage order directly (store_brev), so no CPU permutation.
        let stored = if h <= 1 {
            mat.values
                .iter()
                .map(|f| f.as_canonical_u64())
                .collect::<Vec<u64>>()
        } else {
            let log_h = h.trailing_zeros() as usize;
            let coeffs = to_u64s(&mat.values);
            gpu_ntt(&coeffs, h, w, log_h)
        };
        BitReversalPerm::new_view(RowMajorMatrix::new(
            stored.into_iter().map(Goldilocks::new).collect(),
            w,
        ))
    }

    /// Override the trait default: do the whole coset-LDE device-side (see `gpu_coset_lde_bitrev`),
    /// which is what the PCS calls to commit. Bit-identical to `Radix2DitParallel::coset_lde_batch`.
    fn coset_lde_batch(
        &self,
        mat: RowMajorMatrix<Goldilocks>,
        added_bits: usize,
        shift: Goldilocks,
    ) -> Self::Evaluations {
        let (h, w) = (mat.height(), mat.width());
        let big = h << added_bits;
        let stored: Vec<u64> = if h < 2 {
            // degree-<1 (constant) poly ⇒ the same value at every coset point; replicate the single row.
            let row: Vec<u64> = (0..w)
                .map(|c| mat.values.get(c).map(|f| f.as_canonical_u64()).unwrap_or(0))
                .collect();
            (0..big).flat_map(|_| row.clone()).collect()
        } else {
            let evals = to_u64s(&mat.values);
            gpu_coset_lde_bitrev(&evals, h, w, added_bits, shift.as_canonical_u64())
        };
        BitReversalPerm::new_view(RowMajorMatrix::new(
            stored.into_iter().map(Goldilocks::new).collect(),
            w,
        ))
    }
}

/// Poseidon2-Goldilocks-8 round constants + internal diagonal, canonical-u64, in the layout the kernels
/// expect (`rci`: 4×8 external-initial, `rcp`: 22 internal, `rcf`: 4×8 external-final, `diag`: 8).
/// Sourced from p3's exported constants — the same ones `default_goldilocks_poseidon2_8` uses, so the
/// GPU permutation is bit-identical to the CPU hasher used in `verify_batch`.
fn poseidon2_consts() -> (Vec<u64>, Vec<u64>, Vec<u64>, Vec<u64>) {
    let flat = |rows: &[[Goldilocks; 8]]| {
        rows.iter()
            .flatten()
            .map(|x| x.as_canonical_u64())
            .collect()
    };
    (
        flat(&GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_INITIAL),
        GOLDILOCKS_POSEIDON2_RC_8_INTERNAL
            .iter()
            .map(|x| x.as_canonical_u64())
            .collect(),
        flat(&GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_FINAL),
        MATRIX_DIAG_8_GOLDILOCKS
            .iter()
            .map(|x| x.as_canonical_u64())
            .collect(),
    )
}

/// Build the whole Merkle tree on the GPU: leaf-hash the `h` rows of the row-major (canonical) `h×w`
/// leaf matrix (Poseidon2 sponge), then compress pairwise up to the root. The leaf matrix is produced
/// row-by-row by `fill(row, buf)` (parallel over rows) and marshalled straight into the pinned staging
/// window — the leaf input is by far the widest data we move (the 16-chunk quotient commit's is
/// ~170 MB), so it never materializes host-side. Returns every layer (layer 0 = leaves, last =
/// `[root]`), digests canonical. `h` must be a power of two.
fn gpu_merkle_layers_rows(
    h: usize,
    w: usize,
    fill: impl Fn(usize, &mut [u64]) + Sync,
) -> Vec<Vec<[Goldilocks; 4]>> {
    let _t0 = std::time::Instant::now();
    let (rci, rcp, rcf, diag) = poseidon2_consts();
    let out = with_ctx(|ctx| {
        let q = ctx.pq.queue().clone();
        let ro = |data: &[u64]| {
            ocl::Buffer::<u64>::builder()
                .queue(q.clone())
                .flags(ocl::flags::MEM_READ_ONLY | ocl::flags::MEM_COPY_HOST_PTR)
                .len(data.len().max(1))
                .copy_host_slice(if data.is_empty() { &[0u64] } else { data })
                .build()
                .unwrap()
        };
        let rw = |n: usize| {
            ocl::Buffer::<u64>::builder()
                .queue(q.clone())
                .flags(ocl::flags::MEM_READ_WRITE)
                .len(n)
                .build()
                .unwrap()
        };
        let (rci_b, rcp_b, rcf_b, diag_b) = (ro(&rci), ro(&rcp), ro(&rcf), ro(&diag));
        let leaves = rw(h * 4);
        // Row-band the (wide) leaf input so its device buffer stays under the per-allocation cap; the
        // per-row leaf hash is band-independent, so the digests match a single-shot hash bit-for-bit.
        // The full leaf-digest buffer (h×4) and the compression layers below stay well under the cap.
        let rb = ctx.row_block(w, h);
        let mut r0 = 0usize;
        while r0 < h {
            let nr = rb.min(h - r0);
            let inb = ctx.dev_buf(0, nr * w);
            ctx.upload_rows(&inb, nr, w, |i, buf| fill(r0 + i, buf));
            unsafe {
                ctx.pq
                    .kernel_builder("leaf_hash")
                    .arg(&inb)
                    .arg(&leaves)
                    .arg(r0 as u32)
                    .arg(nr as u32)
                    .arg(w as u32)
                    .arg(&rci_b)
                    .arg(&rcp_b)
                    .arg(&rcf_b)
                    .arg(&diag_b)
                    .global_work_size(nr)
                    .build()
                    .unwrap()
                    .enq()
                    .unwrap();
            }
            r0 += nr;
        }
        let to_digests = |raw: Vec<u64>| -> Vec<[Goldilocks; 4]> {
            raw.chunks_exact(4)
                .map(|c| {
                    [
                        Goldilocks::new(c[0]),
                        Goldilocks::new(c[1]),
                        Goldilocks::new(c[2]),
                        Goldilocks::new(c[3]),
                    ]
                })
                .collect()
        };
        let raw = ctx.download(&leaves, h * 4);
        let mut layers = vec![to_digests(raw)];
        let mut cur = leaves;
        let mut n = h;
        while n > 1 {
            let n_out = n / 2;
            let next = rw(n_out * 4);
            unsafe {
                ctx.pq
                    .kernel_builder("compress_layer")
                    .arg(&cur)
                    .arg(&next)
                    .arg(n_out as u32)
                    .arg(&rci_b)
                    .arg(&rcp_b)
                    .arg(&rcf_b)
                    .arg(&diag_b)
                    .global_work_size(n_out)
                    .build()
                    .unwrap()
                    .enq()
                    .unwrap();
            }
            let raw = ctx.download(&next, n_out * 4);
            layers.push(to_digests(raw));
            cur = next;
            n = n_out;
        }
        layers
    });
    MERKLE_NANOS.fetch_add(_t0.elapsed().as_nanos() as u64, Ordering::Relaxed);
    MERKLE_CALLS.fetch_add(1, Ordering::Relaxed);
    out
}

/// `gpu_merkle_layers_rows` over an already-materialized row-major leaf matrix (test harness).
#[cfg(test)]
fn gpu_merkle_layers(combined: &[u64], h: usize, w: usize) -> Vec<Vec<[Goldilocks; 4]>> {
    gpu_merkle_layers_rows(h, w, |i, buf| {
        buf.copy_from_slice(&combined[i * w..(i + 1) * w])
    })
}

/// Build the GPU tree and extract the `MerkleCap` at `cap_height` — byte-identical to
/// `MerkleTreeMmcs`/`MerkleTreeHidingMmcs`'s commitment. The cap is the layer `2^cap_height` nodes wide
/// (`digest_layers[num_layers-1-cap_height]`, `merkle_tree.rs::cap`); for a tree shorter than the cap
/// (small FRI layers) the cap clamps to the leaf layer (`effective_cap_height = min(cap_height, depth)`).
/// Returns the cap plus every layer (leaf..root) so `open_batch` can read sibling paths up to the cap.
/// (Test harness — the production hiding commit inlines this cap extraction over `_rows`.)
#[cfg(test)]
fn gpu_merkle_cap(
    combined: &[u64],
    h: usize,
    w: usize,
    cap_height: usize,
) -> (
    MerkleCap<Goldilocks, [Goldilocks; 4]>,
    Vec<Vec<[Goldilocks; 4]>>,
) {
    let layers = gpu_merkle_layers(combined, h, w);
    let num_layers = layers.len();
    let eff = cap_height.min(num_layers - 1);
    let cap_idx = num_layers - 1 - eff;
    (MerkleCap::new(layers[cap_idx].clone()), layers)
}

/// Run the quotient DAG interpreter on the GPU (grid-stride, one row per thread). All inputs are flat
/// canonical-`u64` buffers built by `quotient_gpu::gpu_quotient_values`; returns the `qsize` F_p² quotient
/// values as `(c0, c1)` pairs (canonical). See the `quotient` kernel.
#[allow(clippy::too_many_arguments)]
pub(crate) fn gpu_run_quotient(
    op_code: &[u32],
    op_a: &[u32],
    op_b: &[u32],
    consts: &[u64],
    roots: &[u32],
    trace: &[u64],
    width: usize,
    qsize: usize,
    next_step: usize,
    periodic: &[u64],
    n_periodic: usize,
    public: &[u64],
    is_first: &[u64],
    is_last: &[u64],
    is_transition: &[u64],
    inv_vanishing: &[u64],
    alpha0: &[u64],
    alpha1: &[u64],
) -> Vec<u64> {
    let _t0 = std::time::Instant::now();
    let n_ops = op_code.len();
    let n_roots = roots.len();
    let n_threads = qsize.min(1 << 15) as u32; // grid-stride pool cap (scratch = n_threads × n_ops)
    let out = with_proque(|pq| {
        let q = pq.queue().clone();
        let ro64 = |d: &[u64]| {
            ocl::Buffer::<u64>::builder()
                .queue(q.clone())
                .flags(ocl::flags::MEM_READ_ONLY | ocl::flags::MEM_COPY_HOST_PTR)
                .len(d.len().max(1))
                .copy_host_slice(if d.is_empty() { &[0u64] } else { d })
                .build()
                .unwrap()
        };
        let ro32 = |d: &[u32]| {
            ocl::Buffer::<u32>::builder()
                .queue(q.clone())
                .flags(ocl::flags::MEM_READ_ONLY | ocl::flags::MEM_COPY_HOST_PTR)
                .len(d.len().max(1))
                .copy_host_slice(if d.is_empty() { &[0u32] } else { d })
                .build()
                .unwrap()
        };
        let (opc, opa, opb, cst, rts) = (
            ro32(op_code),
            ro32(op_a),
            ro32(op_b),
            ro64(consts),
            ro32(roots),
        );
        let (tr, per, pb) = (ro64(trace), ro64(periodic), ro64(public));
        let (isf, isl, ist, ivn) = (
            ro64(is_first),
            ro64(is_last),
            ro64(is_transition),
            ro64(inv_vanishing),
        );
        let (a0, a1) = (ro64(alpha0), ro64(alpha1));
        let scratch = ocl::Buffer::<u64>::builder()
            .queue(q.clone())
            .flags(ocl::flags::MEM_READ_WRITE)
            .len((n_threads as usize) * n_ops)
            .build()
            .unwrap();
        let outb = ocl::Buffer::<u64>::builder()
            .queue(q.clone())
            .flags(ocl::flags::MEM_WRITE_ONLY)
            .len(qsize * 2)
            .build()
            .unwrap();
        unsafe {
            pq.kernel_builder("quotient")
                .arg(&opc)
                .arg(&opa)
                .arg(&opb)
                .arg(&cst)
                .arg(&rts)
                .arg(n_ops as u32)
                .arg(n_roots as u32)
                .arg(&tr)
                .arg(width as u32)
                .arg(qsize as u32)
                .arg(next_step as u32)
                .arg(&per)
                .arg(n_periodic as u32)
                .arg(&pb)
                .arg(&isf)
                .arg(&isl)
                .arg(&ist)
                .arg(&ivn)
                .arg(&a0)
                .arg(&a1)
                .arg(&scratch)
                .arg(n_threads)
                .arg(&outb)
                .global_work_size(n_threads as usize)
                .build()
                .unwrap()
                .enq()
                .unwrap();
        }
        let mut out = vec![0u64; qsize * 2];
        outb.read(&mut out).enq().unwrap();
        out
    });
    QUOTIENT_NANOS.fetch_add(_t0.elapsed().as_nanos() as u64, Ordering::Relaxed);
    QUOTIENT_CALLS.fetch_add(1, Ordering::Relaxed);
    out
}

/// A GPU-backed Merkle-tree `Mmcs` — a self-consistent drop-in for the PCS's `ValMmcs` that offloads the
/// Poseidon2 leaf-hash + tree compression (≈45% of a proof) to the GPU. `commit` runs on the GPU;
/// `open_batch`/`verify_batch` are CPU (cheap, per-query) using the *same* Poseidon2 constants, so a
/// GPU-built commitment verifies against the CPU hasher bit-for-bit. Non-hiding (no salts) and
/// equal-height matrices only — exactly what `TwoAdicFriPcs` commits (trace / same-height quotient
/// chunks / single FRI layers). Digest = `[Goldilocks; 4]` with `cap_height = 0` (a single root).
#[derive(Clone)]
pub struct GpuMerkleMmcs {
    hash: MyHash,
    compress: MyCompress,
}

impl GpuMerkleMmcs {
    pub fn new() -> Self {
        let perm = default_goldilocks_poseidon2_8();
        Self {
            hash: MyHash::new(perm.clone()),
            compress: MyCompress::new(perm),
        }
    }
}

impl Default for GpuMerkleMmcs {
    fn default() -> Self {
        Self::new()
    }
}

/// Prover data: the committed matrices (for opening) + every tree layer (leaf..root), digests canonical.
pub struct GpuMerkleData<M> {
    matrices: Vec<M>,
    layers: Vec<Vec<[Goldilocks; 4]>>,
}

impl Mmcs<Goldilocks> for GpuMerkleMmcs {
    type ProverData<M> = GpuMerkleData<M>;
    type Commitment = [Goldilocks; 4];
    type Proof = Vec<[Goldilocks; 4]>;
    type Error = ();

    fn commit<M: Matrix<Goldilocks>>(
        &self,
        inputs: Vec<M>,
    ) -> (Self::Commitment, Self::ProverData<M>) {
        let h = inputs[0].height();
        assert!(
            h.is_power_of_two(),
            "GpuMerkleMmcs: height {h} must be a power of two"
        );
        assert!(
            inputs.iter().all(|m| m.height() == h),
            "GpuMerkleMmcs: matrices must be equal height"
        );
        let total_w: usize = inputs.iter().map(|m| m.width()).sum();
        // leaf row i = concat of every matrix's logical row i (matrix order), marshalled straight into
        // the pinned staging window (parallel over rows — the marshalling dominates the commit's CPU
        // cost; each row is independent).
        let layers = gpu_merkle_layers_rows(h, total_w, |i, row_buf| {
            let mut off = 0;
            for m in &inputs {
                for v in m.row(i).expect("row < height") {
                    row_buf[off] = v.as_canonical_u64();
                    off += 1;
                }
            }
        });
        let root = *layers.last().unwrap().first().unwrap();
        (
            root,
            GpuMerkleData {
                matrices: inputs,
                layers,
            },
        )
    }

    fn open_batch<M: Matrix<Goldilocks>>(
        &self,
        index: usize,
        prover_data: &Self::ProverData<M>,
    ) -> BatchOpening<Goldilocks, Self> {
        let opened_values: Vec<Vec<Goldilocks>> = prover_data
            .matrices
            .iter()
            .map(|m| m.row(index).expect("row < height").into_iter().collect())
            .collect();
        // sibling path: at each layer below the root, the digest of the sibling of the current node.
        let mut opening_proof = Vec::with_capacity(prover_data.layers.len().saturating_sub(1));
        let mut idx = index;
        for layer in &prover_data.layers[..prover_data.layers.len() - 1] {
            opening_proof.push(layer[idx ^ 1]);
            idx >>= 1;
        }
        BatchOpening::new(opened_values, opening_proof)
    }

    fn get_matrices<'a, M: Matrix<Goldilocks>>(
        &self,
        prover_data: &'a Self::ProverData<M>,
    ) -> Vec<&'a M> {
        prover_data.matrices.iter().collect()
    }

    fn verify_batch(
        &self,
        commit: &Self::Commitment,
        _dimensions: &[Dimensions],
        index: usize,
        batch_opening: BatchOpeningRef<'_, Goldilocks, Self>,
    ) -> Result<(), Self::Error> {
        let (opened_values, opening_proof) = batch_opening.unpack();
        // leaf = hash of concatenated opened rows (matrix order — same as commit's `combined`).
        let mut cur: [Goldilocks; 4] = self.hash.hash_iter(opened_values.iter().flatten().copied());
        let mut idx = index;
        for sib in opening_proof {
            cur = if idx & 1 == 0 {
                self.compress.compress([cur, *sib])
            } else {
                self.compress.compress([*sib, cur])
            };
            idx >>= 1;
        }
        if &cur == commit {
            Ok(())
        } else {
            Err(())
        }
    }
}

/// A GPU-backed **hiding** Merkle-tree `Mmcs`, byte-compatible with `MerkleTreeHidingMmcs<…, 2, 4, 4>`.
///
/// Like p3's hiding MMCS this is a salted wrapper over the plain Merkle tree: `commit` appends
/// `SALT_ELEMS = 4` random columns to each matrix (`RowMajorMatrix::rand`, the same draw as p3 — a shared
/// RNG seed reproduces p3's salts), builds the tree over the salted rows **on the GPU** (`gpu_merkle_cap`,
/// reusing the bit-exact Poseidon2 kernels), and emits a `MerkleCap`. `open_batch` returns
/// `(openings, (salts, siblings))` and `verify_batch` re-hashes `(opening ‖ salt)` and folds to the cap —
/// the associated types (`MerkleCap<Val,[Val;4]>`, `(Vec<Vec<Val>>, Vec<[Val;4]>)`) are **identical** to
/// `MerkleTreeHidingMmcs`, so a `Proof` produced under this MMCS serializes byte-identically and is
/// accepted by the production verifier. Non-hiding note: equal-height matrices only (what the PCS commits).
pub struct GpuHidingMerkleMmcs {
    rng: std::sync::Mutex<ChaCha20Rng>,
    hash: MyHash,
    compress: MyCompress,
    cap_height: usize,
}

impl GpuHidingMerkleMmcs {
    /// Mirror of `MerkleTreeHidingMmcs::new(hash, compress, cap_height, rng)`.
    pub fn new(hash: MyHash, compress: MyCompress, cap_height: usize, rng: ChaCha20Rng) -> Self {
        Self {
            rng: std::sync::Mutex::new(rng),
            hash,
            compress,
            cap_height,
        }
    }
}

impl Clone for GpuHidingMerkleMmcs {
    fn clone(&self) -> Self {
        // Mirror hiding_mmcs.rs:79-91 — clone the inner rng under the lock.
        Self {
            rng: std::sync::Mutex::new(self.rng.lock().unwrap().clone()),
            hash: self.hash.clone(),
            compress: self.compress.clone(),
            cap_height: self.cap_height,
        }
    }
}

/// Prover data: the committed matrices (unsalted, for opening), the per-matrix salt rows (flat `h×4`),
/// and every tree layer (leaf..root) for sibling extraction.
pub struct GpuHidingData<M> {
    matrices: Vec<M>,
    salts: Vec<Vec<Goldilocks>>,
    layers: Vec<Vec<[Goldilocks; 4]>>,
}

impl Mmcs<Goldilocks> for GpuHidingMerkleMmcs {
    type ProverData<M> = GpuHidingData<M>;
    type Commitment = MerkleCap<Goldilocks, [Goldilocks; 4]>;
    /// (salts, siblings) — identical to `MerkleTreeHidingMmcs::Proof`.
    type Proof = (Vec<Vec<Goldilocks>>, Vec<[Goldilocks; 4]>);
    type Error = ();

    fn commit<M: Matrix<Goldilocks>>(
        &self,
        inputs: Vec<M>,
    ) -> (Self::Commitment, Self::ProverData<M>) {
        let h = inputs[0].height();
        assert!(
            h.is_power_of_two(),
            "GpuHidingMerkleMmcs: height {h} must be a power of two"
        );
        assert!(
            inputs.iter().all(|m| m.height() == h),
            "GpuHidingMerkleMmcs: matrices must be equal height"
        );
        // Salts: one 4-wide random matrix per input, drawn in input order — the exact p3 call
        // (`RowMajorMatrix::rand(rng, h, SALT_ELEMS)` per matrix), so a shared seed reproduces p3's salts.
        let salts: Vec<Vec<Goldilocks>> = {
            let mut rng = self.rng.lock().unwrap();
            inputs
                .iter()
                .map(|_| RowMajorMatrix::rand(&mut *rng, h, 4).values)
                .collect()
        };
        // leaf row i = concat over matrices of [mat_k row i ‖ salt_k row i] (p3's HorizontalPair
        // order), marshalled straight into the pinned staging window. Parallel over rows — this
        // marshalling (materializing the wide LDE rows to canonical u64) is the dominant CPU cost of
        // the quotient commit; each row is independent.
        let total_w: usize = inputs.iter().map(|m| m.width() + 4).sum();
        let layers = gpu_merkle_layers_rows(h, total_w, |i, row_buf| {
            let mut off = 0;
            for (m, salt) in inputs.iter().zip(&salts) {
                for v in m.row(i).expect("row < height") {
                    row_buf[off] = v.as_canonical_u64();
                    off += 1;
                }
                for c in 0..4 {
                    row_buf[off] = salt[i * 4 + c].as_canonical_u64();
                    off += 1;
                }
            }
        });
        let eff = self.cap_height.min(layers.len() - 1);
        let cap = MerkleCap::new(layers[layers.len() - 1 - eff].clone());
        (
            cap,
            GpuHidingData {
                matrices: inputs,
                salts,
                layers,
            },
        )
    }

    fn open_batch<M: Matrix<Goldilocks>>(
        &self,
        index: usize,
        prover_data: &Self::ProverData<M>,
    ) -> BatchOpening<Goldilocks, Self> {
        let openings: Vec<Vec<Goldilocks>> = prover_data
            .matrices
            .iter()
            .map(|m| m.row(index).expect("row < height").into_iter().collect())
            .collect();
        let salts: Vec<Vec<Goldilocks>> = prover_data
            .salts
            .iter()
            .map(|s| s[index * 4..index * 4 + 4].to_vec())
            .collect();
        let num_layers = prover_data.layers.len();
        let cap_idx = num_layers - 1 - self.cap_height.min(num_layers - 1);
        let mut siblings = Vec::with_capacity(cap_idx);
        let mut idx = index;
        for layer in &prover_data.layers[..cap_idx] {
            siblings.push(layer[idx ^ 1]);
            idx >>= 1;
        }
        BatchOpening::new(openings, (salts, siblings))
    }

    fn get_matrices<'a, M: Matrix<Goldilocks>>(
        &self,
        prover_data: &'a Self::ProverData<M>,
    ) -> Vec<&'a M> {
        prover_data.matrices.iter().collect()
    }

    fn verify_batch(
        &self,
        commit: &Self::Commitment,
        _dimensions: &[Dimensions],
        index: usize,
        batch_opening: BatchOpeningRef<'_, Goldilocks, Self>,
    ) -> Result<(), Self::Error> {
        let (openings, proof) = batch_opening.unpack();
        let (salts, siblings) = (&proof.0, &proof.1);
        // leaf = hash of concat [opening_k ‖ salt_k] in matrix order (same as commit's `combined`).
        let leaf_input = openings
            .iter()
            .zip(salts.iter())
            .flat_map(|(o, s)| o.iter().chain(s.iter()).copied());
        let mut cur: [Goldilocks; 4] = self.hash.hash_iter(leaf_input);
        let mut idx = index;
        for sib in siblings {
            cur = if idx & 1 == 0 {
                self.compress.compress([cur, *sib])
            } else {
                self.compress.compress([*sib, cur])
            };
            idx >>= 1;
        }
        // after folding to the cap layer, `idx` is the position within the cap.
        if commit.roots().get(idx) == Some(&cur) {
            Ok(())
        } else {
            Err(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_dft::Radix2DitParallel;
    use rand::{RngExt, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    /// GpuDft.dft_batch is bit-identical to Radix2DitParallel across sizes incl. the real 2^16 LDE.
    #[test]
    #[ignore = "requires an OpenCL runtime + GPU"]
    fn gpu_dft_matches_p3() {
        let mut rng = ChaCha20Rng::seed_from_u64(1);
        for &(log_h, w) in &[(1usize, 1usize), (4, 3), (8, 5), (12, 2), (16, 19)] {
            let h = 1 << log_h;
            let vals: Vec<Goldilocks> = (0..h * w)
                .map(|_| Goldilocks::new(rng.random::<u64>() % 0xFFFF_FFFF_0000_0001))
                .collect();
            let mat = RowMajorMatrix::new(vals, w);
            let cpu = Radix2DitParallel::<Goldilocks>::default()
                .dft_batch(mat.clone())
                .to_row_major_matrix();
            let gpu = GpuDft.dft_batch(mat).to_row_major_matrix();
            assert_eq!(cpu.values, gpu.values, "GpuDft != p3 at h=2^{log_h} w={w}");
        }
    }

    /// GpuDft.coset_lde_batch — the device-side iDFT → coset-scale → forward-NTT pipeline, the exact
    /// call the PCS commits through — is bit-identical to `Radix2DitParallel::coset_lde_batch` across
    /// sizes/widths including the production shapes (2^12×19 trace, 2^12×2 quotient chunks, blowup 4).
    #[test]
    #[ignore = "requires an OpenCL runtime + GPU"]
    fn gpu_coset_lde_matches_p3() {
        let mut rng = ChaCha20Rng::seed_from_u64(2);
        let shift = Goldilocks::GENERATOR;
        // Include the batch (w=49) and aggregator-ish (w=53) widths so the column-tiling path is exercised.
        for &(log_h, w, added) in &[
            (1usize, 1usize, 1usize),
            (4, 3, 2),
            (8, 5, 3),
            (12, 2, 4),
            (12, 19, 4),
            (12, 49, 4),
            (10, 53, 4),
        ] {
            let h = 1 << log_h;
            let vals: Vec<Goldilocks> = (0..h * w)
                .map(|_| Goldilocks::new(rng.random::<u64>() % 0xFFFF_FFFF_0000_0001))
                .collect();
            let mat = RowMajorMatrix::new(vals, w);
            let cpu = Radix2DitParallel::<Goldilocks>::default()
                .coset_lde_batch(mat.clone(), added, shift)
                .to_row_major_matrix();
            let gpu = GpuDft
                .coset_lde_batch(mat, added, shift)
                .to_row_major_matrix();
            assert_eq!(
                cpu.values, gpu.values,
                "GpuDft coset_lde != p3 at h=2^{log_h} w={w} added={added}"
            );
        }
    }

    /// Column-tiling is transparent: with `LATTICA_GPU_COL_BLOCK` forcing multi-block tiling (C=1,2,3),
    /// the stitched coset-LDE stays bit-identical to p3. This proves the sub-tiling that keeps each
    /// device buffer under the per-allocation cap changes only the tile shape, never the output values —
    /// the byte-compat guarantee that lets wide (batch ≥16 tx / aggregator) traces LDE on-device.
    /// Run serially (the GPU context + the env var are process-global): `--test-threads=1`.
    #[test]
    #[ignore = "requires an OpenCL runtime + GPU; run with --test-threads=1"]
    fn gpu_coset_lde_column_tiling_matches_p3() {
        let mut rng = ChaCha20Rng::seed_from_u64(7);
        let shift = Goldilocks::GENERATOR;
        for cb in [1usize, 2, 3] {
            std::env::set_var("LATTICA_GPU_COL_BLOCK", cb.to_string());
            for &(log_h, w, added) in &[(8usize, 7usize, 3usize), (10, 19, 4), (6, 49, 2)] {
                let h = 1 << log_h;
                let vals: Vec<Goldilocks> = (0..h * w)
                    .map(|_| Goldilocks::new(rng.random::<u64>() % 0xFFFF_FFFF_0000_0001))
                    .collect();
                let mat = RowMajorMatrix::new(vals, w);
                let cpu = Radix2DitParallel::<Goldilocks>::default()
                    .coset_lde_batch(mat.clone(), added, shift)
                    .to_row_major_matrix();
                let gpu = GpuDft
                    .coset_lde_batch(mat, added, shift)
                    .to_row_major_matrix();
                assert_eq!(
                    cpu.values, gpu.values,
                    "tiled GpuDft coset_lde != p3 at C={cb} h=2^{log_h} w={w} added={added}"
                );
            }
        }
        std::env::remove_var("LATTICA_GPU_COL_BLOCK");
    }

    /// END-TO-END: prove the REAL production join-split circuit with GPU-accelerated LDE, then assert
    /// the STANDARD (CPU) verifier accepts it — the consensus criterion (production is hiding, so
    /// full proofs are non-deterministic; "verifies" is the right check, not byte-equality).
    #[test]
    #[ignore = "requires an OpenCL runtime + GPU; runs a real proof"]
    fn gpu_joinsplit_proof_verifies() {
        use crate::joinsplit_air::{self, JoinSplitAir};
        let w = joinsplit_air::demo_witness();
        let pis = joinsplit_air::public_values(&w);
        let bytes =
            crate::config::gpu::proof_to_bytes(&JoinSplitAir, joinsplit_air::build_trace(&w), &pis);
        assert!(
            joinsplit_air::verify_bytes(&bytes, &pis),
            "GPU-proved join-split must verify under the standard verifier"
        );
    }

    /// Same for the v3 shielded-HTLC circuit.
    #[test]
    #[ignore = "requires an OpenCL runtime + GPU; runs a real proof"]
    fn gpu_htlc_proof_verifies() {
        use crate::htlc_air::{self, HtlcAir};
        let w = htlc_air::demo_htlc_witness();
        let pis = htlc_air::public_values(&w);
        let bytes = crate::config::gpu::proof_to_bytes(&HtlcAir, htlc_air::build_trace(&w), &pis);
        assert!(
            htlc_air::verify_bytes(&bytes, &pis),
            "GPU-proved HTLC must verify under the standard verifier"
        );
    }

    /// H3 KILLER TEST: a proof made with the GPU **hiding** config — GPU LDE *and* GPU Merkle
    /// (`GpuHidingMerkleMmcs`) — verifies under the STANDARD production verifier. This proves the GPU
    /// hiding path is byte-compatible end-to-end (the whole FRI query/open/verify exercises the salted
    /// tree), so the existing verifier / C-ABI / node accept GPU-accelerated proofs unchanged.
    #[test]
    #[ignore = "requires an OpenCL runtime + GPU; runs a real proof"]
    fn gpu_joinsplit_proof_verifies_hiding() {
        use crate::joinsplit_air::{self, JoinSplitAir};
        let w = joinsplit_air::demo_witness();
        let pis = joinsplit_air::public_values(&w);
        let bytes = crate::config::gpu::proof_to_bytes_hiding(
            &JoinSplitAir,
            joinsplit_air::build_trace(&w),
            &pis,
        );
        assert!(
            joinsplit_air::verify_bytes(&bytes, &pis),
            "GPU-hiding join-split proof must verify under the standard production verifier"
        );
    }

    /// H3 killer test, HTLC.
    #[test]
    #[ignore = "requires an OpenCL runtime + GPU; runs a real proof"]
    fn gpu_htlc_proof_verifies_hiding() {
        use crate::htlc_air::{self, HtlcAir};
        let w = htlc_air::demo_htlc_witness();
        let pis = htlc_air::public_values(&w);
        let bytes =
            crate::config::gpu::proof_to_bytes_hiding(&HtlcAir, htlc_air::build_trace(&w), &pis);
        assert!(
            htlc_air::verify_bytes(&bytes, &pis),
            "GPU-hiding HTLC proof must verify under the standard production verifier"
        );
    }

    /// Honest CPU-vs-GPU wall-clock for proving the real join-split circuit (prints; never asserts a
    /// speedup — the LDE kernel is faster per-DFT, but the end-to-end win needs a GPU coset_lde override,
    /// which is a follow-on). Both proofs verify.
    #[test]
    #[ignore = "requires an OpenCL runtime + GPU; benchmark"]
    fn gpu_joinsplit_benchmark() {
        use crate::joinsplit_air::{self, JoinSplitAir};
        use std::time::Instant;
        let w = joinsplit_air::demo_witness();
        let pis = joinsplit_air::public_values(&w);
        let runs = 5;
        let mut cpu_ms = f64::MAX;
        let mut gpu_ms = f64::MAX;
        for _ in 0..runs {
            let t = Instant::now();
            let b = joinsplit_air::prove_to_bytes(&w);
            cpu_ms = cpu_ms.min(t.elapsed().as_secs_f64() * 1e3);
            assert!(joinsplit_air::verify_bytes(&b, &pis));
            super::prof_reset();
            let t = Instant::now();
            let b = crate::config::gpu::proof_to_bytes(
                &JoinSplitAir,
                joinsplit_air::build_trace(&w),
                &pis,
            );
            gpu_ms = gpu_ms.min(t.elapsed().as_secs_f64() * 1e3);
            assert!(joinsplit_air::verify_bytes(&b, &pis));
        }
        let (ntt_ms, ntt_calls, _mk_ms, _mk_calls) = super::prof_report();
        println!("join-split prove (best of {runs}): CPU {cpu_ms:.1}ms | GPU-LDE {gpu_ms:.1}ms  (both verify)");
        println!("  of the GPU run: {ntt_ms:.1}ms in {ntt_calls} GPU-NTT calls (the rest — Merkle/quotient/FRI/glue — is CPU)");
    }

    /// Standalone self-consistency for `GpuMerkleMmcs`: GPU-commit a batch of equal-height matrices,
    /// then for several query indices assert `open_batch` produces an opening the (CPU) `verify_batch`
    /// accepts against the GPU root — and that a tampered opening / wrong index is rejected. This is the
    /// de-risking gate before wiring it into the FRI (M2): commit(GPU) ↔ verify(CPU) must agree.
    #[test]
    #[ignore = "requires an OpenCL runtime + GPU"]
    fn gpu_merkle_mmcs_self_consistent() {
        let mmcs = GpuMerkleMmcs::new();
        let mut rng = ChaCha20Rng::seed_from_u64(7);
        for &(log_h, widths) in &[
            (1usize, &[1usize][..]),
            (3, &[2, 5]),
            (6, &[4]),
            (10, &[2, 2, 3]),
            (12, &[7]),
        ] {
            let h = 1usize << log_h;
            let mats: Vec<RowMajorMatrix<Goldilocks>> = widths
                .iter()
                .map(|&w| {
                    RowMajorMatrix::new(
                        (0..h * w)
                            .map(|_| Goldilocks::new(rng.random::<u64>() % 0xFFFF_FFFF_0000_0001))
                            .collect(),
                        w,
                    )
                })
                .collect();
            let dims: Vec<Dimensions> = mats
                .iter()
                .map(|m| Dimensions {
                    width: m.width(),
                    height: h,
                })
                .collect();
            let (commit, data) = mmcs.commit(mats.clone());
            for &idx in &[0usize, 1, h / 3, h / 2, h - 1] {
                let opening = mmcs.open_batch(idx, &data);
                // opened rows must equal the source rows.
                for (m, row) in mats.iter().zip(&opening.opened_values) {
                    let want: Vec<Goldilocks> = m.row(idx).unwrap().into_iter().collect();
                    assert_eq!(&want, row, "open row mismatch at h=2^{log_h} idx={idx}");
                }
                let r#ref = BatchOpeningRef::new(&opening.opened_values, &opening.opening_proof);
                assert_eq!(
                    mmcs.verify_batch(&commit, &dims, idx, r#ref),
                    Ok(()),
                    "verify h=2^{log_h} idx={idx}"
                );
                // tamper: a corrupted opened value must be rejected.
                if h > 1 {
                    let mut bad = opening.opened_values.clone();
                    bad[0][0] += Goldilocks::ONE;
                    let bref = BatchOpeningRef::new(&bad, &opening.opening_proof);
                    assert_eq!(
                        mmcs.verify_batch(&commit, &dims, idx, bref),
                        Err(()),
                        "tampered value accepted"
                    );
                    // wrong index must be rejected (path no longer matches).
                    let wrong = (idx + 1) % h;
                    let wref = BatchOpeningRef::new(&opening.opened_values, &opening.opening_proof);
                    assert_eq!(
                        mmcs.verify_batch(&commit, &dims, wrong, wref),
                        Err(()),
                        "wrong index accepted"
                    );
                }
            }
        }
    }

    /// H1 gate: the GPU `MerkleCap` + sibling paths are BYTE-IDENTICAL to CPU `MerkleTreeMmcs` with
    /// `cap_height = 6` (the production cap). This de-risks the cap + sibling mechanics against the p3
    /// reference in isolation — and confirms the scalar GPU leaf-hash matches p3's SIMD-packed hashing.
    #[test]
    #[ignore = "requires an OpenCL runtime + GPU"]
    fn gpu_merkle_cap_matches_p3() {
        use p3_field::Field;
        use p3_merkle_tree::MerkleTreeMmcs;
        type Cpu = MerkleTreeMmcs<
            <Goldilocks as Field>::Packing,
            <Goldilocks as Field>::Packing,
            MyHash,
            MyCompress,
            2,
            4,
        >;
        let perm = default_goldilocks_poseidon2_8();
        let cpu = Cpu::new(MyHash::new(perm.clone()), MyCompress::new(perm), 6);
        let mut rng = ChaCha20Rng::seed_from_u64(9);
        for &(log_h, widths) in &[
            (7usize, &[1usize][..]),
            (8, &[2, 5]),
            (10, &[4]),
            (12, &[2, 2, 3]),
            (16, &[7]),
        ] {
            let h = 1usize << log_h;
            let mats: Vec<RowMajorMatrix<Goldilocks>> = widths
                .iter()
                .map(|&w| {
                    RowMajorMatrix::new(
                        (0..h * w)
                            .map(|_| Goldilocks::new(rng.random::<u64>() % 0xFFFF_FFFF_0000_0001))
                            .collect(),
                        w,
                    )
                })
                .collect();
            let (cap_cpu, data_cpu) = cpu.commit(mats.clone());
            // GPU: build the concatenated-row leaf buffer, then the cap.
            let total_w: usize = widths.iter().sum();
            let mut combined = vec![0u64; h * total_w];
            for i in 0..h {
                let mut off = i * total_w;
                for m in &mats {
                    for v in m.row(i).unwrap() {
                        combined[off] = v.as_canonical_u64();
                        off += 1;
                    }
                }
            }
            let (cap_gpu, layers) = gpu_merkle_cap(&combined, h, total_w, 6);
            assert_eq!(
                cap_cpu.roots(),
                cap_gpu.roots(),
                "cap mismatch at h=2^{log_h}"
            );
            // sibling paths (up to the cap) must match p3's open_batch.
            let cap_idx = layers.len() - 1 - 6usize.min(layers.len() - 1);
            for &idx in &[0usize, 1, h / 2, h - 1] {
                let (_, sib_cpu) = cpu.open_batch(idx, &data_cpu).unpack();
                let mut sib_gpu = Vec::new();
                let mut j = idx;
                for layer in &layers[..cap_idx] {
                    sib_gpu.push(layer[j ^ 1]);
                    j >>= 1;
                }
                assert_eq!(
                    sib_cpu, sib_gpu,
                    "siblings mismatch at h=2^{log_h} idx={idx}"
                );
            }
        }
    }

    /// H2 GOLD-STANDARD gate: `GpuHidingMerkleMmcs` is byte-compatible with p3's `MerkleTreeHidingMmcs`.
    /// Seed BOTH with the same `ChaCha20Rng` → identical salts → the GPU `MerkleCap` and the
    /// `(salts, siblings)` proof are byte-identical to p3's; and the production CPU hiding verifier
    /// ACCEPTS the GPU commit+opening. This proves byte-compatibility at the MMCS level before the FRI.
    #[test]
    #[ignore = "requires an OpenCL runtime + GPU"]
    fn gpu_hiding_mmcs_matches_p3() {
        use p3_field::Field;
        use p3_merkle_tree::MerkleTreeHidingMmcs;
        type CpuHiding = MerkleTreeHidingMmcs<
            <Goldilocks as Field>::Packing,
            <Goldilocks as Field>::Packing,
            MyHash,
            MyCompress,
            ChaCha20Rng,
            2,
            4,
            4,
        >;
        let perm = default_goldilocks_poseidon2_8();
        let seed = 123u64;
        let cpu = CpuHiding::new(
            MyHash::new(perm.clone()),
            MyCompress::new(perm.clone()),
            6,
            ChaCha20Rng::seed_from_u64(seed),
        );
        let gpu = GpuHidingMerkleMmcs::new(
            MyHash::new(perm.clone()),
            MyCompress::new(perm),
            6,
            ChaCha20Rng::seed_from_u64(seed),
        );
        let mut rng = ChaCha20Rng::seed_from_u64(999);
        for &(log_h, widths) in &[
            (7usize, &[1usize][..]),
            (8, &[2, 5]),
            (10, &[4]),
            (12, &[3, 3]),
            (16, &[7]),
        ] {
            let h = 1usize << log_h;
            let mats: Vec<RowMajorMatrix<Goldilocks>> = widths
                .iter()
                .map(|&w| {
                    RowMajorMatrix::new(
                        (0..h * w)
                            .map(|_| Goldilocks::new(rng.random::<u64>() % 0xFFFF_FFFF_0000_0001))
                            .collect(),
                        w,
                    )
                })
                .collect();
            let dims: Vec<Dimensions> = mats.iter().map(|m| m.dimensions()).collect();
            let (cap_cpu, data_cpu) = cpu.commit(mats.clone());
            let (cap_gpu, data_gpu) = gpu.commit(mats.clone());
            assert_eq!(
                cap_cpu.roots(),
                cap_gpu.roots(),
                "hiding cap mismatch at h=2^{log_h}"
            );
            for &idx in &[0usize, 1, h / 2, h - 1] {
                let op_cpu = cpu.open_batch(idx, &data_cpu);
                let op_gpu = gpu.open_batch(idx, &data_gpu);
                assert_eq!(
                    op_cpu.opened_values, op_gpu.opened_values,
                    "openings mismatch h=2^{log_h} idx={idx}"
                );
                assert_eq!(
                    op_cpu.opening_proof, op_gpu.opening_proof,
                    "(salts,siblings) mismatch h=2^{log_h} idx={idx}"
                );
                // THE byte-compat proof: the production CPU hiding verifier accepts the GPU cap + opening.
                let cpu_ref = BatchOpeningRef::<Goldilocks, CpuHiding>::new(
                    &op_gpu.opened_values,
                    &op_gpu.opening_proof,
                );
                assert!(
                    cpu.verify_batch(&cap_gpu, &dims, idx, cpu_ref).is_ok(),
                    "CPU verifier rejects GPU cap+opening h=2^{log_h} idx={idx}"
                );
                // and self-consistent: the GPU verifier accepts its own opening.
                let gpu_ref = BatchOpeningRef::<Goldilocks, GpuHidingMerkleMmcs>::new(
                    &op_gpu.opened_values,
                    &op_gpu.opening_proof,
                );
                assert!(
                    gpu.verify_batch(&cap_gpu, &dims, idx, gpu_ref).is_ok(),
                    "GPU verifier rejects its own opening"
                );
            }
        }
    }

    /// THE 2× BENCHMARK: prove the real join-split circuit under two apples-to-apples non-hiding configs
    /// — CPU (`Radix2DitParallel` + `MerkleTreeMmcs`) vs GPU (`GpuDft` + `GpuMerkleMmcs`) — with identical
    /// FRI params. Both LDE **and** Merkle now run on the GPU, so this measures the real acceleration
    /// (not just the LDE slice). Asserts each proof verifies under its own config (self-consistent).
    #[test]
    #[ignore = "requires an OpenCL runtime + GPU; benchmark"]
    fn gpu_merkle_benchmark() {
        use crate::config::gpu::{make_bench_config_cpu, make_bench_config_gpu};
        use crate::joinsplit_air::{self, JoinSplitAir};
        use p3_uni_stark::{prove, verify};
        use std::time::Instant;
        let w = joinsplit_air::demo_witness();
        let pis = joinsplit_air::public_values(&w);
        let cpu_cfg = make_bench_config_cpu();
        let gpu_cfg = make_bench_config_gpu();
        // correctness: each proof verifies under its own (self-consistent) config.
        let p_cpu = prove(
            &cpu_cfg,
            &JoinSplitAir,
            joinsplit_air::build_trace(&w),
            &pis,
        );
        assert!(
            verify(&cpu_cfg, &JoinSplitAir, &p_cpu, &pis).is_ok(),
            "CPU-bench proof must verify"
        );
        let p_gpu = prove(
            &gpu_cfg,
            &JoinSplitAir,
            joinsplit_air::build_trace(&w),
            &pis,
        );
        assert!(
            verify(&gpu_cfg, &JoinSplitAir, &p_gpu, &pis).is_ok(),
            "GPU-bench proof must verify"
        );
        // timing: best-of-N wall clock.
        let runs = 5;
        let (mut cpu_ms, mut gpu_ms) = (f64::MAX, f64::MAX);
        super::prof_reset();
        for _ in 0..runs {
            let t = Instant::now();
            let _ = prove(
                &cpu_cfg,
                &JoinSplitAir,
                joinsplit_air::build_trace(&w),
                &pis,
            );
            cpu_ms = cpu_ms.min(t.elapsed().as_secs_f64() * 1e3);
            let t = Instant::now();
            let _ = prove(
                &gpu_cfg,
                &JoinSplitAir,
                joinsplit_air::build_trace(&w),
                &pis,
            );
            gpu_ms = gpu_ms.min(t.elapsed().as_secs_f64() * 1e3);
        }
        let (ntt_ms, ntt_calls, mk_ms, mk_calls) = super::prof_report();
        println!("join-split prove, non-hiding (best of {runs}): CPU {cpu_ms:.1}ms | GPU(LDE+Merkle) {gpu_ms:.1}ms  ({:.2}x)", cpu_ms / gpu_ms);
        println!("  GPU work across {runs} runs: NTT {ntt_ms:.0}ms / {ntt_calls} calls, Merkle {mk_ms:.0}ms / {mk_calls} commits");
    }

    /// H4 — THE PRODUCTION-WORKLOAD BENCHMARK: prove the real join-split circuit under the production CPU
    /// hiding config (`joinsplit_air::prove_to_bytes`) vs the GPU hiding config
    /// (`config::gpu::proof_to_bytes_hiding`) — both `HidingFriPcs` + `is_zk` + salts, and **both verified
    /// under the production verifier**. This is the speedup on the *hiding* workload the node runs.
    #[test]
    #[ignore = "requires an OpenCL runtime + GPU; benchmark"]
    fn gpu_hiding_benchmark() {
        use crate::joinsplit_air::{self, JoinSplitAir};
        use std::time::Instant;
        let w = joinsplit_air::demo_witness();
        let pis = joinsplit_air::public_values(&w);
        // correctness: both proofs verify under the STANDARD production verifier.
        let c = joinsplit_air::prove_to_bytes(&w);
        assert!(
            joinsplit_air::verify_bytes(&c, &pis),
            "CPU hiding proof must verify"
        );
        let g = crate::config::gpu::proof_to_bytes_hiding(
            &JoinSplitAir,
            joinsplit_air::build_trace(&w),
            &pis,
        );
        assert!(
            joinsplit_air::verify_bytes(&g, &pis),
            "GPU hiding proof must verify under production verifier"
        );
        // timing: best-of-N wall clock.
        let runs = 5;
        let (mut cpu_ms, mut gpu_ms) = (f64::MAX, f64::MAX);
        super::prof_reset();
        for _ in 0..runs {
            let t = Instant::now();
            let _ = joinsplit_air::prove_to_bytes(&w);
            cpu_ms = cpu_ms.min(t.elapsed().as_secs_f64() * 1e3);
            let t = Instant::now();
            let _ = crate::config::gpu::proof_to_bytes_hiding(
                &JoinSplitAir,
                joinsplit_air::build_trace(&w),
                &pis,
            );
            gpu_ms = gpu_ms.min(t.elapsed().as_secs_f64() * 1e3);
        }
        let (ntt_ms, ntt_calls, mk_ms, mk_calls) = super::prof_report();
        let (q_ms, q_calls) = super::prof_report_quotient();
        println!("join-split prove, HIDING/production (best of {runs}): CPU {cpu_ms:.1}ms | GPU {gpu_ms:.1}ms  ({:.2}x)", cpu_ms / gpu_ms);
        println!("  GPU work across {runs} runs: NTT {ntt_ms:.0}ms / {ntt_calls} calls, Merkle {mk_ms:.0}ms / {mk_calls} commits, quotient {q_ms:.0}ms / {q_calls} calls (0 = CPU-quotient production path)");
    }
}
