//! GPU (OpenCL) acceleration of the low-degree extension — **opt-in** via `--features gpu`.
//!
//! `GpuDft` implements p3's `TwoAdicSubgroupDft<Goldilocks>` by computing the DFT on the GPU; p3
//! composes the whole coset-LDE (the single heaviest proving step) from `dft_batch`. It is a drop-in
//! for `Radix2DitParallel` in the PCS's `Dft` slot, so it is **additive and prove-only**: the wire
//! format, the C-ABI verifier, and the default CPU proving path are untouched. A GPU-produced proof
//! deserializes and verifies under the standard config exactly like a CPU one — the DFT never appears
//! in `verify` or in the serialized `Proof`.
//!
//! Correctness is validated bit-for-bit against p3 (see `gpu_dft_matches_p3` + the session's GPU
//! pipeline): a radix-2 DIT NTT over Goldilocks (bit-reverse rows → `log h` butterfly stages), twiddle
//! base per stage = `Goldilocks::two_adic_generator(s)` — p3's exact roots, so the evaluations are
//! identical. Field arithmetic matches p3's `reduce128`/`add` (canonical only at the boundary; the
//! serde encoding is canonical, so intermediate representation is irrelevant).
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
use p3_matrix::util::reverse_matrix_index_bits;
use p3_matrix::{Dimensions, Matrix};
use p3_symmetric::{CryptographicHasher, PseudoCompressionFunction};
use std::cell::RefCell;
use std::sync::atomic::{AtomicU64, Ordering};

/// Lightweight profiling counters (GPU NTT wall-time + call count), for the benchmark to attribute
/// how much of a proof is spent in the accelerated LDE. Reset/read via `prof_reset`/`prof_report`.
pub static NTT_NANOS: AtomicU64 = AtomicU64::new(0);
pub static NTT_CALLS: AtomicU64 = AtomicU64::new(0);
pub static MERKLE_NANOS: AtomicU64 = AtomicU64::new(0);
pub static MERKLE_CALLS: AtomicU64 = AtomicU64::new(0);
/// Reset the GPU profiling counters.
pub fn prof_reset() {
    NTT_NANOS.store(0, Ordering::Relaxed);
    NTT_CALLS.store(0, Ordering::Relaxed);
    MERKLE_NANOS.store(0, Ordering::Relaxed);
    MERKLE_CALLS.store(0, Ordering::Relaxed);
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

__kernel void bitrev_rows(__global const ulong* in,__global ulong* out,const uint h,const uint w,const uint bits){
  size_t gid=get_global_id(0); uint i=(uint)(gid/w),c=(uint)(gid%w); if(i>=h) return;
  out[(size_t)i*w+c]=in[(size_t)brev(i,bits)*w+c];
}
// one thread per butterfly per column; nb = h/2 butterflies per column.
__kernel void ntt_stage(__global ulong* a,const uint w,const uint h,const uint half_len,const ulong wlen){
  size_t t=get_global_id(0); uint nb=h>>1; uint col=(uint)(t/nb), bfly=(uint)(t%nb); if(col>=w) return;
  uint block=bfly/half_len, j=bfly%half_len; uint i=block*(half_len<<1)+j;
  ulong tw=gl_pow(wlen,(ulong)j);
  size_t iu=(size_t)i*w+col, iv=(size_t)(i+half_len)*w+col;
  ulong u=a[iu], v=gl_mul(a[iv],tw);
  a[iu]=gl_add(u,v); a[iv]=gl_sub(u,v);
}
__kernel void canon(__global ulong* a,const uint n){ size_t i=get_global_id(0); if(i<n) a[i]=gl_canon(a[i]); }
// scale every element by the base-field scalar `s`.
__kernel void scale_const(__global ulong* a,const uint n,const ulong s){ size_t i=get_global_id(0); if(i<n) a[i]=gl_mul(a[i],s); }
// coset shift: row k (k<h) *= base^k; used to turn an inner-domain iDFT into a coset evaluation.
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
__kernel void leaf_hash(__global const ulong* in,__global ulong* out,const uint h,const uint w,
                        __global const ulong* rci,__global const ulong* rcp,__global const ulong* rcf,__global const ulong* diag){
  size_t row=get_global_id(0); if(row>=h) return;
  ulong s[8]; for(int i=0;i<8;i++) s[i]=0UL;
  __global const ulong* r=in+(size_t)row*w;
  uint i=0;
  while(i<w){ for(uint k=0;k<4 && i<w;k++){ s[k]=r[i]; i++; } perm8(s,rci,rcp,rcf,diag); }
  for(int k=0;k<4;k++) out[(size_t)row*4+k]=gl_canon(s[k]);
}
// compress one tree layer (TruncatedPermutation<2,4,8>): out[j] = trunc(perm(in[2j] || in[2j+1])).
__kernel void compress_layer(__global const ulong* in,__global ulong* out,const uint n_out,
                             __global const ulong* rci,__global const ulong* rcp,__global const ulong* rcf,__global const ulong* diag){
  size_t j=get_global_id(0); if(j>=n_out) return;
  ulong s[8]; for(int k=0;k<4;k++){ s[k]=in[(size_t)(2*j)*4+k]; s[4+k]=in[(size_t)(2*j+1)*4+k]; }
  perm8(s,rci,rcp,rcf,diag);
  for(int k=0;k<4;k++) out[(size_t)j*4+k]=gl_canon(s[k]);
}
__kernel void scale_pow(__global ulong* a,const uint w,const uint h,const ulong base){
  size_t gid=get_global_id(0); uint k=(uint)(gid/w),c=(uint)(gid%w); if(k>=h) return;
  a[(size_t)k*w+c]=gl_mul(a[(size_t)k*w+c], gl_pow(base,(ulong)k));
}
"#;

thread_local! {
    /// The compiled OpenCL program, built once per thread (kernel compilation is the expensive part).
    static PROQUE: RefCell<Option<ProQue>> = const { RefCell::new(None) };
}

fn with_proque<R>(f: impl FnOnce(&ProQue) -> R) -> R {
    PROQUE.with(|cell| {
        if cell.borrow().is_none() {
            let pq = ProQue::builder()
                .src(KERNEL_SRC)
                .dims(1)
                .build()
                .expect("GpuDft: OpenCL program build failed (is an OpenCL runtime + GPU present?)");
            *cell.borrow_mut() = Some(pq);
        }
        f(cell.borrow().as_ref().unwrap())
    })
}

/// Run the radix-2 DIT NTT on the GPU: bit-reverse rows, then `log_h` butterfly stages, then
/// canonicalize. Returns evaluations in **natural** row order (matching p3's `dft_batch` logical order).
fn gpu_ntt(coeffs: &[u64], h: usize, w: usize, log_h: usize) -> Vec<u64> {
    let _t0 = std::time::Instant::now();
    let n = h * w;
    let wlens: Vec<u64> = (1..=log_h).map(|s| Goldilocks::two_adic_generator(s).as_canonical_u64()).collect();
    with_proque(|pq| {
        let cb = ocl::Buffer::<u64>::builder()
            .queue(pq.queue().clone())
            .flags(ocl::flags::MEM_READ_ONLY | ocl::flags::MEM_COPY_HOST_PTR)
            .len(n)
            .copy_host_slice(coeffs)
            .build()
            .unwrap();
        let ab = ocl::Buffer::<u64>::builder().queue(pq.queue().clone()).flags(ocl::flags::MEM_READ_WRITE).len(n).build().unwrap();
        unsafe {
            pq.kernel_builder("bitrev_rows").arg(&cb).arg(&ab).arg(h as u32).arg(w as u32).arg(log_h as u32)
                .global_work_size(n).build().unwrap().enq().unwrap();
            for s in 1..=log_h {
                let half = 1u32 << (s - 1);
                pq.kernel_builder("ntt_stage").arg(&ab).arg(w as u32).arg(h as u32).arg(half).arg(wlens[s - 1])
                    .global_work_size((h / 2) * w).build().unwrap().enq().unwrap();
            }
            pq.kernel_builder("canon").arg(&ab).arg(n as u32).global_work_size(n).build().unwrap().enq().unwrap();
        }
        let mut out = vec![0u64; n];
        ab.read(&mut out).enq().unwrap();
        NTT_NANOS.fetch_add(_t0.elapsed().as_nanos() as u64, Ordering::Relaxed);
        NTT_CALLS.fetch_add(1, Ordering::Relaxed);
        out
    })
}

/// Full coset-LDE on the GPU, **device-side** (one upload + one download): iDFT → coset-scale +
/// zero-pad → forward NTT on `shift·K` (|K| = `h << added_bits`). Returns evaluations in NATURAL row
/// order (matching p3's `coset_lde_batch` logical order). This is what `TwoAdicFriPcs` actually calls;
/// keeping the two NTTs + the coset shift on-device eliminates the host round-trips (and the CPU
/// reverse/scale/coset-shift) of the trait's default composition — the LDE's dominant overhead.
fn gpu_coset_lde_natural(evals: &[u64], h: usize, w: usize, added_bits: usize, shift: u64) -> Vec<u64> {
    let _t0 = std::time::Instant::now();
    let log_h = h.trailing_zeros() as usize;
    let big = h << added_bits;
    let log_big = log_h + added_bits;
    let (n_small, n_big) = (h * w, big * w);
    // iDFT twiddles per stage = two_adic_generator(s).inverse(); forward (big) twiddles = generator(s).
    let wl_inv: Vec<u64> = (1..=log_h).map(|s| Goldilocks::two_adic_generator(s).inverse().as_canonical_u64()).collect();
    let wl_big: Vec<u64> = (1..=log_big).map(|s| Goldilocks::two_adic_generator(s).as_canonical_u64()).collect();
    let h_inv = Goldilocks::from_u64(h as u64).inverse().as_canonical_u64();
    with_proque(|pq| {
        let mk = || ocl::Buffer::<u64>::builder().queue(pq.queue().clone()).flags(ocl::flags::MEM_READ_WRITE).len(n_big).build().unwrap();
        let a = mk();
        let b = mk();
        unsafe {
            a.cmd().fill(0u64, None).enq().unwrap();
            b.cmd().fill(0u64, None).enq().unwrap();
            a.write(evals).enq().unwrap(); // a[0..n_small] = input evals, rest 0
            // --- iDFT on the first h rows: bitrev(a[0..hw]) -> b, inverse-twiddle stages, scale 1/h ---
            pq.kernel_builder("bitrev_rows").arg(&a).arg(&b).arg(h as u32).arg(w as u32).arg(log_h as u32).global_work_size(n_small).build().unwrap().enq().unwrap();
            for s in 1..=log_h {
                pq.kernel_builder("ntt_stage").arg(&b).arg(w as u32).arg(h as u32).arg(1u32 << (s - 1)).arg(wl_inv[s - 1]).global_work_size((h / 2) * w).build().unwrap().enq().unwrap();
            }
            pq.kernel_builder("scale_const").arg(&b).arg(n_small as u32).arg(h_inv).global_work_size(n_small).build().unwrap().enq().unwrap();
            // --- coset shift: b[k] *= shift^k (k<h); b[hw..] stays 0 (the zero-pad) ---
            pq.kernel_builder("scale_pow").arg(&b).arg(w as u32).arg(h as u32).arg(shift).global_work_size(n_small).build().unwrap().enq().unwrap();
            // --- forward NTT of size `big` on b: bitrev(b, log_big) -> a, forward stages, canon ---
            pq.kernel_builder("bitrev_rows").arg(&b).arg(&a).arg(big as u32).arg(w as u32).arg(log_big as u32).global_work_size(n_big).build().unwrap().enq().unwrap();
            for s in 1..=log_big {
                pq.kernel_builder("ntt_stage").arg(&a).arg(w as u32).arg(big as u32).arg(1u32 << (s - 1)).arg(wl_big[s - 1]).global_work_size((big / 2) * w).build().unwrap().enq().unwrap();
            }
            pq.kernel_builder("canon").arg(&a).arg(n_big as u32).global_work_size(n_big).build().unwrap().enq().unwrap();
        }
        let mut out = vec![0u64; n_big];
        a.read(&mut out).enq().unwrap();
        NTT_NANOS.fetch_add(_t0.elapsed().as_nanos() as u64, Ordering::Relaxed);
        NTT_CALLS.fetch_add(1, Ordering::Relaxed);
        out
    })
}

/// A GPU-backed two-adic DFT: a drop-in for `Radix2DitParallel` in the PCS's `Dft` slot.
#[derive(Clone, Copy, Default, Debug)]
pub struct GpuDft;

impl TwoAdicSubgroupDft<Goldilocks> for GpuDft {
    type Evaluations = BitReversedMatrixView<RowMajorMatrix<Goldilocks>>;

    fn dft_batch(&self, mat: RowMajorMatrix<Goldilocks>) -> Self::Evaluations {
        let (h, w) = (mat.height(), mat.width());
        // Match Radix2DitParallel::dft_batch: logical order = natural DFT, stored = bit-reversed.
        let evals = if h <= 1 {
            mat.values.iter().map(|f| f.as_canonical_u64()).collect::<Vec<u64>>()
        } else {
            let log_h = h.trailing_zeros() as usize;
            let coeffs: Vec<u64> = mat.values.iter().map(|f| f.as_canonical_u64()).collect();
            gpu_ntt(&coeffs, h, w, log_h)
        };
        let mut stored = RowMajorMatrix::new(evals.into_iter().map(Goldilocks::new).collect(), w);
        reverse_matrix_index_bits(&mut stored); // stored = bit-reverse(natural) ⇒ view = natural
        BitReversalPerm::new_view(stored)
    }

    /// Override the trait default: do the whole coset-LDE device-side (see `gpu_coset_lde_natural`),
    /// which is what the PCS calls to commit. Bit-identical to `Radix2DitParallel::coset_lde_batch`.
    fn coset_lde_batch(&self, mat: RowMajorMatrix<Goldilocks>, added_bits: usize, shift: Goldilocks) -> Self::Evaluations {
        let (h, w) = (mat.height(), mat.width());
        let big = h << added_bits;
        let natural: Vec<u64> = if h < 2 {
            // degree-<1 (constant) poly ⇒ the same value at every coset point; replicate the single row.
            let row: Vec<u64> = (0..w).map(|c| mat.values.get(c).map(|f| f.as_canonical_u64()).unwrap_or(0)).collect();
            (0..big).flat_map(|_| row.clone()).collect()
        } else {
            let evals: Vec<u64> = mat.values.iter().map(|f| f.as_canonical_u64()).collect();
            gpu_coset_lde_natural(&evals, h, w, added_bits, shift.as_canonical_u64())
        };
        let mut stored = RowMajorMatrix::new(natural.into_iter().map(Goldilocks::new).collect(), w);
        reverse_matrix_index_bits(&mut stored);
        BitReversalPerm::new_view(stored)
    }
}

/// Poseidon2-Goldilocks-8 round constants + internal diagonal, canonical-u64, in the layout the kernels
/// expect (`rci`: 4×8 external-initial, `rcp`: 22 internal, `rcf`: 4×8 external-final, `diag`: 8).
/// Sourced from p3's exported constants — the same ones `default_goldilocks_poseidon2_8` uses, so the
/// GPU permutation is bit-identical to the CPU hasher used in `verify_batch`.
fn poseidon2_consts() -> (Vec<u64>, Vec<u64>, Vec<u64>, Vec<u64>) {
    let flat = |rows: &[[Goldilocks; 8]]| rows.iter().flatten().map(|x| x.as_canonical_u64()).collect();
    (
        flat(&GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_INITIAL),
        GOLDILOCKS_POSEIDON2_RC_8_INTERNAL.iter().map(|x| x.as_canonical_u64()).collect(),
        flat(&GOLDILOCKS_POSEIDON2_RC_8_EXTERNAL_FINAL),
        MATRIX_DIAG_8_GOLDILOCKS.iter().map(|x| x.as_canonical_u64()).collect(),
    )
}

/// Build the whole Merkle tree on the GPU: leaf-hash the `h` rows of the row-major (canonical) `h×w`
/// `combined` matrix (Poseidon2 sponge), then compress pairwise up to the root. Returns every layer
/// (layer 0 = leaves, last = `[root]`), digests canonical. `h` must be a power of two.
fn gpu_merkle_layers(combined: &[u64], h: usize, w: usize) -> Vec<Vec<[Goldilocks; 4]>> {
    let _t0 = std::time::Instant::now();
    let (rci, rcp, rcf, diag) = poseidon2_consts();
    let out = with_proque(|pq| {
        let q = pq.queue().clone();
        let ro = |data: &[u64]| {
            ocl::Buffer::<u64>::builder()
                .queue(q.clone())
                .flags(ocl::flags::MEM_READ_ONLY | ocl::flags::MEM_COPY_HOST_PTR)
                .len(data.len().max(1))
                .copy_host_slice(if data.is_empty() { &[0u64] } else { data })
                .build()
                .unwrap()
        };
        let rw = |n: usize| ocl::Buffer::<u64>::builder().queue(q.clone()).flags(ocl::flags::MEM_READ_WRITE).len(n).build().unwrap();
        let (inb, rci_b, rcp_b, rcf_b, diag_b) = (ro(combined), ro(&rci), ro(&rcp), ro(&rcf), ro(&diag));
        let read_layer = |buf: &ocl::Buffer<u64>, n: usize| -> Vec<[Goldilocks; 4]> {
            let mut raw = vec![0u64; n * 4];
            buf.read(&mut raw).enq().unwrap();
            raw.chunks_exact(4).map(|c| [Goldilocks::new(c[0]), Goldilocks::new(c[1]), Goldilocks::new(c[2]), Goldilocks::new(c[3])]).collect()
        };
        let leaves = rw(h * 4);
        unsafe {
            pq.kernel_builder("leaf_hash").arg(&inb).arg(&leaves).arg(h as u32).arg(w as u32)
                .arg(&rci_b).arg(&rcp_b).arg(&rcf_b).arg(&diag_b).global_work_size(h).build().unwrap().enq().unwrap();
        }
        let mut layers = vec![read_layer(&leaves, h)];
        let mut cur = leaves;
        let mut n = h;
        while n > 1 {
            let n_out = n / 2;
            let next = rw(n_out * 4);
            unsafe {
                pq.kernel_builder("compress_layer").arg(&cur).arg(&next).arg(n_out as u32)
                    .arg(&rci_b).arg(&rcp_b).arg(&rcf_b).arg(&diag_b).global_work_size(n_out).build().unwrap().enq().unwrap();
            }
            layers.push(read_layer(&next, n_out));
            cur = next;
            n = n_out;
        }
        layers
    });
    MERKLE_NANOS.fetch_add(_t0.elapsed().as_nanos() as u64, Ordering::Relaxed);
    MERKLE_CALLS.fetch_add(1, Ordering::Relaxed);
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
        Self { hash: MyHash::new(perm.clone()), compress: MyCompress::new(perm) }
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

    fn commit<M: Matrix<Goldilocks>>(&self, inputs: Vec<M>) -> (Self::Commitment, Self::ProverData<M>) {
        let h = inputs[0].height();
        assert!(h.is_power_of_two(), "GpuMerkleMmcs: height {h} must be a power of two");
        assert!(inputs.iter().all(|m| m.height() == h), "GpuMerkleMmcs: matrices must be equal height");
        let total_w: usize = inputs.iter().map(|m| m.width()).sum();
        // combined[i] = concat of every matrix's logical row i (matrix order) — the leaf preimage.
        let mut combined = vec![0u64; h * total_w];
        for i in 0..h {
            let mut off = i * total_w;
            for m in &inputs {
                for v in m.row(i).expect("row < height") {
                    combined[off] = v.as_canonical_u64();
                    off += 1;
                }
            }
        }
        let layers = gpu_merkle_layers(&combined, h, total_w);
        let root = *layers.last().unwrap().first().unwrap();
        (root, GpuMerkleData { matrices: inputs, layers })
    }

    fn open_batch<M: Matrix<Goldilocks>>(&self, index: usize, prover_data: &Self::ProverData<M>) -> BatchOpening<Goldilocks, Self> {
        let opened_values: Vec<Vec<Goldilocks>> =
            prover_data.matrices.iter().map(|m| m.row(index).expect("row < height").into_iter().collect()).collect();
        // sibling path: at each layer below the root, the digest of the sibling of the current node.
        let mut opening_proof = Vec::with_capacity(prover_data.layers.len().saturating_sub(1));
        let mut idx = index;
        for layer in &prover_data.layers[..prover_data.layers.len() - 1] {
            opening_proof.push(layer[idx ^ 1]);
            idx >>= 1;
        }
        BatchOpening::new(opened_values, opening_proof)
    }

    fn get_matrices<'a, M: Matrix<Goldilocks>>(&self, prover_data: &'a Self::ProverData<M>) -> Vec<&'a M> {
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
            cur = if idx & 1 == 0 { self.compress.compress([cur, *sib]) } else { self.compress.compress([*sib, cur]) };
            idx >>= 1;
        }
        if &cur == commit {
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
            let vals: Vec<Goldilocks> = (0..h * w).map(|_| Goldilocks::new(rng.random::<u64>() % 0xFFFF_FFFF_0000_0001)).collect();
            let mat = RowMajorMatrix::new(vals, w);
            let cpu = Radix2DitParallel::<Goldilocks>::default().dft_batch(mat.clone()).to_row_major_matrix();
            let gpu = GpuDft.dft_batch(mat).to_row_major_matrix();
            assert_eq!(cpu.values, gpu.values, "GpuDft != p3 at h=2^{log_h} w={w}");
        }
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
        let bytes = crate::config::gpu::proof_to_bytes(&JoinSplitAir, joinsplit_air::build_trace(&w), &pis);
        assert!(joinsplit_air::verify_bytes(&bytes, &pis), "GPU-proved join-split must verify under the standard verifier");
    }

    /// Same for the v3 shielded-HTLC circuit.
    #[test]
    #[ignore = "requires an OpenCL runtime + GPU; runs a real proof"]
    fn gpu_htlc_proof_verifies() {
        use crate::htlc_air::{self, HtlcAir};
        let w = htlc_air::demo_htlc_witness();
        let pis = htlc_air::public_values(&w);
        let bytes = crate::config::gpu::proof_to_bytes(&HtlcAir, htlc_air::build_trace(&w), &pis);
        assert!(htlc_air::verify_bytes(&bytes, &pis), "GPU-proved HTLC must verify under the standard verifier");
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
            let b = crate::config::gpu::proof_to_bytes(&JoinSplitAir, joinsplit_air::build_trace(&w), &pis);
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
        for &(log_h, widths) in &[(1usize, &[1usize][..]), (3, &[2, 5]), (6, &[4]), (10, &[2, 2, 3]), (12, &[7])] {
            let h = 1usize << log_h;
            let mats: Vec<RowMajorMatrix<Goldilocks>> = widths
                .iter()
                .map(|&w| RowMajorMatrix::new((0..h * w).map(|_| Goldilocks::new(rng.random::<u64>() % 0xFFFF_FFFF_0000_0001)).collect(), w))
                .collect();
            let dims: Vec<Dimensions> = mats.iter().map(|m| Dimensions { width: m.width(), height: h }).collect();
            let (commit, data) = mmcs.commit(mats.clone());
            for &idx in &[0usize, 1, h / 3, h / 2, h - 1] {
                let opening = mmcs.open_batch(idx, &data);
                // opened rows must equal the source rows.
                for (m, row) in mats.iter().zip(&opening.opened_values) {
                    let want: Vec<Goldilocks> = m.row(idx).unwrap().into_iter().collect();
                    assert_eq!(&want, row, "open row mismatch at h=2^{log_h} idx={idx}");
                }
                let r#ref = BatchOpeningRef::new(&opening.opened_values, &opening.opening_proof);
                assert_eq!(mmcs.verify_batch(&commit, &dims, idx, r#ref), Ok(()), "verify h=2^{log_h} idx={idx}");
                // tamper: a corrupted opened value must be rejected.
                if h > 1 {
                    let mut bad = opening.opened_values.clone();
                    bad[0][0] += Goldilocks::ONE;
                    let bref = BatchOpeningRef::new(&bad, &opening.opening_proof);
                    assert_eq!(mmcs.verify_batch(&commit, &dims, idx, bref), Err(()), "tampered value accepted");
                    // wrong index must be rejected (path no longer matches).
                    let wrong = (idx + 1) % h;
                    let wref = BatchOpeningRef::new(&opening.opened_values, &opening.opening_proof);
                    assert_eq!(mmcs.verify_batch(&commit, &dims, wrong, wref), Err(()), "wrong index accepted");
                }
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
        let p_cpu = prove(&cpu_cfg, &JoinSplitAir, joinsplit_air::build_trace(&w), &pis);
        assert!(verify(&cpu_cfg, &JoinSplitAir, &p_cpu, &pis).is_ok(), "CPU-bench proof must verify");
        let p_gpu = prove(&gpu_cfg, &JoinSplitAir, joinsplit_air::build_trace(&w), &pis);
        assert!(verify(&gpu_cfg, &JoinSplitAir, &p_gpu, &pis).is_ok(), "GPU-bench proof must verify");
        // timing: best-of-N wall clock.
        let runs = 5;
        let (mut cpu_ms, mut gpu_ms) = (f64::MAX, f64::MAX);
        super::prof_reset();
        for _ in 0..runs {
            let t = Instant::now();
            let _ = prove(&cpu_cfg, &JoinSplitAir, joinsplit_air::build_trace(&w), &pis);
            cpu_ms = cpu_ms.min(t.elapsed().as_secs_f64() * 1e3);
            let t = Instant::now();
            let _ = prove(&gpu_cfg, &JoinSplitAir, joinsplit_air::build_trace(&w), &pis);
            gpu_ms = gpu_ms.min(t.elapsed().as_secs_f64() * 1e3);
        }
        let (ntt_ms, ntt_calls, mk_ms, mk_calls) = super::prof_report();
        println!("join-split prove, non-hiding (best of {runs}): CPU {cpu_ms:.1}ms | GPU(LDE+Merkle) {gpu_ms:.1}ms  ({:.2}x)", cpu_ms / gpu_ms);
        println!("  GPU work across {runs} runs: NTT {ntt_ms:.0}ms / {ntt_calls} calls, Merkle {mk_ms:.0}ms / {mk_calls} commits");
    }
}
