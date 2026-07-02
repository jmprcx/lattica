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

use ocl::ProQue;
use p3_dft::TwoAdicSubgroupDft;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField64, TwoAdicField};
use p3_goldilocks::Goldilocks;
use p3_matrix::bitrev::{BitReversalPerm, BitReversedMatrixView};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::util::reverse_matrix_index_bits;
use p3_matrix::Matrix;
use std::cell::RefCell;
use std::sync::atomic::{AtomicU64, Ordering};

/// Lightweight profiling counters (GPU NTT wall-time + call count), for the benchmark to attribute
/// how much of a proof is spent in the accelerated LDE. Reset/read via `prof_reset`/`prof_report`.
pub static NTT_NANOS: AtomicU64 = AtomicU64::new(0);
pub static NTT_CALLS: AtomicU64 = AtomicU64::new(0);
/// Reset the GPU profiling counters.
pub fn prof_reset() {
    NTT_NANOS.store(0, Ordering::Relaxed);
    NTT_CALLS.store(0, Ordering::Relaxed);
}
/// `(total GPU-NTT milliseconds, number of dft_batch calls)` since the last reset.
pub fn prof_report() -> (f64, u64) {
    (NTT_NANOS.load(Ordering::Relaxed) as f64 / 1e6, NTT_CALLS.load(Ordering::Relaxed))
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
        let (ntt_ms, ntt_calls) = super::prof_report();
        println!("join-split prove (best of {runs}): CPU {cpu_ms:.1}ms | GPU-LDE {gpu_ms:.1}ms  (both verify)");
        println!("  of the GPU run: {ntt_ms:.1}ms in {ntt_calls} GPU-NTT calls (the rest — Merkle/quotient/FRI/glue — is CPU)");
    }
}
