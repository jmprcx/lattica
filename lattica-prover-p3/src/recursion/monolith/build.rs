//! Trace builders for the fused monolith: `HidingWitness` + `monolith_build_trace` (and the live
//! `ft_build_trace` full-transcript filler it consumes, shared with the `lineage` AIRs and tests).

use p3_dft::TwoAdicSubgroupDft;
use p3_field::{Field, PrimeCharacteristicRing, TwoAdicField};
use p3_goldilocks::Goldilocks;
use p3_matrix::bitrev::BitReversibleMatrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::{Dimensions, Matrix};
#[cfg(feature = "stream")]
use rand::RngExt as _;

use crate::poseidon2_air::{native_permute, native_steps, BLOCK, W};
use crate::recursion::native_fri::{Challenge, Val};

use super::*;

/// Fill the full-transcript trace from the recorded per-block input states (each = the 8-lane state going
/// into that block's permute), padding to a power-of-two block count with squeeze (carry) continuation.
#[allow(dead_code)]
pub(crate) fn ft_build_trace(block_inputs: &[[Val; W]]) -> RowMajorMatrix<Val> {
    let n = block_inputs.len();
    let padded = n.next_power_of_two();
    let mut t = vec![Val::ZERO; padded * BLOCK * W];
    let mut last_out = [Val::ZERO; W];
    for b in 0..padded {
        let input = if b < n { block_inputs[b] } else { last_out }; // padding: squeeze (carry prev output)
        let rows = native_steps(input);
        for r in 0..BLOCK {
            let base = (b * BLOCK + r) * W;
            t[base..base + W].copy_from_slice(&rows[r]);
        }
        last_out = native_permute(input);
    }
    RowMajorMatrix::new(t, W)
}

// HIDING (is_zk=1) per-query witness the build consumes on top of `per_query`/`quot_paths`/`commit_data`: the
// leaf SALTS (fresh witness felts appended to each committed-row leaf preimage) and the random-round leaf's path
// (the random commitment is a THIRD input round with no analog in the non-hiding args). The committed rows
// themselves are derived from the reduced-opening terms (px-shared), so only the salts + random path are new.
#[allow(dead_code)]
pub(crate) struct HidingWitness {
    pub trace_salt: [Val; 4],
    pub random_salt: [Val; 4],
    pub random_path: Vec<([Val; 4], bool)>, // input_depth merges (random leaf → random cap)
    pub quot_salts: Vec<[Val; 4]>,          // nqc (one per quotient chunk in the multi-matrix leaf)
    pub commit_salts: Vec<[Val; 4]>,        // cm_rounds (one per commit-phase round)
}

pub(crate) type MonolithQuery = (
    (
        usize,
        Vec<(Challenge, Challenge, Val)>,
        Challenge,
        Challenge,
        Vec<(Challenge, Challenge, bool, Val)>,
    ),
    Val,
    Vec<([Val; 4], bool)>,
);

pub(crate) type CommitRoundData = ([Val; 4], [Val; 4], Vec<([Val; 4], bool)>, [Val; 4]);

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum MonolithTracePart {
    Transcript,
    Query { q: usize },
    Padding,
}

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct MonolithTraceRowRange {
    pub kind: MonolithTracePart,
    pub start_row: usize,
    pub rows: usize,
    pub width: usize,
}

impl MonolithTraceRowRange {
    #[allow(dead_code)]
    pub(crate) fn row_range(&self) -> core::ops::Range<usize> {
        self.start_row..self.start_row + self.rows
    }

    #[allow(dead_code)]
    pub(crate) fn felt_len(&self) -> usize {
        self.rows * self.width
    }

    #[allow(dead_code)]
    pub(crate) fn dimensions(&self) -> Dimensions {
        Dimensions {
            width: self.width,
            height: self.rows,
        }
    }
}

/// Return the row chunks that can be emitted independently by an out-of-core monolith trace
/// source. Query chunks are exactly `air.m_period() x air.fused_w()` and match
/// `monolith_build_query_segment`.
#[allow(dead_code)]
pub(crate) fn monolith_trace_row_ranges(air: &MonolithAir) -> Vec<MonolithTraceRowRange> {
    let width = air.fused_w();
    let tr = air.tr();
    let period = air.m_period();
    let mut ranges = Vec::with_capacity(air.n_queries + 2);
    if tr > 0 {
        ranges.push(MonolithTraceRowRange {
            kind: MonolithTracePart::Transcript,
            start_row: 0,
            rows: tr,
            width,
        });
    }
    for q in 0..air.n_queries {
        ranges.push(MonolithTraceRowRange {
            kind: MonolithTracePart::Query { q },
            start_row: tr + q * period,
            rows: period,
            width,
        });
    }
    let used = tr + air.n_queries * period;
    if used < air.height() {
        ranges.push(MonolithTraceRowRange {
            kind: MonolithTracePart::Padding,
            start_row: used,
            rows: air.height() - used,
            width,
        });
    }
    ranges
}

#[allow(dead_code)]
#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub(crate) struct MonolithTraceSource<'a> {
    air: &'a MonolithAir,
    block_inputs: &'a [[Val; W]],
    per_query: &'a [MonolithQuery],
    alpha_fri: [Val; 2],
    index_felts: &'a [Val],
    quot_paths: &'a [Vec<([Val; 4], bool)>],
    commit_data: &'a [Vec<CommitRoundData>],
    pub_window: &'a [Val],
    hiding: Option<&'a [HidingWitness]>,
}

#[allow(dead_code)]
pub(crate) struct MonolithTraceChunkMatrix {
    range: MonolithTraceRowRange,
    values: Vec<Val>,
}

impl MonolithTraceChunkMatrix {
    #[allow(dead_code)]
    pub(crate) fn range(&self) -> MonolithTraceRowRange {
        self.range
    }
}

impl Matrix<Val> for MonolithTraceChunkMatrix {
    fn width(&self) -> usize {
        self.range.width
    }

    fn height(&self) -> usize {
        self.range.rows
    }

    unsafe fn row_unchecked(
        &self,
        r: usize,
    ) -> impl IntoIterator<Item = Val, IntoIter = impl Iterator<Item = Val> + Send + Sync> {
        let start = r * self.range.width;
        self.values[start..start + self.range.width].to_vec()
    }
}

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct MonolithTraceLdeStripe {
    pub start_col: usize,
    pub width: usize,
    pub height: usize,
}

impl MonolithTraceLdeStripe {
    #[allow(dead_code)]
    pub(crate) fn dimensions(&self) -> Dimensions {
        Dimensions {
            width: self.width,
            height: self.height,
        }
    }
}

/// Stream the monolith trace into bounded column stripes, run P3's exact coset LDE on each stripe,
/// bit-reverse rows the same way `TwoAdicFriPcs::commit` does, and hand the result to `consume`.
///
/// This is the first optimized PCS-boundary adapter: it avoids resident allocation of the full
/// input trace (`height * fused_width`) while preserving byte-for-byte resident PCS LDE output.
/// The emitted LDE stripes are still full height; the next consumer can sink them to an out-of-core
/// row store or a chunk-aware PCS/MMCS layer instead of reconstructing a `RowMajorMatrix`.
#[allow(dead_code)]
pub(crate) fn monolith_trace_coset_lde_stripes<D>(
    source: &MonolithTraceSource<'_>,
    dft: &D,
    added_bits: usize,
    shift: Val,
    max_stripe_width: usize,
    mut consume: impl FnMut(MonolithTraceLdeStripe, RowMajorMatrix<Val>),
) where
    D: TwoAdicSubgroupDft<Val>,
{
    assert!(
        max_stripe_width > 0,
        "monolith LDE stripe width must be non-zero"
    );
    let input_height = source.height();
    let output_height = input_height
        .checked_shl(added_bits.try_into().unwrap())
        .expect("monolith LDE output height overflow");
    let full_width = source.width();

    for start_col in (0..full_width).step_by(max_stripe_width) {
        let stripe_width = core::cmp::min(max_stripe_width, full_width - start_col);
        let mut stripe = vec![Val::ZERO; input_height * stripe_width];

        for range in source.ranges() {
            let mut emitted = vec![Val::ZERO; range.felt_len()];
            source.emit_range(range, &mut emitted);
            for row in 0..range.rows {
                let src = row * range.width + start_col;
                let dst = (range.start_row + row) * stripe_width;
                stripe[dst..dst + stripe_width].copy_from_slice(&emitted[src..src + stripe_width]);
            }
        }

        let lde = dft
            .coset_lde_batch(RowMajorMatrix::new(stripe, stripe_width), added_bits, shift)
            .bit_reverse_rows()
            .to_row_major_matrix();
        assert_eq!(
            lde.width(),
            stripe_width,
            "monolith LDE stripe width mismatch"
        );
        assert_eq!(
            lde.height(),
            output_height,
            "monolith LDE stripe height mismatch"
        );
        consume(
            MonolithTraceLdeStripe {
                start_col,
                width: stripe_width,
                height: output_height,
            },
            lde,
        );
    }
}

#[cfg(feature = "stream")]
#[allow(dead_code)]
pub(crate) fn monolith_trace_coset_lde_store<D>(
    source: &MonolithTraceSource<'_>,
    dft: &D,
    added_bits: usize,
    shift: Val,
    max_stripe_width: usize,
) -> std::io::Result<crate::stream_prove::MmapLdeStore>
where
    D: TwoAdicSubgroupDft<Val>,
{
    let output_height = source
        .height()
        .checked_shl(added_bits.try_into().unwrap())
        .expect("monolith LDE output height overflow");
    let store = crate::stream_prove::MmapLdeStore::new(output_height, source.width())?;
    monolith_trace_coset_lde_stripes(
        source,
        dft,
        added_bits,
        shift,
        max_stripe_width,
        |stripe, lde| {
            store.write_col_tile(stripe.start_col, stripe.width, &lde.values);
        },
    );
    Ok(store)
}

#[cfg(feature = "stream")]
#[allow(dead_code)]
pub(crate) fn monolith_trace_hiding_coset_lde_store<D, R>(
    source: &MonolithTraceSource<'_>,
    dft: &D,
    num_random_codewords: usize,
    added_bits: usize,
    shift: Val,
    max_stripe_width: usize,
    pcs_rng: &mut R,
) -> std::io::Result<crate::stream_prove::MmapLdeStore>
where
    D: TwoAdicSubgroupDft<Val>,
    R: rand::Rng + Send + Sync,
{
    assert!(
        max_stripe_width > 0,
        "monolith hiding LDE stripe width must be non-zero"
    );
    let input_height = source.height();
    let input_width = source.width();
    let random_width = input_width + 2 * num_random_codewords;
    let randomized_width = input_width + num_random_codewords;
    let randomized_height = input_height
        .checked_mul(2)
        .expect("monolith hiding randomized height overflow");
    let output_height = randomized_height
        .checked_shl(added_bits.try_into().unwrap())
        .expect("monolith hiding LDE output height overflow");

    let random_store = crate::stream_prove::MmapLdeStore::new(input_height, random_width)?;
    let mut random_row = vec![Val::ZERO; random_width];
    for row in 0..input_height {
        for value in &mut random_row {
            *value = pcs_rng.random();
        }
        random_store.write_row(row, &random_row);
    }

    let store = crate::stream_prove::MmapLdeStore::new(output_height, randomized_width)?;
    for start_col in (0..randomized_width).step_by(max_stripe_width) {
        let stripe_width = core::cmp::min(max_stripe_width, randomized_width - start_col);
        let mut stripe = vec![Val::ZERO; randomized_height * stripe_width];

        if start_col < input_width {
            let original_cols = core::cmp::min(stripe_width, input_width - start_col);
            for range in source.ranges() {
                let mut emitted = vec![Val::ZERO; range.felt_len()];
                source.emit_range(range, &mut emitted);
                for row in 0..range.rows {
                    let src = row * range.width + start_col;
                    let dst = (2 * (range.start_row + row)) * stripe_width;
                    stripe[dst..dst + original_cols]
                        .copy_from_slice(&emitted[src..src + original_cols]);
                }
            }
        }

        for source_row in 0..input_height {
            crate::stream_prove::LeafSource::fill_row(&random_store, source_row, &mut random_row);
            for local_col in 0..stripe_width {
                let col = start_col + local_col;
                let even_dst = (2 * source_row) * stripe_width + local_col;
                if col >= input_width {
                    stripe[even_dst] = random_row[col - input_width];
                }
                let odd_dst = (2 * source_row + 1) * stripe_width + local_col;
                stripe[odd_dst] = random_row[num_random_codewords + col];
            }
        }

        let lde = dft
            .coset_lde_batch(RowMajorMatrix::new(stripe, stripe_width), added_bits, shift)
            .bit_reverse_rows()
            .to_row_major_matrix();
        assert_eq!(
            lde.width(),
            stripe_width,
            "monolith hiding LDE stripe width mismatch"
        );
        assert_eq!(
            lde.height(),
            output_height,
            "monolith hiding LDE stripe height mismatch"
        );
        store.write_col_tile(start_col, stripe_width, &lde.values);
    }

    Ok(store)
}

#[cfg(feature = "stream")]
#[allow(dead_code)]
pub(crate) fn monolith_trace_hiding_commit<D, R1, R2>(
    source: &MonolithTraceSource<'_>,
    dft: &D,
    num_random_codewords: usize,
    added_bits: usize,
    shift: Val,
    max_stripe_width: usize,
    cap_height: usize,
    pcs_rng: &mut R1,
    mmcs_rng: &mut R2,
) -> std::io::Result<crate::stream_prove::StreamCommitData>
where
    D: TwoAdicSubgroupDft<Val>,
    R1: rand::Rng + Send + Sync,
    R2: rand::Rng,
{
    let store = monolith_trace_hiding_coset_lde_store(
        source,
        dft,
        num_random_codewords,
        added_bits,
        shift,
        max_stripe_width,
        pcs_rng,
    )?;
    Ok(crate::stream_prove::stream_commit_store_hiding(
        store, cap_height, mmcs_rng,
    ))
}

#[allow(dead_code)]
#[allow(clippy::type_complexity)]
impl<'a> MonolithTraceSource<'a> {
    pub(crate) fn new(
        air: &'a MonolithAir,
        block_inputs: &'a [[Val; W]],
        per_query: &'a [MonolithQuery],
        alpha_fri: [Val; 2],
        index_felts: &'a [Val],
        quot_paths: &'a [Vec<([Val; 4], bool)>],
        commit_data: &'a [Vec<CommitRoundData>],
        pub_window: &'a [Val],
        hiding: Option<&'a [HidingWitness]>,
    ) -> Self {
        debug_assert_eq!(per_query.len(), air.n_queries);
        debug_assert!(air.tr() + per_query.len() * air.m_period() <= air.height());
        Self {
            air,
            block_inputs,
            per_query,
            alpha_fri,
            index_felts,
            quot_paths,
            commit_data,
            pub_window,
            hiding,
        }
    }

    pub(crate) fn ranges(&self) -> Vec<MonolithTraceRowRange> {
        monolith_trace_row_ranges(self.air)
    }

    pub(crate) fn width(&self) -> usize {
        self.air.fused_w()
    }

    pub(crate) fn height(&self) -> usize {
        self.air.height()
    }

    pub(crate) fn emit_range(&self, range: MonolithTraceRowRange, out: &mut [Val]) {
        let w = self.width();
        assert_eq!(range.width, w, "monolith range width mismatch");
        assert_eq!(
            out.len(),
            range.felt_len(),
            "monolith range output size mismatch"
        );
        out.fill(Val::ZERO);
        match range.kind {
            MonolithTracePart::Transcript => {
                assert!(
                    range.start_row + range.rows <= self.air.tr(),
                    "transcript range exceeds transcript rows"
                );
                assert!(
                    range.start_row < self.air.tr() || range.rows == 0,
                    "transcript range start out of bounds"
                );
                let n = self.block_inputs.len();
                let padded = n.next_power_of_two();
                let end = range.start_row + range.rows;
                let mut row = 0usize;
                let mut copied = 0usize;
                let mut last_out = [Val::ZERO; W];
                for b in 0..padded {
                    let input = if b < n {
                        self.block_inputs[b]
                    } else {
                        last_out
                    };
                    let rows = native_steps(input);
                    for step_row in rows {
                        if row == end {
                            break;
                        }
                        if row >= range.start_row {
                            let dst = copied * w;
                            out[dst..dst + W].copy_from_slice(&step_row);
                            copied += 1;
                        }
                        row += 1;
                    }
                    last_out = native_permute(input);
                    if row == end {
                        break;
                    }
                }
                debug_assert_eq!(copied, range.rows);
            }
            MonolithTracePart::Query { q } => {
                assert!(q < self.per_query.len(), "query range index out of bounds");
                assert_eq!(
                    range.start_row,
                    self.air.tr() + q * self.air.m_period(),
                    "query range start mismatch"
                );
                assert_eq!(
                    range.rows,
                    self.air.m_period(),
                    "query range row count mismatch"
                );
                fill_monolith_query_segment(
                    self.air,
                    out,
                    q,
                    &self.per_query[q],
                    self.index_felts,
                    self.quot_paths,
                    self.commit_data,
                    self.hiding,
                );
            }
            MonolithTracePart::Padding => {
                let used = self.air.tr() + self.per_query.len() * self.air.m_period();
                assert_eq!(
                    used,
                    self.air.tr() + self.air.n_queries * self.air.m_period(),
                    "padding start mismatch"
                );
                assert!(
                    range.start_row >= used && range.start_row + range.rows <= self.air.height(),
                    "padding range out of bounds"
                );
            }
        }
        fill_monolith_global_columns(self.air, out, self.alpha_fri, self.pub_window);
    }

    pub(crate) fn emit_matrix(&self, range: MonolithTraceRowRange) -> MonolithTraceChunkMatrix {
        let mut values = vec![Val::ZERO; range.felt_len()];
        self.emit_range(range, &mut values);
        MonolithTraceChunkMatrix { range, values }
    }
}

/// Build one complete query super-tile without allocating the transcript prefix or any other query
/// tiles. The returned rows include the global α_fri carrier and column-window constants, so a future
/// out-of-core trace source can splice this segment directly at `air.tr() + q * air.m_period()`.
#[allow(dead_code)]
#[allow(clippy::type_complexity)]
pub(crate) fn monolith_build_query_segment(
    air: &MonolithAir,
    q: usize,
    query: &MonolithQuery,
    alpha_fri: [Val; 2],
    index_felts: &[Val],
    quot_paths: &[Vec<([Val; 4], bool)>],
    commit_data: &[Vec<CommitRoundData>],
    pub_window: &[Val],
    hiding: Option<&[HidingWitness]>,
) -> RowMajorMatrix<Val> {
    let w = air.fused_w();
    let mut segment = vec![Val::ZERO; air.m_period() * w];
    fill_monolith_query_segment(
        air,
        &mut segment,
        q,
        query,
        index_felts,
        quot_paths,
        commit_data,
        hiding,
    );
    fill_monolith_global_columns(air, &mut segment, alpha_fri, pub_window);
    RowMajorMatrix::new(segment, w)
}

#[allow(clippy::type_complexity)]
fn fill_monolith_query_segment(
    air: &MonolithAir,
    t: &mut [Val],
    q: usize,
    query: &MonolithQuery,
    index_felts: &[Val],
    quot_paths: &[Vec<([Val; 4], bool)>],
    commit_data: &[Vec<CommitRoundData>],
    hiding: Option<&[HidingWitness]>,
) {
    use crate::recursion::fri_fold::native_fold;
    use p3_field::{BasedVectorSpace, PrimeField64};

    let c = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
    let w = air.fused_w();
    debug_assert_eq!(t.len(), air.m_period() * w);
    let g = Goldilocks::two_adic_generator(air.lg());
    let n_rounds = air.nb() - 3;
    let ((index, terms, alpha, ro, rounds), _v, path) = query;
    let index = *index;

    let mut e = *ro;
    for r in 0..=air.cm_rounds() {
        let base = r * w;
        let ec = c(e);
        t[base + QT_E] = ec[0];
        t[base + QT_E + 1] = ec[1];
        if r < rounds.len() {
            let (sib, beta, bit, s) = rounds[r];
            let (sc, bc) = (c(sib), c(beta));
            t[base + QT_S] = sc[0];
            t[base + QT_S + 1] = sc[1];
            t[base + QT_B] = bc[0];
            t[base + QT_B + 1] = bc[1];
            t[base + QT_BIT] = if bit { Val::ONE } else { Val::ZERO };
            t[base + QT_SPT] = s;
            t[base + QT_I2S] = (Val::TWO * s).inverse();
            let (e0, e1) = if bit { (sib, e) } else { (e, sib) };
            e = native_fold(e0, e1, beta, s);
        }
    }

    let base0 = 0;
    let mut acc = Val::ONE;
    for i in 0..air.lg() {
        let bit = (index >> i) & 1;
        t[base0 + QT_DBITS + i] = Val::from_u64(bit as u64);
        acc *= if bit == 1 {
            g.exp_power_of_2(air.lg() - 1 - i)
        } else {
            Val::ONE
        };
        t[base0 + air.qt_acc() + i] = acc;
    }
    let x = <Goldilocks as Field>::GENERATOR * acc;
    let ac = c(*alpha);
    t[base0 + air.qt_alpha()] = ac[0];
    t[base0 + air.qt_alpha() + 1] = ac[1];
    let mut apow = Challenge::ONE;
    for (k, &(z, pz, px)) in terms.iter().enumerate() {
        let (zc, pzc) = (c(z), c(pz));
        t[base0 + air.z(k)] = zc[0];
        t[base0 + air.z(k) + 1] = zc[1];
        t[base0 + air.pz(k)] = pzc[0];
        t[base0 + air.pz(k) + 1] = pzc[1];
        t[base0 + air.px(k)] = px;
        let inv = c((z - Challenge::from(x)).inverse());
        t[base0 + air.inv(k)] = inv[0];
        t[base0 + air.inv(k) + 1] = inv[1];
        let ap = c(apow);
        t[base0 + air.apow(k)] = ap[0];
        t[base0 + air.apow(k) + 1] = ap[1];
        apow *= *alpha;
    }

    let felt = index_felts[q];
    let vv = felt.as_canonical_u64();
    t[base0 + air.sb_x()] = felt;
    for i in 0..64 {
        t[base0 + air.sb_b(i)] = Val::from_u64((vv >> i) & 1);
    }
    let mut qq = (vv >> 32) & 1;
    for k in 1..=31 {
        qq &= (vv >> (32 + k)) & 1;
        t[base0 + air.sb_q(k - 1)] = Val::from_u64(qq);
    }
    let mut rem = vv & ((1u64 << air.lg()) - 1);
    for r in 0..=n_rounds {
        t[r * w + air.idx_rem()] = Val::from_u64(rem);
        if r < n_rounds {
            rem >>= 1;
        }
    }

    let merge_block =
        |t: &mut [Val], blk: usize, node: [Val; 4], sib: [Val; 4], b: bool| -> [Val; 4] {
            let mut inp = [Val::ZERO; W];
            if b {
                inp[..4].copy_from_slice(&sib);
                inp[4..].copy_from_slice(&node);
            } else {
                inp[..4].copy_from_slice(&node);
                inp[4..].copy_from_slice(&sib);
            }
            let rows = native_steps(inp);
            for r in 0..BLOCK {
                let base = (blk * BLOCK + r) * w;
                t[base..base + W].copy_from_slice(&rows[r]);
                t[base + air.m_sib()..base + air.m_sib() + 4].copy_from_slice(&sib);
                t[base + air.m_bit()] = if b { Val::ONE } else { Val::ZERO };
            }
            native_permute(inp)[..4].try_into().unwrap()
        };

    let leaf_hash = |t: &mut [Val], start_block: usize, preimage: &[Val]| -> [Val; 4] {
        let mut state = [Val::ZERO; W];
        let nblk = preimage.len().div_ceil(RATE);
        for b in 0..nblk {
            let clen = core::cmp::min(RATE, preimage.len() - b * RATE);
            state[..clen].copy_from_slice(&preimage[b * RATE..b * RATE + clen]);
            let rows = native_steps(state);
            for r in 0..BLOCK {
                let base = ((start_block + b) * BLOCK + r) * w;
                t[base..base + W].copy_from_slice(&rows[r]);
            }
            state = native_permute(state);
        }
        state[..4].try_into().unwrap()
    };

    let hq = hiding.map(|hh| &hh[q]);
    let mut input_preimage: Vec<Val> = (0..air.trm_committed_w())
        .map(|cc| terms[air.trm_trace(cc)].2)
        .collect();
    let mut quot_preimage: Vec<Val> = Vec::new();
    for i in 0..air.nqc() {
        for j in 0..air.trm_chunk_w() {
            quot_preimage.push(terms[air.trm_quot(i, j)].2);
        }
        if air.is_zk == 1 {
            quot_preimage.extend_from_slice(&hq.unwrap().quot_salts[i]);
        }
    }
    let mut random_preimage: Vec<Val> = Vec::new();
    if air.is_zk == 1 {
        let hqv = hq.unwrap();
        input_preimage.extend_from_slice(&hqv.trace_salt);
        random_preimage = (0..air.random_committed_w())
            .map(|cc| terms[cc].2)
            .collect();
        random_preimage.extend_from_slice(&hqv.random_salt);
    }

    let random_cap_entry: [Val; 4] = if air.is_zk == 1 {
        let mut node = leaf_hash(t, M_INPUT_LEAF, &random_preimage);
        let start = M_INPUT_LEAF + air.random_leaf_blocks();
        for (l, &(sib, b)) in hq.unwrap().random_path.iter().enumerate() {
            node = merge_block(t, start + l, node, sib, b);
        }
        node
    } else {
        [Val::ZERO; 4]
    };

    let trace_cap_entry = {
        let mut node = leaf_hash(t, air.m_input_leaf(), &input_preimage);
        let start = air.m_input_leaf() + air.leaf_blocks();
        for (l, &(sib, b)) in path.iter().enumerate() {
            node = merge_block(t, start + l, node, sib, b);
        }
        node
    };
    let quot_cap_entry = {
        let mut node = leaf_hash(t, air.m_quot_leaf(), &quot_preimage);
        let start = air.m_quot_leaf() + air.quot_leaf_blocks();
        for (l, &(sib, b)) in quot_paths[q].iter().enumerate() {
            node = merge_block(t, start + l, node, sib, b);
        }
        node
    };

    let mut commit_cap_entries = vec![[Val::ZERO; 4]; air.cm_rounds()];
    for (r, (group, _leaf, cpath, _cap)) in commit_data[q].iter().enumerate() {
        let mut cpreimage: Vec<Val> = group.to_vec();
        if air.is_zk == 1 {
            cpreimage.extend_from_slice(&hq.unwrap().commit_salts[r]);
        }
        let mut cnode = leaf_hash(t, air.cm_leaf(r), &cpreimage);
        let start = air.cm_leaf(r) + air.cm_leaf_blocks();
        for (l, &(sib, b)) in cpath.iter().enumerate() {
            cnode = merge_block(t, start + l, cnode, sib, b);
        }
        commit_cap_entries[r] = cnode;
    }

    for r in 0..air.m_period() {
        for (cc, &v) in input_preimage.iter().enumerate() {
            t[r * w + air.ov_c(cc)] = v;
        }
        if air.is_zk == 1 {
            for (cc, &v) in random_preimage.iter().enumerate() {
                t[r * w + air.ov_random(cc)] = v;
            }
        }
        for (cc, &qv) in quot_preimage.iter().enumerate() {
            t[r * w + air.qc(cc)] = qv;
        }
        for (cr, (group, _l, _p, _c)) in commit_data[q].iter().enumerate() {
            for k in 0..4 {
                t[r * w + air.cg(cr, k)] = group[k];
            }
        }
        if air.full_cap() {
            for k in 0..4 {
                t[r * w + air.cap_c(k)] = trace_cap_entry[k];
                t[r * w + air.cap_c(4 + k)] = quot_cap_entry[k];
                for cr in 0..air.cm_rounds() {
                    t[r * w + air.cap_c(8 + 4 * cr + k)] = commit_cap_entries[cr][k];
                }
                if air.is_zk == 1 {
                    t[r * w + air.cap_c(8 + 4 * air.cm_rounds() + k)] = random_cap_entry[k];
                }
            }
        }
    }
}

fn fill_monolith_global_columns(
    air: &MonolithAir,
    t: &mut [Val],
    alpha_fri: [Val; 2],
    pub_window: &[Val],
) {
    let w = air.fused_w();
    debug_assert_eq!(t.len() % w, 0);
    for row in t.chunks_exact_mut(w) {
        row[air.carry()] = alpha_fri[0];
        row[air.carry() + 1] = alpha_fri[1];
    }
    if air.column_window {
        use p3_field::BasedVectorSpace;
        let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
        let zeta = Challenge::from_basis_coefficients_fn(|k| pub_window[2 + k]);
        let mut sch_vals = vec![[Val::ZERO; 2]; air.cm_rounds()];
        let mut s = zeta;
        for sv in sch_vals.iter_mut() {
            s = s * s;
            *sv = cc(s);
        }
        let mut window = Vec::with_capacity(pub_window.len() + 2 * sch_vals.len());
        window.extend_from_slice(pub_window);
        for sv in &sch_vals {
            window.extend_from_slice(sv);
        }
        let start = air.pw(0);
        for row in t.chunks_exact_mut(w) {
            row[start..start + window.len()].copy_from_slice(&window);
        }
    }
}

#[allow(dead_code)]
#[allow(clippy::type_complexity)]
pub(crate) fn monolith_build_trace(
    air: &MonolithAir,
    block_inputs: &[[Val; W]],
    per_query: &[MonolithQuery],
    alpha_fri: [Val; 2],
    index_felts: &[Val],
    quot_paths: &[Vec<([Val; 4], bool)>],
    commit_data: &[Vec<CommitRoundData>],
    pub_window: &[Val], // column-window mode: inner-proof pis values (empty otherwise)
    hiding: Option<&[HidingWitness]>, // is_zk=1 only: per-query salts + random-round path (None is_zk=0)
) -> RowMajorMatrix<Val> {
    let source = MonolithTraceSource::new(
        air,
        block_inputs,
        per_query,
        alpha_fri,
        index_felts,
        quot_paths,
        commit_data,
        pub_window,
        hiding,
    );
    let w = source.width();
    let mut t = vec![Val::ZERO; source.height() * w];
    for range in source.ranges() {
        let start = range.start_row * w;
        let end = start + range.felt_len();
        source.emit_range(range, &mut t[start..end]);
    }
    RowMajorMatrix::new(t, w)
}
