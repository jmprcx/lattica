//! Phase 3 of the streaming-prover plan: an in-crate, prove-only fork that streams the commit so the
//! wide LDE leaves never all reside in RAM at once — the structural RAM win that the Phase 2 mmap
//! allocator could not deliver (the OS cannot stream p3's whole-buffer re-touch pattern from below the
//! `Vec` types; see `spill_alloc`). `verify` and every wire type stay upstream: this fork PRODUCES p3's
//! `Proof<MyConfig>` bytes, it never redefines them.
//!
//! Generalizes the proven `quotient_gpu::prove_gpu` fork (already byte-identical to `p3_uni_stark::prove`)
//! by pushing control BELOW the `Pcs` seam — into the Merkle commit and (later) the FRI open — which is
//! where the residency actually lives.
//!
//! ## This increment — the streaming (frontier) Merkle commit
//! The first, risk-retiring piece (the plan sequences it first, validated standalone before wiring): a
//! Merkle commitment that hashes leaf rows ONE AT A TIME from a streaming source, keeping only the
//! digest layers (`h × DIGEST` fields — tens of MiB) instead of the whole `h × w` leaf matrix (the
//! multi-GB buffer). It is BYTE-IDENTICAL to p3's `MerkleTreeMmcs` commitment for a single power-of-two
//! -height matrix: p3's SIMD `vertically_packed_row` hashing is just lanes of the same per-row digest,
//! and `padded_len(h, 2) == h` for a power-of-two height, so scalar per-row hashing + pairwise compress
//! reproduces p3's exact layers. Pinned by `stream_merkle_matches_p3`.
//!
//! Feature-gated (`stream`, off by default) — RESEARCH, not on any production path.

use crate::config::{Challenge, ChallengeMmcs, Challenger, Dft, MyCompress, MyHash, Val, ValMmcs};
use core::marker::PhantomData;
use p3_challenger::{CanObserve, CanSampleBits, FieldChallenger, GrindingChallenger};
use p3_commit::{BatchOpening, Mmcs};
use p3_dft::{Radix2DFTSmallBatch, TwoAdicSubgroupDft};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use p3_fri::{
    compute_log_arity_for_round, CommitPhaseProofStep, FriFoldingStrategy, FriParameters, FriProof,
    ProverDataWithOpeningPoints, QueryProof, TwoAdicFriFolding, TwoAdicFriFoldingForMmcs,
};
use p3_goldilocks::default_goldilocks_poseidon2_8;
use p3_matrix::bitrev::BitReversibleMatrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleCap;
use p3_symmetric::{CryptographicHasher, PseudoCompressionFunction};
use p3_util::{log2_strict_usize, reverse_slice_index_bits};
use std::ffi::CString;
use std::mem::size_of;
use std::sync::atomic::{AtomicU64, Ordering};

/// Poseidon2 digest width (Goldilocks-8 sponge squeezes 4).
pub const DIGEST: usize = 4;

/// Salt columns appended to each leaf row in the production HIDING commit (`MerkleTreeHidingMmcs<…,4>`).
pub const SALT_ELEMS: usize = 4;

/// A source of `h` leaf rows of width `w`, addressable one row at a time — the seam the streaming store
/// plugs into. `fill_row(i, buf)` writes row `i` (a `w`-wide slice) so the Merkle commit never holds the
/// whole `h × w` leaf matrix; a later increment backs this by an mmap'd, column-tiled LDE store.
pub trait LeafSource: Sync {
    fn height(&self) -> usize;
    fn width(&self) -> usize;
    fn fill_row(&self, row: usize, out: &mut [Val]);
    /// Fill `nr` consecutive rows starting at `r0` into `out` (row-major `nr × width`). The frontier
    /// Merkle reads through THIS (in row-blocks), so a COLUMN-MAJOR store can override it to read `width`
    /// contiguous column-segments — `width` interleaved sequential streams, ~one pass — instead of the
    /// strided per-row gather. The default is the row-major per-row fill.
    fn fill_row_block(&self, r0: usize, nr: usize, out: &mut [Val]) {
        let w = self.width();
        for i in 0..nr {
            self.fill_row(r0 + i, &mut out[i * w..(i + 1) * w]);
        }
    }
}

/// A `LeafSource` over an already-materialized row-major matrix — the Vec-backed store used to pin the
/// streaming Merkle byte-identical before the mmap store exists.
pub struct SliceLeaves<'a> {
    pub vals: &'a [Val],
    pub h: usize,
    pub w: usize,
}

impl LeafSource for SliceLeaves<'_> {
    fn height(&self) -> usize {
        self.h
    }
    fn width(&self) -> usize {
        self.w
    }
    fn fill_row(&self, row: usize, out: &mut [Val]) {
        out.copy_from_slice(&self.vals[row * self.w..(row + 1) * self.w]);
    }
}

/// Streaming Merkle commitment of `src` (single matrix, power-of-two height): hash each leaf row on the
/// fly (only one row + the digest layers ever reside), then compress pairwise up to the `cap_height` cap.
/// Returns the cap digests — byte-identical to `MerkleTreeMmcs::commit(vec![matrix]).0` under the same
/// `MyHash`/`MyCompress`/`CAP_HEIGHT`. This is the frontier build that keeps the wide leaves off the heap.
pub fn stream_merkle_cap<S: LeafSource>(src: &S, cap_height: usize) -> Vec<[Val; DIGEST]> {
    stream_merkle_cap_inner(src, cap_height, None)
}

/// Streaming HIDING Merkle commitment — byte-identical to the PRODUCTION `MerkleTreeHidingMmcs::commit`.
/// Draws the whole `h × SALT_ELEMS` salt matrix up-front from `rng` (exactly p3's `RowMajorMatrix::rand`,
/// same row-major order — the byte-compat rule: draw all salts whole-matrix, up-front, in p3's order),
/// then hashes each leaf as `[row | salt]` (p3's `HorizontalPair`) while streaming the wide rows from
/// `src`. The salt matrix (`h × 4`) is small and resident; the leaves are not.
pub fn stream_merkle_cap_hiding<S, R>(src: &S, cap_height: usize, rng: &mut R) -> Vec<[Val; DIGEST]>
where
    S: LeafSource,
    R: rand::Rng,
{
    let salts = RowMajorMatrix::rand(rng, src.height(), SALT_ELEMS);
    stream_merkle_cap_inner(src, cap_height, Some(&salts.values))
}

fn stream_merkle_cap_inner<S: LeafSource>(src: &S, cap_height: usize, salts: Option<&[Val]>) -> Vec<[Val; DIGEST]> {
    let mut layers = stream_merkle_layers_inner(src, cap_height, salts);
    layers.pop().expect("at least the leaf layer")
}

/// Shared frontier build returning EVERY digest layer (layer 0 = leaves, last = the `cap_height` cap) —
/// what `stream_open` needs for sibling paths. `salts`, when present, is the `h × SALT_ELEMS` matrix
/// (row-major) whose row `r` is appended to leaf row `r` before hashing (the hiding variant); `None` is
/// the plain commit. The layers are small (≈ `h × DIGEST` total); the wide leaves are streamed, never
/// fully resident.
fn stream_merkle_layers_inner<S: LeafSource>(src: &S, cap_height: usize, salts: Option<&[Val]>) -> Vec<Vec<[Val; DIGEST]>> {
    let h = src.height();
    let w = src.width();
    assert!(h.is_power_of_two(), "stream_merkle: leaf height must be a power of two (got {h})");
    if let Some(s) = salts {
        assert_eq!(s.len(), h * SALT_ELEMS, "salt matrix must be h*SALT_ELEMS");
    }
    let perm = default_goldilocks_poseidon2_8();
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm);

    // Leaf digest layer: hash rows in blocks (so a column-major store reads `w` contiguous
    // column-segments per block — one streaming pass — rather than a strided per-row gather). Only the
    // block buffer (ROW_BLOCK × w) and the digests ever reside; the wide leaves are never fully held.
    const ROW_BLOCK: usize = 4096;
    let bh = ROW_BLOCK.min(h);
    let mut block = vec![Val::default(); bh * w];
    let mut leaf: Vec<[Val; DIGEST]> = Vec::with_capacity(h);
    let mut r0 = 0usize;
    while r0 < h {
        let nr = bh.min(h - r0);
        src.fill_row_block(r0, nr, &mut block[..nr * w]);
        for i in 0..nr {
            let data = block[i * w..(i + 1) * w].iter().copied();
            let digest = match salts {
                // leaf = [row | salt], matching p3's `HorizontalPair::new(mat, salts)`
                Some(s) => {
                    let r = r0 + i;
                    hash.hash_iter(data.chain(s[r * SALT_ELEMS..(r + 1) * SALT_ELEMS].iter().copied()))
                }
                None => hash.hash_iter(data),
            };
            leaf.push(digest);
        }
        r0 += nr;
    }

    // Compress pairwise (arity 2) up to the cap, keeping every layer. `h` is a power of two, so every
    // layer length is even until it reaches the cap; a tree shorter than the cap is just the leaf layer.
    let cap_len = (1usize << cap_height).min(leaf.len());
    let mut layers = vec![leaf];
    while layers.last().unwrap().len() > cap_len {
        let next: Vec<[Val; DIGEST]> =
            layers.last().unwrap().chunks_exact(2).map(|c| compress.compress([c[0], c[1]])).collect();
        layers.push(next);
    }
    layers
}

/// Prover data for the streaming commit: the LDE on disk, the hiding salts, and the digest layers
/// (leaves..cap — small). Everything `stream_open` needs to open a query index. `cap()` is the commitment.
pub struct StreamCommitData {
    pub store: MmapLdeStore,
    pub salts: Vec<Val>,
    pub layers: Vec<Vec<[Val; DIGEST]>>,
}

impl StreamCommitData {
    /// The commitment cap (the top digest layer) — byte-identical to the production commitment.
    pub fn cap(&self) -> &[[Val; DIGEST]] {
        self.layers.last().expect("at least the leaf layer")
    }
}

/// The out-of-core equivalent of p3's hiding `Pcs::commit` for one matrix: stream the coset-LDE of
/// `trace` to disk, draw the hiding salts (p3's order), and build the salted Merkle layers. `cap()` is
/// byte-identical to the production commitment; the data opens byte-identically via `stream_open`.
pub fn stream_commit<R: rand::Rng>(
    trace: RowMajorMatrix<Val>,
    added_bits: usize,
    shift: Val,
    c_block: usize,
    cap_height: usize,
    rng: &mut R,
) -> std::io::Result<StreamCommitData> {
    let (h, w) = (trace.height(), trace.width());
    let big = h << added_bits;
    let store = MmapLdeStore::new(big, w)?;
    stream_coset_lde_to_store(&trace, added_bits, shift, c_block, &store);
    let salts = RowMajorMatrix::rand(rng, big, SALT_ELEMS).values;
    let layers = stream_merkle_layers_inner(&store, cap_height, Some(&salts));
    Ok(StreamCommitData { store, salts, layers })
}

/// Open the leaf at `index`: the (unsalted) row, its salt, and the binary Merkle sibling path up to the
/// cap — byte-identical to production's hiding `Mmcs::open_batch` (which returns `opened_values = [row]`,
/// `opening_proof = ([salt], siblings)`). The row is a single strided seek into the store; the salt and
/// the log-length path come from the small resident salts/layers — negligible I/O at 96 queries.
pub fn stream_open(data: &StreamCommitData, index: usize) -> (Vec<Val>, Vec<Val>, Vec<[Val; DIGEST]>) {
    let w = data.store.width();
    let mut row = vec![Val::default(); w];
    data.store.fill_row(index, &mut row);
    let salt = data.salts[index * SALT_ELEMS..(index + 1) * SALT_ELEMS].to_vec();
    // one sibling per binary level, leaf up to (not including) the cap layer
    let mut proof = Vec::with_capacity(data.layers.len().saturating_sub(1));
    let mut idx = index;
    for layer in &data.layers[..data.layers.len() - 1] {
        proof.push(layer[idx ^ 1]);
        idx >>= 1;
    }
    (row, salt, proof)
}

// ── Streaming FRI (P3.6) ────────────────────────────────────────────────────────────────────────
// The commit/open MMCS substrate above is over the BASE field. The FRI commit phase instead commits
// each round's codeword over the EXTENSION field through p3's `ChallengeMmcs = ExtensionMmcs<Val,
// Challenge, ValMmcs>`, which base-flattens each `Challenge` element into its `EXT_D` coordinates
// (element-major, exactly `FlatMatrixView`) and then hides via the SAME production `ValMmcs`. So a FRI
// round commit is just the streaming hiding commit applied to the base-flattened codeword — and a FRI
// query open is `stream_open` + `reconstitute_from_base`. These two functions are the extension-field
// bridge; `stream_prove_fri` (below) drives them round-by-round.

/// Base coordinates per `Challenge` element (`Challenge`'s degree over `Val`). `ExtensionMmcs` flattens
/// each committed extension element into this many consecutive base columns, element-major.
const EXT_D: usize = <Challenge as BasedVectorSpace<Val>>::DIMENSION;

/// Streaming HIDING commit of one FRI-round codeword, byte-identical to p3's per-round
/// `params.mmcs.commit_matrix(RowMajorMatrix::new(folded, arity))` where `params.mmcs` is the production
/// `ExtensionMmcs<Val, Challenge, ValMmcs>`. `folded` is the round's evaluation vector over `Challenge`
/// in the bit-reversed order p3 keeps; reshaped to width `arity` it is the round's leaf matrix.
///
/// The out-of-core reproduction: base-flatten the codeword element-major (matching `FlatMatrixView`) and
/// store it COLUMN-MAJOR on disk (each base column written from `folded` with only `h/arity` `Val`s
/// transient — never the whole base matrix), so the query phase can seek any group by index; draw the
/// `h/arity × SALT_ELEMS` salts in p3's exact `RowMajorMatrix::rand` order; frontier-Merkle the salted
/// leaves keeping only the digest layers + salts resident. Unlike p3 — which keeps EVERY round's whole
/// codeword-as-leaves AND its Merkle tree alive until the query phase — only the current round's store
/// (on disk) and its small digest layers persist.
///
/// `cap()` of the result equals `ExtensionMmcs::commit_matrix(leaves).0` byte-for-byte; `stream_answer_query`
/// opens it byte-identically to p3's `answer_query`.
pub fn stream_commit_codeword<R: rand::Rng>(
    folded: &[Challenge],
    arity: usize,
    cap_height: usize,
    rng: &mut R,
) -> std::io::Result<StreamCommitData> {
    let n = folded.len();
    assert!(arity >= 1 && n % arity == 0, "codeword length {n} must be a multiple of arity {arity}");
    let h_leaf = n / arity;
    let bw = arity * EXT_D; // base-flattened leaf width
    let store = MmapLdeStore::new(h_leaf, bw)?;
    // Write the base-flattened codeword COLUMN-MAJOR, one base column at a time (only `h_leaf` `Val`s
    // transient). Base column `bc` is coordinate `bc % EXT_D` of extension column `bc / EXT_D`, read
    // down the groups — the element-major flatten `FlatMatrixView` (and `flatten_to_base`) produce.
    let mut col = vec![Val::default(); h_leaf];
    for bc in 0..bw {
        let (ec, co) = (bc / EXT_D, bc % EXT_D);
        for (g, c) in col.iter_mut().enumerate() {
            *c = folded[g * arity + ec].as_basis_coefficients_slice()[co];
        }
        store.write_col_tile(bc, 1, &col);
    }
    let salts = RowMajorMatrix::rand(rng, h_leaf, SALT_ELEMS).values;
    let layers = stream_merkle_layers_inner(&store, cap_height, Some(&salts));
    Ok(StreamCommitData { store, salts, layers })
}

/// One FRI query's opening of one commit-phase round — byte-identical to a single step of p3's
/// `answer_query`. Given the round's streamed commit and the query's `current_index` into the round's
/// codeword, seek the containing group (a strided row read from the on-disk store), reconstitute it to
/// the extension field (p3's `reconstitute_from_base`, the inverse of the commit's base-flatten), drop
/// the queried element to leave the `arity-1` sibling values, and package the salt + Merkle path as the
/// `ExtensionMmcs` opening proof (which is the inner hiding proof unchanged). Returns the step and the
/// parent `group_index` — the next round's `current_index`, exactly as p3 threads it.
pub fn stream_answer_query(
    data: &StreamCommitData,
    log_arity: usize,
    current_index: usize,
) -> (CommitPhaseProofStep<Challenge, ChallengeMmcs>, usize) {
    let arity = 1usize << log_arity;
    let index_in_group = current_index % arity;
    let group_index = current_index >> log_arity;
    // Seek the base-flattened group row (`arity * EXT_D` `Val`s), its salt, and the sibling path.
    let (base_row, salt, siblings) = stream_open(data, group_index);
    debug_assert_eq!(base_row.len(), arity * EXT_D);
    let opened_row = <Challenge as BasedVectorSpace<Val>>::reconstitute_from_base(base_row);
    debug_assert_eq!(opened_row.len(), arity);
    // Siblings = every group element except the queried one (p3's `filter(|(j, _)| *j != index_in_group)`).
    let sibling_values: Vec<Challenge> = opened_row
        .into_iter()
        .enumerate()
        .filter(|(j, _)| *j != index_in_group)
        .map(|(_, v)| v)
        .collect();
    let step = CommitPhaseProofStep {
        log_arity: log_arity as u8,
        sibling_values,
        // ExtensionMmcs::Proof == inner hiding Proof == (salts: Vec<Vec<Val>>, siblings: Vec<[Val; DIGEST]>).
        opening_proof: (vec![salt], siblings),
    };
    (step, group_index)
}

/// The FRI commit-phase commitment type — the `ChallengeMmcs` (= its inner hiding `ValMmcs`) commitment,
/// a `MerkleCap` of `DIGEST`-wide digests. `stream_commit_codeword(...).cap()` is exactly its `AsRef`.
type FriCommit = MerkleCap<Val, [Val; DIGEST]>;

/// The production input-commitment prover data (the trace / quotient LDE Merkle trees) that FRI's
/// `open_input` reads at each query. Held resident here (this fork streams the FRI COMMIT phase; the
/// input opens are the separate "batch open at ζ" increment) — `stream_prove_fri` opens them verbatim.
type InputProverData = <ValMmcs as Mmcs<Val>>::ProverData<RowMajorMatrix<Val>>;

/// Streaming, prove-only fork of `p3_fri::prover::prove_fri`, specialized to the production `MyConfig`
/// types, that keeps the commit-phase residency bounded: instead of p3's `Vec<M::ProverData>` — which
/// holds EVERY fold round's whole codeword-as-leaves AND its Merkle tree alive until the query phase —
/// it keeps only the CURRENT round's codeword resident (needed to fold to the next), spills each round's
/// leaves to disk via `stream_commit_codeword`, and retains just the digest layers + salts. The query
/// phase then seeks each round's opened group from disk (`stream_answer_query`).
///
/// BYTE-IDENTICAL to `prove_fri`: every `challenger` observe/sample/grind and every salt draw happens in
/// p3's exact order, the folding reuses p3's own `TwoAdicFriFolding::fold_matrix` verbatim, and the
/// `final_poly` iDFT + arity/PoW transcript steps are unchanged. `params.mmcs` is unused (its per-round
/// salts come from `salt_rng`, which the caller seeds to match `params.mmcs`'s inner RNG); everything else
/// in `params` is read exactly as p3 reads it. `open_input` is p3's verbatim (input opens stay resident).
///
/// Pinned by `stream_prove_fri_matches_p3`.
#[allow(clippy::too_many_arguments)]
pub fn stream_prove_fri<R: rand::Rng>(
    params: &FriParameters<ChallengeMmcs>,
    inputs: Vec<Vec<Challenge>>,
    challenger: &mut Challenger,
    log_global_max_height: usize,
    input_data: &[ProverDataWithOpeningPoints<'_, Challenge, InputProverData>],
    input_mmcs: &ValMmcs,
    salt_rng: &mut R,
    cap_height: usize,
) -> std::io::Result<FriProof<Challenge, ChallengeMmcs, Val, Vec<BatchOpening<Val, ValMmcs>>>> {
    assert!(!inputs.is_empty());
    assert!(params.num_queries > 0, "num_queries must be at least 1 for FRI soundness");
    assert!(params.max_log_arity > 0, "max_log_arity must be at least 1 to guarantee folding progress");
    debug_assert_eq!(log_global_max_height, log2_strict_usize(inputs[0].len()));

    // The folding strategy is stateless (PhantomData) — construct the SAME one p3's PCS `open` uses.
    let folding: TwoAdicFriFoldingForMmcs<Val, ValMmcs> = TwoAdicFriFolding(PhantomData);

    // ── commit phase (streamed) — mirrors p3's `commit_phase` exactly, per round: ─────────────────
    //   stream-commit the codeword (draws salts) → observe cap → grind commit-PoW → sample beta →
    //   fold → (if the next input matches the new height) mix it in with beta^arity.
    let mut inputs_iter = inputs.into_iter().peekable();
    let mut folded = inputs_iter.next().unwrap();
    let mut commits: Vec<FriCommit> = vec![];
    let mut datas: Vec<StreamCommitData> = vec![];
    let mut log_arities: Vec<usize> = vec![];
    let mut pow_witnesses: Vec<Val> = vec![];
    let log_final_height = params.log_blowup + params.log_final_poly_len;

    while folded.len() > params.blowup() * params.final_poly_len() {
        let log_current_height = log2_strict_usize(folded.len());
        let next_input_log_height = inputs_iter.peek().map(|v| log2_strict_usize(v.len()));
        let log_arity =
            compute_log_arity_for_round(log_current_height, next_input_log_height, log_final_height, params.max_log_arity);
        let arity = 1usize << log_arity;
        log_arities.push(log_arity);

        // Stream-commit this round's codeword (spills the leaves to disk, keeps only digest layers).
        let data = stream_commit_codeword(&folded, arity, cap_height, salt_rng)?;
        let commit = FriCommit::from(data.cap().to_vec());
        challenger.observe(commit.clone());
        commits.push(commit);

        let pow_witness = challenger.grind(params.commit_proof_of_work_bits);
        pow_witnesses.push(pow_witness);

        let beta: Challenge = challenger.sample_algebra_element();

        // Reuse p3's folding math verbatim on the (still resident) current codeword. Fully-qualified so
        // the base field `F = Val` is pinned (p3's `commit_phase` pins it via its `FriFoldingStrategy<Val,
        // Challenge>` bound; here `TwoAdicFriFolding`'s blanket impl otherwise leaves `F` ambiguous).
        let leaves = RowMajorMatrix::new(folded, arity);
        folded = FriFoldingStrategy::<Val, Challenge>::fold_matrix(&folding, beta, log_arity, leaves.as_view());

        datas.push(data);

        // Mix in the next input polynomial once we have folded down to its height (p3's beta^arity factor).
        if let Some(v) = inputs_iter.next_if(|v| v.len() == folded.len()) {
            let beta_pow = beta.exp_power_of_2(log_arity);
            folded.iter_mut().zip(v).for_each(|(c, x)| *c += beta_pow * x);
        }
    }

    // Final polynomial: truncate, un-bit-reverse, iDFT — then observe all its coefficients. The iDFT is
    // over the BASE-field FRI subgroup (`Challenge` coordinates DFT'd independently), so pin `F = Val`
    // (`Challenge` is a `BasedVectorSpace` over both `Val` and itself, leaving `default()` ambiguous).
    folded.truncate(params.final_poly_len());
    reverse_slice_index_bits(&mut folded);
    let final_poly = Radix2DFTSmallBatch::<Val>::default().idft_algebra(folded);
    challenger.observe_algebra_slice(&final_poly);

    // Bind the chosen folding arities into the transcript, then grind the query PoW.
    for &log_arity in &log_arities {
        challenger.observe(Val::from_usize(log_arity));
    }
    let query_pow_witness = challenger.grind(params.query_proof_of_work_bits);

    // ── query phase (seek-backed) — sample each index, open the inputs (resident) + each round (disk). ─
    let extra_query_index_bits = FriFoldingStrategy::<Val, Challenge>::extra_query_index_bits(&folding);
    let query_proofs = core::iter::repeat_with(|| {
        let index = challenger.sample_bits(log_global_max_height + extra_query_index_bits);
        let input_proof = stream_open_input(log_global_max_height, index, input_data, input_mmcs);
        let mut current_index = index >> extra_query_index_bits;
        let mut commit_phase_openings = Vec::with_capacity(datas.len());
        for (data, &log_arity) in datas.iter().zip(log_arities.iter()) {
            let (step, group_index) = stream_answer_query(data, log_arity, current_index);
            commit_phase_openings.push(step);
            current_index = group_index;
        }
        QueryProof { input_proof, commit_phase_openings }
    })
    .take(params.num_queries)
    .collect();

    Ok(FriProof {
        commit_phase_commits: commits,
        commit_pow_witnesses: pow_witnesses,
        query_proofs,
        final_poly,
        query_pow_witness,
    })
}

/// FRI `open_input`, verbatim from p3: open each input batch commitment at the query index, shifting the
/// index down for matrices shorter than the global max height. The input opens stay resident in this
/// increment (streaming them is the separate "batch open" step); byte-identical to p3's private `open_input`.
fn stream_open_input(
    log_global_max_height: usize,
    index: usize,
    input_data: &[ProverDataWithOpeningPoints<'_, Challenge, InputProverData>],
    mmcs: &ValMmcs,
) -> Vec<BatchOpening<Val, ValMmcs>> {
    input_data
        .iter()
        .map(|(data, _)| {
            let log_max_height = log2_strict_usize(mmcs.get_max_height(data));
            let bits_reduced = log_global_max_height - log_max_height;
            let reduced_index = index >> bits_reduced;
            mmcs.open_batch(reduced_index, data)
        })
        .collect()
}

/// A file-backed (mmap'd) store for one `h × w` LDE matrix, held **COLUMN-MAJOR** (element `(row, col)`
/// at `map[col*h + row]`) — the out-of-core substrate that keeps the multi-GB LDE off the anonymous heap.
/// Column-major is what makes both directions ONE sequential pass and dodges the transpose barrier:
/// - **write** a column-tile → each column is a contiguous segment `[(c0+c)*h, (c0+c+1)*h)`, so the whole
///   LDE is written in one forward pass as `c0` advances (independent of the tile width);
/// - **read** for the frontier Merkle → `fill_row_block` reads `w` contiguous column-segments per row-block
///   (w interleaved sequential streams), one pass over the store.
///
/// Access is EXPLICIT and sequential, so the OS streams it (evicts behind the read head) instead of
/// thrashing on p3's blind whole-buffer re-touch (the Phase 2 allocator's failure). Later, FRI opening
/// reads individual rows by `fill_row` (sparse strided seeks — cheap at 96 queries).
pub struct MmapLdeStore {
    map: *mut Val,
    n: usize,
    h: usize,
    w: usize,
    fd: libc::c_int,
}

// SAFETY: `map` is a stable, process-private mmap for the store's lifetime; the streaming commit writes
// each tile BEFORE any read of it, so there is never a concurrent write+read of the same region.
unsafe impl Send for MmapLdeStore {}
unsafe impl Sync for MmapLdeStore {}

static LDE_STORE_SEQ: AtomicU64 = AtomicU64::new(0);

impl MmapLdeStore {
    /// Create a fresh zero-filled `h × w` store in `$LATTICA_SPILL_DIR` (else the temp dir). The file is
    /// unlinked immediately, so it is reclaimed on drop or crash.
    pub fn new(h: usize, w: usize) -> std::io::Result<Self> {
        let n = h.checked_mul(w).expect("store dimensions overflow");
        let bytes = n.checked_mul(size_of::<Val>()).expect("store byte size overflow");
        let dir = std::env::var("LATTICA_SPILL_DIR")
            .ok()
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| std::env::temp_dir().to_string_lossy().into_owned());
        let seq = LDE_STORE_SEQ.fetch_add(1, Ordering::Relaxed);
        let path = format!("{dir}/lat-lde-{}-{seq}.tmp", std::process::id());
        let cpath = CString::new(path).map_err(|_| std::io::Error::from(std::io::ErrorKind::InvalidInput))?;
        // SAFETY: raw file + mmap syscalls with a valid NUL-terminated path and a checked byte length.
        unsafe {
            let fd = libc::open(cpath.as_ptr(), libc::O_RDWR | libc::O_CREAT | libc::O_EXCL, 0o600);
            if fd < 0 {
                return Err(std::io::Error::last_os_error());
            }
            libc::unlink(cpath.as_ptr());
            if libc::ftruncate(fd, bytes as libc::off_t) != 0 {
                let e = std::io::Error::last_os_error();
                libc::close(fd);
                return Err(e);
            }
            let m = libc::mmap(std::ptr::null_mut(), bytes, libc::PROT_READ | libc::PROT_WRITE, libc::MAP_SHARED, fd, 0);
            if m == libc::MAP_FAILED {
                let e = std::io::Error::last_os_error();
                libc::close(fd);
                return Err(e);
            }
            Ok(Self { map: m as *mut Val, n, h, w, fd })
        }
    }

    /// The whole store as a slice (ftruncate-zeroed, then overwritten by the LDE writes).
    #[inline]
    fn slice(&self) -> &[Val] {
        // SAFETY: `map` covers `n` initialized `Val` elements (zeroed at creation) for the store's lifetime.
        unsafe { std::slice::from_raw_parts(self.map, self.n) }
    }

    /// Write a `h × cw` ROW-MAJOR LDE tile (columns `[c0, c0+cw)`, `tile[r*cw + c]`) into the COLUMN-MAJOR
    /// store: column `c0+c` fills the contiguous segment `[(c0+c)*h, (c0+c+1)*h)`. As `c0` advances across
    /// tiles this writes the whole store front-to-back in one sequential pass. The per-column transpose of
    /// the (small, resident) tile is in-RAM; the disk write is sequential.
    pub fn write_col_tile(&self, c0: usize, cw: usize, tile: &[Val]) {
        debug_assert_eq!(tile.len(), self.h * cw, "tile must be h*cw");
        debug_assert!((c0 + cw) * self.h <= self.n, "column tile out of bounds");
        for c in 0..cw {
            // SAFETY: `[(c0+c)*h, +h)` is in-bounds; distinct columns are disjoint; written before any read.
            let dst = unsafe { std::slice::from_raw_parts_mut(self.map.add((c0 + c) * self.h), self.h) };
            for (r, d) in dst.iter_mut().enumerate() {
                *d = tile[r * cw + c];
            }
        }
    }
}

impl Drop for MmapLdeStore {
    fn drop(&mut self) {
        // SAFETY: `map`/`fd` were produced by `mmap`/`open` in `new` and are freed exactly once here.
        unsafe {
            libc::munmap(self.map as *mut libc::c_void, self.n * size_of::<Val>());
            libc::close(self.fd);
        }
    }
}

impl LeafSource for MmapLdeStore {
    fn height(&self) -> usize {
        self.h
    }
    fn width(&self) -> usize {
        self.w
    }
    /// One row by strided gather across the `w` column-segments — for sparse FRI-query reads.
    fn fill_row(&self, row: usize, out: &mut [Val]) {
        let s = self.slice();
        for (c, o) in out.iter_mut().enumerate() {
            *o = s[c * self.h + row];
        }
    }
    /// A block of `nr` rows, read as `w` contiguous column-segments `[c*h + r0, +nr)` (w interleaved
    /// sequential streams over the store) transposed into `out` (row-major `nr × w`) — one streaming pass.
    fn fill_row_block(&self, r0: usize, nr: usize, out: &mut [Val]) {
        let s = self.slice();
        for c in 0..self.w {
            let seg = &s[c * self.h + r0..c * self.h + r0 + nr];
            for i in 0..nr {
                out[i * self.w + c] = seg[i];
            }
        }
    }
}

/// Compute the coset-LDE of `trace` a COLUMN-TILE at a time and write each tile into the COLUMN-MAJOR
/// `store` (via `write_col_tile`), so only one `big × c_block` tile ever resides, never the whole
/// `big × w` LDE, and the store is written FRONT-TO-BACK in ONE sequential pass (each column is a
/// contiguous segment). Byte-identical to what p3's `TwoAdicFriPcs::commit` COMMITS —
/// `coset_lde_batch(trace, added_bits, shift).bit_reverse_rows().to_row_major_matrix()` (the extra
/// `bit_reverse_rows` is the one p3 applies before the MMCS commit, so the stored order matches the
/// committed matrix the open reads via `get_matrices`) — because columns are independent polynomials (a
/// column subset yields identical per-column output) and the row bit-reversal is column-independent, so
/// tiling and the reversal commute. `store` must be `big × w` (`big = h << added_bits`).
///
/// Paired with the frontier Merkle's transposed-block read, the whole out-of-core commit is ~2
/// sequential passes over the store, INDEPENDENT of `w` — so it is RAM-bounded AND fast, unlike the
/// row-major-store predecessor (`w/c_block` passes) and the Phase 2 allocator (thrashed under pressure).
pub fn stream_coset_lde_to_store(trace: &RowMajorMatrix<Val>, added_bits: usize, shift: Val, c_block: usize, store: &MmapLdeStore) {
    let (h, w) = (trace.height(), trace.width());
    let big = h << added_bits;
    assert_eq!(store.height(), big, "store height must be the blown-up height");
    assert_eq!(store.width(), w, "store width must match the trace");
    assert!(c_block >= 1, "column block must be >= 1");
    let dft = Dft::default();
    let mut c0 = 0usize;
    while c0 < w {
        let cw = c_block.min(w - c0);
        // gather columns [c0, c0+cw) into a narrow h×cw matrix
        let mut sub = Vec::with_capacity(h * cw);
        for r in 0..h {
            sub.extend_from_slice(&trace.values[r * w + c0..r * w + c0 + cw]);
        }
        // coset-LDE the narrow tile -> big×cw, then bit-reverse rows into p3's COMMITTED order (the extra
        // `.bit_reverse_rows()` p3's `TwoAdicFriPcs::commit` applies), then discard the tile.
        let lde = dft.coset_lde_batch(RowMajorMatrix::new(sub, cw), added_bits, shift).bit_reverse_rows().to_row_major_matrix();
        store.write_col_tile(c0, cw, &lde.values);
        c0 += cw;
    }
}

/// A read-only `Matrix<Val>` VIEW over a committed-LDE `MmapLdeStore` — the disk-backed matrix that p3's
/// `open`-at-ζ reduction reads verbatim. The heavy step of the open, `rowwise_packed_dot_product` over the
/// WHOLE blown-up LDE (`two_adic_pcs.rs`), is `Matrix`-generic, so running it on this view keeps the LDE on
/// disk and streams it row by row while producing the byte-identical `reduced_openings` the FRI consumes.
/// (The barycentric low-coset eval needs a dense `RowMajorMatrix`, but it reads only the first
/// `height >> log_blowup` rows — trace-sized — so that slice is materialized resident separately.)
///
/// A row is a stride-`h` gather across the column-major store (`map[c*h + r]`); the reduction's sequential
/// row walk therefore reads each column-segment in order — the same streaming access pattern as the commit.
pub struct StoreMatrix<'a> {
    store: &'a MmapLdeStore,
}

impl<'a> StoreMatrix<'a> {
    pub fn new(store: &'a MmapLdeStore) -> Self {
        Self { store }
    }
}

impl Matrix<Val> for StoreMatrix<'_> {
    #[inline]
    fn width(&self) -> usize {
        self.store.w
    }
    #[inline]
    fn height(&self) -> usize {
        self.store.h
    }
    #[inline]
    unsafe fn row_subseq_unchecked(
        &self,
        r: usize,
        start: usize,
        end: usize,
    ) -> impl IntoIterator<Item = Val, IntoIter = impl Iterator<Item = Val> + Send + Sync> {
        // Column-major store: element (r, c) is at `map[c*h + r]`, so a row is a stride-`h` gather. This is
        // the one required accessor (the trait derives `row`/`row_slice`/`get` from it); bounds are the
        // caller's `unsafe` contract (`r < height`, `start <= end <= width`) → every index is `< n`.
        let s = self.store.slice();
        let h = self.store.h;
        (start..end).map(move |c| s[c * h + r])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::CAP_HEIGHT; // test-only: the production Merkle cap height
    use p3_commit::Mmcs;
    use p3_field::Field;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_merkle_tree::MerkleTreeMmcs;

    type RefMmcs = MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, 2, DIGEST>;

    /// The streaming (frontier) Merkle cap is byte-identical to p3's `MerkleTreeMmcs` commitment across
    /// heights/widths — proving the wide leaves can be hashed one row at a time (never fully resident)
    /// without changing the commitment. This is the standalone gate the plan requires before wiring the
    /// streaming store into the commit.
    #[test]
    fn stream_merkle_matches_p3() {
        let perm = default_goldilocks_poseidon2_8();
        let mmcs = RefMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm), CAP_HEIGHT);
        for &(log_h, w) in &[(3usize, 1usize), (6, 5), (7, 2), (10, 49), (12, 53), (13, 1291)] {
            let h = 1usize << log_h;
            // deterministic pseudo-random leaf values (canonical Goldilocks)
            let vals: Vec<Val> = (0..h * w)
                .map(|i| Val::new((i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) % 0xFFFF_FFFF_0000_0001))
                .collect();
            let mat = RowMajorMatrix::new(vals.clone(), w);
            let (p3_commit, _) = mmcs.commit(vec![mat]);
            let mine = stream_merkle_cap(&SliceLeaves { vals: &vals, h, w }, CAP_HEIGHT);
            // p3's commitment is the `MerkleCap` (AsRef<[digest]>) at CAP_HEIGHT
            let p3_cap: &[[Val; DIGEST]] = p3_commit.as_ref();
            assert_eq!(p3_cap, mine.as_slice(), "streaming Merkle cap != p3 at h=2^{log_h} w={w}");
        }
    }

    /// The streaming HIDING Merkle cap is byte-identical to the PRODUCTION salted `MerkleTreeHidingMmcs`
    /// commitment — same salts (a fresh rng of the same seed, drawn via p3's `RowMajorMatrix::rand` order)
    /// and `[row | salt]` leaves. This matches the actual production commit (the non-hiding test above
    /// validated the tree structure; production is hiding).
    #[test]
    fn stream_merkle_hiding_matches_p3() {
        use p3_merkle_tree::MerkleTreeHidingMmcs;
        use rand::SeedableRng;
        use rand_chacha::ChaCha20Rng;
        type HidingMmcs = MerkleTreeHidingMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, ChaCha20Rng, 2, DIGEST, SALT_ELEMS>;
        let perm = default_goldilocks_poseidon2_8();
        for &(log_h, w, seed) in &[(3usize, 1usize, 1u64), (6, 5, 2), (10, 49, 3), (12, 53, 4), (13, 1291, 5)] {
            let h = 1usize << log_h;
            let vals: Vec<Val> = (0..h * w)
                .map(|i| Val::new((i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) % 0xFFFF_FFFF_0000_0001))
                .collect();
            let mat = RowMajorMatrix::new(vals.clone(), w);
            let mmcs = HidingMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), CAP_HEIGHT, ChaCha20Rng::seed_from_u64(seed));
            let (p3_commit, _) = mmcs.commit(vec![mat]);
            let mut rng = ChaCha20Rng::seed_from_u64(seed);
            let mine = stream_merkle_cap_hiding(&SliceLeaves { vals: &vals, h, w }, CAP_HEIGHT, &mut rng);
            let p3_cap: &[[Val; DIGEST]] = p3_commit.as_ref();
            assert_eq!(p3_cap, mine.as_slice(), "streaming HIDING Merkle cap != p3 at h=2^{log_h} w={w} seed={seed}");
        }
    }

    /// Column-tiled LDE written into the mmap store is byte-identical to p3's COMMITTED LDE —
    /// `coset_lde_batch(...).bit_reverse_rows().to_row_major_matrix()`, the exact matrix
    /// `TwoAdicFriPcs::commit` commits — the whole LDE never residing (only one `big × c_block` tile).
    #[test]
    fn stream_lde_matches_p3() {
        let dft = Dft::default();
        let shift = <Val as Field>::GENERATOR;
        for &(log_h, w, added, cblk) in &[(4usize, 3usize, 2usize, 1usize), (8, 5, 3, 2), (10, 49, 4, 8), (12, 53, 4, 16)] {
            let h = 1usize << log_h;
            let vals: Vec<Val> = (0..h * w)
                .map(|i| Val::new((i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) % 0xFFFF_FFFF_0000_0001))
                .collect();
            let mat = RowMajorMatrix::new(vals, w);
            let p3_lde = dft.coset_lde_batch(mat.clone(), added, shift).bit_reverse_rows().to_row_major_matrix();
            let big = h << added;
            let store = MmapLdeStore::new(big, w).unwrap();
            stream_coset_lde_to_store(&mat, added, shift, cblk, &store);
            // reconstruct the row-major matrix from the COLUMN-MAJOR store and compare to p3's whole LDE
            let mut got = vec![Val::default(); big * w];
            store.fill_row_block(0, big, &mut got);
            assert_eq!(got, p3_lde.values, "streamed LDE store (row-major view) != p3 at h=2^{log_h} w={w} cblk={cblk}");
        }
    }

    /// End-to-end out-of-core commit: column-tiled LDE into the mmap store + frontier Merkle equals p3's
    /// committed-order (`coset_lde_batch(...).bit_reverse_rows()`) + `MerkleTreeMmcs` commitment — i.e. the
    /// commitment `TwoAdicFriPcs::commit` produces. Neither the whole LDE nor the whole leaf matrix ever
    /// resides — this is the substrate that actually cuts the prover's RAM.
    #[test]
    fn stream_lde_merkle_matches_p3() {
        let dft = Dft::default();
        let shift = <Val as Field>::GENERATOR;
        let perm = default_goldilocks_poseidon2_8();
        let mmcs = RefMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm), CAP_HEIGHT);
        for &(log_h, w, added, cblk) in &[(7usize, 2usize, 4usize, 1usize), (10, 49, 4, 8), (12, 53, 4, 16)] {
            let h = 1usize << log_h;
            let big = h << added;
            let vals: Vec<Val> = (0..h * w)
                .map(|i| Val::new((i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) % 0xFFFF_FFFF_0000_0001))
                .collect();
            let mat = RowMajorMatrix::new(vals, w);
            let p3_lde = dft.coset_lde_batch(mat.clone(), added, shift).bit_reverse_rows().to_row_major_matrix();
            let (p3_commit, _) = mmcs.commit(vec![p3_lde]);
            let store = MmapLdeStore::new(big, w).unwrap();
            stream_coset_lde_to_store(&mat, added, shift, cblk, &store);
            let mine = stream_merkle_cap(&store, CAP_HEIGHT);
            let p3_cap: &[[Val; DIGEST]] = p3_commit.as_ref();
            assert_eq!(p3_cap, mine.as_slice(), "streamed LDE+Merkle != p3 at h=2^{log_h} w={w} cblk={cblk}");
        }
    }

    /// `stream_commit` + `stream_open` open a query index byte-identical to production's HIDING
    /// `Mmcs::commit` + `open_batch`: same opened row, same salt, same Merkle sibling path — the full
    /// out-of-core commit/open MMCS primitive that the streamed FRI open will drive.
    #[test]
    fn stream_open_matches_p3() {
        use p3_commit::Mmcs;
        use p3_merkle_tree::MerkleTreeHidingMmcs;
        use rand::SeedableRng;
        use rand_chacha::ChaCha20Rng;
        type HidingMmcs = MerkleTreeHidingMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, ChaCha20Rng, 2, DIGEST, SALT_ELEMS>;
        let dft = Dft::default();
        let shift = <Val as Field>::GENERATOR;
        let perm = default_goldilocks_poseidon2_8();
        for &(log_h, w, added, cblk, seed) in &[(6usize, 5usize, 3usize, 2usize, 1u64), (10, 49, 4, 8, 2), (12, 53, 4, 16, 3)] {
            let h = 1usize << log_h;
            let big = h << added;
            let vals: Vec<Val> = (0..h * w)
                .map(|i| Val::new((i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) % 0xFFFF_FFFF_0000_0001))
                .collect();
            let mat = RowMajorMatrix::new(vals, w);
            let p3_lde = dft.coset_lde_batch(mat.clone(), added, shift).bit_reverse_rows().to_row_major_matrix();
            let mmcs = HidingMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), CAP_HEIGHT, ChaCha20Rng::seed_from_u64(seed));
            let (p3_commit, p3_data) = mmcs.commit(vec![p3_lde]);
            let mut rng = ChaCha20Rng::seed_from_u64(seed);
            let data = stream_commit(mat, added, shift, cblk, CAP_HEIGHT, &mut rng).unwrap();
            assert_eq!(p3_commit.as_ref(), data.cap(), "commit cap != p3 at h=2^{log_h} w={w}");
            for &idx in &[0usize, 1, big / 3, big / 2, big - 1] {
                let (p3_openings, (p3_salts, p3_sibs)) = mmcs.open_batch(idx, &p3_data).unpack();
                let (row, salt, sibs) = stream_open(&data, idx);
                assert_eq!(p3_openings[0], row, "opened row != p3 at idx {idx} (h=2^{log_h} w={w})");
                assert_eq!(p3_salts[0], salt, "salt != p3 at idx {idx}");
                assert_eq!(p3_sibs, sibs, "sibling path != p3 at idx {idx}");
            }
        }
    }

    /// The streaming FRI-round commit + open (over the EXTENSION field) is byte-identical to p3's
    /// production `ExtensionMmcs<Val, Challenge, ValMmcs>::commit_matrix` + a single `answer_query` step.
    /// This retires the extension-flatten (`FlatMatrixView`) / reconstitution + hiding-over-extension
    /// risk standalone — the two primitives `stream_prove_fri` drives round-by-round. Covers binary and
    /// higher-arity folds (`log_arity` 1..3), which change only the leaf width (`arity * EXT_D`).
    #[test]
    fn stream_fri_commit_open_matches_p3() {
        use crate::config::ValMmcs;
        use p3_fri::CommitPhaseProofStep;
        use rand::SeedableRng;
        use rand_chacha::ChaCha20Rng;
        let perm = default_goldilocks_poseidon2_8();
        // (log_h, log_arity, seed): a height-2^log_h extension codeword folded into groups of 2^log_arity.
        for &(log_h, log_arity, seed) in &[(4usize, 1usize, 10u64), (8, 1, 11), (8, 2, 12), (10, 3, 13), (6, 2, 14)] {
            let h = 1usize << log_h;
            let arity = 1usize << log_arity;
            // Deterministic pseudo-random extension codeword (p3's StandardUniform draw order).
            let folded: Vec<Challenge> =
                RowMajorMatrix::<Challenge>::rand(&mut ChaCha20Rng::seed_from_u64(seed ^ 0xC0DE), h, 1).values;
            let leaves = RowMajorMatrix::new(folded.clone(), arity); // (h/arity) × arity, extension

            // Reference: the production ExtensionMmcs over the hiding ValMmcs, salts seeded.
            let val_mmcs = ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), CAP_HEIGHT, ChaCha20Rng::seed_from_u64(seed));
            let challenge_mmcs = ChallengeMmcs::new(val_mmcs);
            let (ref_commit, ref_data) = challenge_mmcs.commit_matrix(leaves);

            // Mine: the same salt stream (a freshly seeded ChaCha20Rng), streamed out-of-core.
            let data = stream_commit_codeword(&folded, arity, CAP_HEIGHT, &mut ChaCha20Rng::seed_from_u64(seed)).unwrap();

            let ref_cap: &[[Val; DIGEST]] = ref_commit.as_ref();
            assert_eq!(ref_cap, data.cap(), "FRI round commit cap != p3 at log_h={log_h} arity={arity}");

            // Open several indices; compare the full CommitPhaseProofStep bytes (postcard = wire).
            for &current_index in &[0usize, 1, arity, h / 3, h / 2, h - 1] {
                let index_in_group = current_index % arity;
                let group_index = current_index >> log_arity;
                // Reference: p3's answer_query for one round (open the group, drop the queried element).
                let (mut ref_rows, ref_proof) = challenge_mmcs.open_batch(group_index, &ref_data).unpack();
                let ref_row = ref_rows.pop().unwrap();
                let ref_sibs: Vec<Challenge> =
                    ref_row.into_iter().enumerate().filter(|(j, _)| *j != index_in_group).map(|(_, v)| v).collect();
                let ref_step = CommitPhaseProofStep::<Challenge, ChallengeMmcs> {
                    log_arity: log_arity as u8,
                    sibling_values: ref_sibs,
                    opening_proof: ref_proof,
                };
                let (my_step, my_group) = stream_answer_query(&data, log_arity, current_index);
                assert_eq!(my_group, group_index, "parent group_index != p3 at idx={current_index}");
                let a = postcard::to_allocvec(&ref_step).unwrap();
                let b = postcard::to_allocvec(&my_step).unwrap();
                assert_eq!(a, b, "answer_query step != p3 at log_h={log_h} arity={arity} idx={current_index}");
            }
        }
    }

    /// The full streaming FRI prover is byte-identical to p3's production `prove_fri`. Seed both salt
    /// sources identically and drive both from a fresh (identical) challenger over the same inputs +
    /// input commitments; the entire `FriProof` (commit-phase caps, per-round PoW witnesses, `final_poly`,
    /// every query's input-open + commit-phase openings, query PoW) must serialize byte-for-byte. This is
    /// the primary P3.6 gate — it exercises the streamed commit phase, the folding (reused verbatim), the
    /// arity/final-poly/PoW transcript, and the seek-backed query phase all at once.
    ///
    /// Cases: a multi-input fold (three descending heights, arity-4 rounds, `open_input` at two commitment
    /// heights so `bits_reduced ∈ {0, 2}`), and a single-input fold (one height → arity 16 then 2, the
    /// no-next-input path). Production FRI parameters (`log_blowup=4`, cap 6, arity 4, 16-bit query PoW).
    #[test]
    fn stream_prove_fri_matches_p3() {
        use crate::config::{production_fri, ValMmcs};
        use p3_fri::prover::prove_fri;
        use p3_fri::{TwoAdicFriFolding, TwoAdicFriFoldingForMmcs};
        use rand::SeedableRng;
        use rand_chacha::ChaCha20Rng;
        let perm = default_goldilocks_poseidon2_8();

        // (FRI input log-heights [descending, distinct], input-commitment log-heights [for open_input]).
        let cases: &[(&[usize], &[usize])] = &[(&[10, 8, 6], &[10, 8]), (&[9], &[9])];

        for (ci, (in_heights, mmcs_heights)) in cases.iter().enumerate() {
            let seed = 100 + ci as u64;
            let log_gmh = in_heights[0];

            // FRI inputs: one pseudo-random extension codeword per height (descending), p3's rand order.
            let mut cw_rng = ChaCha20Rng::seed_from_u64(seed ^ 0xF71);
            let inputs: Vec<Vec<Challenge>> = in_heights
                .iter()
                .map(|&lh| RowMajorMatrix::<Challenge>::rand(&mut cw_rng, 1usize << lh, 1).values)
                .collect();

            // Input commitments (for open_input): one hiding commit per height, sharing one ValMmcs.
            // Built ONCE and shared, so both provers read identical stored rows/salts (open draws no rng).
            let input_mmcs = ValMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm.clone()), CAP_HEIGHT, ChaCha20Rng::seed_from_u64(seed ^ 0x1157));
            let mut mat_rng = ChaCha20Rng::seed_from_u64(seed ^ 0x9A7);
            let in_datas: Vec<_> = mmcs_heights
                .iter()
                .map(|&lh| input_mmcs.commit_matrix(RowMajorMatrix::<Val>::rand(&mut mat_rng, 1usize << lh, 3)).1)
                .collect();
            let input_data: Vec<_> = in_datas.iter().map(|d| (d, Vec::<Vec<Challenge>>::new())).collect();

            // Reference p3 `prove_fri` and my streaming fork, both driven from identical fresh challengers
            // over the same inputs + input commitments + salt seed. The two prove calls run inside a
            // SINGLE-THREAD rayon pool so p3's query-PoW grind (`find_map_any`, non-deterministic across
            // threads — verified: p3-vs-p3 disagrees at higher arity) returns the same witness for both
            // from their identical challenger state. Byte-identity is a property of the deterministic
            // transcript→proof transform; the grind's thread-race is p3's and orthogonal to this fork.
            let fri = production_fri(ChallengeMmcs::new(ValMmcs::new(
                MyHash::new(perm.clone()), MyCompress::new(perm.clone()), CAP_HEIGHT, ChaCha20Rng::seed_from_u64(seed),
            )));
            let folding: TwoAdicFriFoldingForMmcs<Val, ValMmcs> = TwoAdicFriFolding(PhantomData);
            let pool = rayon::ThreadPoolBuilder::new().num_threads(1).build().unwrap();
            let (p3_proof, my_proof) = pool.install(|| {
                let mut ch1 = Challenger::new(perm.clone());
                let p3 = prove_fri(&folding, &fri, inputs.clone(), &mut ch1, log_gmh, &input_data, &input_mmcs);
                let mut ch2 = Challenger::new(perm.clone());
                let mut salt_rng = ChaCha20Rng::seed_from_u64(seed);
                let my = stream_prove_fri(&fri, inputs.clone(), &mut ch2, log_gmh, &input_data, &input_mmcs, &mut salt_rng, CAP_HEIGHT)
                    .expect("stream_prove_fri");
                (p3, my)
            });

            // Localize any divergence to a specific FriProof field before the full-bytes assert.
            assert_eq!(
                p3_proof.commit_phase_commits.iter().map(|c| c.as_ref().to_vec()).collect::<Vec<_>>(),
                my_proof.commit_phase_commits.iter().map(|c| c.as_ref().to_vec()).collect::<Vec<_>>(),
                "case {ci}: commit_phase_commits differ"
            );
            assert_eq!(p3_proof.commit_pow_witnesses, my_proof.commit_pow_witnesses, "case {ci}: commit_pow_witnesses differ");
            assert_eq!(p3_proof.final_poly, my_proof.final_poly, "case {ci}: final_poly differ");
            assert_eq!(p3_proof.query_pow_witness, my_proof.query_pow_witness, "case {ci}: query_pow_witness differ");
            for (qi, (pq, mq)) in p3_proof.query_proofs.iter().zip(my_proof.query_proofs.iter()).enumerate() {
                assert_eq!(
                    postcard::to_allocvec(&pq.input_proof).unwrap(),
                    postcard::to_allocvec(&mq.input_proof).unwrap(),
                    "case {ci} query {qi}: input_proof differs"
                );
                for (ri, (ps, ms)) in pq.commit_phase_openings.iter().zip(mq.commit_phase_openings.iter()).enumerate() {
                    assert_eq!(
                        postcard::to_allocvec(ps).unwrap(),
                        postcard::to_allocvec(ms).unwrap(),
                        "case {ci} query {qi} round {ri}: commit_phase_opening differs (log_arity p3={} mine={})",
                        ps.log_arity, ms.log_arity
                    );
                }
                assert_eq!(pq.commit_phase_openings.len(), mq.commit_phase_openings.len(), "case {ci} query {qi}: round count differs");
            }
            let a = postcard::to_allocvec(&p3_proof).unwrap();
            let b = postcard::to_allocvec(&my_proof).unwrap();
            assert_eq!(a, b, "stream_prove_fri != p3 prove_fri at case {ci} in_heights={in_heights:?}");
        }
    }

    /// `StoreMatrix` (the disk-backed `Matrix<Val>` view) reproduces its store byte-for-byte AND drives
    /// p3's whole-LDE open reduction identically to a resident `RowMajorMatrix`. This is the keystone for
    /// the streamed open-at-ζ: (a) exhaustive per-row equality proves the strided column-major reads are
    /// faithful; (b) `rowwise_packed_dot_product` — the exact `Matrix`-generic op p3's `open` runs over the
    /// whole blown-up LDE to build `reduced_openings` — yields identical `Challenge` outputs whether the
    /// matrix is on disk or in RAM (so the reduction can stream the LDE off the heap, byte-identically).
    #[test]
    fn store_matrix_reads_like_p3_reduction() {
        use p3_field::{ExtensionField, PackedFieldExtension};
        use rand::SeedableRng;
        use rand_chacha::ChaCha20Rng;
        use rayon::prelude::*;
        for &(log_h, w, seed) in &[(6usize, 5usize, 1u64), (10, 49, 2), (8, 53, 3), (7, 1291, 4)] {
            let h = 1usize << log_h;
            let mut rng = ChaCha20Rng::seed_from_u64(seed);
            let src = RowMajorMatrix::<Val>::rand(&mut rng, h, w);
            // Write the resident matrix into a column-major store (each column a contiguous segment).
            let store = MmapLdeStore::new(h, w).unwrap();
            for c in 0..w {
                let col: Vec<Val> = (0..h).map(|r| src.values[r * w + c]).collect();
                store.write_col_tile(c, 1, &col);
            }
            let sm = StoreMatrix::new(&store);
            assert_eq!((sm.width(), sm.height()), (w, h));

            // (a) exhaustive row equality — the disk-backed view reproduces every source row.
            for r in 0..h {
                let got: Vec<Val> = sm.row(r).unwrap().into_iter().collect();
                assert_eq!(got.as_slice(), &src.values[r * w..(r + 1) * w], "row {r} differs (h=2^{log_h} w={w})");
            }

            // (b) the exact op p3's `open` runs over the whole LDE — byte-identical disk-view vs resident.
            let alpha: Challenge = RowMajorMatrix::<Challenge>::rand(&mut rng, 1, 1).values[0];
            let packed: Vec<_> = <Challenge as ExtensionField<Val>>::ExtensionPacking::packed_ext_powers_capped(alpha, w).collect();
            let from_store: Vec<Challenge> = sm.rowwise_packed_dot_product::<Challenge>(&packed).collect();
            let from_mem: Vec<Challenge> = src.rowwise_packed_dot_product::<Challenge>(&packed).collect();
            assert_eq!(from_store, from_mem, "rowwise_packed_dot_product differs (h=2^{log_h} w={w})");
        }
    }

    /// Peak resident set (VmHWM) in MiB, from /proc/self/status.
    fn peak_rss_mib() -> u64 {
        std::fs::read_to_string("/proc/self/status")
            .ok()
            .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM")).map(str::to_string))
            .and_then(|l| l.split_whitespace().nth(1).and_then(|v| v.parse::<u64>().ok()))
            .map(|kb| kb / 1024)
            .unwrap_or(0)
    }

    /// RAM bench: stream a large trace's LDE (blowup 16) into the column-major mmap store and
    /// frontier-Merkle it, entirely out-of-core. The commit's LDE (the multi-GB buffer) lives on disk;
    /// access is EXPLICIT and sequential (one column-major write pass + one transposed-block Merkle read),
    /// so under a cgroup cap it completes with BOUNDED RSS — where the Phase 2 allocator thrashed on p3's
    /// blind whole-buffer re-touch. Run under `systemd-run --user --scope -p MemoryMax=<cap>` on a
    /// nodatacow scratch. Tunables: LATTICA_STREAM_LOGH (18), LATTICA_STREAM_W (53), LATTICA_STREAM_CBLK (4).
    ///
    /// MEASURED: 1.66 GiB LDE (h=2^18, w=53) under a 1 GB HARD cap → RSS 1013 MiB, 41 s — vs 233 s for the
    /// row-major-store predecessor at the same RAM bound (5.6x; ~2 sequential passes, w-independent).
    #[test]
    #[ignore = "bench: out-of-core LDE+Merkle RAM (LATTICA_STREAM_LOGH=<n>, LATTICA_SPILL_DIR=<disk>)"]
    fn stream_commit_ram_bench() {
        let env = |k: &str, d: usize| std::env::var(k).ok().and_then(|s| s.parse().ok()).unwrap_or(d);
        let (log_h, w, cblk, added) = (env("LATTICA_STREAM_LOGH", 18), env("LATTICA_STREAM_W", 53), env("LATTICA_STREAM_CBLK", 4), 4usize);
        let (h, big) = (1usize << log_h, 1usize << (log_h + added));
        let shift = <Val as Field>::GENERATOR;
        // the input trace (h×w) is resident — it is LDE/blowup smaller than the LDE this streams to disk.
        let vals: Vec<Val> = (0..h * w).map(|i| Val::new((i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) % 0xFFFF_FFFF_0000_0001)).collect();
        let mat = RowMajorMatrix::new(vals, w);
        let store = MmapLdeStore::new(big, w).unwrap();
        let t0 = std::time::Instant::now();
        stream_coset_lde_to_store(&mat, added, shift, cblk, &store);
        let cap = stream_merkle_cap(&store, CAP_HEIGHT);
        let secs = t0.elapsed().as_secs_f64();
        assert_eq!(cap.len(), 1usize << CAP_HEIGHT.min(log_h + added), "cap has the expected width");
        println!(
            "STREAM-COMMIT-BENCH log_h={log_h} big=2^{} w={w} cblk={cblk} store={}MiB peak_rss={}MiB commit={secs:.1}s",
            log_h + added,
            (big * w * size_of::<Val>()) / (1 << 20),
            peak_rss_mib(),
        );
    }
}
