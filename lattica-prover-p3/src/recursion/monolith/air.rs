use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{Field, PrimeCharacteristicRing, TwoAdicField};
use p3_goldilocks::Goldilocks;

use crate::poseidon2_air::{ext_linear, int_linear, periodic_table, pow7, BLOCK, W};
use crate::recursion::native_fri::Val;

use super::*;

// =================================================================================================
// Phase 4.D — THE MONOLITH: the transcript region + the super-tile region fused into ONE AIR. The transcript
// derives the challenges (α_fri, β_r) + the canonical query indices; each super-tile (block 0 arith + blocks
// 1..5 inline input-Merkle) reads those DERIVED values (carrier / per-round + per-query one-hots / SB) and
// verifies its query AND authenticates its opened value to the committed cap. Region masks: S_TRANS (sponge),
// S_QUERY (super-tiles), S_MERKLE (the super-tile Merkle blocks); Poseidon rounds fire on S_TRANS ∪ S_MERKLE.
// This is the input-Merkle fusion (most of accept-iff-p3::verify); the commit-phase + quotient openings + the
// constraint epilogue are the remaining stages. Validated: the fused AIR proves over the real milestone proof.
// =================================================================================================

#[allow(dead_code)]
pub(crate) struct MonolithAir {
    pub counts: Vec<u8>,
    pub binds: Vec<usize>,
    pub index_binds: Vec<(usize, usize)>,
    pub n_queries: usize,
    pub n_terms: usize,
    /// When true the inner AIR is the NON-degenerate `CounterAir` (`next = cur + 1`): the OOD epilogue uses
    /// the `−1` transition and each opening's Merkle terminal is the index-selected cap entry carried per
    /// super-tile (the counter's 64 cap entries differ per query), rather than ConstAir's single shared cap.
    /// `false` keeps the exact validated ConstAir path (phase4d) untouched.
    pub inner_counter: bool,
    /// When true the inner-proof "public inputs" (challenges, indices, final_poly, caps, pub value) are read
    /// from a WITNESS column window held constant across the whole monolith instead of `public_values()` — so
    /// K instances can be TILED in one aggregator AIR (public inputs are global, witness columns can vary per
    /// tile). The monolith's internal binds (squeeze↦challenge, terminal↦cap, SB↦index, OOD↦pub) pin the
    /// window, so it stays sound; only the block tx-root is public in the aggregator. `false` = pis mode.
    pub column_window: bool,
    /// Number of INNER PROOFS tiled in this AIR (the aggregator). Each instance is a full column-window
    /// monolith (transcript + super-tiles) laid out row-disjoint; the periodic pattern repeats per instance,
    /// the transcript IV / carrier holds become per-instance (p_inst_first / p_inst_last). 1 = single monolith.
    pub k_instances: usize,
    /// When true (aggregator only; requires `column_window`), a global-persistent tx-root fold is fused in:
    /// each instance folds its verified inner public value `pvs[0]` (the `pw(pub_pi)` carrier) into a running
    /// Merkle–Damgård root via two Poseidon blocks in the instance's tail slack — `s_k = merge([DOM,0,0,0],
    /// [pvs0,0,0,0])` then `root = merge(root, s_k)` (IV=0), exactly as `agg_root`/`batch_root`. The root's 4
    /// lanes are the ONLY public inputs (the node-seam block tx-root); every inner datum stays witness.
    pub fold: bool,
    /// When true (requires `fold`), the per-instance s_k is the FULL `batch_joinsplit_air::tx_statement_digest`
    /// — a `FOLD_SK_BLOCKS`-chunk Merkle–Damgård chain `merge(...merge(merge([DOM_TXROOT,0,0,0], anchor), nf₀)
    /// …, tx_binding)` over the join-split statement (anchor ‖ nullifiers ‖ out_cms ‖ [fee,mint,0,0] ‖
    /// tx_binding), read from the inner-pi window at the join-split PI offsets — so the emitted block tx-root is
    /// BYTE-IDENTICAL to `batch_root` (the node consensus seam is unchanged). `false` keeps the 1-value
    /// `s_k = merge([DOM,0,0,0],[pvs0,0,0,0])` fold (the ConstAir aggregator milestone), byte-for-byte.
    pub fold_txstmt: bool,
    /// The inner AIR's constraints as p3 `SymbolicExpression` trees (from `get_symbolic_constraints`). When
    /// NON-EMPTY, the monolith verifies a general MULTI-COLUMN inner data-driven: the OOD epilogue walks these
    /// trees (`eval_symbolic_circuit`) with witnessed selectors (folded·inv_van==quot), the opened-row carrier
    /// widens to `w_inner_f` felts (2·W reduced-opening terms + px-sharing, W-value leaf), and it reuses the
    /// non-constant full-cap + cap-mux machinery. EMPTY keeps the 1-column ConstAir/CounterAir paths (the
    /// hardcoded cleared-form epilogue) byte-for-byte.
    pub constraints: Vec<p3_uni_stark::SymbolicExpression<Val>>,
    /// Inner trace width W (columns) when `constraints` is non-empty; ignored (treated as 1) otherwise.
    pub w_inner_f: usize,
    /// Inner public-value count when `constraints` is non-empty; ignored (treated as 1) otherwise.
    pub n_pub_f: usize,
    /// Inner PERIODIC-column count (symbolic mode). Their values at ζ are verifier-computed publics (a pis
    /// region after the commit caps), consumed by the symbolic evaluator's `Periodic` leaves. 0 for inners
    /// with no periodic columns (Fibonacci/Mul).
    pub n_periodic_f: usize,
    /// HIDING (is_zk=1) mode. When 1, the inner is a ZK proof (HidingFriPcs): the super-tile gains a THIRD
    /// input round (the random-polynomial commitment, prepended as a copy of the trace input-leaf region),
    /// input/quotient leaves are SALTED (preimage = committed_row ‖ 4 salt) and the quotient leaf is the
    /// multi-matrix concat over nqc chunks, the reduced opening spans the merged (public ‖ codewords) rows,
    /// and the OOD epilogue's constraint domain is HALVED (z_h uses cm_rounds−is_zk). 0 = the exact
    /// non-hiding path (every existing test), byte-for-byte. Geometry mirrors `hiding_commit_layout`.
    pub is_zk: usize,
    /// The inner config's Merkle-cap height (caps have 2^cap_height entries; = log2 of the proof's
    /// `MerkleCap.roots().len()`, proof-derivable). The wire/milestone config uses 6; RECURSION-path inner
    /// configs choose SMALL caps — each cap observe absorbs 2^cap_height·4 felts into the transcript, so at
    /// cap 6 the (2+is_zk+cm_rounds) cap absorbs dominate the whole trace (~64 sponge blocks EACH; the
    /// hiding join-split's 16 absorbs alone forced 2^17 rows), while a small cap trades them for slightly
    /// deeper per-query Merkle paths. Every existing construction passes 6 ⇒ all geometry methods reproduce
    /// the old CM_CAP_HEIGHT-const values byte-for-byte.
    pub cap_height: usize,
    /// NARROW-ARITH mode (the deep-tree wrap's W5 size lever). When true the arith super-tile drops the
    /// fold-only helper columns from each DEEP term — the reduced-opening fold is externalized to a narrow-tall
    /// slack region (`src/wrap` `AssembledArithWrapAir`), so `inv(k)`/`apow(k)` are never read. The per-term
    /// stride shrinks 9→5 felts (`[z, pz, px]` kept: `pz` is the epilogue's opening, `z`/`px` feed the wrap's
    /// input binding). `false` = the exact 9-felt/term layout every non-wrap construction uses, byte-for-byte
    /// (the `pinned_constraint_fingerprints` guard covers is_zk 0/1 at false). Set true ONLY by the wrap.
    pub narrow_arith: bool,
}

#[allow(dead_code)]
impl MonolithAir {
    // symbolic (data-driven multi-column) mode iff the inner AIR's constraint trees are provided.
    pub(crate) fn symbolic(&self) -> bool {
        !self.constraints.is_empty()
    }
    // inner trace width W (columns): the provided width in symbolic mode, else 1 (ConstAir/CounterAir).
    pub(crate) fn w_inner(&self) -> usize {
        if self.symbolic() {
            self.w_inner_f
        } else {
            1
        }
    }
    // inner public-value count: the provided count in symbolic mode, else 1.
    pub(crate) fn n_pub(&self) -> usize {
        if self.symbolic() {
            self.n_pub_f
        } else {
            1
        }
    }
    // ---- RUNTIME super-tile geometry (the leaf-block / nqc dimensions vary per inner; the FRI depth stays
    // compile-time). All derived from the SAME formula as `commit_layout`/the compile-time consts, so at
    // leaf_blocks=1/nqc=1 (every current inner: W≤RATE, degree-≤2 ⇒ nqc=1) they EQUAL M_INPUT_TERM/…/M_PERIOD
    // byte-for-byte; a wide inner (W>RATE) grows leaf_blocks and the whole super-tile follows. ----
    // input-Merkle leaf-hash blocks = ceil(W_inner / RATE) (PaddingFreeSponge absorbs RATE felts/block).
    // input-Merkle leaf felt width (the opened row hashed to the leaf). is_zk=0 = the inner trace row (w_inner);
    // is_zk=1 = the COMMITTED row (w_inner ‖ codewords) ‖ salt — the salted hiding leaf (hiding_commit_layout).
    pub(crate) fn input_leaf_felts(&self) -> usize {
        self.w_inner() + if self.is_zk == 1 { HIDING_NUM_CW + HIDING_SALT } else { 0 }
    }
    pub(crate) fn leaf_blocks(&self) -> usize {
        self.input_leaf_felts().div_ceil(RATE)
    }
    // quotient chunks: is_zk=0 derives nqc = n_quot()/2 from the 2·nqc quotient reduced-opening terms. is_zk=1's
    // reduced opening has a different decomposition (random round + merged widths + 2× chunks), so nqc is solved
    // from n_terms = (RAND_PUB+CW) + 2·(W+CW) + nqc·(2+CW). ConstAir/…/Wide nqc=1; Cube nqc=2; join-split nqc=8;
    // hiding ConstAir nqc=4 (2× the is_zk=0 count).
    pub(crate) fn nqc(&self) -> usize {
        if self.is_zk == 1 {
            let random = HIDING_RAND_PUB + HIDING_NUM_CW;
            let trace = self.w_inner() + HIDING_NUM_CW;
            (self.n_terms - random - 2 * trace) / (2 + HIDING_NUM_CW)
        } else {
            self.n_quot() / 2
        }
    }
    // quotient-Merkle leaf felts: is_zk=0 = 2·nqc (the chunk F_p² openings, one matrix); is_zk=1 = the
    // MULTI-MATRIX concat over nqc chunks, each committed row (F_p² ‖ codewords) ‖ salt.
    pub(crate) fn quot_leaf_felts(&self) -> usize {
        if self.is_zk == 1 {
            self.nqc() * (2 + HIDING_NUM_CW + HIDING_SALT)
        } else {
            2 * self.nqc()
        }
    }
    pub(crate) fn quot_leaf_blocks(&self) -> usize {
        self.quot_leaf_felts().div_ceil(RATE)
    }
    // input/quotient Merkle path depth to the cap (= log_global − cap_height), runtime with the FRI depth.
    pub(crate) fn input_depth(&self) -> usize {
        self.lg() - self.cap_height
    }
    // commit round r's Merkle-path depth, runtime with the FRI depth (was the DP_LOG_HEIGHT-pinned cm_depth(r)).
    pub(crate) fn cm_depth_r(&self, r: usize) -> usize {
        cm_depth_at(r, self.lg(), self.cap_height)
    }
    // HIDING random-round leaf felts (is_zk=1): committed random row (RAND_PUB ‖ codewords) ‖ salt.
    pub(crate) fn random_leaf_felts(&self) -> usize {
        HIDING_RAND_PUB + HIDING_NUM_CW + HIDING_SALT
    }
    pub(crate) fn random_leaf_blocks(&self) -> usize {
        self.random_leaf_felts().div_ceil(RATE)
    }
    // HIDING random-round terminal block (is_zk=1): leaf + input_depth path, prepended at M_INPUT_LEAF.
    pub(crate) fn m_random_term(&self) -> usize {
        M_INPUT_LEAF + (self.random_leaf_blocks() - 1) + self.input_depth()
    }
    // first input-(trace-)leaf block: M_INPUT_LEAF (is_zk=0), else after the random-round region (is_zk=1).
    pub(crate) fn m_input_leaf(&self) -> usize {
        if self.is_zk == 1 {
            self.m_random_term() + 1
        } else {
            M_INPUT_LEAF
        }
    }
    pub(crate) fn m_input_term(&self) -> usize {
        self.m_input_leaf() + (self.leaf_blocks() - 1) + self.input_depth()
    }
    pub(crate) fn m_quot_leaf(&self) -> usize {
        self.m_input_term() + 1
    }
    pub(crate) fn m_quot_term(&self) -> usize {
        self.m_quot_leaf() + (self.quot_leaf_blocks() - 1) + self.input_depth()
    }
    // commit-phase leaf felts: the arity-2 fold group (4 base felts); HIDING (is_zk=1) salts it (+SALT), so the
    // salted commit leaf is a 2-block sponge (like the input leaves). is_zk=0 ⇒ 4 felts / 1 block (byte-for-byte).
    pub(crate) fn cm_leaf_felts(&self) -> usize {
        4 + if self.is_zk == 1 { HIDING_SALT } else { 0 }
    }
    pub(crate) fn cm_leaf_blocks(&self) -> usize {
        self.cm_leaf_felts().div_ceil(RATE)
    }
    // commit round r: cm_leaf_blocks leaf-hash blocks then cm_depth_r(r) merges, laid out cumulatively after the
    // quotient terminal.
    pub(crate) fn cm_leaf(&self, r: usize) -> usize {
        let mut blk = self.m_quot_term() + 1;
        for r2 in 0..r {
            blk += (self.cm_leaf_blocks() - 1) + self.cm_depth_r(r2) + 1;
        }
        blk
    }
    pub(crate) fn cm_term(&self, r: usize) -> usize {
        self.cm_leaf(r) + (self.cm_leaf_blocks() - 1) + self.cm_depth_r(r)
    }
    pub(crate) fn m_nblocks(&self) -> usize {
        self.cm_term(self.cm_rounds() - 1) + 1
    }
    pub(crate) fn m_period(&self) -> usize {
        self.m_nblocks() * BLOCK
    }
    // a NON-CONSTANT inner (counter or any symbolic multi-column) needs the full committed cap + the
    // index-selecting cap-mux (per-query cap entries differ), rather than ConstAir's single shared entry.
    pub(crate) fn full_cap(&self) -> bool {
        self.inner_counter || self.symbolic() || self.is_zk == 1
    }
    // symbolic mode witnesses the three Lagrange selectors at ζ (is_first, is_last, inv_van = 3 ext = 6 felts),
    // bound to their ζ-definitions, so the constraint tree is evaluated with selector VALUES (no per-constraint
    // inverse-clearing). Placed after the column window; is_trans = ζ−g^{-1} is computed inline (no column).
    pub(crate) fn sel_base(&self) -> usize {
        self.pw_base() + if self.column_window { self.pis_count() + 2 * self.cm_rounds() } else { 0 }
    }
    pub(crate) fn sel(&self, i: usize) -> usize {
        self.sel_base() + i // 0,1 = is_first; 2,3 = is_last; 4,5 = inv_van
    }
    // quotient DEEP terms = n_terms − the 2·W trace terms.
    pub(crate) fn n_quot(&self) -> usize {
        self.n_terms - 2 * self.w_inner()
    }

    // ---- HIDING (is_zk=1) reduced-opening TERM offsets. is_zk=1 prepends a random round (RAND_PUB+CW terms) and
    // widens every committed matrix by HIDING_NUM_CW codewords; the trace opens at zeta and zeta_next, the
    // quotient at zeta over nqc chunks. is_zk=0 reduces to the legacy [trace(W) | next(W) | quot(2*nqc)] layout,
    // so every offset below is byte-for-byte at is_zk=0. ----
    pub(crate) fn cw(&self) -> usize {
        if self.is_zk == 1 { HIDING_NUM_CW } else { 0 }
    }
    // committed trace-row width (px-bound reduced-opening terms per opening point): W, or W+CW hiding.
    pub(crate) fn trm_committed_w(&self) -> usize {
        self.w_inner() + self.cw()
    }
    // first trace-zeta term index (past the prepended random round when is_zk=1).
    pub(crate) fn trm_trace_base(&self) -> usize {
        if self.is_zk == 1 { HIDING_RAND_PUB + HIDING_NUM_CW } else { 0 }
    }
    pub(crate) fn trm_next_base(&self) -> usize {
        self.trm_trace_base() + self.trm_committed_w()
    }
    pub(crate) fn trm_quot_base(&self) -> usize {
        self.trm_next_base() + self.trm_committed_w()
    }
    // committed quotient-chunk width (2 F_p^2 components + CW codewords hiding).
    pub(crate) fn trm_chunk_w(&self) -> usize {
        2 + self.cw()
    }
    pub(crate) fn trm_trace(&self, c: usize) -> usize {
        self.trm_trace_base() + c
    }
    pub(crate) fn trm_next(&self, c: usize) -> usize {
        self.trm_next_base() + c
    }
    pub(crate) fn trm_quot(&self, i: usize, j: usize) -> usize {
        self.trm_quot_base() + i * self.trm_chunk_w() + j
    }
    // committed random-row width (px-bound prefix of the random leaf preimage): RAND_PUB + CW (is_zk=1).
    pub(crate) fn random_committed_w(&self) -> usize {
        HIDING_RAND_PUB + self.cw()
    }
    // per-chunk stride in the quotient-leaf preimage: committed chunk row (+ salt hiding).
    pub(crate) fn quot_chunk_stride(&self) -> usize {
        self.trm_chunk_w() + if self.is_zk == 1 { HIDING_SALT } else { 0 }
    }
    // HIDING random-round cap pis region (a full cap; the random commitment varies per query so the cap-mux
    // selects cap[index>>input_depth]); placed AFTER the qwt region. is_zk=0 => absent (byte-for-byte).
    pub(crate) fn random_cap_base(&self) -> usize {
        self.qwt_base() + self.qwt_len()
    }
    // opened-row carrier felt c: the authenticated trace-leaf preimage, shared across ζ/ζ_next terms. Width
    // input_leaf_felts() (= w_inner is_zk=0; = W‖codewords‖salt is_zk=1).
    pub(crate) fn ov_c(&self, c: usize) -> usize {
        self.ov() + c
    }
    // HIDING (is_zk=1) random-round leaf-preimage carrier felt c, after the trace-leaf carriers.
    pub(crate) fn ov_random(&self, c: usize) -> usize {
        self.ov() + self.input_leaf_felts() + c
    }
    // width of the random-round carrier region (0 for is_zk=0).
    pub(crate) fn random_carriers(&self) -> usize {
        if self.is_zk == 1 {
            self.random_leaf_felts()
        } else {
            0
        }
    }
    // start of the commit-phase fold-group carriers, after the leaf-preimage carriers. is_zk=0: opened row
    // (w_inner) + quotient (2·nqc = n_quot). is_zk=1: trace-leaf (W‖cw‖salt) + random-leaf + quotient-leaf
    // (nqc multi-matrix ‖ salt) preimages. (input_leaf_felts/quot_leaf_felts equal w_inner/2·nqc at is_zk=0,
    // so this is byte-for-byte there.)
    pub(crate) fn carriers_base(&self) -> usize {
        self.ov() + self.input_leaf_felts() + self.random_carriers() + self.quot_leaf_felts()
    }
    pub(crate) fn nb(&self) -> usize {
        self.binds.len()
    }
    pub(crate) fn ni(&self) -> usize {
        self.index_binds.len()
    }
    // ---- RUNTIME FRI depth, derived from the transcript binds ([α_stark, ζ, α_fri, β_0..β_{cm_rounds−1}] ⇒
    // nb = 3 + cm_rounds). So the whole FRI geometry is per-inner: log_global = cm_rounds + LOG_BLOWUP and the
    // inner's degree_bits = cm_rounds. No field / no constructor change (db=6: nb=9 ⇒ cm_rounds=6, lg=10 —
    // exactly the old DP_LOG_HEIGHT=10 / CM_ROUNDS=6 / M_DEGREE_BITS=6 consts). ----
    pub(crate) fn cm_rounds(&self) -> usize {
        self.nb() - 3
    }
    pub(crate) fn lg(&self) -> usize {
        self.cm_rounds() + LOG_BLOWUP
    }
    // arith-tile column layout (was the QT_ACC/QT_ALPHA/QT_TERMS consts): the DEEP index bits + acc chain scale
    // with log_global, so the per-term region base is runtime.
    pub(crate) fn qt_acc(&self) -> usize {
        QT_DBITS + self.lg()
    }
    pub(crate) fn qt_alpha(&self) -> usize {
        self.qt_acc() + self.lg()
    }
    pub(crate) fn qt_terms(&self) -> usize {
        self.qt_alpha() + 2
    }
    // arith (super-tile block 0) — the QT_* layout. Per-term stride is 9 (full) or 5 (narrow: the fold-only
    // `inv`/`apow` dropped; `[z, pz, px]` kept — see `narrow_arith`).
    pub(crate) fn arith_stride(&self) -> usize {
        if self.narrow_arith {
            5
        } else {
            9
        }
    }
    pub(crate) fn z(&self, k: usize) -> usize {
        self.qt_terms() + self.arith_stride() * k
    }
    pub(crate) fn pz(&self, k: usize) -> usize {
        self.z(k) + 2
    }
    pub(crate) fn px(&self, k: usize) -> usize {
        self.z(k) + 4
    }
    // `inv`/`apow` exist only in FULL mode (the inline fold's helpers); never read when `narrow_arith`.
    pub(crate) fn inv(&self, k: usize) -> usize {
        self.z(k) + 5
    }
    pub(crate) fn apow(&self, k: usize) -> usize {
        self.z(k) + 7
    }
    pub(crate) fn tile_w(&self) -> usize {
        self.qt_terms() + self.arith_stride() * self.n_terms
    }
    // index decomposition (SB) on the super-tile arith head + the fold-bit shift register
    pub(crate) fn sb_x(&self) -> usize {
        self.tile_w()
    }
    pub(crate) fn sb_b(&self, i: usize) -> usize {
        self.sb_x() + 1 + i
    }
    pub(crate) fn sb_q(&self, k: usize) -> usize {
        self.sb_x() + 65 + k
    }
    pub(crate) fn idx_rem(&self) -> usize {
        self.sb_x() + 96
    }
    pub(crate) fn carry(&self) -> usize {
        self.idx_rem() + 1 // α_fri carrier (2 lanes)
    }
    pub(crate) fn ov(&self) -> usize {
        self.carry() + 2 // opened-value carrier (the input-Merkle leaf preimage)
    }
    pub(crate) fn qc(&self, i: usize) -> usize {
        // quotient-leaf-preimage carriers, after the trace-leaf (+ random-leaf when is_zk=1) carriers. is_zk=0:
        // ov + w_inner + i (2·nqc felts, unchanged); is_zk=1: after the trace + random leaf preimages.
        self.ov() + self.input_leaf_felts() + self.random_carriers() + i
    }
    pub(crate) fn cg(&self, r: usize, k: usize) -> usize {
        self.carriers_base() + 4 * r + k // commit-phase group carriers: 6 rounds × 4 felts (the fold group {e_r, sib_r})
    }
    // full-cap mode only: per-super-tile cap-entry carriers (8 openings × 4 felts) — the index-selected cap
    // entry (input, quotient, 6 commit rounds), seeded at the arith head, held to each opening's terminal.
    pub(crate) fn cap_c(&self, g: usize) -> usize {
        self.carriers_base() + 4 * self.cm_rounds() + g // g: input 0..4, quotient 4..8, commit r 8+4r..8+4r+4
    }
    pub(crate) fn n_cap_c(&self) -> usize {
        // cap-entry carriers: input + quotient + cm_rounds commit (2+R), plus the RANDOM round when is_zk=1.
        (2 + self.is_zk + self.cm_rounds()) * 4
    }
    // column-window: the inner-proof "pis" as a witness column window (held constant across the instance) so
    // the monolith can be tiled. Placed after all other columns.
    pub(crate) fn pw_base(&self) -> usize {
        self.carriers_base() + 4 * self.cm_rounds() + if self.full_cap() { self.n_cap_c() } else { 0 }
    }
    pub(crate) fn pw(&self, i: usize) -> usize {
        self.pw_base() + i
    }
    // column-window: the ζ-squaring chain S_1..S_6 (6 ext = 12 felts) held after the pis window. In pis mode
    // ζ is a degree-0 public constant so ζ^(2^6) is inline (degree 0); in column-window ζ is a degree-1 witness,
    // so the epilogue's z_h uses these witnessed squares (each S_{i+1}=S_i², degree 2) to keep the degree bounded.
    pub(crate) fn sch(&self, j: usize) -> usize {
        self.pw_base() + self.pis_count() + j
    }
    // the inner-proof "pis" size: challenges + indices + final_poly + trace/quot caps + pub + commit caps
    // (full caps in counter mode so the cap-mux can select; single entries for ConstAir).
    pub(crate) fn n_periodic(&self) -> usize {
        if self.symbolic() {
            self.n_periodic_f
        } else {
            0
        }
    }
    pub(crate) fn commit_caps_len(&self) -> usize {
        if self.full_cap() {
            (0..self.cm_rounds()).map(|r| self.commit_cap_size(r) * 4).sum::<usize>()
        } else {
            self.cm_rounds() * 4
        }
    }
    // periodic column values at ζ (2 felts each): a pis region AFTER the commit caps (symbolic mode only).
    pub(crate) fn periodic_base(&self) -> usize {
        self.ccap_base() + self.commit_caps_len()
    }
    // quotient recompose weights zps_i (nqc F_p² publics = 2·nqc felts), a pis region AFTER the periodic values.
    // Present ONLY when nqc>1 (nqc=1 recomposes as the single chunk c0+c1·X with implicit weight 1, so no region
    // ⇒ byte-for-byte). Verifier-computed from ζ + the public quotient sub-domains (like the periodic values):
    // zps_i = Π_{j≠i}(s_db−c_j)/(c_i−c_j), consumed by the epilogue's quotient(ζ) = Σ_i zps_i·chunk_i.
    pub(crate) fn qwt_base(&self) -> usize {
        self.periodic_base() + self.n_periodic() * 2
    }
    pub(crate) fn qwt_len(&self) -> usize {
        if (self.symbolic() || self.is_zk == 1) && self.nqc() > 1 {
            2 * self.nqc()
        } else {
            0
        }
    }
    pub(crate) fn pis_count(&self) -> usize {
        self.random_cap_base() + if self.is_zk == 1 { self.cap_stride() } else { 0 }
    }
    // pis cap layout — the FULL cap (2^cap_height entries) for a non-constant inner (so the cap-mux can select
    // cap[index>>shift] by the index bits), a single shared entry (stride 4) for ConstAir. For ConstAir these
    // give the exact current offsets (cap, cap+4, cap+8, cap+9).
    pub(crate) fn cap_stride(&self) -> usize {
        if self.full_cap() {
            (1 << self.cap_height) * 4 // full trace/quotient cap: 2^cap_height entries × 4
        } else {
            4
        }
    }
    pub(crate) fn cap_base(&self) -> usize {
        2 * self.nb() + self.ni() + 2 // after challenges + index felts + final_poly[0]
    }
    pub(crate) fn qcap_base(&self) -> usize {
        self.cap_base() + self.cap_stride()
    }
    pub(crate) fn pub_pi(&self) -> usize {
        self.qcap_base() + self.cap_stride()
    }
    pub(crate) fn ccap_base(&self) -> usize {
        self.pub_pi() + self.n_pub() // after the n_pub inner public values
    }
    // commit-phase round r cap: the codeword folds to height 2^(log_global−(r+1)); its cap has
    // 2^min(cap_height, that) entries, and the selecting index is `index >> ((r+1)+depth_r)`.
    pub(crate) fn commit_bits(&self, r: usize) -> usize {
        core::cmp::min(self.cap_height, self.lg() - (r + 1))
    }
    pub(crate) fn commit_cap_size(&self, r: usize) -> usize {
        1 << self.commit_bits(r)
    }
    pub(crate) fn commit_shift(&self, r: usize) -> usize {
        (r + 1) + (self.lg() - (r + 1)).saturating_sub(self.cap_height)
    }
    pub(crate) fn commit_cap_base(&self, r: usize) -> usize {
        self.ccap_base() + (0..r).map(|r2| self.commit_cap_size(r2) * 4).sum::<usize>()
    }
    pub(crate) fn fused_w(&self) -> usize {
        // sel_base = pw_base (+ column-window window); + 3 witnessed Lagrange selectors (6 felts, symbolic);
        // + the witnessed constraint-fold accumulators (column-window only — see fold_acc / FOLD_CHUNK).
        self.sel_base() + if self.symbolic() { 6 + 2 * self.n_fold_acc() } else { 0 }
    }
    // The α-Horner fold of the inner AIR's C_inner constraints (`folded = folded·α_stark + c_k`) is checked
    // against quotient(ζ) in ONE expression. In COLUMN-WINDOW mode α_stark is a degree-1 witness column (the
    // pi window), so folding all C_inner inline makes that expression degree ≈ base + C_inner (91 for the
    // 81-constraint join-split ⇒ log_nqc 7 ⇒ the quotient can't be committed at log_blowup 4: unsound AND a
    // 2^23-domain RAM blow-up). Fix: CHUNK the fold — witness the running partial fold every FOLD_CHUNK
    // constraints (`fold_acc`) and continue the Horner from that degree-1 column, capping the degree at
    // ≈ base + FOLD_CHUNK (≤ 16). pis-mode folds α as a degree-0 public constant, so it needs no chunking (0
    // accumulators). Verified by `phase8_joinsplit_aggregator_probe` (max_deg / log_nqc).
    pub(crate) const FOLD_CHUNK: usize = 7;
    pub(crate) fn n_fold_acc(&self) -> usize {
        if self.symbolic() && self.column_window {
            self.constraints.len().div_ceil(Self::FOLD_CHUNK).saturating_sub(1) // chunk boundaries = n_chunks − 1
        } else {
            0
        }
    }
    // witnessed constraint-fold accumulator i (F_p² pair), after the 3 Lagrange selectors in the fused region.
    pub(crate) fn fold_acc(&self, i: usize) -> usize {
        self.sel_base() + 6 + 2 * i
    }
    // aggregator fold columns (only when `fold`): 8 Poseidon lanes (the two merge permutations) + 4 lanes for
    // the global-persistent running root, appended after the column-window window.
    pub(crate) fn fold_w(&self) -> usize {
        self.fused_w() + if self.fold { W + 4 } else { 0 }
    }
    pub(crate) fn af_p(&self, i: usize) -> usize {
        self.fused_w() + i // fold Poseidon state lane i (0..W)
    }
    pub(crate) fn af_root(&self, k: usize) -> usize {
        self.fused_w() + W + k // running-root lane k (0..4)
    }
    // The fold blocks live in the instance's tail slack: n_sk_blocks() s_k-chain blocks then 1 ROOT block, the
    // last ending at inst_h−1 (coincident with P_INST_LAST). Old (1-value) fold: 1 s_k + 1 root = 2 blocks.
    // tx_statement fold: FOLD_SK_BLOCKS (7 for join-split) s_k blocks + 1 root = 8.
    pub(crate) fn n_sk_blocks(&self) -> usize {
        if self.fold_txstmt {
            self.fold_chunk_srcs().len()
        } else {
            1
        }
    }
    pub(crate) fn n_fold_blocks(&self) -> usize {
        if self.fold {
            self.n_sk_blocks() + 1
        } else {
            0
        }
    }
    pub(crate) fn fold_sk_block(&self) -> usize {
        self.inst_h() / BLOCK - self.n_fold_blocks()
    }
    // The join-split statement chunks in `tx_statement_digest` fold order — each entry is the 4 inner-pi-window
    // pub-region offsets of a merge chunk (None = a zero lane), matching `batch_joinsplit_air::statement_chunks`
    // EXACTLY: anchor, each nullifier, each out_cm, [fee, mint, 0, 0], tx_binding. Only used when fold_txstmt.
    pub(crate) fn fold_chunk_srcs(&self) -> Vec<[Option<usize>; 4]> {
        use crate::joinsplit_air::{PI_ANCHOR, PI_FEE, PI_MINT, PI_NF, PI_OUTCM, PI_TXBIND};
        use crate::spend_common::{DIGEST, M_OUT, N_IN};
        let mut v: Vec<[Option<usize>; 4]> = Vec::new();
        v.push(core::array::from_fn(|k| Some(PI_ANCHOR + k)));
        for i in 0..N_IN {
            v.push(core::array::from_fn(|k| Some(PI_NF + i * DIGEST + k)));
        }
        for j in 0..M_OUT {
            v.push(core::array::from_fn(|k| Some(PI_OUTCM + j * DIGEST + k)));
        }
        v.push([Some(PI_FEE), Some(PI_MINT), None, None]);
        v.push(core::array::from_fn(|k| Some(PI_TXBIND + k)));
        v
    }
    // Merkle columns overlay the arith Poseidon lanes on the Merkle rows (disjoint rows).
    pub(crate) fn m_sib(&self) -> usize {
        8
    }
    pub(crate) fn m_bit(&self) -> usize {
        12
    }
    // periodic indices
    pub(crate) fn p_round(&self, r: usize) -> usize {
        FT_BIND_START + self.nb() + self.ni() + r
    }
    pub(crate) fn p_query(&self, q: usize) -> usize {
        FT_BIND_START + self.nb() + self.ni() + self.cm_rounds() + q // after the cm_rounds P_ROUND one-hots
    }
    pub(crate) fn m_base(&self) -> usize {
        FT_BIND_START + self.nb() + self.ni() + self.cm_rounds() + self.n_queries
    }
    pub(crate) fn m_tf(&self) -> usize {
        self.m_base()
    }
    pub(crate) fn m_tl(&self) -> usize {
        self.m_base() + 1
    }
    pub(crate) fn m_leaf(&self) -> usize {
        self.m_base() + 2
    }
    pub(crate) fn m_term(&self) -> usize {
        self.m_base() + 3
    }
    pub(crate) fn s_trans(&self) -> usize {
        self.m_base() + 4
    }
    pub(crate) fn s_query(&self) -> usize {
        self.m_base() + 5
    }
    pub(crate) fn s_merkle(&self) -> usize {
        self.m_base() + 6
    }
    pub(crate) fn s_trans_trans(&self) -> usize {
        self.m_base() + 7
    }
    pub(crate) fn p_st_last(&self) -> usize {
        self.m_base() + 8
    }
    pub(crate) fn q_leaf(&self) -> usize {
        self.m_base() + 9 // quotient-Merkle leaf head
    }
    pub(crate) fn q_term(&self) -> usize {
        self.m_base() + 10 // quotient-Merkle terminal
    }
    pub(crate) fn c_leaf(&self, r: usize) -> usize {
        self.m_base() + 11 + r // commit-phase leaf-hash one-hots (6)
    }
    pub(crate) fn c_term(&self, r: usize) -> usize {
        self.m_base() + 11 + self.cm_rounds() + r // commit-phase terminal one-hots (cm_rounds)
    }
    pub(crate) fn tr(&self) -> usize {
        self.counts.len().next_power_of_two() * BLOCK
    }
    pub(crate) fn inst_h(&self) -> usize {
        (self.tr() + self.n_queries * self.m_period()).next_power_of_two() // one inner-proof instance
    }
    pub(crate) fn height(&self) -> usize {
        self.k_instances * self.inst_h() // K instances tiled row-disjoint
    }
    // per-instance first/last row one-hots (appended after the single-instance periodic columns): the
    // transcript IV fires at each instance's first row; the carrier holds reset at each instance's last row.
    // fold periodic selectors (only when `fold`), appended in single_periodic after the commit terminals so
    // they tile per-instance: active on both fold blocks (Poseidon step gate), and the four block-boundary
    // one-hots (SK seed / s_k link / ROOT-in / ROOT update).
    // multi-block input-leaf periodic one-hots (appended after the commit terminals, before the fold/inst
    // selectors): the subsequent-block absorb heads + the leaf-internal capacity-carry boundary + the
    // short-final rate-carry boundary. ALL absent (0 columns) at leaf_blocks=1 (W≤RATE), so the milestone
    // periodic layout is byte-for-byte and every downstream index (fold/inst) is unshifted.
    pub(crate) fn leaf_absorb_base(&self) -> usize {
        self.c_term(self.cm_rounds() - 1) + 1
    }
    pub(crate) fn n_in_absorb(&self) -> usize {
        if self.leaf_blocks() > 1 {
            (self.leaf_blocks() - 1) // ia_in(1..leaf_blocks): absorb heads
                + 1 // in_boundary: leaf-internal capacity carry (union)
                + usize::from(self.input_leaf_felts() % RATE != 0) // in_last_carry: short-final rate carry
        } else {
            0
        }
    }
    // absorb head for input-leaf block b (b in 1..leaf_blocks): block (M_INPUT_LEAF+b) first row.
    pub(crate) fn ia_in(&self, b: usize) -> usize {
        self.leaf_absorb_base() + (b - 1)
    }
    // capacity-carry one-hot at the leaf-internal block boundaries (union of blocks M_INPUT_LEAF..+leaf_blocks−2 last rows).
    pub(crate) fn in_boundary(&self) -> usize {
        self.leaf_absorb_base() + (self.leaf_blocks() - 1)
    }
    // short-final rate-carry one-hot: the boundary INTO the short final block (only when W % RATE ≠ 0).
    pub(crate) fn in_last_carry(&self) -> usize {
        self.in_boundary() + 1
    }
    // MULTI-BLOCK QUOTIENT leaf one-hots (2·nqc > RATE), appended after the input-leaf ones — same machinery
    // as ia_in/in_boundary/in_last_carry but for the quotient-Merkle leaf (blocks m_quot_leaf..+quot_leaf_blocks).
    // All absent (0 columns) at quot_leaf_blocks=1 (2·nqc ≤ RATE), so nqc≤2 is byte-for-byte.
    pub(crate) fn quot_absorb_base(&self) -> usize {
        self.leaf_absorb_base() + self.n_in_absorb()
    }
    pub(crate) fn n_quot_absorb(&self) -> usize {
        if self.quot_leaf_blocks() > 1 {
            (self.quot_leaf_blocks() - 1) // iq_(1..quot_leaf_blocks): absorb heads
                + 1 // q_boundary: capacity carry (union)
                + usize::from(self.quot_leaf_felts() % RATE != 0) // q_last_carry: short-final
        } else {
            0
        }
    }
    // absorb head for quotient-leaf block b (b in 1..quot_leaf_blocks): block (m_quot_leaf+b) first row.
    pub(crate) fn iq_(&self, b: usize) -> usize {
        self.quot_absorb_base() + (b - 1)
    }
    pub(crate) fn q_boundary(&self) -> usize {
        self.quot_absorb_base() + (self.quot_leaf_blocks() - 1)
    }
    pub(crate) fn q_last_carry(&self) -> usize {
        self.q_boundary() + 1
    }
    // base of the fold selectors (shifted past BOTH the input- and quotient-leaf absorb one-hots).
    pub(crate) fn fold_base(&self) -> usize {
        self.quot_absorb_base() + self.n_quot_absorb()
    }
    pub(crate) fn n_fold_p(&self) -> usize {
        if !self.fold {
            0
        } else if self.fold_txstmt {
            5 + self.n_sk_blocks() // active + n_sk s_k-block first-rows + sklink + sklast + rootin + rootupd
        } else {
            5 // active + sk (block-0 seed) + sklast + rootin + rootupd
        }
    }
    pub(crate) fn p_fold_active(&self) -> usize {
        self.fold_base()
    }
    // 1-value-fold block-0 seed (fold_txstmt=false); in tx_statement mode block 0's first row is p_fold_first(0).
    pub(crate) fn p_fold_sk(&self) -> usize {
        self.fold_base() + 1
    }
    // tx_statement mode: per-s_k-block first-row one-hot (chunk injection; b=0 also seeds [DOM,0,0,0]).
    pub(crate) fn p_fold_first(&self, b: usize) -> usize {
        self.fold_base() + 1 + b // b in 0..n_sk_blocks()
    }
    // tx_statement mode: the union one-hot over the s_k-chain internal boundaries (last rows of s_k blocks
    // 0..n_sk−2), carrying each merge output → the next block's rate-low.
    pub(crate) fn p_fold_sklink(&self) -> usize {
        self.fold_base() + 1 + self.n_sk_blocks()
    }
    // sklast/rootin/rootupd shift past the per-block first-rows in tx_statement mode; unchanged (base+2..4) in
    // 1-value mode.
    fn fold_tail_base(&self) -> usize {
        self.fold_base() + if self.fold_txstmt { 2 + self.n_sk_blocks() } else { 2 }
    }
    pub(crate) fn p_fold_sklast(&self) -> usize {
        self.fold_tail_base()
    }
    pub(crate) fn p_fold_rootin(&self) -> usize {
        self.fold_tail_base() + 1
    }
    pub(crate) fn p_fold_rootupd(&self) -> usize {
        self.fold_tail_base() + 2
    }
    // ---- HIDING random-round leaf periodic selectors (is_zk=1): the random-polynomial commitment opens as a
    // THIRD input round, laid out as a salted leaf (blocks M_INPUT_LEAF..) + input_depth path, mirroring the
    // trace leaf. Appended AFTER the fold selectors so is_zk=0 keeps p_inst_first/p_inst_last byte-for-byte. ----
    pub(crate) fn random_absorb_base(&self) -> usize {
        self.fold_base() + self.n_fold_p()
    }
    pub(crate) fn n_random_periodic(&self) -> usize {
        if self.is_zk == 1 {
            2 // p_random_leaf (head) + p_random_term (terminal)
                + (self.random_leaf_blocks() - 1) // subsequent-block absorb heads
                + usize::from(self.random_leaf_blocks() > 1) // capacity-carry boundary
                + usize::from(self.random_leaf_blocks() > 1 && self.random_leaf_felts() % RATE != 0) // short-final
        } else {
            0
        }
    }
    pub(crate) fn p_random_leaf(&self) -> usize {
        self.random_absorb_base()
    }
    pub(crate) fn p_random_term(&self) -> usize {
        self.random_absorb_base() + 1
    }
    pub(crate) fn p_random_absorb(&self, b: usize) -> usize {
        self.random_absorb_base() + 2 + (b - 1)
    }
    pub(crate) fn p_random_boundary(&self) -> usize {
        self.random_absorb_base() + 2 + (self.random_leaf_blocks() - 1)
    }
    pub(crate) fn p_random_last_carry(&self) -> usize {
        self.p_random_boundary() + 1
    }
    // HIDING commit-leaf internal boundary (is_zk=1, 2-block salted commit leaf): a capacity-carry one-hot at
    // each round's block-0→block-1 boundary. Appended after the random region. Absent at is_zk=0 (byte-for-byte).
    pub(crate) fn commit_absorb_base(&self) -> usize {
        self.random_absorb_base() + self.n_random_periodic()
    }
    pub(crate) fn n_commit_absorb(&self) -> usize {
        if self.is_zk == 1 && self.cm_leaf_blocks() > 1 {
            1 // a single UNION capacity-carry one-hot over every round's commit-leaf block-0→block-1 boundary
        } else {
            0
        }
    }
    pub(crate) fn c_bnd(&self) -> usize {
        self.commit_absorb_base()
    }
    pub(crate) fn p_inst_first(&self) -> usize {
        self.commit_absorb_base() + self.n_commit_absorb()
    }
    pub(crate) fn p_inst_last(&self) -> usize {
        self.p_inst_first() + 1
    }
    pub(crate) fn periodic(&self) -> Vec<Vec<Val>> {
        // build the single-instance pattern, then tile it K× + append the per-instance first/last one-hots.
        let single = self.single_periodic();
        let inst_h = self.inst_h();
        let k = self.k_instances;
        let h = k * inst_h;
        let mut cols: Vec<Vec<Val>> = single
            .iter()
            .map(|c| {
                let mut tiled = Vec::with_capacity(h);
                for _ in 0..k {
                    tiled.extend_from_slice(c);
                }
                tiled
            })
            .collect();
        let mut first = vec![Val::ZERO; h];
        let mut last = vec![Val::ZERO; h];
        for i in 0..k {
            first[i * inst_h] = Val::ONE;
            last[i * inst_h + inst_h - 1] = Val::ONE;
        }
        cols.push(first); // P_INST_FIRST
        cols.push(last); // P_INST_LAST
        cols
    }
    pub(crate) fn single_periodic(&self) -> Vec<Vec<Val>> {
        let h = self.inst_h();
        let tr = self.tr();
        let nb_used = self.counts.len();
        let count_of = |b: usize| -> Val { if b < nb_used { Val::from_u64(self.counts[b] as u64) } else { Val::ZERO } };
        let mut cols = periodic_table(); // 11 round
        let mut block_last = vec![Val::ZERO; h];
        for blk in 0..(h / BLOCK) {
            block_last[blk * BLOCK + BLOCK - 1] = Val::ONE;
        }
        cols.push(block_last); // P_BLOCK_LAST (every block of the whole trace)
        let mut count = vec![Val::ZERO; h];
        let mut count_next = vec![Val::ZERO; h];
        let mut is_sq_next = vec![Val::ZERO; h];
        for r in 0..tr {
            let b = r / BLOCK;
            count[r] = count_of(b);
            count_next[r] = count_of(b + 1);
            is_sq_next[r] = if (b + 1 >= nb_used) || self.counts[b + 1] == 0 { Val::ONE } else { Val::ZERO };
        }
        cols.push(count);
        cols.push(count_next);
        cols.push(is_sq_next);
        for &blk in &self.binds {
            let mut col = vec![Val::ZERO; h];
            col[blk * BLOCK + BLOCK - 1] = Val::ONE;
            cols.push(col);
        }
        for &(blk, _lane) in &self.index_binds {
            let mut col = vec![Val::ZERO; h];
            col[blk * BLOCK + BLOCK - 1] = Val::ONE;
            cols.push(col);
        }
        let mp = self.m_period();
        let st_off = |q: usize, row: usize| tr + q * mp + row;
        // P_ROUND_0..cm_rounds−1 — block 0 rows 0..cm_rounds of every super-tile (the FRI-fold rows)
        for r in 0..self.cm_rounds() {
            let mut col = vec![Val::ZERO; h];
            for q in 0..self.n_queries {
                col[st_off(q, r)] = Val::ONE;
            }
            cols.push(col);
        }
        // P_QUERY_q — block 0 row 0 of super-tile q (selects the q-th public index felt)
        for q in 0..self.n_queries {
            let mut col = vec![Val::ZERO; h];
            col[st_off(q, 0)] = Val::ONE;
            cols.push(col);
        }
        let tiled = |row: usize| -> Vec<Val> {
            let mut col = vec![Val::ZERO; h];
            for q in 0..self.n_queries {
                col[st_off(q, row)] = Val::ONE;
            }
            col
        };
        cols.push(tiled(0)); // M_TF (arith head)
        cols.push(tiled(self.cm_rounds())); // M_TL (folded_eval / accept row: E_{cm_rounds})
        cols.push(tiled(self.m_input_leaf() * BLOCK)); // M_LEAF (trace leaf-hash head; past the random round when is_zk=1)
        cols.push(tiled(self.m_input_term() * BLOCK + BLOCK - 1)); // M_TERM
        let mut s_trans = vec![Val::ZERO; h];
        for r in 0..tr {
            s_trans[r] = Val::ONE;
        }
        cols.push(s_trans);
        let mut s_query = vec![Val::ZERO; h];
        let mut s_merkle = vec![Val::ZERO; h];
        for q in 0..self.n_queries {
            for r in 0..mp {
                s_query[st_off(q, r)] = Val::ONE;
                if r >= BLOCK {
                    s_merkle[st_off(q, r)] = Val::ONE; // Merkle blocks 1..(nblocks−1) (not the arith block 0)
                }
            }
        }
        cols.push(s_query);
        cols.push(s_merkle);
        let mut s_trans_trans = vec![Val::ZERO; h];
        for r in 0..tr.saturating_sub(1) {
            s_trans_trans[r] = Val::ONE;
        }
        cols.push(s_trans_trans);
        cols.push(tiled(mp - 1)); // P_ST_LAST (super-tile carrier boundary)
        cols.push(tiled(self.m_quot_leaf() * BLOCK)); // Q_LEAF
        cols.push(tiled(self.m_quot_term() * BLOCK + BLOCK - 1)); // Q_TERM
        for r in 0..self.cm_rounds() {
            cols.push(tiled(self.cm_leaf(r) * BLOCK)); // C_LEAF_r (commit-phase leaf-hash head)
        }
        for r in 0..self.cm_rounds() {
            cols.push(tiled(self.cm_term(r) * BLOCK + BLOCK - 1)); // C_TERM_r (commit-phase terminal)
        }
        // MULTI-BLOCK input-leaf one-hots (only leaf_blocks>1): absorb heads for blocks 1..leaf_blocks, the
        // leaf-internal capacity-carry boundary (union), and — if the final block is short — its rate-carry
        // boundary. Absent at leaf_blocks=1, so the milestone layout is unchanged.
        if self.leaf_blocks() > 1 {
            let ml = self.m_input_leaf(); // trace leaf-hash head block (past the random round when is_zk=1)
            for b in 1..self.leaf_blocks() {
                cols.push(tiled((ml + b) * BLOCK)); // ia_in(b): block (m_input_leaf+b) head
            }
            let mut boundary = vec![Val::ZERO; h];
            for q in 0..self.n_queries {
                for b in 1..self.leaf_blocks() {
                    boundary[st_off(q, (ml + b) * BLOCK - 1)] = Val::ONE; // block (m_input_leaf+b−1) last row
                }
            }
            cols.push(boundary); // in_boundary
            if self.input_leaf_felts() % RATE != 0 {
                cols.push(tiled((ml + self.leaf_blocks() - 1) * BLOCK - 1)); // in_last_carry (into the short final block)
            }
        }
        // MULTI-BLOCK quotient-leaf one-hots (only quot_leaf_blocks>1), mirroring the input-leaf ones.
        if self.quot_leaf_blocks() > 1 {
            for b in 1..self.quot_leaf_blocks() {
                cols.push(tiled((self.m_quot_leaf() + b) * BLOCK)); // iq_(b): block (m_quot_leaf+b) head
            }
            let mut qboundary = vec![Val::ZERO; h];
            for q in 0..self.n_queries {
                for b in 1..self.quot_leaf_blocks() {
                    qboundary[st_off(q, (self.m_quot_leaf() + b) * BLOCK - 1)] = Val::ONE; // block (m_quot_leaf+b−1) last row
                }
            }
            cols.push(qboundary); // q_boundary
            if self.quot_leaf_felts() % RATE != 0 {
                cols.push(tiled((self.m_quot_leaf() + self.quot_leaf_blocks() - 1) * BLOCK - 1)); // q_last_carry
            }
        }
        if self.fold && !self.fold_txstmt {
            // 1-value fold: two blocks in the tail slack — SK block (fb) then ROOT block (fb+1, ends at inst_h-1).
            let fb = self.fold_sk_block();
            let mut active = vec![Val::ZERO; h];
            let mut sk = vec![Val::ZERO; h];
            let mut sklast = vec![Val::ZERO; h];
            let mut rootin = vec![Val::ZERO; h];
            let mut rootupd = vec![Val::ZERO; h];
            for r in 0..(2 * BLOCK) {
                active[fb * BLOCK + r] = Val::ONE; // both fold blocks (Poseidon step gate)
            }
            sk[fb * BLOCK] = Val::ONE; // SK block first row (DOM/pvs0 seed)
            sklast[fb * BLOCK + BLOCK - 1] = Val::ONE; // SK block last row (s_k → ROOT rate-high)
            rootin[(fb + 1) * BLOCK] = Val::ONE; // ROOT block first row (rate-low = running root)
            rootupd[(fb + 1) * BLOCK + BLOCK - 1] = Val::ONE; // ROOT block last row (root update)
            cols.push(active);
            cols.push(sk);
            cols.push(sklast);
            cols.push(rootin);
            cols.push(rootupd);
        } else if self.fold {
            // tx_statement fold: n_sk s_k-chain blocks (each merge(prev, chunk_b)) then 1 ROOT block, in the tail
            // slack. Order (matching p_fold_* indices): active, first(0..n_sk), sklink, sklast, rootin, rootupd.
            let fb = self.fold_sk_block();
            let n_sk = self.n_sk_blocks();
            let mut active = vec![Val::ZERO; h];
            for r in 0..((n_sk + 1) * BLOCK) {
                active[fb * BLOCK + r] = Val::ONE; // all n_sk+1 fold blocks (Poseidon step gate)
            }
            cols.push(active);
            for b in 0..n_sk {
                let mut first = vec![Val::ZERO; h];
                first[(fb + b) * BLOCK] = Val::ONE; // s_k block b first row (chunk inject; b=0 also seeds DOM)
                cols.push(first);
            }
            let mut sklink = vec![Val::ZERO; h];
            for b in 0..(n_sk - 1) {
                sklink[(fb + b) * BLOCK + BLOCK - 1] = Val::ONE; // block b output → block b+1 rate-low
            }
            cols.push(sklink);
            let mut sklast = vec![Val::ZERO; h];
            sklast[(fb + n_sk - 1) * BLOCK + BLOCK - 1] = Val::ONE; // last s_k block output (s_k) → ROOT rate-high
            cols.push(sklast);
            let mut rootin = vec![Val::ZERO; h];
            rootin[(fb + n_sk) * BLOCK] = Val::ONE; // ROOT block first row (rate-low = running root)
            cols.push(rootin);
            let mut rootupd = vec![Val::ZERO; h];
            rootupd[(fb + n_sk) * BLOCK + BLOCK - 1] = Val::ONE; // ROOT block last row (root update)
            cols.push(rootupd);
        }
        // HIDING random-round leaf one-hots (is_zk=1): the random-polynomial commitment's salted leaf (blocks
        // M_INPUT_LEAF..+random_leaf_blocks) + input_depth path + terminal, mirroring the trace leaf. Appended
        // AFTER the fold selectors (random_absorb_base = fold_base + n_fold_p); absent at is_zk=0 (byte-for-byte).
        if self.is_zk == 1 {
            cols.push(tiled(M_INPUT_LEAF * BLOCK)); // p_random_leaf (random leaf-hash head)
            cols.push(tiled(self.m_random_term() * BLOCK + BLOCK - 1)); // p_random_term (random terminal)
            if self.random_leaf_blocks() > 1 {
                for b in 1..self.random_leaf_blocks() {
                    cols.push(tiled((M_INPUT_LEAF + b) * BLOCK)); // p_random_absorb(b)
                }
                let mut rboundary = vec![Val::ZERO; h];
                for q in 0..self.n_queries {
                    for b in 1..self.random_leaf_blocks() {
                        rboundary[st_off(q, (M_INPUT_LEAF + b) * BLOCK - 1)] = Val::ONE;
                    }
                }
                cols.push(rboundary); // p_random_boundary
                if self.random_leaf_felts() % RATE != 0 {
                    cols.push(tiled((M_INPUT_LEAF + self.random_leaf_blocks() - 1) * BLOCK - 1)); // p_random_last_carry
                }
            }
        }
        // HIDING commit-leaf internal boundary (is_zk=1, 2-block salted commit leaf): a single UNION one-hot over
        // every round's block-0→block-1 boundary (block cm_leaf(r)'s last row) — the capacity carry.
        if self.is_zk == 1 && self.cm_leaf_blocks() > 1 {
            let mut cbnd = vec![Val::ZERO; h];
            for q in 0..self.n_queries {
                for r in 0..self.cm_rounds() {
                    cbnd[st_off(q, (self.cm_leaf(r) + 1) * BLOCK - 1)] = Val::ONE;
                }
            }
            cols.push(cbnd); // c_bnd (union)
        }
        cols
    }
}

impl BaseAir<Goldilocks> for MonolithAir {
    fn width(&self) -> usize {
        self.fold_w()
    }
    fn num_public_values(&self) -> usize {
        // fold (aggregator): only the block tx-root (4 lanes) is public. column-window (K=1): nothing public —
        // the inner-proof pis live in witness columns. Otherwise the full inner-proof pis.
        if self.fold {
            4
        } else if self.column_window {
            0
        } else {
            self.pis_count()
        }
    }
    fn num_periodic_columns(&self) -> usize {
        self.p_inst_last() + 1 // single-instance columns (+ fold selectors) + P_INST_FIRST + P_INST_LAST
    }
    fn periodic_columns(&self) -> Vec<Vec<Goldilocks>> {
        self.periodic()
    }
}

/// The B/C/I regions the deep-tree **wrap** swaps for lookups (`docs/wrap-construction-plan.md`). `InlineBci`
/// = the monolith's inline high-degree forms (BYTE-IDENTICAL — guarded by the `pinned_constraint_fingerprints`
/// pins); the wrap supplies a lookup form. Additive: `MonolithAir::eval` = `eval_bci` with `InlineBci`, so the
/// audited monolith constraints are unchanged. RESEARCH plumbing; the lookup strategy is `--features lookup`.
pub(crate) trait MonolithBci<AB: AirBuilder<F = Goldilocks>> {
    /// **I (cap-mux):** bind each opening's cap carrier `cap_c[cg_off+k]` (k=0..4) to the index-selected
    /// committed cap entry `pis[cbase + (index>>shift)·4 + k]`, gated by the arith-head `tf`. `openings` =
    /// `(cg_off, shift, bits, cbase)` per opening (trace, quotient, `cm_rounds` commit rounds, [random]).
    fn emit_capmux(
        &self,
        builder: &mut AB,
        air: &MonolithAir,
        cur: &[AB::Expr],
        pis: &[AB::Expr],
        one: &AB::Expr,
        tf: &AB::Expr,
        openings: &[(usize, usize, usize, usize)],
    );

    /// **B/C (OOD epilogue fold):** α-Horner-fold the inner constraints (`c_k = eval_symbolic_circuit(...)`,
    /// chunked via `fold_acc` in column-window mode) and check `folded·inv_van == quot(ζ)`, gated by `tf`.
    /// The `local/next/pubs/periodic` openings + `is_first/is_last/is_trans` selectors are verifier-derived
    /// (the reused H region); only the fold + check (the degree crux) vary by strategy.
    #[allow(clippy::too_many_arguments)]
    fn emit_epilogue(
        &self,
        builder: &mut AB,
        air: &MonolithAir,
        cur: &[AB::Expr],
        tf: &AB::Expr,
        w: &AB::Expr,
        local: &[(AB::Expr, AB::Expr)],
        next: &[(AB::Expr, AB::Expr)],
        pubs: &[(AB::Expr, AB::Expr)],
        periodic: &[(AB::Expr, AB::Expr)],
        is_first: &(AB::Expr, AB::Expr),
        is_last: &(AB::Expr, AB::Expr),
        is_trans: &(AB::Expr, AB::Expr),
        alpha_stark: &(AB::Expr, AB::Expr),
        inv_van: &(AB::Expr, AB::Expr),
        quot: &(AB::Expr, AB::Expr),
    );

    /// **Super-tile arith (DEEP reduced-opening fold):** the FRI DEEP query check — decode the index bits into
    /// the query point `x = GEN·Π g^bit`, bind α_fri, and fold `ro = Σ α^k·(pz_k − px_k)/(z_k − x)`, checking
    /// `QT_E == ro`, gated by `tf`. The inline form lays every one of the `n_terms` terms in COLUMNS
    /// (`9·n_terms`, the dominant inner-scaling width); a narrow-tall strategy instead witnesses `ro` from slack
    /// ROWS (the deep-tree size lever — see `wrap::DeepFoldAir`).
    fn emit_arith(&self, builder: &mut AB, air: &MonolithAir, cur: &[AB::Expr], tf: &AB::Expr, one: &AB::Expr, w: &AB::Expr);
}

/// The monolith's inline B/C/I — the cap-mux as a degree-`bits` product-mux (the current behavior, kept
/// byte-identical). The wrap replaces this with a LogUp (degree 3, width 3, `--features lookup`).
pub(crate) struct InlineBci;

/// The super-tile arith **point derivation** (always inline — cheap, non-inner-scaling): decode the DEEP index
/// bits into the query point `x = GEN·Π g^bit` (the qt_acc chain) and bind α_fri (`qt_alpha == carry`), gated
/// by `tf`. Returns `(x, alpha)` for the reduced-opening fold. Shared by `InlineBci::emit_arith` and the
/// narrow-tall wrap strategy, which reuses the SAME sound point but witnesses `ro` from slack ROWS instead of
/// the `9·n_terms` inline COLUMNS.
pub(crate) fn arith_point<AB: AirBuilder<F = Goldilocks>>(
    builder: &mut AB,
    air: &MonolithAir,
    cur: &[AB::Expr],
    tf: &AB::Expr,
    one: &AB::Expr,
) -> (AB::Expr, (AB::Expr, AB::Expr)) {
    let g = Goldilocks::two_adic_generator(air.lg());
    let carry = air.carry();
    for i in 0..air.lg() {
        let b = cur[QT_DBITS + i].clone();
        builder.assert_zero(tf.clone() * (b.clone() * (one.clone() - b)));
    }
    let mut prev = one.clone();
    for i in 0..air.lg() {
        let ci = AB::Expr::from(g.exp_power_of_2(air.lg() - 1 - i));
        let factor = one.clone() + cur[QT_DBITS + i].clone() * (ci - one.clone());
        builder.assert_zero(tf.clone() * (cur[air.qt_acc() + i].clone() - prev * factor));
        prev = cur[air.qt_acc() + i].clone();
    }
    let x = AB::Expr::from(<Goldilocks as Field>::GENERATOR) * cur[air.qt_acc() + air.lg() - 1].clone();
    // air.qt_alpha() bound to the carried α_fri
    builder.assert_zero(tf.clone() * (cur[air.qt_alpha()].clone() - cur[carry].clone()));
    builder.assert_zero(tf.clone() * (cur[air.qt_alpha() + 1].clone() - cur[carry + 1].clone()));
    let alpha = (cur[air.qt_alpha()].clone(), cur[air.qt_alpha() + 1].clone());
    (x, alpha)
}

/// Bind the super-tile arith head's committed reduced opening `QT_E` to `ro` (the DEEP fold value), gated by
/// `tf` — the O(1) output check. `InlineBci` passes `ro` computed from the `9·n_terms` inline columns; a
/// narrow-tall strategy passes an `ro` witnessed from slack rows. Same binding either way.
pub(crate) fn bind_reduced_opening<AB: AirBuilder<F = Goldilocks>>(builder: &mut AB, cur: &[AB::Expr], tf: &AB::Expr, ro: (AB::Expr, AB::Expr)) {
    builder.assert_zero(tf.clone() * (cur[QT_E].clone() - ro.0));
    builder.assert_zero(tf.clone() * (cur[QT_E + 1].clone() - ro.1));
}

impl<AB: AirBuilder<F = Goldilocks>> MonolithBci<AB> for InlineBci {
    fn emit_capmux(
        &self,
        builder: &mut AB,
        air: &MonolithAir,
        cur: &[AB::Expr],
        pis: &[AB::Expr],
        one: &AB::Expr,
        tf: &AB::Expr,
        openings: &[(usize, usize, usize, usize)],
    ) {
        for &(cg_off, shift, bits, cbase) in openings {
            for k in 0..4 {
                let mut acc = AB::Expr::ZERO;
                for e in 0..(1usize << bits) {
                    let mut sel = AB::Expr::ONE;
                    for j in 0..bits {
                        let b = cur[air.sb_b(shift + j)].clone();
                        sel = sel * if (e >> j) & 1 == 1 { b } else { one.clone() - b };
                    }
                    acc = acc + sel * pis[cbase + e * 4 + k].clone();
                }
                builder.assert_zero(tf.clone() * (cur[air.cap_c(cg_off + k)].clone() - acc));
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_epilogue(
        &self,
        builder: &mut AB,
        air: &MonolithAir,
        cur: &[AB::Expr],
        tf: &AB::Expr,
        w: &AB::Expr,
        local: &[(AB::Expr, AB::Expr)],
        next: &[(AB::Expr, AB::Expr)],
        pubs: &[(AB::Expr, AB::Expr)],
        periodic: &[(AB::Expr, AB::Expr)],
        is_first: &(AB::Expr, AB::Expr),
        is_last: &(AB::Expr, AB::Expr),
        is_trans: &(AB::Expr, AB::Expr),
        alpha_stark: &(AB::Expr, AB::Expr),
        inv_van: &(AB::Expr, AB::Expr),
        quot: &(AB::Expr, AB::Expr),
    ) {
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (
                a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(),
                a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone(),
            )
        };
        let gg = |o: usize| (cur[o].clone(), cur[o + 1].clone());
        let chunked = air.column_window;
        let mut folded = (AB::Expr::ZERO, AB::Expr::ZERO);
        let mut acc_i = 0usize;
        let n_c = air.constraints.len();
        for (k, c) in air.constraints.iter().enumerate() {
            let ci = eval_symbolic_circuit::<AB>(c, local, next, pubs, periodic, is_first, is_last, is_trans, w);
            let fa = emul(folded.clone(), alpha_stark.clone());
            folded = (fa.0 + ci.0, fa.1 + ci.1);
            if chunked && (k + 1) % MonolithAir::FOLD_CHUNK == 0 && k + 1 < n_c {
                let a = gg(air.fold_acc(acc_i)); // bind the witnessed partial fold, then Horner on from it
                builder.assert_zero(tf.clone() * (a.0.clone() - folded.0.clone()));
                builder.assert_zero(tf.clone() * (a.1.clone() - folded.1.clone()));
                folded = a;
                acc_i += 1;
            }
        }
        let chk = emul(folded, inv_van.clone());
        builder.assert_zero(tf.clone() * (chk.0 - quot.0.clone()));
        builder.assert_zero(tf.clone() * (chk.1 - quot.1.clone()));
    }

    fn emit_arith(&self, builder: &mut AB, air: &MonolithAir, cur: &[AB::Expr], tf: &AB::Expr, one: &AB::Expr, w: &AB::Expr) {
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(), a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone())
        };
        let gg = |o: usize| (cur[o].clone(), cur[o + 1].clone());
        let (x, alpha) = arith_point(builder, air, cur, tf, one);
        builder.assert_zero(tf.clone() * (cur[air.apow(0)].clone() - one.clone()));
        builder.assert_zero(tf.clone() * cur[air.apow(0) + 1].clone());
        for k in 1..air.n_terms {
            let prod = emul(gg(air.apow(k - 1)), alpha.clone());
            builder.assert_zero(tf.clone() * (cur[air.apow(k)].clone() - prod.0));
            builder.assert_zero(tf.clone() * (cur[air.apow(k) + 1].clone() - prod.1));
        }
        let mut ro = (AB::Expr::ZERO, AB::Expr::ZERO);
        for k in 0..air.n_terms {
            let z = gg(air.z(k));
            let inv = gg(air.inv(k));
            let z_m_x = (z.0 - x.clone(), z.1);
            let chk = emul(inv.clone(), z_m_x);
            builder.assert_zero(tf.clone() * (chk.0 - one.clone()));
            builder.assert_zero(tf.clone() * chk.1);
            let d = (cur[air.pz(k)].clone() - cur[air.px(k)].clone(), cur[air.pz(k) + 1].clone());
            let t = emul(emul(gg(air.apow(k)), d), inv);
            ro = (ro.0 + t.0, ro.1 + t.1);
        }
        bind_reduced_opening(builder, cur, tf, ro);
    }
}

impl<AB: AirBuilder<F = Goldilocks>> Air<AB> for MonolithAir {
    fn eval(&self, builder: &mut AB) {
        self.eval_bci(builder, &InlineBci);
    }
}

impl MonolithAir {
    /// The monolith constraint system, parameterized over the B/C/I emission strategy (`bci`). `eval` calls
    /// this with `InlineBci` (byte-identical); the wrap calls it with a lookup strategy.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn eval_bci<AB: AirBuilder<F = Goldilocks>, S: MonolithBci<AB>>(&self, builder: &mut AB, bci: &S) {
        let main = builder.main();
        let cur: Vec<AB::Expr> = main.current_slice().iter().map(|&x| x.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&x| x.into()).collect();
        let p: Vec<AB::Expr> = builder.periodic_values().iter().map(|&x| x.into()).collect();
        // COLUMN-WINDOW: read the inner-proof "pis" from the witness column window (held constant across the
        // instance) instead of public inputs, so the monolith can be tiled. The internal binds pin the window.
        let pis: Vec<AB::Expr> = if self.column_window {
            (0..self.pis_count()).map(|i| cur[self.pw(i)].clone()).collect()
        } else {
            builder.public_values().iter().map(|&x| x.into()).collect()
        };
        let one = AB::Expr::ONE;
        let two = AB::Expr::TWO;
        let half = AB::Expr::from(Goldilocks::ONE.halve());
        let w = AB::Expr::from(Goldilocks::from_u64(MRO_W_EXT));
        let pow2 = |i: usize| AB::Expr::from(Goldilocks::from_u64(1u64 << i));
        let emul = |a: (AB::Expr, AB::Expr), b: (AB::Expr, AB::Expr)| -> (AB::Expr, AB::Expr) {
            (a.0.clone() * b.0.clone() + w.clone() * a.1.clone() * b.1.clone(), a.0.clone() * b.1.clone() + a.1.clone() * b.0.clone())
        };
        let gg = |o: usize| (cur[o].clone(), cur[o + 1].clone());
        let s_trans = p[self.s_trans()].clone();
        let s_merkle = p[self.s_merkle()].clone();
        let s_pos = s_trans.clone() + s_merkle.clone(); // Poseidon rounds fire on transcript ∪ Merkle
        let stt = p[self.s_trans_trans()].clone();
        let tf = p[self.m_tf()].clone();
        let tl = p[self.m_tl()].clone();
        let ext_pubs = 2 * self.nb();
        let fp0 = pis[ext_pubs + self.ni()].clone();
        let fp1 = pis[ext_pubs + self.ni() + 1].clone();
        let cap = ext_pubs + self.ni() + 2;

        // ---------- Poseidon2 rounds (transcript sponge ∪ super-tile Merkle blocks) ----------
        let is_init = p[0].clone();
        let is_full = p[1].clone();
        let is_partial = p[2].clone();
        let rc: Vec<AB::Expr> = (0..W).map(|i| p[3 + i].clone()).collect();
        let mut init_s: [AB::Expr; W] = core::array::from_fn(|i| cur[i].clone());
        ext_linear(&mut init_s);
        let mut full_s: [AB::Expr; W] = core::array::from_fn(|i| pow7(cur[i].clone() + rc[i].clone()));
        ext_linear(&mut full_s);
        let mut part_s: [AB::Expr; W] =
            core::array::from_fn(|i| if i == 0 { pow7(cur[0].clone() + rc[0].clone()) } else { cur[i].clone() });
        int_linear(&mut part_s);
        for i in 0..W {
            let step = is_init.clone() * (nxt[i].clone() - init_s[i].clone())
                + is_full.clone() * (nxt[i].clone() - full_s[i].clone())
                + is_partial.clone() * (nxt[i].clone() - part_s[i].clone());
            builder.when_transition().assert_zero(s_pos.clone() * step);
        }

        // ---------- transcript: first-row capacity (per instance), sponge linkage, ext + index binds ----------
        {
            // per-instance first row (= global row 0 when k_instances=1): the sponge IV.
            let pif = p[self.p_inst_first()].clone();
            builder.assert_zero(pif.clone() * (cur[CAP_LANE].clone() - p[FT_COUNT].clone()));
            for i in (CAP_LANE + 1)..W {
                builder.assert_zero(pif.clone() * cur[i].clone());
            }
        }
        {
            let bl = p[FT_P_BLOCK_LAST].clone();
            builder.when_transition().assert_zero(stt.clone() * bl.clone() * (nxt[CAP_LANE].clone() - cur[CAP_LANE].clone() - p[FT_COUNT_NEXT].clone()));
            for i in (CAP_LANE + 1)..W {
                builder.when_transition().assert_zero(stt.clone() * bl.clone() * (nxt[i].clone() - cur[i].clone()));
            }
            for i in 0..RATE {
                builder.when_transition().assert_zero(stt.clone() * bl.clone() * p[FT_IS_SQ_NEXT].clone() * (nxt[i].clone() - cur[i].clone()));
            }
        }
        for j in 0..self.nb() {
            let b = p[FT_BIND_START + j].clone();
            builder.assert_zero(b.clone() * (cur[3].clone() - pis[2 * j].clone()));
            builder.assert_zero(b * (cur[2].clone() - pis[2 * j + 1].clone()));
        }
        let idx_start = FT_BIND_START + self.nb();
        for (k, &(_blk, lane)) in self.index_binds.iter().enumerate() {
            let b = p[idx_start + k].clone();
            builder.assert_zero(b * (cur[lane].clone() - pis[ext_pubs + k].clone()));
        }

        // ---------- α_fri carrier (per-instance-persistent): held (except across instance boundaries); pinned
        // at α_fri's bind row ----------
        let carry = self.carry();
        let not_inst_last = one.clone() - p[self.p_inst_last()].clone();
        builder.when_transition().assert_zero(not_inst_last.clone() * (nxt[carry].clone() - cur[carry].clone()));
        builder.when_transition().assert_zero(not_inst_last.clone() * (nxt[carry + 1].clone() - cur[carry + 1].clone()));
        let alpha_bind = p[FT_BIND_START + 2].clone();
        builder.assert_zero(alpha_bind.clone() * (cur[carry].clone() - cur[3].clone()));
        builder.assert_zero(alpha_bind * (cur[carry + 1].clone() - cur[2].clone()));

        // ---------- column-window: the inner-proof pis window is held constant across the whole instance ----
        // (global-persistent for K=1; the aggregator resets it per instance). The binds/terminals/OOD pin it.
        if self.column_window {
            // per-instance-persistent (reset across instance boundaries so each inner has its own window).
            for i in 0..self.pis_count() {
                builder.when_transition().assert_zero(not_inst_last.clone() * (nxt[self.pw(i)].clone() - cur[self.pw(i)].clone()));
            }
            for j in 0..(2 * self.cm_rounds()) {
                builder.when_transition().assert_zero(not_inst_last.clone() * (nxt[self.sch(j)].clone() - cur[self.sch(j)].clone()));
            }
        }

        // ---------- super-tile arith (block 0, gated by M_TF / P_ROUND / M_TL) ----------
        // Factored through the B/C/I strategy: `InlineBci` re-emits the `9·n_terms`-COLUMN inline fold verbatim
        // (byte-identical); a narrow-tall strategy witnesses `ro` from slack ROWS (the deep-tree size lever).
        bci.emit_arith(builder, self, &cur, &tf, &one, &w);
        // β_r binding (per-round one-hots → public β_r = binds[3+r])
        for r in 0..(self.nb() - 3) {
            let pr = p[self.p_round(r)].clone();
            let bidx = 3 + r;
            builder.assert_zero(pr.clone() * (cur[QT_B].clone() - pis[2 * bidx].clone()));
            builder.assert_zero(pr * (cur[QT_B + 1].clone() - pis[2 * bidx + 1].clone()));
        }
        // index binding: canonical decomposition + DEEP/fold bits pinned to the transcript's index felt
        let mut sel = AB::Expr::ZERO;
        for q in 0..self.n_queries {
            sel = sel + p[self.p_query(q)].clone() * pis[ext_pubs + q].clone();
        }
        builder.assert_zero(tf.clone() * cur[self.sb_x()].clone() - sel);
        for i in 0..64 {
            let b = cur[self.sb_b(i)].clone();
            builder.assert_zero(tf.clone() * (b.clone() * (one.clone() - b)));
        }
        let mut recon = AB::Expr::ZERO;
        for i in 0..64 {
            recon = recon + cur[self.sb_b(i)].clone() * pow2(i);
        }
        builder.assert_zero(tf.clone() * (cur[self.sb_x()].clone() - recon));
        builder.assert_zero(tf.clone() * (cur[self.sb_q(0)].clone() - cur[self.sb_b(32)].clone() * cur[self.sb_b(33)].clone()));
        for k in 2..=31 {
            builder.assert_zero(tf.clone() * (cur[self.sb_q(k - 1)].clone() - cur[self.sb_q(k - 2)].clone() * cur[self.sb_b(32 + k)].clone()));
        }
        let mut lo = AB::Expr::ZERO;
        for i in 0..32 {
            lo = lo + cur[self.sb_b(i)].clone() * pow2(i);
        }
        builder.assert_zero(tf.clone() * (cur[self.sb_q(30)].clone() * lo));
        for i in 0..self.lg() {
            builder.assert_zero(tf.clone() * (cur[QT_DBITS + i].clone() - cur[self.sb_b(i)].clone()));
        }
        let mut qidx = AB::Expr::ZERO;
        for i in 0..self.lg() {
            qidx = qidx + cur[self.sb_b(i)].clone() * pow2(i);
        }
        builder.assert_zero(tf.clone() * (cur[self.idx_rem()].clone() - qidx));
        let mut round_mask = AB::Expr::ZERO;
        for r in 0..(self.nb() - 3) {
            round_mask = round_mask + p[self.p_round(r)].clone();
        }
        builder
            .when_transition()
            .assert_zero(round_mask.clone() * (cur[self.idx_rem()].clone() - two.clone() * nxt[self.idx_rem()].clone() - cur[QT_BIT].clone()));
        // bit-aware fold (transitions on the round rows)
        let bit = cur[QT_BIT].clone();
        let i2s = cur[QT_I2S].clone();
        let spt = cur[QT_SPT].clone();
        builder.when_transition().assert_zero(round_mask.clone() * (bit.clone() * (one.clone() - bit.clone())));
        builder.when_transition().assert_zero(round_mask.clone() * (i2s.clone() * (two.clone() * spt) - one.clone()));
        let sign = one.clone() - two.clone() * bit;
        let e = (cur[QT_E].clone(), cur[QT_E + 1].clone());
        let s = (cur[QT_S].clone(), cur[QT_S + 1].clone());
        let bb = (cur[QT_B].clone(), cur[QT_B + 1].clone());
        let sum = (e.0.clone() + s.0.clone(), e.1.clone() + s.1.clone());
        let diff = (e.0 - s.0, e.1 - s.1);
        let prod = emul(diff, bb);
        let fold0 = sum.0 * half.clone() + sign.clone() * prod.0 * i2s.clone();
        let fold1 = sum.1 * half.clone() + sign * prod.1 * i2s;
        builder.when_transition().assert_zero(round_mask.clone() * (nxt[QT_E].clone() - fold0));
        builder.when_transition().assert_zero(round_mask * (nxt[QT_E + 1].clone() - fold1));
        // accept (M_TL): folded_eval == final_poly[0]
        builder.assert_zero(tl.clone() * (cur[QT_E].clone() - fp0));
        builder.assert_zero(tl * (cur[QT_E + 1].clone() - fp1));

        // ---------- constraint epilogue (OOD check), gated by M_TF on every super-tile arith head ----------
        // ζ, α_stark are transcript-bound publics (degree 0), so the Lagrange selectors at ζ are public
        // constants and the OOD relation folded(ζ)·Z_H(ζ)^{-1} == quotient(ζ) is LINEAR in the witness OOD
        // openings QT_pz(0..3). Multiply through by Z_H·(ζ−1) to avoid inverses:
        //   z_h·α·(local−pub) + is_trans·(ζ−1)·(next−local) == z_h·(ζ−1)·(c0 + c1·X),   quotient(ζ)=c0+c1·X.
        {
            let alpha_stark = (pis[0].clone(), pis[1].clone());
            let zeta = (pis[2].clone(), pis[3].clone());
            // S_6 = ζ^(2^degree_bits). In pis mode ζ is a degree-0 public constant ⇒ inline squaring (degree 0).
            // In column-window ζ is a degree-1 witness ⇒ use the witnessed squaring chain (S_{i+1}=S_i², bound
            // degree 2) so z_h stays degree 1 and the OOD constraint doesn't blow up.
            // constraint-domain degree bits: HALVED under is_zk (init_trace_domain = degree >> is_zk), so
            // z_h = ζ^(2^(cm_rounds−is_zk))−1 and the domain generator uses cm_rounds−is_zk. is_zk=0 ⇒ cm_rounds
            // (byte-for-byte).
            let cdb = self.cm_rounds() - self.is_zk;
            let z_h = if self.column_window {
                let mut prev = zeta.clone();
                for i in 0..cdb {
                    let si = (cur[self.sch(2 * i)].clone(), cur[self.sch(2 * i) + 1].clone());
                    let sq = emul(prev.clone(), prev.clone());
                    builder.assert_zero(tf.clone() * (si.0.clone() - sq.0));
                    builder.assert_zero(tf.clone() * (si.1.clone() - sq.1));
                    prev = si;
                }
                (prev.0 - one.clone(), prev.1)
            } else {
                let mut s = zeta.clone();
                for _ in 0..cdb {
                    s = emul(s.clone(), s.clone());
                }
                (s.0 - one.clone(), s.1)
            };
            let g_inv = AB::Expr::from(Goldilocks::two_adic_generator(cdb).inverse());
            let is_trans = (zeta.0.clone() - g_inv, zeta.1.clone());
            let zm1 = (zeta.0.clone() - one.clone(), zeta.1.clone());
            let w_in = self.w_inner();
            if self.symbolic() {
                // DATA-DRIVEN MULTI-COLUMN: verify the inner from its p3 SymbolicExpression trees. Witness the
                // three Lagrange selectors + bind them to their ζ-definitions (is_first·(ζ−1)=z_h;
                // is_last·(ζ−g^{-1})=z_h; inv_van·z_h=1; is_trans=ζ−g^{-1} inline), then walk each constraint tree
                // (eval_symbolic_circuit) with the selector VALUES, Horner-fold, and check folded·inv_van==quot(ζ)
                // — exactly p3::verify_constraints, no per-constraint inverse-clearing. Handles ANY inner AIR.
                let is_first = gg(self.sel(0));
                let is_last = gg(self.sel(2));
                let inv_van = gg(self.sel(4));
                let bif = emul(is_first.clone(), zm1.clone());
                builder.assert_zero(tf.clone() * (bif.0 - z_h.0.clone()));
                builder.assert_zero(tf.clone() * (bif.1 - z_h.1.clone()));
                let bil = emul(is_last.clone(), is_trans.clone());
                builder.assert_zero(tf.clone() * (bil.0 - z_h.0.clone()));
                builder.assert_zero(tf.clone() * (bil.1 - z_h.1.clone()));
                let biv = emul(inv_van.clone(), z_h.clone());
                builder.assert_zero(tf.clone() * (biv.0 - one.clone()));
                builder.assert_zero(tf.clone() * biv.1);
                let local: Vec<(AB::Expr, AB::Expr)> = (0..w_in).map(|c| gg(self.pz(self.trm_trace(c)))).collect();
                let next: Vec<(AB::Expr, AB::Expr)> = (0..w_in).map(|c| gg(self.pz(self.trm_next(c)))).collect();
                // recompose quotient(ζ) from the nqc chunk-openings: Σ_i zps_i·(pz(2W+2i)+pz(2W+2i+1)·X). nqc=1 ⇒
                // the single chunk c0+c1·X (implicit weight 1, byte-for-byte); nqc>1 ⇒ verifier-computed weights
                // zps_i (the qwt pis region) — exactly p3's recompose_quotient_from_chunks (validated by the oracle).
                let quot = {
                    let mut acc = (AB::Expr::ZERO, AB::Expr::ZERO);
                    for i in 0..self.nqc() {
                        let d0 = gg(self.pz(self.trm_quot(i, 0)));
                        let d1 = gg(self.pz(self.trm_quot(i, 1)));
                        let chunk = (d0.0.clone() + w.clone() * d1.1.clone(), d0.1.clone() + d1.0.clone());
                        let weighted = if self.nqc() == 1 {
                            chunk
                        } else {
                            let zps = (pis[self.qwt_base() + 2 * i].clone(), pis[self.qwt_base() + 2 * i + 1].clone());
                            emul(zps, chunk)
                        };
                        acc = (acc.0 + weighted.0, acc.1 + weighted.1);
                    }
                    acc
                };
                let pubs: Vec<(AB::Expr, AB::Expr)> = (0..self.n_pub()).map(|i| (pis[self.pub_pi() + i].clone(), AB::Expr::ZERO)).collect();
                // periodic column values at ζ (verifier-computed publics in the periodic pis region).
                let periodic: Vec<(AB::Expr, AB::Expr)> = (0..self.n_periodic()).map(|i| (pis[self.periodic_base() + 2 * i].clone(), pis[self.periodic_base() + 2 * i + 1].clone())).collect();
                // B/C (OOD epilogue fold) — routed through the strategy so the wrap can replace the inline
                // eval_symbolic_circuit + α-Horner with lookups (byte-identical under InlineBci; the reused
                // selector binds + openings above stay inline).
                bci.emit_epilogue(
                    builder, self, &cur, &tf, &w, &local, &next, &pubs, &periodic, &is_first, &is_last,
                    &is_trans, &alpha_stark, &inv_van, &quot,
                );
            } else {
                // 1-COLUMN ConstAir/CounterAir: the 2-constraint form (1 first-row + 1 transition):
                //   z_h·α·(local−pub) + is_trans·(ζ−1)·(next−local[−1]) == z_h·(ζ−1)·(c0+c1·X).
                let p1 = emul(z_h.clone(), alpha_stark.clone()); // z_h·α
                let p2 = emul(is_trans.clone(), zm1.clone()); // is_trans·(ζ−1)
                let p3v = emul(z_h.clone(), zm1.clone()); // z_h·(ζ−1)
                let pub_val = pis[self.pub_pi()].clone();
                let local = gg(self.pz(self.trm_trace(0)));
                let next = gg(self.pz(self.trm_next(0)));
                // recompose quotient(ζ) from the nqc chunk-openings: weight-1 single chunk when nqc=1 (byte-for-byte
                // c0+c1·X); verifier-computed weights zps_i (qwt pis region) when nqc>1 — the hiding ConstAir has
                // nqc=4. Exactly p3's recompose_quotient_from_chunks, matching the symbolic path above.
                let quot = {
                    let mut acc = (AB::Expr::ZERO, AB::Expr::ZERO);
                    for i in 0..self.nqc() {
                        let d0 = gg(self.pz(self.trm_quot(i, 0)));
                        let d1 = gg(self.pz(self.trm_quot(i, 1)));
                        let chunk = (d0.0.clone() + w.clone() * d1.1.clone(), d0.1.clone() + d1.0.clone());
                        let weighted = if self.nqc() == 1 {
                            chunk
                        } else {
                            let zps = (pis[self.qwt_base() + 2 * i].clone(), pis[self.qwt_base() + 2 * i + 1].clone());
                            emul(zps, chunk)
                        };
                        acc = (acc.0 + weighted.0, acc.1 + weighted.1);
                    }
                    acc
                };
                let lm = (local.0.clone() - pub_val, local.1.clone());
                let trans_const = if self.inner_counter { one.clone() } else { AB::Expr::ZERO };
                let nl = (next.0 - local.0 - trans_const, next.1 - local.1);
                let t1 = emul(p1, lm);
                let t2 = emul(p2, nl);
                let rhs = emul(p3v, quot);
                builder.assert_zero(tf.clone() * (t1.0 + t2.0 - rhs.0));
                builder.assert_zero(tf.clone() * (t1.1 + t2.1 - rhs.1));
            }
            // z-term binding: bind each opened point z to its transcript-derived value — ζ for the random,
            // trace-ζ, and quotient terms; ζ·g_trace (the HALVED constraint-domain generator) for the trace-ζ_next
            // block [trm_next_base, trm_quot_base). is_zk=0 ⇒ [0,W)→ζ, [W,2W)→ζ·g, [2W,·)→ζ (byte-for-byte). So
            // each QT_pz(k) is genuinely the opening AT its point.
            let g_trace = AB::Expr::from(Goldilocks::two_adic_generator(cdb));
            for k in 0..self.n_terms {
                let at_next = k >= self.trm_next_base() && k < self.trm_quot_base();
                let (zx, zy) = if at_next {
                    (zeta.0.clone() * g_trace.clone(), zeta.1.clone() * g_trace.clone())
                } else {
                    (zeta.0.clone(), zeta.1.clone())
                };
                builder.assert_zero(tf.clone() * (cur[self.z(k)].clone() - zx));
                builder.assert_zero(tf.clone() * (cur[self.z(k) + 1].clone() - zy));
            }
        }

        // ---------- opened-value carrier: held WITHIN each super-tile (S_QUERY · not-boundary) so it doesn't
        // leak across the transcript→query boundary; == QT_px(0) at the arith head; the leaf preimage. ----
        let hold = p[self.s_query()].clone() * (one.clone() - p[self.p_st_last()].clone());
        // opened-row carrier (input_leaf_felts felts): held within the super-tile. Its committed-row prefix
        // (trm_committed_w felts) feeds BOTH its ζ term px(trm_trace(c)) AND its ζ_next term px(trm_next(c))
        // (px-sharing — one authenticated value → two DEEP terms) and the leaf. The trailing HIDING_SALT felts
        // (is_zk=1) are the free leaf salt: held but not px-bound (authenticated by folding to the committed cap).
        for c in 0..self.input_leaf_felts() {
            let ovc = self.ov_c(c);
            builder.when_transition().assert_zero(hold.clone() * (nxt[ovc].clone() - cur[ovc].clone()));
            if c < self.trm_committed_w() {
                builder.assert_zero(tf.clone() * (cur[ovc].clone() - cur[self.px(self.trm_trace(c))].clone())); // @ ζ
                builder.assert_zero(tf.clone() * (cur[ovc].clone() - cur[self.px(self.trm_next(c))].clone())); // @ ζ_next
            }
        }
        // HIDING random-round carrier (random_leaf_felts felts, is_zk=1): the random-polynomial committed row
        // (px-bound to the random reduced-opening terms px(0..random_committed_w)) ‖ free salt; held.
        if self.is_zk == 1 {
            for c in 0..self.random_leaf_felts() {
                let ovr = self.ov_random(c);
                builder.when_transition().assert_zero(hold.clone() * (nxt[ovr].clone() - cur[ovr].clone()));
                if c < self.random_committed_w() {
                    builder.assert_zero(tf.clone() * (cur[ovr].clone() - cur[self.px(c)].clone()));
                }
            }
        }
        // quotient opened-value carriers (quot_leaf_felts felts): the multi-matrix concat over nqc chunks. Each
        // chunk's committed-row prefix (trm_chunk_w felts) is px-bound to its reduced-opening terms px(trm_quot(i,j))
        // (the nqc chunk-openings at the query row); the trailing HIDING_SALT per chunk (is_zk=1) is free salt. Held.
        {
            let stride = self.quot_chunk_stride();
            for c in 0..self.quot_leaf_felts() {
                let qcj = self.qc(c);
                builder.when_transition().assert_zero(hold.clone() * (nxt[qcj].clone() - cur[qcj].clone()));
                let (i, j) = (c / stride, c % stride);
                if j < self.trm_chunk_w() {
                    builder.assert_zero(tf.clone() * (cur[qcj].clone() - cur[self.px(self.trm_quot(i, j))].clone()));
                }
            }
        }
        // commit-phase group carriers: seed the bit-ordered fold group {e_r, sib_r} at fold row r (p_round(r));
        // held within the super-tile so round r's leaf-hash block can absorb it (group[0..2]=lo, [2..4]=hi).
        for r in 0..self.cm_rounds() {
            let pr = p[self.p_round(r)].clone();
            let bit = cur[QT_BIT].clone();
            let nbit = one.clone() - bit.clone();
            let (e0, e1) = (cur[QT_E].clone(), cur[QT_E + 1].clone());
            let (sib0, sib1) = (cur[QT_S].clone(), cur[QT_S + 1].clone());
            builder.assert_zero(pr.clone() * (cur[self.cg(r, 0)].clone() - (nbit.clone() * e0.clone() + bit.clone() * sib0.clone())));
            builder.assert_zero(pr.clone() * (cur[self.cg(r, 1)].clone() - (nbit.clone() * e1.clone() + bit.clone() * sib1.clone())));
            builder.assert_zero(pr.clone() * (cur[self.cg(r, 2)].clone() - (nbit.clone() * sib0 + bit.clone() * e0)));
            builder.assert_zero(pr.clone() * (cur[self.cg(r, 3)].clone() - (nbit * sib1 + bit * e1)));
            for k in 0..4 {
                builder.when_transition().assert_zero(hold.clone() * (nxt[self.cg(r, k)].clone() - cur[self.cg(r, k)].clone()));
            }
        }

        // ---------- super-tile inline Merkle (input + quotient blocks, gated by S_MERKLE) ----------
        // input-Merkle leaf (blocks M_INPUT_LEAF..+leaf_blocks): a PaddingFreeSponge over the W-value opened
        // trace row, RATE felts absorbed per block. First block: rate lanes 0..min(W,RATE) = opened_row, the
        // rest = 0 (fresh state). At W≤RATE this is the single-block milestone leaf (byte-for-byte).
        let leaf = p[self.m_leaf()].clone();
        let lc0 = core::cmp::min(self.input_leaf_felts(), RATE);
        for c in 0..lc0 {
            builder.assert_zero(leaf.clone() * (cur[c].clone() - cur[self.ov_c(c)].clone()));
        }
        for i in lc0..W {
            builder.assert_zero(leaf.clone() * cur[i].clone());
        }
        // subsequent leaf blocks (W>RATE): each absorb head overwrites the rate lanes with the next chunk of the
        // opened row; the leaf-internal boundary carries the sponge capacity (and, for a short final block, the
        // rate lanes that chunk doesn't overwrite) — exactly PaddingFreeSponge's overwrite-mode duplex.
        for b in 1..self.leaf_blocks() {
            let ia = p[self.ia_in(b)].clone();
            let clen = core::cmp::min(RATE, self.input_leaf_felts() - b * RATE);
            for k in 0..clen {
                builder.assert_zero(ia.clone() * (cur[k].clone() - cur[self.ov_c(b * RATE + k)].clone()));
            }
        }
        if self.leaf_blocks() > 1 {
            let bnd = p[self.in_boundary()].clone();
            for k in RATE..W {
                builder.when_transition().assert_zero(bnd.clone() * (nxt[k].clone() - cur[k].clone())); // capacity carry
            }
            if self.input_leaf_felts() % RATE != 0 {
                let lc = p[self.in_last_carry()].clone();
                let rem = self.input_leaf_felts() - (self.leaf_blocks() - 1) * RATE;
                for k in rem..RATE {
                    builder.when_transition().assert_zero(lc.clone() * (nxt[k].clone() - cur[k].clone())); // short-final rate carry
                }
            }
        }
        // quotient-Merkle leaf (blocks m_quot_leaf..+quot_leaf_blocks): a PaddingFreeSponge over the 2·nqc-felt
        // quotient row (the nqc chunk-openings), RATE felts/block — the SAME multi-block machinery as the input
        // leaf. First block: rate 0..min(2·nqc,RATE) = qc, rest 0. Single block for nqc≤2 (2·nqc≤RATE).
        let qleaf = p[self.q_leaf()].clone();
        let qlc0 = core::cmp::min(self.quot_leaf_felts(), RATE);
        for k in 0..qlc0 {
            builder.assert_zero(qleaf.clone() * (cur[k].clone() - cur[self.qc(k)].clone()));
        }
        for i in qlc0..W {
            builder.assert_zero(qleaf.clone() * cur[i].clone());
        }
        // subsequent quotient-leaf blocks (2·nqc>RATE): absorb the next chunk + carry capacity / short-final rate.
        for b in 1..self.quot_leaf_blocks() {
            let iq = p[self.iq_(b)].clone();
            let clen = core::cmp::min(RATE, self.quot_leaf_felts() - b * RATE);
            for k in 0..clen {
                builder.assert_zero(iq.clone() * (cur[k].clone() - cur[self.qc(b * RATE + k)].clone()));
            }
        }
        if self.quot_leaf_blocks() > 1 {
            let bnd = p[self.q_boundary()].clone();
            for k in RATE..W {
                builder.when_transition().assert_zero(bnd.clone() * (nxt[k].clone() - cur[k].clone())); // capacity carry
            }
            if self.quot_leaf_felts() % RATE != 0 {
                let lc = p[self.q_last_carry()].clone();
                let rem = self.quot_leaf_felts() - (self.quot_leaf_blocks() - 1) * RATE;
                for k in rem..RATE {
                    builder.when_transition().assert_zero(lc.clone() * (nxt[k].clone() - cur[k].clone())); // short-final rate carry
                }
            }
        }
        // HIDING random-round leaf (is_zk=1, blocks M_INPUT_LEAF..+random_leaf_blocks): a salted PaddingFreeSponge
        // over the random-polynomial committed row ‖ salt (random_leaf_felts felts), RATE/block — the SAME
        // multi-block machinery as the trace leaf, then input_depth merges (via the generic merge link) to the
        // random cap. The random terminal binds to the random cap carrier (a full cap; random varies per query).
        if self.is_zk == 1 {
            let rleaf = p[self.p_random_leaf()].clone();
            let rlc0 = core::cmp::min(self.random_leaf_felts(), RATE);
            for c in 0..rlc0 {
                builder.assert_zero(rleaf.clone() * (cur[c].clone() - cur[self.ov_random(c)].clone()));
            }
            for i in rlc0..W {
                builder.assert_zero(rleaf.clone() * cur[i].clone());
            }
            for b in 1..self.random_leaf_blocks() {
                let ia = p[self.p_random_absorb(b)].clone();
                let clen = core::cmp::min(RATE, self.random_leaf_felts() - b * RATE);
                for k in 0..clen {
                    builder.assert_zero(ia.clone() * (cur[k].clone() - cur[self.ov_random(b * RATE + k)].clone()));
                }
            }
            if self.random_leaf_blocks() > 1 {
                let bnd = p[self.p_random_boundary()].clone();
                for k in RATE..W {
                    builder.when_transition().assert_zero(bnd.clone() * (nxt[k].clone() - cur[k].clone())); // capacity carry
                }
                if self.random_leaf_felts() % RATE != 0 {
                    let lc = p[self.p_random_last_carry()].clone();
                    let rem = self.random_leaf_felts() - (self.random_leaf_blocks() - 1) * RATE;
                    for k in rem..RATE {
                        builder.when_transition().assert_zero(lc.clone() * (nxt[k].clone() - cur[k].clone())); // short-final rate carry
                    }
                }
            }
            // random terminal (block m_random_term) == the query's index-selected random cap entry, carried per
            // super-tile in cap_c group (8 + 4·cm_rounds) and seeded at the arith head by the cap-mux below.
            let rterm = p[self.p_random_term()].clone();
            for k in 0..4 {
                builder.assert_zero(rterm.clone() * (cur[k].clone() - cur[self.cap_c(8 + 4 * self.cm_rounds() + k)].clone()));
            }
        }
        // commit-phase leaves (blocks CM_LEAF[r]): absorb the bit-ordered fold group carried in cg(r,·).
        for r in 0..self.cm_rounds() {
            let cl = p[self.c_leaf(r)].clone();
            for k in 0..4 {
                builder.assert_zero(cl.clone() * (cur[k].clone() - cur[self.cg(r, k)].clone()));
            }
            for i in 4..W {
                builder.assert_zero(cl.clone() * cur[i].clone());
            }
        }
        // HIDING commit-leaf 2nd block (is_zk=1, blocks cm_leaf(r)+1): the salt is absorbed into the rate lanes
        // (free — authenticated by folding to the committed cap), and the capacity carries from block 0. Only the
        // capacity-carry boundary is constrained; the generic Poseidon step then produces the leaf output.
        if self.is_zk == 1 && self.cm_leaf_blocks() > 1 {
            let cb = p[self.c_bnd()].clone();
            for k in RATE..W {
                builder.when_transition().assert_zero(cb.clone() * (nxt[k].clone() - cur[k].clone())); // capacity carry
            }
        }
        builder.assert_zero(s_merkle.clone() * (cur[self.m_bit()].clone() * (one.clone() - cur[self.m_bit()].clone())));
        {
            // bit-ordered merge link across Merkle block boundaries, EXCEPT after any terminal (input/quotient/
            // random/commit) — the block after a terminal is a fresh leaf-hash seeded from its carrier, not a
            // merge — and EXCEPT a multi-block leaf's INTERNAL boundary (a sponge absorb-continuation).
            // All excluded one-hots fire on last rows of DISTINCT blocks (the super-tile layout is strictly
            // sequential), so Π(1−t_i) == 1−Σ t_i on every trace row — and the SUM form is degree-1 in the
            // exclusions at ANY depth. BOTH modes use it: the product's degree grew by one per commit round
            // (7 + cm_rounds + boundary factors) and crossed the outer quotient/LDE capacity budget
            // (log_nqc ≤ log_blowup, maxdeg ≤ 16 — exceeding it SILENTLY corrupts the quotient:
            // row-wise-satisfied trace, garbage quotient, OodEvaluationMismatch) first at hiding db≥4, then
            // at the is_zk=0 REAL join-split shape (db=12, cm_rounds=12, multi-block leaves ⇒ product degree
            // 21 — caught by phase8_joinsplit_degree_probe, exactly as the latent-budget note predicted).
            // The is_zk=1 expression tree is unchanged term-for-term; is_zk=0 migrated product→sum
            // (a deliberate constraint-set change, re-pinned in constraint_fingerprint).
            let not_term = {
                let mut term_sum = p[self.m_term()].clone() + p[self.q_term()].clone();
                if self.is_zk == 1 {
                    term_sum = term_sum + p[self.p_random_term()].clone();
                }
                for r in 0..self.cm_rounds() {
                    term_sum = term_sum + p[self.c_term(r)].clone();
                }
                if self.leaf_blocks() > 1 {
                    term_sum = term_sum + p[self.in_boundary()].clone();
                }
                if self.quot_leaf_blocks() > 1 {
                    term_sum = term_sum + p[self.q_boundary()].clone();
                }
                if self.is_zk == 1 {
                    if self.random_leaf_blocks() > 1 {
                        term_sum = term_sum + p[self.p_random_boundary()].clone();
                    }
                    if self.cm_leaf_blocks() > 1 {
                        term_sum = term_sum + p[self.c_bnd()].clone(); // commit-leaf block-0→block-1 boundary
                    }
                }
                one.clone() - term_sum
            };
            let link = s_merkle.clone() * p[FT_P_BLOCK_LAST].clone() * (one.clone() - p[self.p_st_last()].clone()) * not_term;
            let nb_ = nxt[self.m_bit()].clone();
            let sib = self.m_sib();
            for k in 0..4 {
                builder.when_transition().assert_zero(link.clone() * (nxt[k].clone() - ((one.clone() - nb_.clone()) * cur[k].clone() + nb_.clone() * nxt[sib + k].clone())));
                builder.when_transition().assert_zero(link.clone() * (nxt[4 + k].clone() - ((one.clone() - nb_.clone()) * nxt[sib + k].clone() + nb_.clone() * cur[k].clone())));
            }
        }
        // input terminal (block 5) == trace cap entry; quotient terminal (block 10) == quotient cap entry.
        let term = p[self.m_term()].clone();
        let qterm = p[self.q_term()].clone();
        if self.full_cap() {
            // NON-CONSTANT inner (counter or Fibonacci): cap entries DIFFER per query — each terminal equals
            // the query's index-selected cap entry, carried per super-tile (seeded at the arith head from the
            // per-query cap pis via the p_query one-hots, held to the terminals).
            for k in 0..4 {
                builder.assert_zero(term.clone() * (cur[k].clone() - cur[self.cap_c(k)].clone())); // input
                builder.assert_zero(qterm.clone() * (cur[k].clone() - cur[self.cap_c(4 + k)].clone())); // quotient
            }
            for r in 0..self.cm_rounds() {
                let ct = p[self.c_term(r)].clone();
                for k in 0..4 {
                    builder.assert_zero(ct.clone() * (cur[k].clone() - cur[self.cap_c(8 + 4 * r + k)].clone()));
                }
            }
            // hold the cap carriers across the super-tile; SEED them at the arith head (M_TF) via the CAP-MUX:
            // cap_c[opening][k] = Σ_{e} (Π_j sel_bit_j(e)) · pis[cap_base + e·4 + k], selecting entry
            // `index >> shift` from the FULL cap by the index bits [shift .. shift+bits] (the validated
            // SampleBits bits sb_b). This BINDS each terminal to the index-selected committed cap entry.
            let hold = p[self.s_query()].clone() * (one.clone() - p[self.p_st_last()].clone());
            for g in 0..self.n_cap_c() {
                builder.when_transition().assert_zero(hold.clone() * (nxt[self.cap_c(g)].clone() - cur[self.cap_c(g)].clone()));
            }
            // (cg_offset, shift, bits, cap_base) per opening: trace, quotient, then self.cm_rounds() commit rounds.
            // trace/quotient are at the max height, so the cap-selecting shift is input_depth (log_global−cap), runtime.
            let mut openings = vec![(0usize, self.input_depth(), self.cap_height, self.cap_base()), (4, self.input_depth(), self.cap_height, self.qcap_base())];
            for r in 0..self.cm_rounds() {
                openings.push((8 + 4 * r, self.commit_shift(r), self.commit_bits(r), self.commit_cap_base(r)));
            }
            // HIDING random round (is_zk=1): a full cap at max height (shift = input_depth), cap_c group
            // (8 + 4·cm_rounds), selecting cap[index>>input_depth] from the random commitment's cap pis region.
            if self.is_zk == 1 {
                openings.push((8 + 4 * self.cm_rounds(), self.input_depth(), self.cap_height, self.random_cap_base()));
            }
            bci.emit_capmux(builder, self, &cur, &pis, &one, &tf, &openings);
        } else {
            // ConstAir: all cap entries equal → a single shared cap entry per opening (the validated path).
            let qcap = self.qcap_base();
            let ccap = self.ccap_base();
            for k in 0..4 {
                builder.assert_zero(term.clone() * (cur[k].clone() - pis[cap + k].clone()));
                builder.assert_zero(qterm.clone() * (cur[k].clone() - pis[qcap + k].clone()));
            }
            for r in 0..self.cm_rounds() {
                let ct = p[self.c_term(r)].clone();
                for k in 0..4 {
                    builder.assert_zero(ct.clone() * (cur[k].clone() - pis[ccap + 4 * r + k].clone()));
                }
            }
        }

        // ---------- aggregator tx-root fold (only when `fold`) ----------
        // Poseidon blocks in each instance's tail slack fold the verified inner statement into a global-
        // persistent Merkle–Damgård root, IV=0, held except at each instance's ROOT update (which writes the
        // new root into the next instance's first row); the final root == the block tx-root, the ONLY public
        // input. `!fold_txstmt`: 1-value `s_k = merge([DOM,0,0,0],[pvs0,0,0,0])` (matches agg_root). `fold_txstmt`:
        // the FULL `tx_statement_digest` — n_sk s_k-chain blocks `merge(...merge([DOM,0,0,0],anchor)…,tx_binding)`
        // over the statement chunks read from the pi window — so root is BYTE-IDENTICAL to `batch_root`.
        if self.fold {
            let txroot: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
            let dom = AB::Expr::from(Goldilocks::from_u64(crate::domains::DOM_TXROOT)); // DOM_AGG = DOM_TXROOT
            // fold Poseidon step (reuses the period-BLOCK round schedule is_init/is_full/is_partial/rc), gated to
            // ALL fold blocks by P_FOLD_ACTIVE. The round schedule zeroes at each block's last row (the output
            // row), so the block-boundary transitions are step-free and the seed/link/inject one-hots take over.
            let fa = p[self.p_fold_active()].clone();
            let mut f_init: [AB::Expr; W] = core::array::from_fn(|i| cur[self.af_p(i)].clone());
            ext_linear(&mut f_init);
            let mut f_full: [AB::Expr; W] = core::array::from_fn(|i| pow7(cur[self.af_p(i)].clone() + rc[i].clone()));
            ext_linear(&mut f_full);
            let mut f_part: [AB::Expr; W] =
                core::array::from_fn(|i| if i == 0 { pow7(cur[self.af_p(0)].clone() + rc[0].clone()) } else { cur[self.af_p(i)].clone() });
            int_linear(&mut f_part);
            for i in 0..W {
                let step = is_init.clone() * (nxt[self.af_p(i)].clone() - f_init[i].clone())
                    + is_full.clone() * (nxt[self.af_p(i)].clone() - f_full[i].clone())
                    + is_partial.clone() * (nxt[self.af_p(i)].clone() - f_part[i].clone());
                builder.when_transition().assert_zero(fa.clone() * step);
            }
            if !self.fold_txstmt {
                // SK block seed: [DOM, 0,0,0, pvs0, 0,0,0].
                let psk = p[self.p_fold_sk()].clone();
                builder.assert_zero(psk.clone() * (cur[self.af_p(0)].clone() - dom.clone()));
                builder.assert_zero(psk.clone() * (cur[self.af_p(4)].clone() - cur[self.pw(self.pub_pi())].clone()));
                for i in [1usize, 2, 3, 5, 6, 7] {
                    builder.assert_zero(psk.clone() * cur[self.af_p(i)].clone());
                }
                // SK block last row: s_k (output lanes 0..4) → ROOT block rate-high (next row lanes 4..8).
                let pskl = p[self.p_fold_sklast()].clone();
                for k in 0..4 {
                    builder.when_transition().assert_zero(pskl.clone() * (nxt[self.af_p(4 + k)].clone() - cur[self.af_p(k)].clone()));
                }
            } else {
                // tx_statement s_k chain: each s_k block b injects chunk_b into rate-high (lanes 4..8) at its
                // first row (from the pi window at the join-split PI offsets); block 0 also seeds rate-low
                // (lanes 0..4) = [DOM, 0,0,0]. Block b's rate-low for b>0 is the previous block's output, via
                // the sklink carry below. This reproduces `merge(prev, chunk_b)` per block.
                let srcs = self.fold_chunk_srcs();
                for (b, chunk) in srcs.iter().enumerate() {
                    let pf = p[self.p_fold_first(b)].clone();
                    for (k, &src) in chunk.iter().enumerate() {
                        let ck = match src {
                            Some(off) => cur[self.pw(self.pub_pi() + off)].clone(),
                            None => AB::Expr::ZERO,
                        };
                        builder.assert_zero(pf.clone() * (cur[self.af_p(4 + k)].clone() - ck));
                    }
                    if b == 0 {
                        builder.assert_zero(pf.clone() * (cur[self.af_p(0)].clone() - dom.clone()));
                        for k in 1..4 {
                            builder.assert_zero(pf.clone() * cur[self.af_p(k)].clone());
                        }
                    }
                }
                // s_k-chain internal link: block b output (last row lanes 0..4) → block b+1 rate-low (next row).
                let plink = p[self.p_fold_sklink()].clone();
                for k in 0..4 {
                    builder.when_transition().assert_zero(plink.clone() * (nxt[self.af_p(k)].clone() - cur[self.af_p(k)].clone()));
                }
                // last s_k block output (= s_k) → ROOT block rate-high (lanes 4..8).
                let pskl = p[self.p_fold_sklast()].clone();
                for k in 0..4 {
                    builder.when_transition().assert_zero(pskl.clone() * (nxt[self.af_p(4 + k)].clone() - cur[self.af_p(k)].clone()));
                }
            }
            // ROOT block first row: rate-low == the running root column (both modes).
            let prin = p[self.p_fold_rootin()].clone();
            for k in 0..4 {
                builder.assert_zero(prin.clone() * (cur[self.af_p(k)].clone() - cur[self.af_root(k)].clone()));
            }
            // running root: IV=0 at global row 0; held except at each instance's ROOT update; the ROOT block
            // output at the global last row == the block tx-root (the single public input).
            let prup = p[self.p_fold_rootupd()].clone();
            for k in 0..4 {
                builder.when_first_row().assert_zero(cur[self.af_root(k)].clone());
                builder.when_transition().assert_zero((one.clone() - prup.clone()) * (nxt[self.af_root(k)].clone() - cur[self.af_root(k)].clone()));
                builder.when_transition().assert_zero(prup.clone() * (nxt[self.af_root(k)].clone() - cur[self.af_p(k)].clone()));
                builder.when_last_row().assert_zero(cur[self.af_p(k)].clone() - txroot[k].clone());
            }
        }
    }
}
