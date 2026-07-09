//! Trace builders for the fused monolith: `HidingWitness` + `monolith_build_trace` (and the live
//! `ft_build_trace` full-transcript filler it consumes, shared with the `lineage` AIRs and tests).

use p3_field::{Field, PrimeCharacteristicRing, TwoAdicField};
use p3_goldilocks::Goldilocks;
use p3_matrix::dense::RowMajorMatrix;

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

#[allow(dead_code)]
#[allow(clippy::type_complexity)]
pub(crate) fn monolith_build_trace(
    air: &MonolithAir,
    block_inputs: &[[Val; W]],
    per_query: &[(
        (usize, Vec<(Challenge, Challenge, Val)>, Challenge, Challenge, Vec<(Challenge, Challenge, bool, Val)>),
        Val,
        Vec<([Val; 4], bool)>,
    )],
    alpha_fri: [Val; 2],
    index_felts: &[Val],
    quot_paths: &[Vec<([Val; 4], bool)>],
    commit_data: &[Vec<([Val; 4], [Val; 4], Vec<([Val; 4], bool)>, [Val; 4])>],
    pub_window: &[Val],                  // column-window mode: the inner-proof pis values (empty otherwise)
    hiding: Option<&[HidingWitness]>,    // is_zk=1 only: per-query salts + random-round path (None for is_zk=0)
) -> RowMajorMatrix<Val> {
    use crate::recursion::fri_fold::native_fold;
    use p3_field::{BasedVectorSpace, PrimeField64};
    let c = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
    let h = air.height();
    let w = air.fused_w();
    let tr = air.tr();
    let g = Goldilocks::two_adic_generator(air.lg());
    let n_rounds = air.nb() - 3;
    let mut t = vec![Val::ZERO; h * w];
    // transcript region
    let ft = ft_build_trace(block_inputs);
    for r in 0..tr {
        for i in 0..W {
            t[r * w + i] = ft.values[r * W + i];
        }
    }
    // super-tile region
    for (q, ((index, terms, alpha, ro, rounds), _v, path)) in per_query.iter().enumerate() {
        let off = tr + q * air.m_period();
        // (the opened row is derived from the first W reduced-opening terms below — px-sharing)
        // arith block 0: fold chain E_0..E_{cm_rounds} (runtime with the FRI depth)
        let mut e = *ro;
        for r in 0..=air.cm_rounds() {
            let base = (off + r) * w;
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
        // arith head (row 0): DEEP + reduced + α/term columns
        let base0 = off * w;
        let mut acc = Val::ONE;
        for i in 0..air.lg() {
            let bit = (index >> i) & 1;
            t[base0 + QT_DBITS + i] = Val::from_u64(bit as u64);
            acc *= if bit == 1 { g.exp_power_of_2(air.lg() - 1 - i) } else { Val::ONE };
            t[base0 + air.qt_acc() + i] = acc;
        }
        let x = <Goldilocks as Field>::GENERATOR * acc;
        let ac = c(*alpha);
        t[base0 + air.qt_alpha()] = ac[0];
        t[base0 + air.qt_alpha() + 1] = ac[1];
        let mut apow = Challenge::ONE;
        for (k, &(z, pz, px)) in terms.iter().enumerate() {
            let (zc, pzc) = (c(z), c(pz));
            // NARROW: `z` is not stored (re-derived = ζ / ζ·g). FULL: store it.
            if !air.narrow_arith {
                t[base0 + air.z(k)] = zc[0];
                t[base0 + air.z(k) + 1] = zc[1];
            }
            // NARROW-OPENINGS drops `pz` from the tile too (externalized to the sponge-opening bus); FULL/NARROW-ARITH store it.
            if !air.narrow_openings {
                t[base0 + air.pz(k)] = pzc[0];
                t[base0 + air.pz(k) + 1] = pzc[1];
            }
            // `px`/`inv`/`apow` are FULL-only: NARROW sources px from the ov/qc carrier + externalizes the fold.
            if !air.narrow_arith {
                t[base0 + air.px(k)] = px;
                let inv = c((z - Challenge::from(x)).inverse());
                t[base0 + air.inv(k)] = inv[0];
                t[base0 + air.inv(k) + 1] = inv[1];
                let ap = c(apow);
                t[base0 + air.apow(k)] = ap[0];
                t[base0 + air.apow(k) + 1] = ap[1];
            }
            apow *= *alpha;
        }
        // SB (canonical index decomposition) on the arith head + the idx_rem shift register
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
            t[(off + r) * w + air.idx_rem()] = Val::from_u64(rem);
            if r < n_rounds {
                rem >>= 1;
            }
        }
        // helper: fill a merge block at `blk` (input = bit-ordered(node, sib)); returns the next node.
        let merge_block = |t: &mut [Val], off: usize, blk: usize, node: [Val; 4], sib: [Val; 4], b: bool| -> [Val; 4] {
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
                let base = (off + blk * BLOCK + r) * w;
                t[base..base + W].copy_from_slice(&rows[r]);
                t[base + air.m_sib()..base + air.m_sib() + 4].copy_from_slice(&sib);
                t[base + air.m_bit()] = if b { Val::ONE } else { Val::ZERO };
            }
            native_permute(inp)[..4].try_into().unwrap()
        };
        // generic salted leaf-hash: absorb `preimage` RATE felts/block over ceil(len/RATE) blocks (PaddingFree-
        // Sponge overwrite-mode — a short final block leaves the un-overwritten rate lanes carrying), filling
        // blocks start_block.. and returning the sponge output. Used for every leaf (random/trace/quot/commit);
        // at is_zk=0 the preimage is the raw committed row (no salt), so this is the exact milestone leaf-hash.
        let leaf_hash = |t: &mut [Val], off: usize, start_block: usize, preimage: &[Val]| -> [Val; 4] {
            let mut state = [Val::ZERO; W];
            let nblk = preimage.len().div_ceil(RATE);
            for b in 0..nblk {
                let clen = core::cmp::min(RATE, preimage.len() - b * RATE);
                state[..clen].copy_from_slice(&preimage[b * RATE..b * RATE + clen]); // overwrite rate lanes 0..clen
                let rows = native_steps(state);
                for r in 0..BLOCK {
                    let base = (off + (start_block + b) * BLOCK + r) * w;
                    t[base..base + W].copy_from_slice(&rows[r]);
                }
                state = native_permute(state);
            }
            state[..4].try_into().unwrap()
        };
        let hq = hiding.map(|hh| &hh[q]);
        // leaf preimages = the committed row (from the reduced-opening px terms, px-shared) ‖ salt (is_zk=1, fresh
        // witness — authenticated by folding to the committed cap). is_zk=0 ⇒ the raw opened row / 2·nqc quotient
        // row (byte-for-byte).
        let mut input_preimage: Vec<Val> = (0..air.trm_committed_w()).map(|cc| terms[air.trm_trace(cc)].2).collect();
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
            random_preimage = (0..air.random_committed_w()).map(|cc| terms[cc].2).collect();
            random_preimage.extend_from_slice(&hqv.random_salt);
        }
        // HIDING random-round leaf (is_zk=1): blocks M_INPUT_LEAF.., then input_depth merges → the random cap entry.
        let random_cap_entry: [Val; 4] = if air.is_zk == 1 {
            let mut node = leaf_hash(&mut t, off, M_INPUT_LEAF, &random_preimage);
            let start = M_INPUT_LEAF + air.random_leaf_blocks();
            for (l, &(sib, b)) in hq.unwrap().random_path.iter().enumerate() {
                node = merge_block(&mut t, off, start + l, node, sib, b);
            }
            node
        } else {
            [Val::ZERO; 4]
        };
        // inline (trace) input-Merkle: multi-block salted leaf (blocks m_input_leaf..) + input_depth merges.
        let trace_cap_entry = {
            let mut node = leaf_hash(&mut t, off, air.m_input_leaf(), &input_preimage);
            let start = air.m_input_leaf() + air.leaf_blocks();
            for (l, &(sib, b)) in path.iter().enumerate() {
                node = merge_block(&mut t, off, start + l, node, sib, b);
            }
            node
        };
        // inline quotient-Merkle: multi-block (multi-matrix salted, is_zk=1) leaf (blocks m_quot_leaf..) + merges.
        let quot_cap_entry = {
            let mut node = leaf_hash(&mut t, off, air.m_quot_leaf(), &quot_preimage);
            let start = air.m_quot_leaf() + air.quot_leaf_blocks();
            for (l, &(sib, b)) in quot_paths[q].iter().enumerate() {
                node = merge_block(&mut t, off, start + l, node, sib, b);
            }
            node
        };
        // inline commit-phase Merkle: cm_rounds rounds, each a (salted, is_zk=1 ⇒ 2-block) leaf-hash + `depth`
        // merges, authenticating every fold sibling to commit_phase_commits[r].
        let mut commit_cap_entries = vec![[Val::ZERO; 4]; air.cm_rounds()];
        for (r, (group, _leaf, cpath, _cap)) in commit_data[q].iter().enumerate() {
            let mut cpreimage: Vec<Val> = group.to_vec();
            if air.is_zk == 1 {
                cpreimage.extend_from_slice(&hq.unwrap().commit_salts[r]);
            }
            let mut cnode = leaf_hash(&mut t, off, air.cm_leaf(r), &cpreimage);
            let start = air.cm_leaf(r) + air.cm_leaf_blocks();
            for (l, &(sib, b)) in cpath.iter().enumerate() {
                cnode = merge_block(&mut t, off, start + l, cnode, sib, b);
            }
            commit_cap_entries[r] = cnode; // this round's commit-Merkle terminal == the selected commit cap
        }
        // carriers held within this super-tile: the input/random/quot leaf preimages + the fold groups (+ the
        // per-query cap-entry carriers, including the random cap, when verifying a non-constant/hiding inner).
        for r in 0..air.m_period() {
            for (cc, &v) in input_preimage.iter().enumerate() {
                t[(off + r) * w + air.ov_c(cc)] = v;
            }
            if air.is_zk == 1 {
                for (cc, &v) in random_preimage.iter().enumerate() {
                    t[(off + r) * w + air.ov_random(cc)] = v;
                }
            }
            for (cc, &qv) in quot_preimage.iter().enumerate() {
                t[(off + r) * w + air.qc(cc)] = qv;
            }
            for (cr, (group, _l, _p, _c)) in commit_data[q].iter().enumerate() {
                for k in 0..4 {
                    t[(off + r) * w + air.cg(cr, k)] = group[k];
                }
            }
            if air.full_cap() {
                for k in 0..4 {
                    t[(off + r) * w + air.cap_c(k)] = trace_cap_entry[k];
                    t[(off + r) * w + air.cap_c(4 + k)] = quot_cap_entry[k];
                    for cr in 0..air.cm_rounds() {
                        t[(off + r) * w + air.cap_c(8 + 4 * cr + k)] = commit_cap_entries[cr][k];
                    }
                    if air.is_zk == 1 {
                        t[(off + r) * w + air.cap_c(8 + 4 * air.cm_rounds() + k)] = random_cap_entry[k];
                    }
                }
            }
        }
    }
    // α_fri carrier held across the whole trace
    for r in 0..h {
        t[r * w + air.carry()] = alpha_fri[0];
        t[r * w + air.carry() + 1] = alpha_fri[1];
    }
    // column-window: fill the inner-proof pis window + the ζ-squaring chain (held constant across the trace).
    if air.column_window {
        use p3_field::BasedVectorSpace;
        let cc = |x: Challenge| -> [Val; 2] { x.as_basis_coefficients_slice().try_into().unwrap() };
        let zeta = Challenge::from_basis_coefficients_fn(|k| pub_window[2 + k]); // ζ = pis[2,3]
        let mut sch_vals = vec![[Val::ZERO; 2]; air.cm_rounds()];
        let mut s = zeta;
        for sv in sch_vals.iter_mut() {
            s = s * s; // S_{i+1} = S_i²
            *sv = cc(s);
        }
        for r in 0..h {
            for (i, &v) in pub_window.iter().enumerate() {
                t[r * w + air.pw(i)] = v;
            }
            for (i, sv) in sch_vals.iter().enumerate() {
                t[r * w + air.sch(2 * i)] = sv[0];
                t[r * w + air.sch(2 * i) + 1] = sv[1];
            }
        }
    }
    RowMajorMatrix::new(t, w)
}
