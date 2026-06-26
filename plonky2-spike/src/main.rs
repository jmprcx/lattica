//! ZK-01 spike — the shielded spend statement on **plonky2** (transparent, FRI-based, ZK-capable).
//!
//! Compare against the Winterfell `lattica-prover`: plonky2 provides **zero-knowledge** out of the
//! box (`standard_recursion_zk_config`), a **vetted Poseidon** hash gadget over the same Goldilocks
//! field, and **range-check / select** as gadgets — so the whole spend statement is expressed in a
//! few dozen lines, versus the hand-written AIR (periodic selectors, `rem` columns, round
//! constraints) in Winterfell. This spike decides ZK-01 (Winterfell has no ZK).
//!
//! Statement (public: root, nf, out_cm, fee, tx_binding; private: the note + output + path):
//!   ownership   recipient = Poseidon(nk)[0]
//!   commitment  cm  = Poseidon(recipient, value, rho, rcm)
//!   membership  cm folds (general position) up a 2-level path to `root`
//!   nullifier   nf  = Poseidon(nk, rho, pos)
//!   output      out_cm = Poseidon(out_recipient, out_value, out_rho, out_rcm)
//!   balance     value = out_value + fee
//!   range       value, out_value < 2^32
//! All under a zero-knowledge proof.

use anyhow::Result;
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::hash_types::{HashOut, HashOutTarget};
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};
use plonky2::plonk::config::{Hasher, PoseidonGoldilocksConfig};
use plonky2::plonk::proof::ProofWithPublicInputs;

const D: usize = 2;
type C = PoseidonGoldilocksConfig;
type F = GoldilocksField;

const DEPTH: usize = 2; // membership levels (demo; plonky2 scales to 32 by looping)
const RANGE_BITS: usize = 32;

/// Private witness for one spend.
#[derive(Clone, Copy)]
struct Witness {
    nk: u64,
    value: u64,
    rho: u64,
    rcm: u64,
    pos: u64,
    siblings: [[u64; 4]; DEPTH],
    bits: [bool; DEPTH],
    out_recipient: u64,
    out_value: u64,
    out_rho: u64,
    out_rcm: u64,
    fee: u64,
    tx_binding: [u64; 4],
}

/// Input targets needed to assign the witness.
struct Targets {
    nk: Target,
    value: Target,
    rho: Target,
    rcm: Target,
    pos: Target,
    siblings: [HashOutTarget; DEPTH],
    bits: [BoolTarget; DEPTH],
    out_recipient: Target,
    out_value: Target,
    out_rho: Target,
    out_rcm: Target,
    fee: Target,
    tx_binding: HashOutTarget,
}

fn h(elems: &[u64]) -> [u64; 4] {
    let inputs: Vec<F> = elems.iter().map(|&x| F::from_canonical_u64(x)).collect();
    let out: HashOut<F> = PoseidonHash::hash_no_pad(&inputs);
    [
        out.elements[0].to_canonical_u64(),
        out.elements[1].to_canonical_u64(),
        out.elements[2].to_canonical_u64(),
        out.elements[3].to_canonical_u64(),
    ]
}

/// Native oracle: the public (root, nf, out_cm) for a witness.
fn native_public(w: &Witness) -> ([u64; 4], [u64; 4], [u64; 4]) {
    let recipient = h(&[w.nk])[0];
    let mut node = h(&[recipient, w.value, w.rho, w.rcm]); // cm
    for d in 0..DEPTH {
        let (l, r) = if w.bits[d] { (w.siblings[d], node) } else { (node, w.siblings[d]) };
        node = h(&[l[0], l[1], l[2], l[3], r[0], r[1], r[2], r[3]]);
    }
    let nf = h(&[w.nk, w.rho, w.pos]);
    let out_cm = h(&[w.out_recipient, w.out_value, w.out_rho, w.out_rcm]);
    (node, nf, out_cm)
}

/// Build the spend circuit. Public-input order: root(4) ‖ nf(4) ‖ out_cm(4) ‖ fee(1) ‖ tx_binding(4).
fn build(zk: bool) -> (CircuitData<F, C, D>, Targets) {
    let config = if zk {
        CircuitConfig::standard_recursion_zk_config()
    } else {
        CircuitConfig::standard_recursion_config()
    };
    let mut b = CircuitBuilder::<F, D>::new(config);

    let nk = b.add_virtual_target();
    let value = b.add_virtual_target();
    let rho = b.add_virtual_target();
    let rcm = b.add_virtual_target();
    let pos = b.add_virtual_target();
    let siblings: [HashOutTarget; DEPTH] = core::array::from_fn(|_| b.add_virtual_hash());
    let bits: [BoolTarget; DEPTH] = core::array::from_fn(|_| b.add_virtual_bool_target_safe());
    let out_recipient = b.add_virtual_target();
    let out_value = b.add_virtual_target();
    let out_rho = b.add_virtual_target();
    let out_rcm = b.add_virtual_target();
    let fee = b.add_virtual_target();
    let tx_binding = b.add_virtual_hash();

    // ownership: recipient = Poseidon(nk)[0]
    let recipient = b.hash_n_to_hash_no_pad::<PoseidonHash>(vec![nk]).elements[0];

    // commitment: cm = Poseidon(recipient, value, rho, rcm)
    let mut node = b.hash_n_to_hash_no_pad::<PoseidonHash>(vec![recipient, value, rho, rcm]);

    // membership: fold cm up a general-position path to the root
    for d in 0..DEPTH {
        let sib = siblings[d];
        let bit = bits[d];
        // (left, right) = bit ? (sib, node) : (node, sib), element-wise
        let mut inputs = Vec::with_capacity(8);
        for i in 0..4 {
            inputs.push(b.select(bit, sib.elements[i], node.elements[i]));
        }
        for i in 0..4 {
            inputs.push(b.select(bit, node.elements[i], sib.elements[i]));
        }
        node = b.hash_n_to_hash_no_pad::<PoseidonHash>(inputs);
    }
    b.register_public_inputs(&node.elements); // root

    // nullifier: nf = Poseidon(nk, rho, pos)
    let nf = b.hash_n_to_hash_no_pad::<PoseidonHash>(vec![nk, rho, pos]);
    b.register_public_inputs(&nf.elements);

    // output commitment
    let out_cm = b.hash_n_to_hash_no_pad::<PoseidonHash>(vec![out_recipient, out_value, out_rho, out_rcm]);
    b.register_public_inputs(&out_cm.elements);

    // value-balance: value = out_value + fee
    let out_plus_fee = b.add(out_value, fee);
    b.connect(value, out_plus_fee);

    // range: value, out_value < 2^RANGE_BITS (gadget — no hand-rolled bit columns)
    b.range_check(value, RANGE_BITS);
    b.range_check(out_value, RANGE_BITS);

    // fee + tx-binding as public inputs (tx-binding ties the proof to its transaction)
    b.register_public_input(fee);
    b.register_public_inputs(&tx_binding.elements);

    let data = b.build::<C>();
    let t = Targets {
        nk, value, rho, rcm, pos, siblings, bits, out_recipient, out_value, out_rho, out_rcm, fee, tx_binding,
    };
    (data, t)
}

fn prove(data: &CircuitData<F, C, D>, t: &Targets, w: &Witness) -> Result<ProofWithPublicInputs<F, C, D>> {
    let mut pw = PartialWitness::new();
    pw.set_target(t.nk, F::from_canonical_u64(w.nk))?;
    pw.set_target(t.value, F::from_canonical_u64(w.value))?;
    pw.set_target(t.rho, F::from_canonical_u64(w.rho))?;
    pw.set_target(t.rcm, F::from_canonical_u64(w.rcm))?;
    pw.set_target(t.pos, F::from_canonical_u64(w.pos))?;
    for d in 0..DEPTH {
        let sib = HashOut::from_vec(w.siblings[d].iter().map(|&x| F::from_canonical_u64(x)).collect());
        pw.set_hash_target(t.siblings[d], sib)?;
        pw.set_bool_target(t.bits[d], w.bits[d])?;
    }
    pw.set_target(t.out_recipient, F::from_canonical_u64(w.out_recipient))?;
    pw.set_target(t.out_value, F::from_canonical_u64(w.out_value))?;
    pw.set_target(t.out_rho, F::from_canonical_u64(w.out_rho))?;
    pw.set_target(t.out_rcm, F::from_canonical_u64(w.out_rcm))?;
    pw.set_target(t.fee, F::from_canonical_u64(w.fee))?;
    let txb = HashOut::from_vec(w.tx_binding.iter().map(|&x| F::from_canonical_u64(x)).collect());
    pw.set_hash_target(t.tx_binding, txb)?;
    data.prove(pw)
}

fn sample() -> Witness {
    Witness {
        nk: 0x5555_6666,
        value: 1000,
        rho: 0x1111_2222,
        rcm: 0x3333_4444,
        pos: 42,
        siblings: [[1, 2, 3, 4], [5, 6, 7, 8]],
        bits: [false, true],
        out_recipient: 0xBEEF,
        out_value: 900,
        out_rho: 0x7777,
        out_rcm: 0x8888,
        fee: 100,
        tx_binding: [9, 10, 11, 12],
    }
}

fn main() -> Result<()> {
    use std::time::Instant;
    let w = sample();

    let t0 = Instant::now();
    let (data, targets) = build(true); // zero-knowledge
    let build_ms = t0.elapsed().as_millis();

    let t1 = Instant::now();
    let proof = prove(&data, &targets, &w)?;
    let prove_ms = t1.elapsed().as_millis();

    let size = proof.to_bytes().len();

    // public-input cross-check against the native oracle
    let (root, nf, out_cm) = native_public(&w);
    let pi: Vec<u64> = proof.public_inputs.iter().map(|x| x.to_canonical_u64()).collect();
    let pi_root = &pi[0..4];
    let pi_nf = &pi[4..8];
    let pi_out = &pi[8..12];
    assert_eq!(pi_root, &root, "root mismatch vs native");
    assert_eq!(pi_nf, &nf, "nf mismatch vs native");
    assert_eq!(pi_out, &out_cm, "out_cm mismatch vs native");

    let t2 = Instant::now();
    data.verify(proof.clone())?;
    let verify_ms = t2.elapsed().as_millis();

    // ZK evidence: a second proof of the same statement (re-randomized blinding) differs.
    let proof2 = prove(&data, &targets, &w)?;
    let randomized = proof.to_bytes() != proof2.to_bytes();

    println!("plonky2 spend-core spike (zero-knowledge config)");
    println!("  field            : Goldilocks (64-bit), FRI, transparent, PQ");
    println!("  hash             : Poseidon (vetted gadget)");
    println!("  membership depth : {DEPTH} (general position, gadget select)");
    println!("  range            : {RANGE_BITS}-bit (gadget range_check)");
    println!("  build time       : {build_ms} ms");
    println!("  prove time       : {prove_ms} ms");
    println!("  verify time      : {verify_ms} ms");
    println!("  proof size       : {size} bytes");
    println!("  public inputs    : {} field elements", proof.public_inputs.len());
    println!("  ZK re-randomized : {randomized}");
    println!("  verify           : ACCEPTED");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_spend_verifies_and_matches_native() -> Result<()> {
        let w = sample();
        let (data, t) = build(true);
        let proof = prove(&data, &t, &w)?;
        let (root, nf, out_cm) = native_public(&w);
        let pi: Vec<u64> = proof.public_inputs.iter().map(|x| x.to_canonical_u64()).collect();
        assert_eq!(&pi[0..4], &root);
        assert_eq!(&pi[4..8], &nf);
        assert_eq!(&pi[8..12], &out_cm);
        data.verify(proof)
    }

    #[test]
    fn unbalanced_fails_to_prove() {
        // value != out_value + fee ⇒ the connect() constraint is unsatisfiable ⇒ proving fails.
        let mut w = sample();
        w.value = 1001; // 900 + 100 != 1001
        let (data, t) = build(true);
        assert!(prove(&data, &t, &w).is_err());
    }

    #[test]
    fn out_of_range_fails_to_prove() {
        let mut w = sample();
        w.value = 1u64 << 33; // > 2^32
        w.out_value = (1u64 << 33) - 100; // keep balance so range is what fails
        let (data, t) = build(true);
        assert!(prove(&data, &t, &w).is_err());
    }

    #[test]
    fn tampered_public_root_rejected() -> Result<()> {
        let w = sample();
        let (data, t) = build(true);
        let mut proof = prove(&data, &t, &w)?;
        proof.public_inputs[0] += F::ONE; // claim a different root
        assert!(data.verify(proof).is_err());
        Ok(())
    }

    #[test]
    fn zero_knowledge_proofs_are_randomized() -> Result<()> {
        let w = sample();
        let (data, t) = build(true);
        let p1 = prove(&data, &t, &w)?;
        let p2 = prove(&data, &t, &w)?;
        // both verify; ZK blinding should make the two proofs differ
        data.verify(p1.clone())?;
        data.verify(p2.clone())?;
        assert_ne!(p1.to_bytes(), p2.to_bytes(), "ZK config should re-randomize proofs");
        Ok(())
    }
}
