//! Batch-AIR measurement: proof size vs number of spends in one proof.
//!
//! Run: `cargo run --release --bin batch`. Proves a batch of `n` spends as a single proof (the spend
//! statement tiled `n` times in one trace) and reports the proof size + timings, the per-spend
//! amortized size, and the saving vs `n` separate proofs. Demonstrates the storage win of one proof
//! per block: proof size grows ~log(n), so per-spend bytes fall sharply.

use lattica_prover_p3::full_spend_air::batch_measure;

const SINGLE_KB: f64 = 421.0; // production single-spend proof (lb4 q96 ar4 cap6)

fn main() {
    println!(
        "{:>4} {:>7} {:>11} {:>13} {:>13} {:>10} {:>9}",
        "n", "proven", "proof(KB)", "per-spend(KB)", "n×single(KB)", "prove(ms)", "verify(ms)"
    );
    println!("{}", "-".repeat(74));
    for n in [1usize, 2, 4, 8, 16, 32] {
        let r = batch_measure(n);
        let kb = r.proof_bytes as f64 / 1024.0;
        println!(
            "{:>4} {:>7} {:>11.1} {:>13.1} {:>13.0} {:>10} {:>9}",
            n,
            r.proven_bits,
            kb,
            kb / n as f64,
            SINGLE_KB * n as f64,
            r.prove_ms,
            r.verify_ms
        );
    }
}
