//! Parameter sweep for the spend proof: proof size vs proven security vs prove/verify time.
//!
//! Run: `cargo run --release --bin sweep`. Each row proves a DEPTH-deep spend at the given FRI
//! parameters and measures the real proof size + timings, next to the proven/conjectured bits from
//! Plonky3's security accounting. Informs the C-04 / proof-size parameter choice (docs/sweep is in
//! docs/soundness-budget.md).

use lattica_prover_p3::full_spend_air::{demo_witness, sweep_one, SweepPoint};

fn p(log_blowup: usize, num_queries: usize, query_pow: usize, max_log_arity: usize, cap_height: usize) -> SweepPoint {
    SweepPoint { log_blowup, num_queries, query_pow, commit_pow: 0, max_log_arity, cap_height }
}

fn main() {
    let w = demo_witness();
    // (label, point) — grouped: security/rate tradeoff, then proof-size-only levers.
    let points = [
        ("lb4 q96 ar1 cap0 (old production)", p(4, 96, 16, 1, 0)),
        // proof-size-only levers (arity + cap) at the proven-103 base — find the floor for ≥100:
        ("lb4 q96 ar3 cap0", p(4, 96, 16, 3, 0)),
        ("lb4 q96 ar3 cap4", p(4, 96, 16, 3, 4)),
        ("lb4 q96 ar4 cap4", p(4, 96, 16, 4, 4)),
        ("lb4 q96 ar4 cap6", p(4, 96, 16, 4, 6)),
        ("lb4 q96 ar5 cap6", p(4, 96, 16, 5, 6)),
    ];

    println!(
        "{:<38} {:>6} {:>6} {:>10} {:>8} {:>8}",
        "config", "proven", "conj", "proof(KB)", "prove(ms)", "verify(ms)"
    );
    println!("{}", "-".repeat(86));
    for (label, point) in points {
        let r = sweep_one(&w, &point);
        println!(
            "{:<38} {:>6} {:>6} {:>10.1} {:>8} {:>8}",
            label,
            r.proven_bits,
            r.conjectured_bits,
            r.proof_bytes as f64 / 1024.0,
            r.prove_ms,
            r.verify_ms
        );
    }
}
