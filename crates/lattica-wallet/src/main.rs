//! Lattica wallet CLI.
//!
//! `lattica-wallet demo` runs a complete post-quantum shielded transfer end to end against
//! an in-memory chain and narrates every step.

use lattica_node::{build_transfer, Chain};
use lattica_primitives::sig::{PK_LEN, SIG_LEN};
use lattica_tx::{try_decrypt, FullKey};

fn short(bytes: &[u8]) -> String {
    let n = bytes.len().min(6);
    hex::encode(&bytes[..n])
}

fn main() {
    let cmd = std::env::args().nth(1).unwrap_or_else(|| "demo".to_string());
    match cmd.as_str() {
        "demo" => demo(),
        "keygen" => keygen(),
        other => {
            eprintln!("unknown command: {other}\nusage: lattica-wallet [demo|keygen]");
            std::process::exit(2);
        }
    }
}

fn keygen() {
    let key = FullKey::from_seed([42u8; 32]).expect("keygen");
    let addr = key.address();
    println!("Lattica account");
    println!("  recipient id : {}…", short(&addr.recipient_id()));
    println!("  ML-KEM ek    : {}… ({} bytes)", short(&addr.kem_ek), addr.kem_ek.len());
    println!("  ML-DSA pk    : {}… ({} bytes)", short(&key.sig.pk_bytes()), PK_LEN);
}

fn demo() {
    println!("=== Lattica: post-quantum shielded transfer demo ===\n");

    let mut chain = Chain::new();
    let alice = FullKey::from_seed([1u8; 32]).expect("alice");
    let bob = FullKey::from_seed([2u8; 32]).expect("bob");
    println!("Alice and Bob each hold a post-quantum account (ML-KEM + ML-DSA keys).\n");

    // 1. Mint funds to Alice.
    let (alice_note, alice_pos) = chain.mint(&alice.address(), 1000, [11u8; 32]).expect("mint");
    println!("[mint]   1000 minted to Alice as a shielded note at tree position {alice_pos}.");
    println!("         note commitment {}… inserted; anchor now {}…", short(&alice_note.commitment()), short(&chain.anchor()));
    match try_decrypt(&alice, &chain.transmitted[0]) {
        Some(n) => println!("         Alice trial-decrypts her note: value = {}.\n", n.value),
        None => println!("         (decryption failed!)\n"),
    }

    // 2. Alice builds a shielded transfer to Bob: 900 to Bob, 100 fee.
    let anchor = chain.anchor();
    let path = chain.merkle_path(alice_pos).expect("path");
    let tx = build_transfer(&alice, &alice_note, alice_pos, path, anchor, &bob.address(), 900, 100)
        .expect("build");
    println!("[build]  Alice spends her note: 900 to Bob, 100 fee.");
    println!("         nullifier    {}… (revealed; unlinkable to the note)", short(&tx.spends[0].nullifier));
    println!("         FRI proof    {} bytes (transparent, hash-based, no trusted setup)", tx.spends[0].auth.proof.len());
    println!("         binding sig  {SIG_LEN} bytes (ML-DSA)");
    let total = tx.spends[0].auth.proof.len() + SIG_LEN + tx.outputs[0].note.ciphertext.len() + tx.outputs[0].note.kem_ct.len();
    println!("         tx size     ~{total} bytes\n");

    // 3. The node validates and applies it.
    match chain.verify_and_apply(&tx) {
        Ok(()) => println!("[node]   transaction ACCEPTED: binding sig ✓  membership ✓  nullifier-unseen ✓  STARK ✓  balance ✓\n"),
        Err(e) => {
            println!("[node]   transaction REJECTED: {e}");
            std::process::exit(1);
        }
    }

    // 4. Bob scans the chain and decrypts his note.
    let bobs: Vec<_> = chain.transmitted.iter().filter_map(|tn| try_decrypt(&bob, tn)).collect();
    println!("[scan]   Bob scans {} transmitted notes; {} decrypt to him.", chain.transmitted.len(), bobs.len());
    if let Some(n) = bobs.first() {
        println!("         Bob receives a shielded note worth {}.\n", n.value);
    }

    // 5. Double-spend attempt.
    match chain.verify_and_apply(&tx) {
        Ok(()) => println!("[replay] ERROR: double-spend was accepted!"),
        Err(e) => println!("[replay] re-submitting the same transaction is REJECTED: {e}."),
    }

    println!("\nEvery cryptographic step above relies only on hash and lattice hardness —");
    println!("no elliptic-curve discrete log anywhere. Quantum-safe by construction.");
}
