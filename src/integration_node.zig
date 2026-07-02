//! Real in-node integration: drive the live node (`node.zig`) end-to-end against the **real** Rust
//! prover/verifier (`lattica_joinsplit_prove` / `lattica_joinsplit_verify`), not the mock backends.
//!
//! This exercises the one seam the `zig build test` suite cannot (the mock backends + this host's
//! linker hide it): Zig builds the witness → Rust proves → Zig reconstructs the public inputs → Rust
//! verifies → the node applies / rejects. Built as a relocatable object and linked with the system
//! toolchain (so gcc's crt is handled), since Zig's own linker can't link the libc-dependent Rust
//! staticlib here:
//!   zig build-obj src/integration_node.zig -OReleaseSafe -lc -femit-bin=integration_node.o
//!   cc integration_node.o lattica-prover-p3/target/release/liblattica_prover_p3.a -lpthread -ldl -lm
//!   ./a.out   # exits 0 on success

const std = @import("std");
const node = @import("node.zig");
const tx = @import("tx.zig");
const ffi = @import("ffi.zig");
const poseidon2 = @import("poseidon2.zig");

// The production C ABI implemented by lattica-prover-p3 (extern declarations centralized in
// prover_abi.zig, mirroring lattica-prover-p3/include/lattica_prover_p3.h).
const prover_abi = @import("prover_abi.zig");
const lattica_joinsplit_prove = prover_abi.lattica_joinsplit_prove;
const lattica_joinsplit_verify = prover_abi.lattica_joinsplit_verify;
const lattica_htlc_prove = prover_abi.lattica_htlc_prove;
const lattica_htlc_verify = prover_abi.lattica_htlc_verify;
const lattica_batch_prove = prover_abi.lattica_batch_prove;
const lattica_batch_verify = prover_abi.lattica_batch_verify;
const lattica_htlc_batch_prove = prover_abi.lattica_htlc_batch_prove;
const lattica_htlc_batch_verify = prover_abi.lattica_htlc_batch_verify;

export fn main() callconv(.c) c_int {
    run() catch |e| {
        std.debug.print("FAIL: {s}\n", .{@errorName(e)});
        return 1;
    };
    return 0;
}

const Err = error{ BobDidNotReceive, DoubleSpendAccepted, TamperAccepted, WrongError, BatchRootMismatch, BatchRejected };

fn run() !void {
    const a = std.heap.c_allocator;

    // Install the REAL backends (production wiring).
    ffi.setJoinSplitProveBackend(&lattica_joinsplit_prove);
    ffi.setJoinSplitBackend(&lattica_joinsplit_verify);

    var chain = try node.Chain.init(a);
    defer chain.deinit();
    const alice = try tx.FullKey.fromSeed([_]u8{1} ** 32);
    const bob = try tx.FullKey.fromSeed([_]u8{2} ** 32);

    // Alice holds a 1000 note + a zero-value padding note (both real tree members).
    const m0 = try chain.bootstrapMint(alice.address(), 1000, [_]u8{11} ** 32);
    const m1 = try chain.bootstrapMint(alice.address(), 0, [_]u8{12} ** 32);
    const inputs = [_]node.InputSpend{
        .{ .note = m0.note, .position = m0.pos, .path = try chain.merklePath(a, m0.pos) },
        .{ .note = m1.note, .position = m1.pos, .path = try chain.merklePath(a, m1.pos) },
    };
    const outs = [_]node.OutputReq{.{ .recipient = bob.address(), .value = 900 }};

    // buildTransfer runs the REAL prover (Zig-encoded witness -> Rust prove).
    const t = try node.buildTransfer(a, alice, &inputs, &outs, 100, 0, chain.anchor());
    std.debug.print("real prove: proof = {d} bytes\n", .{t.proof.len});

    // Audit C-01, real-verifier path — run on the FRESH (unspent) tx so it reaches the verifier (the
    // reordered validation rejects an already-spent tx as DoubleSpend before verifying). Swapping in an
    // unproven output commitment (outputs[j].cm is the single source bound by both the proof's public
    // inputs and tx_binding) ⇒ the REAL verifier rejects; nothing is applied (anchor unchanged).
    {
        const anchor_before = chain.anchor();
        var tampered = t;
        tampered.outputs[0].cm[0] +%= 1;
        if (chain.verifyAndApply(tampered)) |_| {
            return Err.TamperAccepted;
        } else |e| if (e != node.TxError.BadAuthProof) return Err.WrongError;
        if (!std.mem.eql(u8, &anchor_before, &chain.anchor())) return Err.TamperAccepted;
        std.debug.print("ghost/tampered out_cm: REJECT (real verifier)\n", .{});
    }

    // verifyAndApply runs the REAL verifier (Zig-reconstructed public inputs -> Rust verify).
    try chain.verifyAndApply(t);
    std.debug.print("real verify (in-node): ACCEPT\n", .{});

    // Bob decrypts exactly his 900 note.
    var bob_total: u64 = 0;
    for (chain.transmitted.items) |tn| {
        if (tx.tryDecrypt(a, bob, tn)) |n| bob_total += n.value;
    }
    if (bob_total != 900) return Err.BobDidNotReceive;
    std.debug.print("bob receives: {d}\n", .{bob_total});

    // Replay is a double-spend.
    if (chain.verifyAndApply(t)) |_| {
        return Err.DoubleSpendAccepted;
    } else |e| if (e != node.TxError.DoubleSpend) return Err.WrongError;
    std.debug.print("double-spend (replay): REJECT\n", .{});

    // --- v3: a REAL shielded HTLC LOCK → REDEEM lifecycle (Zig builds the lock + spend witnesses, Rust
    //         proves, Zig reconstructs the public inputs, Rust verifies, the node applies). This covers
    //         the cross-language witness/PI byte-match for BOTH htlc_air paths (PLAIN-inputs-HTLC-output
    //         lock + HTLC-input spend) that the mock backends cannot. ---
    ffi.setHtlcProveBackend(&lattica_htlc_prove);
    ffi.setHtlcBackend(&lattica_htlc_verify);
    const dave = try tx.FullKey.fromSeed([_]u8{5} ** 32); // the locker
    const carol = try tx.FullKey.fromSeed([_]u8{3} ** 32); // the redeem party
    const refunder = try tx.FullKey.fromSeed([_]u8{4} ** 32);
    const preimage = [_]u8{0xAB} ** 32;
    var sha: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(&preimage, &sha, .{});
    const hashlock = poseidon2.digestBytes(poseidon2.digestFromBytes(sha));
    const redeem_tag = carol.address().recipientId();
    const refund_tag = refunder.address().recipientId();
    const timeout: u64 = 100;

    // LOCK: Dave funds 1000 and locks it into an HTLC note (redeem=Carol, refund=Refunder).
    const f0 = try chain.bootstrapMint(dave.address(), 1000, [_]u8{21} ** 32);
    const f1 = try chain.bootstrapMint(dave.address(), 0, [_]u8{22} ** 32);
    const li = [_]node.InputSpend{
        .{ .note = f0.note, .position = f0.pos, .path = try chain.merklePath(a, f0.pos) },
        .{ .note = f1.note, .position = f1.pos, .path = try chain.merklePath(a, f1.pos) },
    };
    const lock = try node.buildHtlcLock(a, dave, &li, redeem_tag, refund_tag, hashlock, timeout, 1000, 0, 50, chain.anchor());
    const htlc_pos = f1.pos + 1; // the lock's output 0 (the HTLC note) lands right after Dave's funded notes
    std.debug.print("real htlc lock: proof = {d} bytes\n", .{lock.tx.proof.len});
    try chain.applyHtlc(lock.tx, 50);
    std.debug.print("real htlc lock verify (in-node): ACCEPT\n", .{});

    // A refund before the timeout must be rejected by the REAL prover (time-lock holds end to end). The
    // locked note is untouched (the build fails before any state change), so the redeem below proceeds.
    {
        const d_ref = try chain.bootstrapMint(refunder.address(), 0, [_]u8{23} ** 32);
        const refund = node.HtlcSpend{ .note = lock.note, .position = htlc_pos, .path = try chain.merklePath(a, htlc_pos), .claim_div = refunder.address().div, .mode = 0, .redeem_tag = redeem_tag, .refund_tag = refund_tag, .hashlock = hashlock, .timeout = timeout, .preimage = null };
        const d_in = node.InputSpend{ .note = d_ref.note, .position = d_ref.pos, .path = try chain.merklePath(a, d_ref.pos) };
        const o_ref = [_]node.OutputReq{.{ .recipient = refunder.address(), .value = 1000 }};
        if (node.buildHtlcSpend(a, refunder, refund, d_in, &o_ref, 0, 50, chain.anchor())) |_| { // height 50 < timeout 100
            return Err.TamperAccepted;
        } else |e| if (e != node.TxError.ProveFailed) return Err.WrongError;
        std.debug.print("refund before timeout: REJECT (real prover)\n", .{});
    }

    // REDEEM: Carol spends the created HTLC note before the timeout (opening from the communicated lock).
    const cdummy = try chain.bootstrapMint(carol.address(), 0, [_]u8{24} ** 32);
    const spend = node.HtlcSpend{ .note = lock.note, .position = htlc_pos, .path = try chain.merklePath(a, htlc_pos), .claim_div = carol.address().div, .mode = 1, .redeem_tag = redeem_tag, .refund_tag = refund_tag, .hashlock = hashlock, .timeout = timeout, .preimage = preimage };
    const sdummy = node.InputSpend{ .note = cdummy.note, .position = cdummy.pos, .path = try chain.merklePath(a, cdummy.pos) };
    const outs2 = [_]node.OutputReq{.{ .recipient = carol.address(), .value = 1000 }};
    const ht = try node.buildHtlcSpend(a, carol, spend, sdummy, &outs2, 0, 60, chain.anchor()); // height 60 < timeout 100
    std.debug.print("real htlc redeem: proof = {d} bytes\n", .{ht.proof.len});
    try chain.applyHtlc(ht, 60);
    std.debug.print("real htlc redeem verify (in-node): ACCEPT\n", .{});
    var carol_total: u64 = 0;
    for (chain.transmitted.items) |tn| {
        if (tx.tryDecrypt(a, carol, tn)) |n| carol_total += n.value;
    }
    if (carol_total != 1000) return Err.BobDidNotReceive;
    std.debug.print("carol redeemed (real htlc lifecycle): {d}\n", .{carol_total});

    // --- v3: REAL batch aggregation — TWO join-splits proven as ONE proof; the node recomputes the
    //         block tx-root from the tx statements (no witnesses) and the real verifier checks the one
    //         proof. This is the definitive Zig↔Rust byte-match for the batch fold. ---
    ffi.setBatchProveBackend(&lattica_batch_prove);
    ffi.setBatchBackend(&lattica_batch_verify);
    {
        const eve = try tx.FullKey.fromSeed([_]u8{6} ** 32);
        const g0 = try chain.bootstrapMint(eve.address(), 500, [_]u8{30} ** 32);
        const g1 = try chain.bootstrapMint(eve.address(), 0, [_]u8{31} ** 32);
        const g2 = try chain.bootstrapMint(eve.address(), 700, [_]u8{32} ** 32);
        const g3 = try chain.bootstrapMint(eve.address(), 0, [_]u8{33} ** 32);
        const anchor = chain.anchor();
        const inA = [_]node.InputSpend{
            .{ .note = g0.note, .position = g0.pos, .path = try chain.merklePath(a, g0.pos) },
            .{ .note = g1.note, .position = g1.pos, .path = try chain.merklePath(a, g1.pos) },
        };
        const inB = [_]node.InputSpend{
            .{ .note = g2.note, .position = g2.pos, .path = try chain.merklePath(a, g2.pos) },
            .{ .note = g3.note, .position = g3.pos, .path = try chain.merklePath(a, g3.pos) },
        };
        const outA = [_]node.OutputReq{.{ .recipient = bob.address(), .value = 450 }};
        const outB = [_]node.OutputReq{.{ .recipient = bob.address(), .value = 650 }};
        const ba = try node.buildTransferWitness(a, eve, &inA, &outA, 50, 0, anchor);
        defer a.free(ba.witness);
        defer for (ba.tx.outputs) |t_| a.free(t_.ciphertext);
        const bb = try node.buildTransferWitness(a, eve, &inB, &outB, 50, 0, anchor);
        defer a.free(bb.witness);
        defer for (bb.tx.outputs) |t_| a.free(t_.ciphertext);

        // concatenate the two prover witnesses and prove them as ONE batch proof (REAL prover)
        const wcat = try a.alloc(u8, ba.witness.len + bb.witness.len);
        defer a.free(wcat);
        @memcpy(wcat[0..ba.witness.len], ba.witness);
        @memcpy(wcat[ba.witness.len..], bb.witness);
        const r = try ffi.proveBatch(a, wcat, 2);
        defer a.free(r.proof);
        std.debug.print("real batch prove: 2 txs -> {d}-byte proof\n", .{r.proof.len});

        // the node recomputes the SAME tx-root from the two tx statements (no witnesses needed)
        const txs = [_]node.ShieldedTx{ ba.tx, bb.tx };
        const node_root = node.batchRoot(&txs);
        if (!std.mem.eql(u8, &node_root, &r.root)) return Err.BatchRootMismatch;
        std.debug.print("batch tx-root: Zig node == Rust circuit\n", .{});

        // the real verifier accepts the single batch proof against that root…
        if (!ffi.verifyBatch(r.proof, r.root)) return Err.BatchRejected;
        std.debug.print("real batch verify: ACCEPT\n", .{});

        // …and rejects a tampered root (any altered tx statement ⇒ a different root ⇒ reject)
        var bad = r.root;
        bad[0] +%= 1;
        if (ffi.verifyBatch(r.proof, bad)) return Err.TamperAccepted;
        std.debug.print("batch verify vs tampered root: REJECT\n", .{});

        // APPLY: ONE proof authorizes both txs; the node applies them atomically (no per-tx verify).
        try chain.applyBatch(&txs, r.proof);
        if (!chain.nullifiers.contains(ba.tx.nullifiers[0]) or !chain.nullifiers.contains(bb.tx.nullifiers[0])) return Err.BatchRejected;
        std.debug.print("real batch APPLY: 2 txs applied via one proof\n", .{});
        // re-applying is a double-spend (both txs' nullifiers are now in the set).
        if (chain.applyBatch(&txs, r.proof)) |_| return Err.DoubleSpendAccepted else |e| if (e != node.TxError.DoubleSpend) return Err.WrongError;
        std.debug.print("batch re-apply: REJECT (double-spend)\n", .{});
    }

    // --- v3: REAL HTLC batch — two HTLC redeems proven as ONE proof; the node recomputes the HTLC
    //         tx-root (incl. current_height + redeem_hashlock) and the real verifier checks one proof. ---
    ffi.setHtlcBatchProveBackend(&lattica_htlc_batch_prove);
    ffi.setHtlcBatchBackend(&lattica_htlc_batch_verify);
    {
        // two fresh locks (dave → carol), then two redeem WITNESSES batched into one proof.
        const ga = try chain.bootstrapMint(dave.address(), 300, [_]u8{40} ** 32);
        const gb = try chain.bootstrapMint(dave.address(), 0, [_]u8{41} ** 32);
        const lockA = try node.buildHtlcLock(a, dave, &[_]node.InputSpend{
            .{ .note = ga.note, .position = ga.pos, .path = try chain.merklePath(a, ga.pos) },
            .{ .note = gb.note, .position = gb.pos, .path = try chain.merklePath(a, gb.pos) },
        }, redeem_tag, refund_tag, hashlock, timeout, 300, 0, 50, chain.anchor());
        const posA = gb.pos + 1; // lock output 0 (the HTLC note)
        try chain.applyHtlc(lockA.tx, 50);

        const gc = try chain.bootstrapMint(dave.address(), 400, [_]u8{42} ** 32);
        const gd = try chain.bootstrapMint(dave.address(), 0, [_]u8{43} ** 32);
        const lockB = try node.buildHtlcLock(a, dave, &[_]node.InputSpend{
            .{ .note = gc.note, .position = gc.pos, .path = try chain.merklePath(a, gc.pos) },
            .{ .note = gd.note, .position = gd.pos, .path = try chain.merklePath(a, gd.pos) },
        }, redeem_tag, refund_tag, hashlock, timeout, 400, 0, 50, chain.anchor());
        const posB = gd.pos + 1;
        try chain.applyHtlc(lockB.tx, 50);

        // build the two redeem witnesses (no per-tx prove); carol redeems both before the timeout.
        const da = try chain.bootstrapMint(carol.address(), 0, [_]u8{44} ** 32);
        const db = try chain.bootstrapMint(carol.address(), 0, [_]u8{45} ** 32);
        const anchor2 = chain.anchor();
        const spendA = node.HtlcSpend{ .note = lockA.note, .position = posA, .path = try chain.merklePath(a, posA), .claim_div = carol.address().div, .mode = 1, .redeem_tag = redeem_tag, .refund_tag = refund_tag, .hashlock = hashlock, .timeout = timeout, .preimage = preimage };
        const spendB = node.HtlcSpend{ .note = lockB.note, .position = posB, .path = try chain.merklePath(a, posB), .claim_div = carol.address().div, .mode = 1, .redeem_tag = redeem_tag, .refund_tag = refund_tag, .hashlock = hashlock, .timeout = timeout, .preimage = preimage };
        const dummyA = node.InputSpend{ .note = da.note, .position = da.pos, .path = try chain.merklePath(a, da.pos) };
        const dummyB = node.InputSpend{ .note = db.note, .position = db.pos, .path = try chain.merklePath(a, db.pos) };
        const oA = [_]node.OutputReq{.{ .recipient = carol.address(), .value = 300 }};
        const oB = [_]node.OutputReq{.{ .recipient = carol.address(), .value = 400 }};
        const hwa = try node.buildHtlcSpendWitness(a, carol, spendA, dummyA, &oA, 0, 60, anchor2);
        defer a.free(hwa.witness);
        defer for (hwa.tx.outputs) |t_| a.free(t_.ciphertext);
        const hwb = try node.buildHtlcSpendWitness(a, carol, spendB, dummyB, &oB, 0, 60, anchor2);
        defer a.free(hwb.witness);
        defer for (hwb.tx.outputs) |t_| a.free(t_.ciphertext);

        const wcat = try a.alloc(u8, hwa.witness.len + hwb.witness.len);
        defer a.free(wcat);
        @memcpy(wcat[0..hwa.witness.len], hwa.witness);
        @memcpy(wcat[hwa.witness.len..], hwb.witness);
        const hr = try ffi.proveHtlcBatch(a, wcat, 2);
        defer a.free(hr.proof);
        std.debug.print("real HTLC batch prove: 2 redeems -> {d}-byte proof\n", .{hr.proof.len});

        const htxs = [_]node.ShieldedHtlcTx{ hwa.tx, hwb.tx };
        const node_hroot = node.htlcBatchRoot(&htxs);
        if (!std.mem.eql(u8, &node_hroot, &hr.root)) return Err.BatchRootMismatch;
        std.debug.print("HTLC batch tx-root: Zig node == Rust circuit\n", .{});
        if (!ffi.verifyHtlcBatch(hr.proof, hr.root)) return Err.BatchRejected;
        std.debug.print("real HTLC batch verify: ACCEPT\n", .{});
        var hbad = hr.root;
        hbad[0] +%= 1;
        if (ffi.verifyHtlcBatch(hr.proof, hbad)) return Err.TamperAccepted;
        std.debug.print("HTLC batch verify vs tampered root: REJECT\n", .{});

        // APPLY: ONE proof authorizes both redeems; the node applies them (pins height = 60) + emits the
        // two redeem preimage events for cross-chain watchers.
        const events_before = chain.redeemEvents().len;
        try chain.applyHtlcBatch(&htxs, hr.proof, 60);
        if (!chain.nullifiers.contains(hwa.tx.nullifiers[0]) or !chain.nullifiers.contains(hwb.tx.nullifiers[0])) return Err.BatchRejected;
        if (chain.redeemEvents().len != events_before + 2) return Err.BatchRejected;
        std.debug.print("real HTLC batch APPLY: 2 redeems applied (+2 preimage events) via one proof\n", .{});
        if (chain.applyHtlcBatch(&htxs, hr.proof, 60)) |_| return Err.DoubleSpendAccepted else |e| if (e != node.TxError.DoubleSpend) return Err.WrongError;
        std.debug.print("HTLC batch re-apply: REJECT (double-spend)\n", .{});
    }

    std.debug.print("OK: real in-node prove -> ghost-reject -> verify -> double-spend-reject (+ HTLC lock/redeem/refund-timelock + join-split & HTLC one-proof-per-block)\n", .{});
}
