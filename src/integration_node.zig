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

// The production C ABI implemented by lattica-prover-p3.
extern fn lattica_joinsplit_prove(
    witness_ptr: [*]const u8,
    witness_len: usize,
    proof_out: [*]u8,
    proof_cap: usize,
    proof_len: *usize,
    pi_out: [*]u8,
    pi_cap: usize,
    pi_len: *usize,
) callconv(.c) i32;
extern fn lattica_joinsplit_verify(
    proof: [*]const u8,
    proof_len: usize,
    pi: [*]const u8,
    pi_len: usize,
) callconv(.c) i32;

export fn main() callconv(.c) c_int {
    run() catch |e| {
        std.debug.print("FAIL: {s}\n", .{@errorName(e)});
        return 1;
    };
    return 0;
}

const Err = error{ BobDidNotReceive, DoubleSpendAccepted, TamperAccepted, WrongError };

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
    const m0 = try chain.mint(alice.address(), 1000, [_]u8{11} ** 32);
    const m1 = try chain.mint(alice.address(), 0, [_]u8{12} ** 32);
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

    std.debug.print("OK: real in-node prove -> ghost-reject -> verify -> double-spend-reject\n", .{});
}
