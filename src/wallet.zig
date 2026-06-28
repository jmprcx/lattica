//! Lattica wallet CLI.
//!
//! `lattica-wallet demo` runs a complete post-quantum shielded transfer end to end against an
//! in-memory chain and narrates every step. `keygen` prints a deterministic account, and
//! `bench` times the (stub) authorization proof alongside the real PQ primitive sizes.

const std = @import("std");
const p = @import("primitives.zig");
const tx = @import("tx.zig");
const poseidon2 = @import("poseidon2.zig");
const tree = @import("tree.zig");
const node = @import("node.zig");

/// First 6 bytes of `bytes` as 12 lowercase hex characters.
fn hex6(bytes: []const u8) [12]u8 {
    const digits = "0123456789abcdef";
    var out: [12]u8 = undefined;
    var i: usize = 0;
    while (i < 6) : (i += 1) {
        out[i * 2] = digits[bytes[i] >> 4];
        out[i * 2 + 1] = digits[bytes[i] & 0x0f];
    }
    return out;
}

pub fn main(init: std.process.Init) !void {
    const a = init.arena.allocator();

    const args = try init.minimal.args.toSlice(a);
    const cmd: []const u8 = if (args.len >= 2) args[1] else "demo";

    if (std.mem.eql(u8, cmd, "demo")) {
        try demo(a);
    } else if (std.mem.eql(u8, cmd, "keygen")) {
        try keygen();
    } else if (std.mem.eql(u8, cmd, "bench")) {
        try bench(init.io);
    } else {
        std.debug.print("unknown command: {s}\nusage: lattica-wallet [demo|keygen|bench]\n", .{cmd});
        std.process.exit(2);
    }
}

fn keygen() !void {
    const key = try tx.FullKey.fromSeed([_]u8{42} ** 32);
    const addr = key.address();
    const rid = addr.recipientId();
    const pk = key.sig.pkBytes();
    std.debug.print("Lattica account (keys derived deterministically from the seed)\n", .{});
    std.debug.print("  recipient id : {s}…\n", .{hex6(&rid)});
    std.debug.print("  ML-KEM ek    : {s}… ({d} bytes)\n", .{ hex6(&addr.kem_ek), addr.kem_ek.len });
    std.debug.print("  ML-DSA pk    : {s}… ({d} bytes)\n", .{ hex6(&pk), p.PK_LEN });
}

fn elapsedMs(t0: std.Io.Timestamp, t1: std.Io.Timestamp) f64 {
    const ns: i128 = @as(i128, t1.toNanoseconds()) - @as(i128, t0.toNanoseconds());
    return @as(f64, @floatFromInt(ns)) / 1e6;
}

fn bench(io: std.Io) !void {
    const iters: u32 = 5000;
    const fiters: f64 = @floatFromInt(iters);
    var sink: u64 = 0;

    // The in-circuit / on-chain hash primitive.
    var st = [_]u64{ 1, 2, 3, 4, 5, 6, 7, 8 };
    const t0 = std.Io.Clock.now(.awake, io);
    var i: u32 = 0;
    while (i < iters) : (i += 1) poseidon2.permute(&st);
    const permute_us = elapsedMs(t0, std.Io.Clock.now(.awake, io)) * 1000.0 / fiters;
    sink +%= st[0];

    // On-chain note commitment.
    const rcp = [_]u8{3} ** 32;
    const rho = [_]u8{7} ** 32;
    const rcm = [_]u8{9} ** 32;
    const nk = [_]u8{5} ** 32;
    const t1 = std.Io.Clock.now(.awake, io);
    i = 0;
    while (i < iters) : (i += 1) sink +%= p.noteCommitment(.{ .recipient = &rcp, .value = 1000, .rho = &rho, .rcm = &rcm })[0];
    const commit_us = elapsedMs(t1, std.Io.Clock.now(.awake, io)) * 1000.0 / fiters;

    // On-chain nullifier.
    const t2 = std.Io.Clock.now(.awake, io);
    i = 0;
    while (i < iters) : (i += 1) sink +%= p.nullifier(&nk, &rho, i)[0];
    const nf_us = elapsedMs(t2, std.Io.Clock.now(.awake, io)) * 1000.0 / fiters;

    // Merkle internal node.
    const left = [_]u8{1} ** 32;
    const right = [_]u8{2} ** 32;
    const t3 = std.Io.Clock.now(.awake, io);
    i = 0;
    while (i < iters) : (i += 1) sink +%= tree.merkleHash(&left, &right)[0];
    const merge_us = elapsedMs(t3, std.Io.Clock.now(.awake, io)) * 1000.0 / fiters;

    std.debug.print("Lattica on-chain hashing — Poseidon2-Goldilocks ({d} iters)\n", .{iters});
    std.debug.print("  permute      : {d:.3} µs/op\n", .{permute_us});
    std.debug.print("  note commit  : {d:.3} µs/op\n", .{commit_us});
    std.debug.print("  nullifier    : {d:.3} µs/op\n", .{nf_us});
    std.debug.print("  merkle node  : {d:.3} µs/op\n", .{merge_us});
    std.debug.print("post-quantum primitive sizes:\n", .{});
    std.debug.print("  ML-DSA sig   : {d} bytes\n", .{p.SIG_LEN});
    std.debug.print("  ML-DSA pk    : {d} bytes\n", .{p.PK_LEN});
    std.debug.print("  ML-KEM ct    : {d} bytes\n", .{p.CT_LEN});
    std.debug.print("  join-split proof: ~0.5 MB (transparent, hash-based; prove/verify timed in lattica-prover-p3)\n", .{});
    if (sink == 0xdead_beef) std.debug.print("", .{}); // keep `sink` live
}

fn demo(a: std.mem.Allocator) !void {
    std.debug.print("=== Lattica: post-quantum shielded join-split demo ===\n\n", .{});

    // Install the mock prover/verifier backends. In production these are the Rust
    // lattica_joinsplit_prove / lattica_joinsplit_verify (joinsplit_air); the mocks model the
    // proof's tx-binding so the flow runs without linking the staticlib.
    node.mock.install();
    defer node.mock.uninstall();

    var chain = try node.Chain.init(a);
    const alice = try tx.FullKey.fromSeed([_]u8{1} ** 32);
    const bob = try tx.FullKey.fromSeed([_]u8{2} ** 32);
    std.debug.print("Alice and Bob each hold a post-quantum account (ML-KEM + ML-DSA keys).\n\n", .{});

    // 1. Mint funds to Alice: a 1000 note plus a zero-value note to pad the fixed 2-in shape.
    const m0 = try chain.bootstrapMint(alice.address(), 1000, [_]u8{11} ** 32);
    const m1 = try chain.bootstrapMint(alice.address(), 0, [_]u8{12} ** 32);
    std.debug.print("[mint]   1000 minted to Alice (+ a 0-value padding note); anchor now {s}…\n", .{hex6(&chain.anchor())});
    if (tx.tryDecrypt(a, alice, chain.transmitted.items[0])) |n| {
        std.debug.print("         Alice trial-decrypts her note: value = {d}.\n\n", .{n.value});
    }

    // 2. Alice builds a hidden-value join-split to Bob: 900 to Bob, 100 fee.
    const anchor = chain.anchor();
    const inputs = [_]node.InputSpend{
        .{ .note = m0.note, .position = m0.pos, .path = try chain.merklePath(a, m0.pos) },
        .{ .note = m1.note, .position = m1.pos, .path = try chain.merklePath(a, m1.pos) },
    };
    const outs = [_]node.OutputReq{.{ .recipient = bob.address(), .value = 900 }};
    const t = try node.buildTransfer(a, alice, &inputs, &outs, 100, 0, anchor);
    std.debug.print("[build]  Alice spends 2 notes → 900 to Bob + 0 dummy, 100 fee (values hidden).\n", .{});
    std.debug.print("         nullifiers   {s}…, {s}… (revealed; unlinkable to the notes)\n", .{ hex6(&t.nullifiers[0]), hex6(&t.nullifiers[1]) });
    std.debug.print("         join-split proof {d} bytes (mock backend; the real proof is ~0.5 MB)\n\n", .{t.proof.len});

    // 3. The node validates and applies it (proof verify + anchor + nullifier-unseen).
    if (chain.verifyAndApply(t)) |_| {
        std.debug.print("[node]   transaction ACCEPTED: proof ✓  anchor-known ✓  nullifiers-unseen ✓\n\n", .{});
    } else |err| {
        std.debug.print("[node]   transaction REJECTED: {s}\n", .{@errorName(err)});
        std.process.exit(1);
    }

    // 4. Bob scans the chain and decrypts his note.
    var bob_count: usize = 0;
    var bob_value: u64 = 0;
    for (chain.transmitted.items) |tn| {
        if (tx.tryDecrypt(a, bob, tn)) |n| {
            bob_count += 1;
            bob_value = n.value;
        }
    }
    std.debug.print("[scan]   Bob scans {d} transmitted notes; {d} decrypt to him.\n", .{ chain.transmitted.items.len, bob_count });
    if (bob_count > 0) {
        std.debug.print("         Bob receives a shielded note worth {d}.\n\n", .{bob_value});
    }

    // 5. Double-spend attempt.
    if (chain.verifyAndApply(t)) |_| {
        std.debug.print("[replay] ERROR: double-spend was accepted!\n", .{});
    } else |err| {
        std.debug.print("[replay] re-submitting the same transaction is REJECTED: {s}.\n", .{@errorName(err)});
    }

    std.debug.print("\nEvery cryptographic step above relies only on hash and lattice hardness —\n", .{});
    std.debug.print("no elliptic-curve discrete log anywhere. Quantum-safe by construction.\n", .{});
}
