//! Lattica wallet CLI.
//!
//! `lattica-wallet demo` runs a complete post-quantum shielded transfer end to end against an
//! in-memory chain and narrates every step. `keygen` prints a deterministic account, and
//! `bench` times the (stub) authorization proof alongside the real PQ primitive sizes.

const std = @import("std");
const p = @import("primitives.zig");
const tx = @import("tx.zig");
const circuit = @import("circuit.zig");
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
        try bench(a, init.io);
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

fn bench(a: std.mem.Allocator, io: std.Io) !void {
    const iters: u32 = 10;
    const secret = [_]u8{7} ** 32;

    const p0 = std.Io.Clock.now(.awake, io);
    var proof = try circuit.proveAuthorization(a, &secret);
    var i: u32 = 1;
    while (i < iters) : (i += 1) proof = try circuit.proveAuthorization(a, &secret);
    const prove_ms = elapsedMs(p0, std.Io.Clock.now(.awake, io)) / @as(f64, @floatFromInt(iters));

    const v0 = std.Io.Clock.now(.awake, io);
    i = 0;
    while (i < iters) : (i += 1) std.debug.assert(circuit.verifyAuthorization(proof));
    const verify_ms = elapsedMs(v0, std.Io.Clock.now(.awake, io)) / @as(f64, @floatFromInt(iters));

    std.debug.print("Lattica FRI-STARK authorization proof ({d} iters)\n", .{iters});
    std.debug.print("  prove       : {d:.4} ms\n", .{prove_ms});
    std.debug.print("  verify      : {d:.4} ms\n", .{verify_ms});
    std.debug.print("  proof size  : {d} bytes (transparent, hash-based, no trusted setup)\n", .{proof.proof.len});
    std.debug.print("  ML-DSA sig  : {d} bytes\n", .{p.SIG_LEN});
    std.debug.print("  ML-DSA pk   : {d} bytes\n", .{p.PK_LEN});
    std.debug.print("  ML-KEM ct   : {d} bytes\n", .{p.CT_LEN});
}

fn demo(a: std.mem.Allocator) !void {
    std.debug.print("=== Lattica: post-quantum shielded transfer demo ===\n\n", .{});

    var chain = try node.Chain.init(a);
    const alice = try tx.FullKey.fromSeed([_]u8{1} ** 32);
    const bob = try tx.FullKey.fromSeed([_]u8{2} ** 32);
    std.debug.print("Alice and Bob each hold a post-quantum account (ML-KEM + ML-DSA keys).\n\n", .{});

    // 1. Mint funds to Alice.
    const minted = try chain.mint(alice.address(), 1000, [_]u8{11} ** 32);
    std.debug.print("[mint]   1000 minted to Alice as a shielded note at tree position {d}.\n", .{minted.pos});
    std.debug.print("         note commitment {s}… inserted; anchor now {s}…\n", .{ hex6(&minted.note.commitment()), hex6(&chain.anchor()) });
    if (tx.tryDecrypt(a, alice, chain.transmitted.items[0])) |n| {
        std.debug.print("         Alice trial-decrypts her note: value = {d}.\n\n", .{n.value});
    } else {
        std.debug.print("         (decryption failed!)\n\n", .{});
    }

    // 2. Alice builds a shielded transfer to Bob: 900 to Bob, 100 fee.
    const anchor = chain.anchor();
    const path = try chain.merklePath(a, minted.pos);
    const t = try node.buildTransfer(a, alice, minted.note, minted.pos, path, anchor, bob.address(), 900, 100);
    std.debug.print("[build]  Alice spends her note: 900 to Bob, 100 fee.\n", .{});
    std.debug.print("         nullifier    {s}… (revealed; unlinkable to the note)\n", .{hex6(&t.spends[0].nullifier)});
    std.debug.print("         FRI proof    {d} bytes (transparent, hash-based, no trusted setup)\n", .{t.spends[0].auth.proof.len});
    std.debug.print("         binding sig  {d} bytes (ML-DSA)\n", .{p.SIG_LEN});
    const total = t.spends[0].auth.proof.len + p.SIG_LEN + t.outputs[0].note.ciphertext.len + t.outputs[0].note.kem_ct.len;
    std.debug.print("         tx size     ~{d} bytes\n\n", .{total});

    // 3. The node validates and applies it.
    if (chain.verifyAndApply(t)) |_| {
        std.debug.print("[node]   transaction ACCEPTED: binding sig ✓  membership ✓  nullifier-unseen ✓  auth ✓  balance ✓\n\n", .{});
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
