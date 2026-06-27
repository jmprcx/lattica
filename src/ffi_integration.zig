//! End-to-end FFI integration test: **prove (Rust) → verify (Rust, across the C ABI) →
//! double-spend rejected**, linking the real `lattica-prover-p3` staticlib.
//!
//! Run: build the staticlib first (`cd lattica-prover-p3 && cargo build --release`), then
//! `zig build test-ffi`. Demonstrates the production verify seam on a real join-split proof, that
//! the protocol-side `poseidon2.zig` hashes equal the circuit's public inputs (C-03), and the node's
//! nullifier-set double-spend check.
//!
//! NOTE: on hosts whose `crt1.o` carries a `.sframe` section (gcc/binutils ≥ ~2025), Zig 0.16's
//! linkers can't link the libc-dependent Rust staticlib here. The identical flow, linked with the
//! system toolchain, is in `lattica-prover-p3/tests/ffi_integration.c` (run via `cc … .a` — verified
//! passing). This Zig version is the node-side test for a toolchain whose linker handles the host crt.

const std = @import("std");
const ffi = @import("ffi.zig");
const poseidon2 = @import("poseidon2.zig");
const testing = std.testing;

// The production C ABI implemented by the prover crate.
extern fn lattica_joinsplit_prove_demo(
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

const NullifierSet = std.AutoHashMap([32]u8, void);

/// Node-side spend application: verify the proof, then reject if any nullifier is already spent;
/// otherwise insert them. Returns true iff the spend is accepted.
fn applySpend(set: *NullifierSet, proof: []const u8, pi: []const u8, nfs: []const [32]u8) !bool {
    if (lattica_joinsplit_verify(proof.ptr, proof.len, pi.ptr, pi.len) != 0) return false;
    for (nfs) |nf| if (set.contains(nf)) return false; // double-spend
    for (nfs) |nf| try set.put(nf, {});
    return true;
}

test "ffi integration: prove(rust) -> verify -> double-spend rejected" {
    const a = testing.allocator;

    // 1. Prove the demo join-split in Rust, across the ABI.
    const proof = try a.alloc(u8, 1 << 20);
    defer a.free(proof);
    var pi: [256]u8 = undefined;
    var proof_len: usize = 0;
    var pi_len: usize = 0;
    try testing.expectEqual(@as(i32, 0), lattica_joinsplit_prove_demo(proof.ptr, proof.len, &proof_len, &pi, pi.len, &pi_len));
    try testing.expectEqual(ffi.JoinSplitPublicInputs.ENCODED_LEN, pi_len);
    const proof_bytes = proof[0..proof_len];
    const pi_bytes = pi[0..pi_len];

    // 2. The real Rust verifier accepts the real proof (the node's verify seam).
    ffi.setJoinSplitBackend(&lattica_joinsplit_verify); // node installs it at startup
    try testing.expectEqual(@as(i32, 0), lattica_joinsplit_verify(proof_bytes.ptr, proof_bytes.len, pi_bytes.ptr, pi_bytes.len));

    // 3. C-03: the protocol's poseidon2 hashes equal the circuit's public inputs.
    //    Demo input 0 is nk=7, rho=11 at tree position 0 ⇒ nf_0 = H(DOM_NF, 7, 11, 0), at pi[32..64].
    const nf0 = poseidon2.digestBytes(poseidon2.nullifierHash(7, 11, 0));
    try testing.expectEqualSlices(u8, nf0[0..], pi_bytes[32..64]);

    // 4. Tampered public inputs are rejected.
    pi[0] +%= 1;
    try testing.expect(lattica_joinsplit_verify(proof_bytes.ptr, proof_bytes.len, pi_bytes.ptr, pi_bytes.len) != 0);
    pi[0] -%= 1;

    // 5. Double-spend: the node's nullifier set accepts the first spend, rejects the replay.
    var set = NullifierSet.init(a);
    defer set.deinit();
    var nf_a: [32]u8 = undefined;
    @memcpy(&nf_a, pi_bytes[32..64]); // nf_0
    var nf_b: [32]u8 = undefined;
    @memcpy(&nf_b, pi_bytes[64..96]); // nf_1
    const nfs = [_][32]u8{ nf_a, nf_b };
    try testing.expect(try applySpend(&set, proof_bytes, pi_bytes, &nfs)); // first spend accepted
    try testing.expect(!(try applySpend(&set, proof_bytes, pi_bytes, &nfs))); // replay rejected
}
