const std = @import("std");

// Lattica — quantum-safe shielded payments (Zig port).
//
// A single-package build: every module is a plain `.zig` file under `src/` that imports its
// dependencies by relative path, so no inter-module wiring is needed here. The `wallet`
// executable is the CLI entry point; the `test` step compiles `src/tests.zig`, which pulls in
// every module's unit tests into one binary.
pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const exe = b.addExecutable(.{
        .name = "lattica-wallet",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/wallet.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    b.installArtifact(exe);

    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| run_cmd.addArgs(args);
    const run_step = b.step("run", "Run the wallet CLI (e.g. `zig build run -- demo`)");
    run_step.dependOn(&run_cmd.step);

    const unit_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/tests.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    const run_tests = b.addRunArtifact(unit_tests);
    const test_step = b.step("test", "Run all unit + integration tests");
    test_step.dependOn(&run_tests.step);

    // Production-mode compile probe (audit M-09/M-10): builds the consensus surface with
    // `lattica_production = true`, so `node.bootstrapMint` and `node.mock` are compiled out — a
    // successful compile proves the live path uses no genesis/test-only helpers. Compiling is the test.
    const prod_probe = b.addExecutable(.{
        .name = "lattica-production-probe",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/production_probe.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    const check_prod = b.step("check-production", "Compile the production-mode probe (test-only APIs gated out)");
    check_prod.dependOn(&prod_probe.step);
    test_step.dependOn(&prod_probe.step); // always exercised by `zig build test`

    // End-to-end FFI integration test: links the prebuilt Rust prover staticlib.
    // Build it first: `cd lattica-prover-p3 && cargo build --release`.
    const ffi_it_mod = b.createModule(.{
        .root_source_file = b.path("src/ffi_integration.zig"),
        .target = target,
        .optimize = optimize,
        .link_libc = true,
    });
    ffi_it_mod.addObjectFile(b.path("lattica-prover-p3/target/release/liblattica_prover_p3.a"));
    ffi_it_mod.linkSystemLibrary("unwind", .{});
    const ffi_it = b.addTest(.{ .root_module = ffi_it_mod });
    ffi_it.use_lld = true; // self-hosted ELF linker can't handle crt1.o's .sframe (gcc 16); use LLD
    const run_ffi_it = b.addRunArtifact(ffi_it);
    const ffi_step = b.step("test-ffi", "FFI integration test (run cargo build --release in lattica-prover-p3 first)");
    ffi_step.dependOn(&run_ffi_it.step);
}
