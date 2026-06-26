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
}
