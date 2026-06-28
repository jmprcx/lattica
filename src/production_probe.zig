//! Production-mode compile probe (audit M-09 / M-10).
//!
//! This module sets `lattica_production`, which makes `node.zig` compile **out** its genesis/test-only
//! helpers — `Chain.bootstrapMint` and the `mock` backend. It then references only the production
//! consensus surface. A successful compile is the assertion: if the live consensus path ever depended
//! on a test-only helper (an accidental `bootstrapMint`/`mock` call, or a mock-installing default), this
//! probe would fail to compile. Built by `zig build check-production` and as a dependency of
//! `zig build test`. It is not a runtime test.
const node = @import("node.zig");

/// Turn on production mode for the whole module graph rooted at this file.
pub const lattica_production = true;

pub fn main() void {
    // Force semantic analysis of the production API under `lattica_production = true`.
    _ = &node.Chain.init;
    _ = &node.Chain.deinit;
    _ = &node.Chain.verifyAndApply;
    _ = &node.Chain.applyCoinbase;
    _ = &node.Chain.anchor;
    _ = &node.Chain.isKnownAnchor;
    _ = &node.Chain.merklePath;
    _ = &node.buildTransfer;
}
