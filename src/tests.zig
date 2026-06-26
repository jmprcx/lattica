//! Test aggregator: referencing each module here pulls its `test` blocks into the single
//! `zig build test` binary.

test {
    _ = @import("primitives.zig");
    _ = @import("field.zig");
    _ = @import("stark.zig");
    _ = @import("tree.zig");
    _ = @import("tx.zig");
    _ = @import("circuit.zig");
    _ = @import("node.zig");
}
