//! Test aggregator: referencing each module here pulls its `test` blocks into the single
//! `zig build test` binary.

test {
    _ = @import("primitives.zig");
    _ = @import("field.zig");
    _ = @import("codec.zig");
    _ = @import("protocol.zig");
    _ = @import("ffi.zig");
    _ = @import("tree.zig");
    _ = @import("tx.zig");
    _ = @import("node.zig");
    _ = @import("kat.zig");
}
