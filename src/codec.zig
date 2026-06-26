//! Canonical binary encoding for consensus objects.
//!
//! This generalizes the audit's I-01 fix into a reusable encoder/decoder with one rule set, so
//! every consensus object on the wire has a single valid byte representation:
//!
//!   * integers are fixed-width little-endian;
//!   * byte fields (hashes, keys, ciphertexts) have exact, known lengths;
//!   * field elements must be canonical (`< field.P`);
//!   * decoding must consume *all* input — trailing bytes are rejected.
//!
//! Transaction ids / binding digests are computed over canonically-encoded bytes only, so a
//! malleable re-encoding cannot produce a different-yet-valid transaction.

const std = @import("std");
const Allocator = std.mem.Allocator;
const field = @import("field.zig");

pub const Error = error{
    Truncated,
    TrailingBytes,
    NonCanonicalField,
    LengthTooLarge,
};

pub const Writer = struct {
    buf: std.ArrayList(u8) = .empty,

    pub fn deinit(self: *Writer, a: Allocator) void {
        self.buf.deinit(a);
    }
    pub fn u8v(self: *Writer, a: Allocator, v: u8) !void {
        try self.buf.append(a, v);
    }
    pub fn u32v(self: *Writer, a: Allocator, v: u32) !void {
        var le: [4]u8 = undefined;
        std.mem.writeInt(u32, &le, v, .little);
        try self.buf.appendSlice(a, &le);
    }
    pub fn u64v(self: *Writer, a: Allocator, v: u64) !void {
        var le: [8]u8 = undefined;
        std.mem.writeInt(u64, &le, v, .little);
        try self.buf.appendSlice(a, &le);
    }
    /// A canonical field element (must already be `< P`).
    pub fn felt(self: *Writer, a: Allocator, v: u64) !void {
        std.debug.assert(v < field.P);
        try self.u64v(a, v);
    }
    /// A fixed-length byte field (length is implied by the schema, not encoded).
    pub fn fixed(self: *Writer, a: Allocator, bytes: []const u8) !void {
        try self.buf.appendSlice(a, bytes);
    }
    /// A length-prefixed variable byte field (u32 length + bytes). Used for proofs/ciphertexts
    /// whose length varies but must still round-trip canonically.
    pub fn varBytes(self: *Writer, a: Allocator, bytes: []const u8) !void {
        if (bytes.len > std.math.maxInt(u32)) return Error.LengthTooLarge;
        try self.u32v(a, @intCast(bytes.len));
        try self.buf.appendSlice(a, bytes);
    }
    pub fn toOwnedSlice(self: *Writer, a: Allocator) ![]u8 {
        return self.buf.toOwnedSlice(a);
    }
};

pub const Reader = struct {
    data: []const u8,
    pos: usize = 0,

    pub fn init(data: []const u8) Reader {
        return .{ .data = data };
    }
    pub fn getBytes(self: *Reader, n: usize) Error![]const u8 {
        if (self.pos + n > self.data.len) return Error.Truncated;
        const s = self.data[self.pos .. self.pos + n];
        self.pos += n;
        return s;
    }
    pub fn u8v(self: *Reader) Error!u8 {
        return (try self.getBytes(1))[0];
    }
    pub fn u32v(self: *Reader) Error!u32 {
        return std.mem.readInt(u32, (try self.getBytes(4))[0..4], .little);
    }
    pub fn u64v(self: *Reader) Error!u64 {
        return std.mem.readInt(u64, (try self.getBytes(8))[0..8], .little);
    }
    /// A field element; rejects non-canonical encodings (`>= P`).
    pub fn felt(self: *Reader) Error!u64 {
        const v = try self.u64v();
        if (v >= field.P) return Error.NonCanonicalField;
        return v;
    }
    pub fn fixed(self: *Reader, comptime n: usize) Error![n]u8 {
        var out: [n]u8 = undefined;
        @memcpy(&out, try self.getBytes(n));
        return out;
    }
    /// Borrow a length-prefixed variable byte field (slice into the input; no allocation).
    pub fn varBytes(self: *Reader) Error![]const u8 {
        const n = try self.u32v();
        return self.getBytes(n);
    }
    /// Must be called at the end of decoding: rejects trailing bytes.
    pub fn finish(self: *Reader) Error!void {
        if (self.pos != self.data.len) return Error.TrailingBytes;
    }
};

// ---------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------

const testing = std.testing;

test "codec: round trip of mixed fields" {
    const a = testing.allocator;
    var w = Writer{};
    defer w.deinit(a);
    try w.u8v(a, 0x5a);
    try w.u64v(a, 0x0102_0304_0506_0708);
    try w.felt(a, 12345);
    try w.fixed(a, &([_]u8{0xAB} ** 32));
    try w.varBytes(a, "hello");
    const bytes = try w.toOwnedSlice(a);
    defer a.free(bytes);

    var r = Reader.init(bytes);
    try testing.expectEqual(@as(u8, 0x5a), try r.u8v());
    try testing.expectEqual(@as(u64, 0x0102_0304_0506_0708), try r.u64v());
    try testing.expectEqual(@as(u64, 12345), try r.felt());
    try testing.expectEqual([_]u8{0xAB} ** 32, try r.fixed(32));
    try testing.expectEqualStrings("hello", try r.varBytes());
    try r.finish();
}

test "codec: rejects trailing bytes" {
    const a = testing.allocator;
    var w = Writer{};
    defer w.deinit(a);
    try w.u64v(a, 7);
    const bytes = try w.toOwnedSlice(a);
    defer a.free(bytes);
    const extended = try a.alloc(u8, bytes.len + 1);
    defer a.free(extended);
    @memcpy(extended[0..bytes.len], bytes);
    extended[bytes.len] = 0;
    var r = Reader.init(extended);
    _ = try r.u64v();
    try testing.expectError(Error.TrailingBytes, r.finish());
}

test "codec: rejects non-canonical field element" {
    var le: [8]u8 = undefined;
    std.mem.writeInt(u64, &le, field.P, .little); // P is not a canonical residue
    var r = Reader.init(&le);
    try testing.expectError(Error.NonCanonicalField, r.felt());
}

test "codec: truncation is rejected" {
    const short = [_]u8{ 1, 2, 3 };
    var r = Reader.init(&short);
    try testing.expectError(Error.Truncated, r.u64v());
}
