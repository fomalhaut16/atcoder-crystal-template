# version:20260804
require "json"

DEBUG = true

# const
INF = 1_i64 << 60
INF32 = 1 << 30
EPS = 1e-9
MOD_TREAP = Int64::MAX
MOD = 998_244_353_i64
MOD2 = 1_000_000_007_i64
MOD128 = 998_244_353_i128

# main code
# require using 'return' instead of 'exit'
def solve
end

# I/O
module HyperFastIO
    lib LibC
        fun memcpy(dest : Void*, src : Void*, n : UInt64) : Void*
        fun memmove(dest : Void*, src : Void*, n : UInt64) : Void*
        fun read(fd : Int32, buf : Void*, count : UInt64) : Int64
        fun write(fd : Int32, buf : Void*, count : UInt64) : Int64
    end

    BUF = 1 << 20
    MAXDIGITS = 1000
    MARGIN = MAXDIGITS + 24
    MAXLIMBS = MAXDIGITS // 8 + 4

    OT = begin
        t = Pointer(UInt32).malloc(10000)
        10u32.times { |a| 10.times { |b| 10.times { |c| 10.times { |d|
            t[a * 1000 + b * 100 + c * 10 + d] = a + 48 | b + 48 << 8 | c + 48 << 16 | d + 48 << 24
        } } } }
        t
    end

    struct HugeInt
        include Comparable(HugeInt)
        getter limbs : Pointer(UInt32); getter n : Int32; getter neg : Bool

        def initialize(@limbs : Pointer(UInt32), @n : Int32, @neg : Bool); end
        def self.zero : HugeInt; HugeInt.new(Pointer(UInt32).malloc(1, 0_u32), 1, false); end
        def zero? : Bool; n == 1 && limbs[0] == 0_u32; end

        def - : HugeInt; zero? ? self : HugeInt.new(limbs, n, !neg); end
        def abs : HugeInt; neg ? -self : self; end

        private def cmp_mag(o : HugeInt) : Int32
            return (n <=> o.n) if n != o.n
            i = n - 1
            while i >= 0
                return (limbs[i] <=> o.limbs[i]) if limbs[i] != o.limbs[i]
                i -= 1
            end
            0
        end

        private def add_mag(a : Pointer(UInt32), na : Int32, b : Pointer(UInt32), nb : Int32, lr : Pointer(UInt32)) : Int32
            a, na, b, nb = b, nb, a, na if na < nb
            carry = 0_u32; i = 0
            while i < nb
                s = a[i] &+ b[i] &+ carry
                s >= 100000000_u32 ? (lr[i] = s &- 100000000_u32; carry = 1_u32) : (lr[i] = s; carry = 0_u32)
                i += 1
            end
            while i < na
                s = a[i] &+ carry
                s >= 100000000_u32 ? (lr[i] = s &- 100000000_u32; carry = 1_u32) : (lr[i] = s; carry = 0_u32)
                i += 1
            end
            if carry > 0; lr[na] = carry; na += 1; end
            na
        end

        private def sub_mag(a : Pointer(UInt32), na : Int32, b : Pointer(UInt32), nb : Int32, lr : Pointer(UInt32)) : Int32
            borrow = 0_i64; i = 0
            while i < nb
                d = a[i].to_i64 &- b[i].to_i64 &- borrow
                d < 0 ? (lr[i] = (d &+ 100000000).to_u32!; borrow = 1) : (lr[i] = d.to_u32!; borrow = 0)
                i += 1
            end
            while i < na
                d = a[i].to_i64 &- borrow
                d < 0 ? (lr[i] = (d &+ 100000000).to_u32!; borrow = 1) : (lr[i] = d.to_u32!; borrow = 0)
                i += 1
            end
            m = na
            while m > 1 && lr[m - 1] == 0_u32; m -= 1; end
            m
        end

        def +(o : HugeInt) : HugeInt
            lr = Pointer(UInt32).malloc(Math.max(n, o.n) + 1)
            if neg == o.neg
                HugeInt.new(lr, add_mag(limbs, n, o.limbs, o.n, lr), neg)
            else
                c = cmp_mag(o)
                if c == 0
                    lr[0] = 0_u32; HugeInt.new(lr, 1, false)
                elsif c > 0
                    HugeInt.new(lr, sub_mag(limbs, n, o.limbs, o.n, lr), neg)
                else
                    HugeInt.new(lr, sub_mag(o.limbs, o.n, limbs, n, lr), o.neg)
                end
            end
        end

        def -(o : HugeInt) : HugeInt; self + (-o); end

        def <=>(other : HugeInt) : Int32
            return (neg ? -1 : 1) if neg != other.neg
            neg ? -cmp_mag(other) : cmp_mag(other)
        end

        def to_s(io : IO) : Nil
            io << '-' if neg
            io << limbs[n - 1]
            i = n - 2
            while i >= 0
                v = limbs[i]
                io << '0' if v < 10000000_u32
                io << '0' if v < 1000000_u32
                io << '0' if v < 100000_u32
                io << '0' if v < 10000_u32
                io << '0' if v < 1000_u32
                io << '0' if v < 100_u32
                io << '0' if v < 10_u32
                io << v
                i -= 1
            end
        end
    end

    class Scanner
        @buf : Bytes; @ptr : UInt8*; @idx : Int32; @len : Int32; @bigscratch : Pointer(UInt32)
        def initialize
            @buf = Bytes.new(BUF + 64); @ptr = @buf.to_unsafe; @idx = 0; @len = 0
            @bigscratch = Pointer(UInt32).malloc(MAXLIMBS)
        end

        private def refill : Int32
            r = LibC.read(0, @ptr.as(Void*), BUF); return 0 if r <= 0
            @len = r.to_i32; @ptr[@len] = 0_u8; @idx = 0; r.to_i32
        end

        private def ensure : Bool; @idx < @len || refill > 0; end

        private def ensure_margin(need : Int32) : Nil
            return if @len - @idx >= need
            rem = @len - @idx
            LibC.memmove(@ptr.as(Void*), (@ptr + @idx).as(Void*), rem.to_u64)
            @idx = 0; @len = rem
            r = LibC.read(0, (@ptr + @len).as(Void*), (BUF - @len).to_u64)
            @len += r > 0 ? r.to_i32 : 0
            @ptr[@len] = 0_u8
        end

        macro def_read(name, type)
            def {{name}} : {{type}}
                while ensure && @ptr[@idx] <= 32_u8; @idx += 1; end
                neg = false
                if ensure && @ptr[@idx] == 45_u8; neg = true; @idx += 1; end
                n = {{type}}.zero
                while ensure && @idx + 8 <= @len
                    tmp = (@ptr + @idx).as(UInt64*).value
                    tmp &-= 0x3030303030303030_u64
                    break if (tmp & 0x8080808080808080_u64) != 0
                    tmp = (tmp &* 10 &+ (tmp >> 8)) & 0x00ff00ff00ff00ff_u64
                    tmp = (tmp &* 100 &+ (tmp >> 16)) & 0x0000ffff0000ffff_u64
                    tmp = (tmp &* 10000 &+ (tmp >> 32)) & 0x00000000ffffffff_u64
                    n = n &* 100000000 &+ tmp
                    @idx += 8
                end
                while ensure && @ptr[@idx] >= 48_u8 && @ptr[@idx] <= 57_u8
                    n = n &* 10 &+ (@ptr[@idx] ^ 48_u8); @idx += 1
                end
                neg ? ({{type}}.zero &- n) : n
            end
        end

        def_read(readint, Int32)
        def_read(readlong, Int64)
        def_read(readi128, Int128)

        def readbig : HugeInt
            while ensure && @ptr[@idx] <= 32_u8; @idx += 1; end
            ensure_margin(MARGIN)
            neg = false
            if @ptr[@idx] == 45_u8; neg = true; @idx += 1; end
            start = @idx
            while @idx + 8 <= @len
                tmp = (@ptr + @idx).as(UInt64*).value
                tmp &-= 0x3030303030303030_u64
                break if (tmp & 0x8080808080808080_u64) != 0
                @idx += 8
            end
            while @ptr[@idx] >= 48_u8 && @ptr[@idx] <= 57_u8; @idx += 1; end
            tail = @idx
            nlimbs = 0
            scratch = @bigscratch
            p = tail
            while p - start >= 8
                p -= 8
                tmp = (@ptr + p).as(UInt64*).value
                tmp &-= 0x3030303030303030_u64
                tmp = (tmp &* 10 &+ (tmp >> 8)) & 0x00ff00ff00ff00ff_u64
                tmp = (tmp &* 100 &+ (tmp >> 16)) & 0x0000ffff0000ffff_u64
                tmp = (tmp &* 10000 &+ (tmp >> 32)) & 0x00000000ffffffff_u64
                scratch[nlimbs] = tmp.to_u32!
                nlimbs += 1
            end
            if p > start
                v = 0_u32; i = start
                while i < p; v = v &* 10 &+ (@ptr[i] ^ 48_u8); i += 1; end
                scratch[nlimbs] = v; nlimbs += 1
            end
            if nlimbs == 0; scratch[0] = 0_u32; nlimbs = 1; end
            neg = false if nlimbs == 1 && scratch[0] == 0_u32
            limbs = Pointer(UInt32).malloc(nlimbs)
            scratch.copy_to(limbs, nlimbs)
            HugeInt.new(limbs, nlimbs, neg)
        end

        def readchar : Char; while ensure && @ptr[@idx] <= 32_u8; @idx += 1; end; @idx += 1; @ptr[@idx - 1].chr; end

        def readoneint : Int32
            while ensure && @ptr[@idx] <= 32_u8; @idx += 1; end
            @idx += 1; (@ptr[@idx - 1] - 48_u8).to_i32
        end

        def readstring : String
            while ensure && @ptr[@idx] <= 32_u8; @idx += 1; end
            start = @idx; while ensure && @ptr[@idx] > 32_u8; @idx += 1; end
            String.new(@ptr + start, @idx - start)
        end
    end

    class Writer
        OUT = 1 << 20

        def initialize
            @buf = Bytes.new(OUT); @ptr = @buf.to_unsafe; @idx = 0
            @rev = StaticArray(UInt32, 24).new(0u32)
        end

        private def flush_buf : Nil; if @idx > 0; LibC.write(1, @ptr.as(Void*), @idx.to_u64); @idx = 0; end; end
        private def putb(b : UInt8) : Nil; flush_buf if @idx + 1 > OUT; @ptr[@idx] = b; @idx += 1; end

        private def write_group(n : UInt32) : Nil
            if 1000 <= n
                flush_buf if @idx + 4 > OUT
                (@ptr + @idx).as(UInt32*).value = OT[n]; @idx += 4
            elsif 100 <= n
                v = OT[n]; putb((v >> 8).to_u8!); putb((v >> 16).to_u8!); putb((v >> 24).to_u8!)
            elsif 10 <= n
                v = OT[n]; putb((v >> 16).to_u8!); putb((v >> 24).to_u8!)
            else
                putb(48u8 &+ n.to_u8!)
            end
        end

        private def write_padded4(n : UInt32) : Nil
            flush_buf if @idx + 4 > OUT
            (@ptr + @idx).as(UInt32*).value = OT[n]; @idx += 4
        end

        def write_i64(x : Int64) : Nil
            mag = x < 0 ? (0_i64 &- x).to_u64! : x.to_u64!
            putb(45_u8) if x < 0
            t = 0
            while mag >= 10000_u64
                q = mag // 10000_u64
                @rev.unsafe_put(t, (mag &- q &* 10000_u64).to_u32!); t += 1
                mag = q
            end
            write_group(mag.to_u32!)
            while t > 0
                t -= 1
                write_padded4(@rev.unsafe_fetch(t))
            end
        end

        def write_i32(x : Int32) : Nil; write_i64(x.to_i64); end

        def write_i128(x : Int128) : Nil
            mag = x < 0 ? (0_i128 &- x).to_u128! : x.to_u128!
            putb(45_u8) if x < 0
            t = 0
            while mag > UInt64::MAX.to_u128!
                q = mag // 100000000_u128
                r4 = (mag &- q &* 100000000_u128).to_u32!
                hi4 = r4 // 10000_u32; lo4 = r4 &- hi4 &* 10000_u32
                @rev.unsafe_put(t, lo4); t += 1
                @rev.unsafe_put(t, hi4); t += 1
                mag = q
            end
            n1 = mag.to_u64!
            while n1 >= 10000_u64
                q = n1 // 10000_u64
                @rev.unsafe_put(t, (n1 &- q &* 10000_u64).to_u32!); t += 1
                n1 = q
            end
            write_group(n1.to_u32!)
            while t > 0
                t -= 1
                write_padded4(@rev.unsafe_fetch(t))
            end
        end

        def write_big(x : HugeInt) : Nil
            limbs = x.limbs; n = x.n
            putb(45_u8) if x.neg
            v = limbs[n - 1]
            hi = v // 10000_u32; lo = v &- hi &* 10000_u32
            if hi > 0; write_group(hi); write_padded4(lo); else; write_group(lo); end
            i = n - 2
            while i >= 0
                vv = limbs[i]
                h2 = vv // 10000_u32; l2 = vv &- h2 &* 10000_u32
                write_padded4(h2); write_padded4(l2)
                i -= 1
            end
        end

        def puts_i64(x : Int64) : Nil; write_i64(x); putb(10_u8); end
        def puts_i32(x : Int32) : Nil; write_i64(x.to_i64); putb(10_u8); end
        def puts_i128(x : Int128) : Nil; write_i128(x); putb(10_u8); end
        def puts_big(x : HugeInt) : Nil; write_big(x); putb(10_u8); end
        def write_string(s : String) : Nil; s.each_byte { |b| putb(b) }; end
        def puts_string(s : String) : Nil; write_string(s); putb(10_u8); end
        def flush : Nil; flush_buf; end
    end

    SC = Scanner.new
    WR = Writer.new
    at_exit { WR.flush }

    module Helpers
        def integer; HyperFastIO::SC.readint end
        def long; HyperFastIO::SC.readlong end
        def i128; HyperFastIO::SC.readi128 end
        def big; HyperFastIO::SC.readbig end
        def char; HyperFastIO::SC.readchar end
        def string; HyperFastIO::SC.readstring end
        def oneint; HyperFastIO::SC.readoneint end
        def double; string.to_f64 end

        def arr_int(n); Array.new(n) { integer } end
        def arr_long(n); Array.new(n) { long } end
        def arr_i128(n); Array.new(n) { i128 } end
        def arr_big(n); Array.new(n) { big } end
        def arr_char(n); Array.new(n) { char } end
        def arr_string(n); Array.new(n) { string } end
        def arr_double(n); Array.new(n) { double } end
        def multi_int(n); Array.new(n) { integer } end
        def multi_long(n); Array.new(n) { long } end

        def integer2; {integer, integer} end
        def integer3; {integer, integer, integer} end
        def integer4; {integer, integer, integer, integer} end
        def long2; {long, long} end
        def long3; {long, long, long} end
        def long4; {long, long, long, long} end
        def i1282; {i128, i128} end
        def i1283; {i128, i128, i128} end
        def big2; {big, big} end
        def big3; {big, big, big} end
        def string2; {string, string} end

        def grid_char(rows, cols); Array.new(rows) { Array.new(cols) { char } } end
        def grid_int(rows, cols); Array.new(rows) { Array.new(cols) { integer } } end
        def grid_long(rows, cols); Array.new(rows) { Array.new(cols) { long } } end
        def grid_oneint(rows, cols); Array.new(rows) { Array.new(cols) { oneint } } end

        def slice_int(h, w); a = Slice(Int32).new(h * w); a.to_unsafe.tap { |ptr| (0...h*w).each { |i| ptr[i] = integer } }; a end
        def slice_oneint(h, w); a = Slice(Int32).new(h * w); a.to_unsafe.tap { |ptr| (0...h*w).each { |i| ptr[i] = oneint } }; a end
        def slice_long(n); a = Slice(Int64).new(n); n.times { |i| a[i] = long }; a end
    end
end
include HyperFastIO::Helpers

def puts(x)
    case x
    when Int32
        HyperFastIO::WR.puts_i32(x)
    when Int64
        HyperFastIO::WR.puts_i64(x)
    when Int128
        HyperFastIO::WR.puts_i128(x)
    when HyperFastIO::HugeInt
        HyperFastIO::WR.puts_big(x)
    when String
        HyperFastIO::WR.puts_string(x)
    when Char
        HyperFastIO::WR.puts_string(x.to_s)
    when Array
        if !x.empty? && x[0].is_a?(Array)
            x.each { |row| puts row }
        else
            x.each_with_index do |e, i|
                HyperFastIO::WR.write_string(" ") if i > 0
                case e
                when Int32
                    HyperFastIO::WR.write_i32(e)
                when Int64
                    HyperFastIO::WR.write_i64(e)
                when Int128
                    HyperFastIO::WR.write_i128(e)
                when HyperFastIO::HugeInt
                    HyperFastIO::WR.write_big(e)
                when String
                    HyperFastIO::WR.write_string(e)
                else
                    HyperFastIO::WR.write_string(e.to_s)
                end
            end
            HyperFastIO::WR.puts_string("")
        end
    else
        HyperFastIO::WR.puts_string(x.to_s)
    end
end

def print(x)
    case x
    when Int32
        HyperFastIO::WR.write_i32(x)
    when Int64
        HyperFastIO::WR.write_i64(x)
    when Int128
        HyperFastIO::WR.write_i128(x)
    when HyperFastIO::HugeInt
        HyperFastIO::WR.write_big(x)
    when String
        HyperFastIO::WR.write_string(x)
    when Char
        HyperFastIO::WR.write_string(x.to_s)
    when Array
        x.each_with_index do |e, i|
            HyperFastIO::WR.write_string(" ") if i > 0
            case e
            when Int32
                HyperFastIO::WR.write_i32(e)
            when Int64
                HyperFastIO::WR.write_i64(e)
            when Int128
                HyperFastIO::WR.write_i128(e)
            when HyperFastIO::HugeInt
                HyperFastIO::WR.write_big(e)
            when String
                HyperFastIO::WR.write_string(e)
            else
                HyperFastIO::WR.write_string(e.to_s)
            end
        end
    else
        HyperFastIO::WR.write_string(x.to_s)
    end
end

def yes; HyperFastIO::WR.puts_string("Yes") end
def no;  HyperFastIO::WR.puts_string("No") end
def yesno(b : Bool); b ? yes : no end
def flush; HyperFastIO::WR.flush end


# union-find
class UnionFind(T)
    @parent : Array(T)

    def initialize(n : Int32)
        @parent = Array(T).new(n) { -1 }
    end

    def find(x : Int32) : Int32
        if @parent[x] < 0
            x
        else
            @parent[x] = find(@parent[x])
        end
    end

    def unite(x : Int32, y : Int32) : Bool
        x = find(x)
        y = find(y)
        return false if x == y

        if -@parent[x] < -@parent[y]
            x, y = y, x
        end

        @parent[x] += @parent[y]
        @parent[y] = x
        true
    end

    def same(x : Int32, y : Int32) : Bool
        find(x) == find(y)
    end

    def size(x : Int32) : T
        -@parent[find(x)]
    end

    def component_count : Int32
        cnt = 0
        @parent.each { |v| cnt += 1 if v < 0 }
        cnt
    end

    def to_a : Array(Array(Int32))
        groups = Hash(Int32, Array(Int32)).new { |h, k| h[k] = [] of Int32 }

        @parent.size.times do |i|
            root = find(i)
            groups[root] << i
        end

        groups.values
    end

    def debug_snapshot(limit = 200)
        if @parent.size <= limit
            {
                kind: "unionfind",
                n: @parent.size,
                parent: @parent
            }
        else
            debug_snapshot_roots
        end
    end

    def debug_snapshot_roots
        groups = Hash(Int32, Array(Int32)).new { |h, k| h[k] = [] of Int32 }

        @parent.size.times do |i|
            root = find(i)
            groups[root] << i
        end

        {
            kind: "unionfind_groups",
            n: @parent.size,
            groups: groups.values
        }
    end
end

# set
macro set(*elems)
    {% if elems.size == 1 && elems[0].is_a?(Path) %}
        Set({{elems[0]}}).new
    {% else %}
        Set{ {{elems.splat}} }
    {% end %}
end

# deque
macro deque(*elems)
    {% if elems.size == 0 %}
        Deque.new
    {% elsif elems.size == 1 && (elems[0].is_a?(Path) || elems[0].is_a?(Generic)) %}
        Deque({{elems[0]}}).new
    {% elsif elems.size == 1 && elems[0].is_a?(ArrayLiteral) %}
        Deque.new({{elems[0]}})
    {% else %}
        Deque{ {{elems.splat}} }
    {% end %}
end

# utils
def is_digit?(c : Char); c.ascii_number? end
def is_alphabet?(c : Char); c.ascii_letter? end
def alphabet_to_num(c : Char) : Int32; c.downcase.ord - 'a'.ord + 1; end
def num_to_alphabet(n : Int32) : Char; ('a'.ord + n - 1).chr; end
def chmin!(a : Array, i : Int32, v); a[i] = v if v < a[i]; end
def chmax!(a : Array, i : Int32, v); a[i] = v if v > a[i]; end
def swap!(a : Array, i : Int32, j : Int32); a[i], a[j] = a[j], a[i]; end
def to_bin(n : Int, len : Int32); n.to_s(2).rjust(len, '0'); end
def to_oct(n : Int, len : Int32) : String; n.to_s(8).rjust(len, '0'); end
def to_hex(n : Int, len : Int32) : String; n.to_s(16).rjust(len, '0'); end
def from_bin(s : String) : Int32; s.to_i(2); end
def from_oct(s : String) : Int32; s.to_i(8); end
def from_hex(s : String) : Int32; s.to_i(16); end
def bit_on?(n : Int, i : Int32) : Bool; (n >> i) & 1 == 1; end
def bit_set(n : Int, i : Int32) : Int; n | (1 << i); end
def bit_unset(n : Int, i : Int32) : Int; n & ~(1 << i); end

# grid
DY = [-1, 1, 0, 0]
DX = [0, 0, -1, 1]
DY8 = [-1, -1, -1, 0, 0, 1, 1, 1]
DX8 = [-1, 0, 1, -1, 1, -1, 0, 1]
def in_grid?(h, w, y, x); 0 <= y && y < h && 0 <= x && x < w end
def to_id(y, x, w); y * w + x end
def from_id(id, w); {id // w, id % w} end
def each_adj4(y, x, h, w)
    4.times do |d|
        ny = y + DY[d]; nx = x + DX[d]
        yield ny, nx if 0 <= ny && ny < h && 0 <= nx && nx < w
    end
end
def each_adj8(y, x, h, w)
    8.times do |d|
        ny = y + DY8[d]; nx = x + DX8[d]
        yield ny, nx if 0 <= ny && ny < h && 0 <= nx && nx < w
    end
end

# unweighted graph helper
def graph(n, m, directed = false, one_indexed = true)
    g = Array.new(n) { [] of Int32 }
    m.times do
        u = integer; v = integer
        if one_indexed; u -= 1; v -= 1; end
        g[u] << v
        g[v] << u unless directed
    end
    g
end

# weighted graph helper
def wgraph(n, m, directed = false, one_indexed = true)
    g = Array.new(n) { [] of {Int32, Int64} }
    m.times do
        u = integer; v = integer; w = long
        if one_indexed; u -= 1; v -= 1; end
        g[u] << {v, w}
        g[v] << {u, w} unless directed
    end
    g
end

# priority queue
class PriorityQueue(T)
    @heap : Array(T)
    @higher_priority : Proc(T, T, Bool)

    def initialize(&@higher_priority : T, T -> Bool)
        @heap = [] of T
    end

    def initialize
        @heap = [] of T
        @higher_priority = ->(a : T, b : T) { a < b }
    end

    def initialize(array : Array(T), &@higher_priority : T, T -> Bool)
        @heap = array.dup
        heapify
    end

    def initialize(array : Array(T))
        @heap = array.dup
        @higher_priority = ->(a : T, b : T) { a < b }
        heapify
    end

    protected def initialize(@heap : Array(T), @higher_priority : Proc(T, T, Bool))
    end

    def self.max : self; PriorityQueue(T).new { |a, b| a > b } end
    def self.max(array : Array(T)) : self; PriorityQueue(T).new(array) { |a, b| a > b } end
    def empty? : Bool; @heap.empty? end
    def size : Int32; @heap.size end
    def clear; @heap.clear end
    def to_a : Array(T); @heap.dup end
    def dup : PriorityQueue(T); PriorityQueue(T).new(@heap.dup, @higher_priority) end

    def to_sorted_a : Array(T)
        copy = self.dup
        res = Array(T).new(copy.size)
        while v = copy.pop?
            res << v
        end
        res
    end

    def peek? : T?; @heap[0]? end
    def peek : T; @heap.empty? ? raise(IndexError.new("priority queue is empty")) : @heap[0] end

    def push(value : T) : self
        @heap << value
        sift_up(@heap.size - 1)
        self
    end

    def push(*values : T) : self
        values.each { |v| push(v) }
        self
    end

    def <<(value : T) : self; push(value) end

    def pop? : T?
        return nil if @heap.empty?
        top = @heap[0]
        last = @heap.pop
        return top if @heap.empty?
        @heap[0] = last
        sift_down(0)
        top
    end

    def pop : T; pop? || raise(IndexError.new("priority queue is empty")) end

    def pop_push(value : T) : T?
        if @heap.empty?
            push(value)
            return nil
        end
        top = @heap[0]
        @heap[0] = value
        sift_down(0)
        top
    end

    # ----- private helpers ----- #
    private def heapify; (@heap.size // 2 - 1).downto(0) { |i| sift_down(i) } end
    private def parent(index : Int32) : Int32; (index - 1) // 2 end
    private def left_child(index : Int32) : Int32; index * 2 + 1 end
    private def right_child(index : Int32) : Int32; index * 2 + 2 end

    private def sift_up(index : Int32)
        while index > 0
            par = parent(index)
            break unless @higher_priority.call(@heap[index], @heap[par])
            @heap[par], @heap[index] = @heap[index], @heap[par]
            index = par
        end
    end

    private def sift_down(index : Int32)
        n = @heap.size
        loop do
            left = left_child(index)
            break if left >= n
            right = right_child(index)
            child = right < n && @higher_priority.call(@heap[right], @heap[left]) ? right : left
            break unless @higher_priority.call(@heap[child], @heap[index])
            @heap[index], @heap[child] = @heap[child], @heap[index]
            index = child
        end
    end
end

# radix sort
module RadixSort
    PASSES_32 = 4
    PASSES_64 = 8

    def self.sort!(a : Array(Int32)) : Array(Int32)
        n = a.size
        return a if n <= 1
        buf = Array(Int32).new(n) { 0 }
        src = a.to_unsafe
        dst = buf.to_unsafe
        flip = 0x8000_0000_u32

        hist = Pointer(Int32).malloc(256 * PASSES_32, 0)
        i = 0
        while i < n
            key = src[i].to_u32! ^ flip
            p = 0
            while p < PASSES_32
                b = ((key >> (p << 3)) & 0xFF).to_i32
                hist[(p << 8) + b] &+= 1
                p &+= 1
            end
            i &+= 1
        end

        pass = 0
        while pass < PASSES_32
            base = pass << 8
            shift = pass << 3

            skip = false
            b = 0
            while b < 256
                cnt = hist[base + b]
                if cnt == n
                    skip = true
                    break
                end
                if cnt != 0
                    break
                end
                b &+= 1
            end
            if skip
                pass &+= 1
                next
            end

            sum = 0
            b = 0
            while b < 256
                c = hist[base + b]
                hist[base + b] = sum
                sum &+= c
                b &+= 1
            end

            i = 0
            while i < n
                v = src[i]
                bb = (((v.to_u32! ^ flip) >> shift) & 0xFF).to_i32
                pos = hist[base + bb]
                hist[base + bb] = pos &+ 1
                dst[pos] = v
                i &+= 1
            end

            src, dst = dst, src
            pass &+= 1
        end

        if src != a.to_unsafe
            src.copy_to(a.to_unsafe, n)
        end
        a
    end

    def self.sort!(a : Array(Int64)) : Array(Int64)
        n = a.size
        return a if n <= 1
        buf = Array(Int64).new(n) { 0_i64 }
        src = a.to_unsafe
        dst = buf.to_unsafe
        flip = 0x8000_0000_0000_0000_u64

        hist = Pointer(Int32).malloc(256 * PASSES_64, 0)
        i = 0
        while i < n
            key = src[i].to_u64! ^ flip
            p = 0
            while p < PASSES_64
                b = ((key >> (p << 3)) & 0xFF).to_i32
                hist[(p << 8) + b] &+= 1
                p &+= 1
            end
            i &+= 1
        end

        pass = 0
        while pass < PASSES_64
            base = pass << 8
            shift = pass << 3

            skip = false
            b = 0
            while b < 256
                cnt = hist[base + b]
                if cnt == n
                    skip = true
                    break
                end
                if cnt != 0
                    break
                end
                b &+= 1
            end
            if skip
                pass &+= 1
                next
            end

            sum = 0
            b = 0
            while b < 256
                c = hist[base + b]
                hist[base + b] = sum
                sum &+= c
                b &+= 1
            end

            i = 0
            while i < n
                v = src[i]
                bb = (((v.to_u64! ^ flip) >> shift) & 0xFF).to_i32
                pos = hist[base + bb]
                hist[base + bb] = pos &+ 1
                dst[pos] = v
                i &+= 1
            end

            src, dst = dst, src
            pass &+= 1
        end

        if src != a.to_unsafe
            src.copy_to(a.to_unsafe, n)
        end
        a
    end
end

# extensions
class Array(T)
    def shape : Array(Int32)
        s = [] of Int32; cur = self.as(Array)
        loop do
            s << cur.size; break if cur.empty?
            break unless (x = cur[0]).is_a?(Array)
            cur = x.as(Array)
        end
        s
    end
    
    def p_grid
        raise "p_grid expects a 2D array, but got #{shape.size}D (shape: #{shape})" if shape.size != 2
        puts "[\n#{map(&.inspect).join(",\n").lines.map { |l| "  #{l}" }.join("\n")}\n]"
    end
end

class String
    def delete_at(n); self[0, n] + self[(n + 1)..]; end
    def replace_at(n, c); self[0, n] + c + self[(n + 1)..]; end
    def insert_at(n, c); self[0, n] + c + self[n..]; end
    def to_digits : Array(Int32); chars.map { |c| c - '0' }; end
    def palindrome? : Bool; self == reverse; end
    def drop_first(n); self[n..]? || ""; end
    def drop_last(n); n >= size ? "" : self[0...size - n]; end
end

struct Char
    def vowel?; "aeiouAEIOU".includes?(self); end
    def consonant?; ascii_letter? && !vowel?; end
    def to_digit; self - '0'; end
    def alpha_index; ascii_lowercase? ? self - 'a' : self - 'A'; end
end

solve