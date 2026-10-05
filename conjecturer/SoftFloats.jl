module SoftFloats

using BFloat16s: BFloat16
using SIMD: Vec, vifelse

################################################################################


export SoftFloat


struct SoftFloat{P}
    data::UInt64
end


@inline SoftFloat{P}(s::Bool, e::Integer, m::Integer) where {P} =
    SoftFloat{P}(((s % UInt64) << 63) |
        (((e % UInt64) & 0x0000_0000_7FFF_FFFF) << 32) |
        (m % UInt32 % UInt64))


@inline Base.signbit(x::SoftFloat) = !iszero(x.data >> 63)
@inline Base.exponent(x::SoftFloat) = (((x.data << 1) % Int64) >> 33) % Int
@inline Base.mantissa(x::SoftFloat) = x.data % UInt32


@inline Base.zero(::Type{SoftFloat{P}}) where {P} =
    SoftFloat{P}(0x4000_0000_0000_0000)
@inline Base.one(::Type{SoftFloat{P}}) where {P} =
    SoftFloat{P}(0x0000_0000_0000_0000)
@inline Base.iszero(x::SoftFloat) =
    ((x.data & 0x7FFF_FFFF_FFFF_FFFF) == 0x4000_0000_0000_0000)
@inline Base.isone(x::SoftFloat) = iszero(x.data)


@inline Base.:-(x::SoftFloat{P}) where {P} =
    SoftFloat{P}(xor(x.data, 0x8000_0000_0000_0000))

@inline Base.copysign(x::SoftFloat{P}, y::Any) where {P} =
    SoftFloat{P}((x.data & 0x7FFF_FFFF_FFFF_FFFF) |
        ((signbit(y) % UInt64) << 63))


################################################################################


export SoftFloatVec


struct SoftFloatVec{M,P}
    data::Vec{M,UInt64}
end


################################################################################


export two_sum


const _ROUNDING_MIDPOINT = 0x8000_0000_0000_0000


@inline _abs_ge(x::SoftFloat{P}, y::SoftFloat{P}) where {P} =
    (((x.data << 1) % Int64) >= ((y.data << 1) % Int64))


@inline function two_sum(x::SoftFloat{P}, y::SoftFloat{P}) where {P}

    # Define compile-time constants.
    _zero = zero(SoftFloat{P})
    _hidden_bit = one(UInt64) << (P - 1)
    _mantissa_mask = _hidden_bit - one(UInt64)

    # Order addends by magnitude.
    in_order = _abs_ge(x, y)
    a = ifelse(in_order, x, y)
    b = ifelse(in_order, y, x)

    # Return early if at least one addend is zero.
    if iszero(b)
        s = ifelse(signbit(x) & signbit(y), -_zero, _zero)
        s = ifelse(iszero(a), s, a)
        return (s, _zero)
    end

    # Return early if exponents are too far apart to interact.
    ea = exponent(a)
    eb = exponent(b)
    de = ea - eb
    if de > P + 1
        return (a, b)
    end

    # Compute exact sum.
    ma = (_hidden_bit | Base.mantissa(a)) << de
    mb = (_hidden_bit | Base.mantissa(b))
    ms = ifelse(signbit(x) == signbit(y), ma + mb, ma - mb)

    # Return early if no rounding is necessary.
    num_bits = 64 - leading_zeros(ms)
    if iszero(num_bits)
        return (_zero, _zero)
    elseif num_bits <= P
        shift = P - num_bits
        es = eb - shift
        ms <<= shift
        s = SoftFloat{P}(signbit(a), es, _mantissa_mask & ms)
        return (s, _zero)
    end

    # Compute rounding direction and round exact sum.
    num_rounded = num_bits - P
    me = ms << (64 - num_rounded)
    ms >>= num_rounded
    round_up = ((me > _ROUNDING_MIDPOINT) |
        ((me == _ROUNDING_MIDPOINT) & isodd(ms)))
    ms += round_up

    # Detect and correct rounding-induced carry.
    es = eb + num_rounded + ((ms >> P) % Int)

    # Return early if rounded-off bits are all zero.
    s = SoftFloat{P}(signbit(a), es, _mantissa_mask & ms)
    if iszero(me)
        return (s, _zero)
    end

    # Construct and return rounding error term.
    abs_me = abs(me % Int64) % UInt64
    ee = eb + num_rounded - (P + leading_zeros(abs_me))
    me = (abs_me << leading_zeros(abs_me)) >> (64 - P)
    e = SoftFloat{P}(xor(signbit(a), round_up), ee, _mantissa_mask & me)
    return (s, e)
end


################################################################################

end # module SoftFloats
