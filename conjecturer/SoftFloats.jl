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


@inline SoftFloat{P}(s::UInt64, e::Integer, m::UInt64) where {P} =
    SoftFloat{P}(s | (((e % UInt64) & 0x0000_0000_7FFF_FFFF) << 32) | m)


@inline Base.signbit(x::SoftFloat) = !iszero(x.data >> 63)
@inline Base.exponent(x::SoftFloat) = (((x.data << 1) % Int64) >> 33) % Int
@inline Base.mantissa(x::SoftFloat) = x.data % UInt32


@inline Base.zero(::Type{SoftFloat{P}}) where {P} =
    SoftFloat{P}(0x4000_0000_0000_0000)
@inline Base.one(::Type{SoftFloat{P}}) where {P} =
    SoftFloat{P}(one(UInt64) << (P - 1))
@inline Base.iszero(x::SoftFloat) = iszero(Base.mantissa(x))
@inline Base.isone(x::SoftFloat{P}) where {P} =
    (x.data == (one(UInt64) << (P - 1)))


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


export two_sum, two_prod


const _ROUNDING_MIDPOINT = 0x8000_0000_0000_0000


@inline _signbit_u64(x::SoftFloat) = (x.data & 0x8000_0000_0000_0000)


@inline _abs_ge(x::SoftFloat{P}, y::SoftFloat{P}) where {P} =
    (((x.data << 1) % Int64) >= ((y.data << 1) % Int64))


@inline function two_sum(x::SoftFloat{P}, y::SoftFloat{P}) where {P}

    # Define compile-time constants.
    _zero = zero(SoftFloat{P})
    _leading_bit = one(UInt64) << (P - 1)

    # Return early if at least one addend is zero.
    if iszero(_leading_bit & Base.mantissa(x) & Base.mantissa(y))
        s = ifelse(iszero(x), y, x)
        signed_zero = ifelse(signbit(x) & signbit(y), -_zero, _zero)
        return (ifelse(iszero(s), signed_zero, s), _zero)
    end

    # Order addends by magnitude.
    in_order = _abs_ge(x, y)
    a = ifelse(in_order, x, y)
    b = ifelse(in_order, y, x)

    # Return early if exponents are too far apart to interact.
    ea = exponent(a)
    eb = exponent(b)
    de = ea - eb
    if de > P + 1
        return (a, b)
    end

    # Compute exact sum, widening mantissas before alignment.
    sa = _signbit_u64(a)
    sb = _signbit_u64(b)
    ma = (Base.mantissa(a) % UInt64) << (de & 63)
    mb = (Base.mantissa(b) % UInt64)
    ms = ifelse(sa == sb, ma + mb, ma - mb)

    # Return early if no rounding is necessary.
    num_bits = 64 - leading_zeros(ms)
    if iszero(num_bits)
        return (_zero, _zero)
    elseif num_bits <= P
        shift = P - num_bits
        es = eb - shift
        ms <<= shift & 63
        return (SoftFloat{P}(sa, es, ms), _zero)
    end

    # Compute rounding direction and round exact sum.
    num_rounded = num_bits - P
    me = ms << (64 - num_rounded)
    ms >>= num_rounded & 63
    round_up = me > _ROUNDING_MIDPOINT - (ms & one(UInt64))
    ms += round_up

    # Detect and correct rounding-induced carry.
    carry = ms >> P
    es = eb + num_rounded + (carry % Int)
    ms >>= carry & 63

    # Return early if rounded-off bits are all zero.
    if iszero(me)
        return (SoftFloat{P}(sa, es, ms), _zero)
    end

    # Construct and return rounding error term.
    abs_me = abs(me % Int64) % UInt64
    se = xor(sa, (round_up % UInt64) << 63)
    ee = eb + num_rounded - (P + leading_zeros(abs_me))
    me = (abs_me << leading_zeros(abs_me)) >> (64 - P)
    return (SoftFloat{P}(sa, es, ms), SoftFloat{P}(se, ee, me))

end


@inline function two_prod(x::SoftFloat{P}, y::SoftFloat{P}) where {P}

    # Define compile-time constants.
    _zero = zero(SoftFloat{P})
    _ez = exponent(_zero)

    # Compute exact product, widening mantissas before multiplication.
    sp = xor(_signbit_u64(x), _signbit_u64(y))
    mp = (Base.mantissa(x) % UInt64) * (Base.mantissa(y) % UInt64)
    mp_iszero = iszero(mp)

    # Determine the presence of an extra bit and adjust exponents accordingly.
    extra_bit = (mp >> (2 * P - 1)) & one(UInt64)
    ep = exponent(x) + exponent(y) + (extra_bit % Int)
    ee = ep - P

    # Compute rounding direction and round exact product.
    num_rounded = (P - 1) + (extra_bit % Int)
    me = mp << (64 - num_rounded)
    mp >>= (num_rounded & 63)
    round_up = me > _ROUNDING_MIDPOINT - (mp & one(UInt64))
    mp += round_up

    # Detect and correct rounding-induced carry.
    carry = mp >> P
    ep += carry % Int
    mp >>= carry & 63

    # Construct and return rounding error term.
    abs_me = abs(me % Int64) % UInt64
    se = xor(sp, (round_up % UInt64) << 63)
    ee -= leading_zeros(abs_me)
    me = (abs_me << (leading_zeros(abs_me) & 63)) >> (64 - P)
    pz = SoftFloat{P}(sp, _ez, zero(UInt64))
    return (ifelse(mp_iszero, pz, SoftFloat{P}(sp, ep, mp)),
        ifelse(iszero(abs_me), _zero, SoftFloat{P}(se, ee, me)))

end


################################################################################

end # module SoftFloats
