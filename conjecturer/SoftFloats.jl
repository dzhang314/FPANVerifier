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
        (((e % UInt64) << 32) & 0x7FFF_FFFF_0000_0000) |
        (m % UInt32 % UInt64))


@inline SoftFloat{P}(s::UInt64, e::Integer, m::UInt64) where {P} =
    SoftFloat{P}(s | (((e % UInt64) << 32) & 0x7FFF_FFFF_0000_0000) | m)


@inline Base.signbit(x::SoftFloat) = x.data >= 0x8000_0000_0000_0000
@inline Base.exponent(x::SoftFloat) =
    (reinterpret(Int64, x.data << 1) >> 33) % Int
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


export two_sum, two_prod


@inline _signbit_u64(x::SoftFloat) = x.data & 0x8000_0000_0000_0000


@inline _abs_ge(x::SoftFloat{P}, y::SoftFloat{P}) where {P} =
    reinterpret(Int64, x.data << 1) >= reinterpret(Int64, y.data << 1)


@inline function two_sum(x::SoftFloat{P}, y::SoftFloat{P}) where {P}

    # Define compile-time constants.
    _zero = zero(SoftFloat{P})
    _leading_bit = one(UInt64) << (P - 1)

    # Return early if at least one addend is zero.
    if iszero(_leading_bit & Base.mantissa(x) & Base.mantissa(y))
        s = ifelse(iszero(x), y, x)
        sz = ifelse(signbit(x) & signbit(y), -_zero, _zero)
        return (ifelse(iszero(s), sz, s), _zero)
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

    # Widen and align mantissas and compute exact sum.
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

    # Split exact sum into rounded sum and round-off error.
    num_rounded = num_bits - P
    me = ms << (64 - num_rounded)
    ms >>= num_rounded & 63

    # Compute rounding direction and round exact sum.
    round_up = me > 0x8000_0000_0000_0000 - (ms & one(UInt64))
    ms += round_up

    # Detect and correct rounding-induced carry.
    carry = ms >> P
    es = eb + num_rounded + (carry % Int)
    ms >>= carry & 63

    # Return early if round-off bits are all zero.
    if iszero(me)
        return (SoftFloat{P}(sa, es, ms), _zero)
    end

    # Compute and return exact rounding error.
    abs_me = reinterpret(UInt64, abs(reinterpret(Int64, me)))
    se = xor(sa, (round_up % UInt64) << 63)
    ee = eb + num_rounded - (P + leading_zeros(abs_me))
    me = (abs_me << leading_zeros(abs_me)) >> (64 - P)
    return (SoftFloat{P}(sa, es, ms), SoftFloat{P}(se, ee, me))

end


@inline function two_prod(x::SoftFloat{P}, y::SoftFloat{P}) where {P}

    # Define compile-time constants.
    _zero = zero(SoftFloat{P})
    _ez = exponent(_zero)

    # Widen mantissas and compute exact product.
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
    round_up = me > 0x8000_0000_0000_0000 - (mp & one(UInt64))
    mp += round_up

    # Detect and correct rounding-induced carry.
    carry = mp >> P
    ep += carry % Int
    mp >>= carry & 63

    # Compute and return exact rounding error.
    abs_me = reinterpret(UInt64, abs(reinterpret(Int64, me)))
    se = xor(sp, (round_up % UInt64) << 63)
    ee -= leading_zeros(abs_me)
    me = (abs_me << (leading_zeros(abs_me) & 63)) >> (64 - P)
    pz = SoftFloat{P}(sp, _ez, zero(UInt64))
    return (ifelse(mp_iszero, pz, SoftFloat{P}(sp, ep, mp)),
        ifelse(iszero(abs_me), _zero, SoftFloat{P}(se, ee, me)))

end


################################################################################


export TinyFloat


struct TinyFloat{P}
    data::UInt16
end


@inline TinyFloat{P}(s::Bool, e::Integer, m::Integer) where {P} =
    TinyFloat{P}(((s % UInt16) << 15) |
        (((e % UInt16) << (P - 1)) & 0x7FFF) |
        ((m % UInt16) & ((one(UInt16) << (P - 1)) - one(UInt16))))


@inline TinyFloat{P}(s::UInt16, e::Integer, m::Integer) where {P} =
    TinyFloat{P}(s | (((e % UInt16) << (P - 1)) & 0x7FFF) |
        ((m % UInt16) & ((one(UInt16) << (P - 1)) - one(UInt16))))


@inline Base.signbit(x::TinyFloat) = x.data >= 0x8000
@inline Base.exponent(x::TinyFloat{P}) where {P} =
    (reinterpret(Int16, x.data << 1) >> P) % Int
@inline Base.mantissa(x::TinyFloat{P}) where {P} =
    x.data & ((one(UInt16) << (P - 1)) - one(UInt16))


@inline Base.zero(::Type{TinyFloat{P}}) where {P} = TinyFloat{P}(0x4000)
@inline Base.one(::Type{TinyFloat{P}}) where {P} = TinyFloat{P}(0x0000)
@inline Base.iszero(x::TinyFloat) = (x.data & 0x7FFF) == 0x4000
@inline Base.isone(x::TinyFloat) = iszero(x.data)


@inline Base.:-(x::TinyFloat{P}) where {P} = TinyFloat{P}(xor(x.data, 0x8000))

@inline Base.copysign(x::TinyFloat{P}, y::Any) where {P} =
    TinyFloat{P}((x.data & 0x7FFF) | ((signbit(y) % UInt16) << 15))


################################################################################


@inline _signbit_u16(x::TinyFloat) = x.data & 0x8000


@inline _abs_ge(x::TinyFloat{P}, y::TinyFloat{P}) where {P} =
    reinterpret(Int16, x.data << 1) >= reinterpret(Int16, y.data << 1)


@inline function two_sum(x::TinyFloat{P}, y::TinyFloat{P}) where {P}

    # Define compile-time constants.
    _zero = zero(TinyFloat{P})
    _leading_bit = one(UInt32) << (P - 1)

    # Return early if at least one addend is zero.
    if iszero(x) | iszero(y)
        s = ifelse(iszero(x), y, x)
        sz = ifelse(signbit(x) & signbit(y), -_zero, _zero)
        return (ifelse(iszero(s), sz, s), _zero)
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

    # Widen and align mantissas and compute exact sum.
    sa = _signbit_u16(a)
    sb = _signbit_u16(b)
    ma = (_leading_bit | (Base.mantissa(a) % UInt32)) << (de & 31)
    mb = (_leading_bit | (Base.mantissa(b) % UInt32))
    ms = ifelse(sa == sb, ma + mb, ma - mb)

    # Return early if no rounding is necessary.
    num_bits = 32 - leading_zeros(ms)
    if iszero(num_bits)
        return (_zero, _zero)
    elseif num_bits <= P
        shift = P - num_bits
        es = eb - shift
        ms <<= shift & 31
        return (TinyFloat{P}(sa, es, ms), _zero)
    end

    # Split exact sum into rounded sum and round-off error.
    num_rounded = num_bits - P
    me = ms << (32 - num_rounded)
    ms >>= num_rounded & 31

    # Compute rounding direction and round exact sum.
    round_up = me > 0x8000_0000 - (ms & one(UInt32))
    ms += round_up

    # Detect and correct rounding-induced carry.
    es = eb + num_rounded + ((ms >> P) % Int)

    # Return early if round-off bits are all zero.
    if iszero(me)
        return (TinyFloat{P}(sa, es, ms), _zero)
    end

    # Compute and return exact rounding error.
    abs_me = reinterpret(UInt32, abs(reinterpret(Int32, me)))
    se = xor(sa, (round_up % UInt16) << 15)
    ee = eb + num_rounded - (P + leading_zeros(abs_me))
    me = (abs_me << leading_zeros(abs_me)) >> (32 - P)
    return (TinyFloat{P}(sa, es, ms), TinyFloat{P}(se, ee, me))

end


@inline function two_prod(x::TinyFloat{P}, y::TinyFloat{P}) where {P}

    # Define compile-time constants.
    _zero = zero(TinyFloat{P})
    _leading_bit = one(UInt32) << (P - 1)

    # Widen mantissas and compute exact product.
    sp = xor(_signbit_u16(x), _signbit_u16(y))
    mx = ifelse(iszero(x), zero(UInt32),
        _leading_bit | (Base.mantissa(x) % UInt32))
    my = ifelse(iszero(y), zero(UInt32),
        _leading_bit | (Base.mantissa(y) % UInt32))
    mp = mx * my
    mp_iszero = iszero(mp)

    # Determine the presence of an extra bit and adjust exponents accordingly.
    extra_bit = (mp >> (2 * P - 1)) & one(UInt32)
    ep = exponent(x) + exponent(y) + (extra_bit % Int)
    ee = ep - P

    # Compute rounding direction and round exact product.
    num_rounded = (P - 1) + (extra_bit % Int)
    me = mp << (32 - num_rounded)
    mp >>= num_rounded & 31
    round_up = me > 0x8000_0000 - (mp & one(UInt32))
    mp += round_up

    # Detect and correct rounding-induced carry.
    ep += (mp >> P) % Int

    # Compute and return exact rounding error.
    abs_me = reinterpret(UInt32, abs(reinterpret(Int32, me)))
    se = xor(sp, (round_up % UInt16) << 15)
    ee -= leading_zeros(abs_me)
    me = (abs_me << (leading_zeros(abs_me) & 31)) >> (32 - P)
    pz = TinyFloat{P}(_zero.data | sp)
    return (ifelse(mp_iszero, pz, TinyFloat{P}(sp, ep, mp)),
        ifelse(iszero(abs_me), _zero, TinyFloat{P}(se, ee, me)))

end


################################################################################


export TinyFloatVec


struct TinyFloatVec{M,P}
    data::Vec{M,UInt16}
end


@inline TinyFloatVec{M,P}(
    s::Vec{M,Bool},
    e::Vec{M,<:Integer},
    m::Vec{M,<:Integer},
) where {M,P} = TinyFloatVec{M,P}((convert(Vec{M,UInt16}, s) << 15) |
    ((convert(Vec{M,UInt16}, e) << (P - 1)) & 0x7FFF) |
    (convert(Vec{M,UInt16}, m) & ((one(UInt16) << (P - 1)) - one(UInt16))))


@inline TinyFloatVec{M,P}(
    s::Vec{M,UInt16},
    e::Vec{M,<:Integer},
    m::Vec{M,<:Integer},
) where {M,P} = TinyFloatVec{M,P}(s |
    ((convert(Vec{M,UInt16}, e) << (P - 1)) & 0x7FFF) |
    (convert(Vec{M,UInt16}, m) & ((one(UInt16) << (P - 1)) - one(UInt16))))


@inline Base.signbit(x::TinyFloatVec) = x.data >= 0x8000
@inline Base.exponent(x::TinyFloatVec{M,P}) where {M,P} =
    reinterpret(Vec{M,Int16}, x.data << 1) >> P
@inline Base.mantissa(x::TinyFloatVec{M,P}) where {M,P} =
    x.data & ((one(UInt16) << (P - 1)) - one(UInt16))


@inline Base.zero(::Type{TinyFloatVec{M,P}}) where {M,P} =
    TinyFloatVec{M,P}(Vec{M,UInt16}(0x4000))
@inline Base.one(::Type{TinyFloatVec{M,P}}) where {M,P} =
    TinyFloatVec{M,P}(Vec{M,UInt16}(0x0000))
@inline Base.iszero(x::TinyFloatVec) = (x.data & 0x7FFF) == 0x4000
@inline Base.isone(x::TinyFloatVec) = iszero(x.data)


@inline Base.:-(x::TinyFloatVec{M,P}) where {M,P} =
    TinyFloatVec{M,P}(xor(x.data, 0x8000))

@inline Base.copysign(x::TinyFloatVec{M,P}, y::Any) where {M,P} =
    TinyFloatVec{M,P}((x.data & 0x7FFF) | ((signbit(y) % UInt16) << 15))

@inline Base.copysign(
    x::TinyFloatVec{M,P},
    y::Union{Vec{M},TinyFloatVec{M}},
) where {M,P} = TinyFloatVec{M,P}(
    (x.data & 0x7FFF) | (convert(Vec{M,UInt16}, signbit(y)) << 15))


################################################################################


@inline _signbit_u16(x::TinyFloatVec) = x.data & 0x8000


@inline _abs_ge(x::TinyFloatVec{M,P}, y::TinyFloatVec{M,P}) where {M,P} =
    reinterpret(Vec{M,Int16}, x.data << 1) >=
        reinterpret(Vec{M,Int16}, y.data << 1)


@inline function _normalize(x::Vec{M,UInt16}) where {M}
    y = x
    y |= y >> 1
    y |= y >> 2
    y |= y >> 4
    y |= y >> 8
    num_leading_zeros = count_ones(~y)
    return (x << (num_leading_zeros & 0x000F), num_leading_zeros)
end


@inline function two_sum(x::TinyFloatVec{M,P}, y::TinyFloatVec{M,P}) where {M,P}

    # Define compile-time constants.
    _zero = zero(TinyFloatVec{M,P})
    _leading_bit = one(UInt16) << (P - 1)

    # Order addends by magnitude.
    in_order = _abs_ge(x, y)
    a = TinyFloatVec{M,P}(vifelse(in_order, x.data, y.data))
    b = TinyFloatVec{M,P}(vifelse(in_order, y.data, x.data))

    # Determine whether exponents are too far apart to interact.
    ea = exponent(a)
    eb = exponent(b)
    de = ea - eb
    far = de > Int16(P + 1)

    # Align mantissas and compute exact sum.
    sa = _signbit_u16(a)
    sb = _signbit_u16(b)
    ma = vifelse(iszero(a), 0x0000, _leading_bit | Base.mantissa(a))
    mb = vifelse(iszero(b), 0x0000, _leading_bit | Base.mantissa(b))
    ma <<= reinterpret(Vec{M,UInt16}, de) & 0x000F
    ms = vifelse(sa == sb, ma + mb, ma - mb)
    ms_iszero = iszero(ms)

    # Split exact sum into rounded sum and round-off error.
    ms, leading_zeros_ms = _normalize(ms)
    es = eb + Int16(16 - P) - reinterpret(Vec{M,Int16}, leading_zeros_ms)
    ee = es - Int16(P)
    me = ms << P
    ms >>= 16 - P

    # Compute rounding direction and round exact sum.
    round_up = me > 0x8000 - (ms & one(UInt16))
    ms += convert(Vec{M,UInt16}, round_up)

    # Detect and correct rounding-induced carry.
    es += reinterpret(Vec{M,Int16}, ms >> P)

    # Compute and normalize exact rounding error.
    abs_me = reinterpret(Vec{M,UInt16}, abs(reinterpret(Vec{M,Int16}, me)))
    me, leading_zeros_me = _normalize(abs_me)
    se = xor(sa, convert(Vec{M,UInt16}, round_up) << 15)
    ee -= reinterpret(Vec{M,Int16}, leading_zeros_me)
    me >>= 16 - P

    # Assemble and return vector results.
    sz = (sa & sb) | _zero.data
    s = TinyFloatVec{M,P}(sa, es, ms)
    s = TinyFloatVec{M,P}(vifelse(ms_iszero, sz, s.data))
    s = TinyFloatVec{M,P}(vifelse(far, a.data, s.data))
    ez = vifelse(iszero(b), _zero.data, b.data)
    e = TinyFloatVec{M,P}(se, ee, me)
    e = TinyFloatVec{M,P}(vifelse(iszero(abs_me), _zero.data, e.data))
    e = TinyFloatVec{M,P}(vifelse(far, ez, e.data))
    return (s, e)

end


################################################################################

end # module SoftFloats
