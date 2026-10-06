module FloatAbstractions

using Base: exponent_bias, exponent_mask, significand_bits, significand_mask,
    uinttype
using Base.Threads: @threads, nthreads
using Mmap: mmap
using Random: shuffle!

################################################ FLOATING-POINT BIT MANIPULATION


export unsafe_exponent,
    mantissa_leading_bit, mantissa_leading_bits,
    mantissa_leading_zeros, mantissa_leading_ones,
    mantissa_trailing_bit, mantissa_trailing_bits,
    mantissa_trailing_zeros, mantissa_trailing_ones


const _BITS_PER_BYTE = div(64, sizeof(UInt64))
@assert _BITS_PER_BYTE * sizeof(UInt32) == 32
@assert _BITS_PER_BYTE * sizeof(UInt64) == 64


@inline function unsafe_exponent(x::T) where {T<:AbstractFloat}
    raw_exponent = reinterpret(Unsigned, x) & exponent_mask(T)
    raw_exponent >>= significand_bits(T)
    return Int(raw_exponent) - exponent_bias(T)
end


@inline mantissa_leading_bit(x::T) where {T<:AbstractFloat} = !iszero(
    (reinterpret(Unsigned, x) >> (significand_bits(T) - 1)) & one(uinttype(T)))


@inline function mantissa_leading_zeros(x::T) where {T<:AbstractFloat}
    shift = _BITS_PER_BYTE * sizeof(T) - significand_bits(T)
    shifted_mask = significand_mask(T) << shift
    return leading_zeros((reinterpret(Unsigned, x) << shift) | ~shifted_mask)
end


@inline function mantissa_leading_ones(x::T) where {T<:AbstractFloat}
    shift = _BITS_PER_BYTE * sizeof(T) - significand_bits(T)
    shifted_mask = significand_mask(T) << shift
    return leading_ones((reinterpret(Unsigned, x) << shift) & shifted_mask)
end


@inline mantissa_leading_bits(x::AbstractFloat) = ifelse(
    mantissa_leading_bit(x),
    mantissa_leading_ones(x),
    mantissa_leading_zeros(x))


@inline mantissa_trailing_bit(x::T) where {T<:AbstractFloat} = !iszero(
    reinterpret(Unsigned, x) & one(uinttype(T)))


@inline function mantissa_trailing_zeros(x::T) where {T<:AbstractFloat}
    return trailing_zeros(reinterpret(Unsigned, x) | ~significand_mask(T))
end


@inline function mantissa_trailing_ones(x::T) where {T<:AbstractFloat}
    return trailing_ones(reinterpret(Unsigned, x) & significand_mask(T))
end


@inline mantissa_trailing_bits(x::AbstractFloat) = ifelse(
    mantissa_trailing_bit(x),
    mantissa_trailing_ones(x),
    mantissa_trailing_zeros(x))


################################################### ABSTRACTION TYPE DEFINITIONS


export FloatAbstraction, EFTAbstraction, TwoSumAbstraction, TwoProdAbstraction,
    SEAbstraction, SETZAbstraction, SELBTZAbstraction, SELTZOAbstraction


# Our packed FloatAbstraction representation assumes that:
# - The exponent fits into a 15-bit signed integer.
# - The number of mantissa bits fits into a 7-bit unsigned integer.
# This just barely accommodates IEEE quadruple precision (binary128) using
# 1 (sign) + 1 (leading bit) + 1 (trailing bit) + 15 (exponent)
# + 7 (leading bit count) + 7 (trailing bit count) = 32 bits.


abstract type FloatAbstraction end


abstract type EFTAbstraction{A<:FloatAbstraction} end


struct TwoSumAbstraction{A<:FloatAbstraction} <: EFTAbstraction{A}
    x::A
    y::A
    s::A
    e::A
end


struct TwoProdAbstraction{A<:FloatAbstraction} <: EFTAbstraction{A}
    x::A
    y::A
    p::A
    e::A
end


@inline Base.isless(a::TwoSumAbstraction{A}, b::TwoSumAbstraction{A}) where
{A<:FloatAbstraction} = isless((a.x, a.y, a.s, a.e), (b.x, b.y, b.s, b.e))
@inline Base.isless(a::TwoProdAbstraction{A}, b::TwoProdAbstraction{A}) where
{A<:FloatAbstraction} = isless((a.x, a.y, a.p, a.e), (b.x, b.y, b.p, b.e))


struct SEAbstraction <: FloatAbstraction
    data::UInt32
end


struct SETZAbstraction <: FloatAbstraction
    data::UInt32
end


struct SELBTZAbstraction <: FloatAbstraction
    data::UInt32
end


struct SELTZOAbstraction <: FloatAbstraction
    data::UInt32
end


@inline Base.isless(a::SEAbstraction, b::SEAbstraction) =
    isless(a.data, b.data)
@inline Base.isless(a::SETZAbstraction, b::SETZAbstraction) =
    isless(a.data, b.data)
@inline Base.isless(a::SELBTZAbstraction, b::SELBTZAbstraction) =
    isless(a.data, b.data)
@inline Base.isless(a::SELTZOAbstraction, b::SELTZOAbstraction) =
    isless(a.data, b.data)


####################################################### ABSTRACTION CONSTRUCTORS


@inline function SEAbstraction(s::Bool, e::Int)
    if !(-16383 <= e <= 16384)
        throw(DomainError(e, "Exponent out of range."))
    end
    return SEAbstraction((UInt32(s) << 31) | (UInt32(e + 16383) << 14))
end


@inline function SETZAbstraction(s::Bool, e::Int, tz::Int)
    if !(-16383 <= e <= 16384)
        throw(DomainError(e, "Exponent out of range."))
    end
    if !(0 <= tz <= 127)
        throw(DomainError(tz, "Number of trailing zeros out of range."))
    end
    return SETZAbstraction((UInt32(s) << 31) |
        (UInt32(e + 16383) << 14) | UInt32(tz))
end


@inline function SELBTZAbstraction(
    s::Bool, lb::Bool,
    e::Int, nlb::Int, ntz::Int,
)
    if !(-16383 <= e <= 16384)
        throw(DomainError(e, "Exponent out of range."))
    end
    if !(0 <= nlb <= 127)
        throw(DomainError(nlb, "Number of leading bits out of range."))
    end
    if !(0 <= ntz <= 127)
        throw(DomainError(ntz, "Number of trailing zeros out of range."))
    end
    return SELBTZAbstraction((UInt32(s) << 31) | (UInt32(lb) << 30) |
        (UInt32(e + 16383) << 14) | (UInt32(nlb) << 7) | UInt32(ntz))
end


@inline function SELTZOAbstraction(
    s::Bool, lb::Bool, tb::Bool,
    e::Int, nlb::Int, ntb::Int,
)
    if !(-16383 <= e <= 16384)
        throw(DomainError(e, "Exponent out of range."))
    end
    if !(0 <= nlb <= 127)
        throw(DomainError(nlb, "Number of leading bits out of range."))
    end
    if !(0 <= ntb <= 127)
        throw(DomainError(ntb, "Number of trailing bits out of range."))
    end
    return SELTZOAbstraction(
        (UInt32(s) << 31) | (UInt32(lb) << 30) | (UInt32(tb) << 29) |
            (UInt32(e + 16383) << 14) | (UInt32(nlb) << 7) | UInt32(ntb))
end


@inline SEAbstraction(x::AbstractFloat) = SEAbstraction(
    signbit(x), unsafe_exponent(x))


@inline SETZAbstraction(x::AbstractFloat) = SETZAbstraction(
    signbit(x), unsafe_exponent(x), mantissa_trailing_zeros(x))


@inline SELBTZAbstraction(x::AbstractFloat) = SELBTZAbstraction(
    signbit(x), mantissa_leading_bit(x),
    unsafe_exponent(x), mantissa_leading_bits(x), mantissa_trailing_zeros(x))


@inline SELTZOAbstraction(x::AbstractFloat) = SELTZOAbstraction(
    signbit(x), mantissa_leading_bit(x), mantissa_trailing_bit(x),
    unsafe_exponent(x), mantissa_leading_bits(x), mantissa_trailing_bits(x))


@inline TwoSumAbstraction{A}(x::T, y::T, s::T, e::T) where
{A<:FloatAbstraction,T<:AbstractFloat} =
    TwoSumAbstraction{A}(A(x), A(y), A(s), A(e))


@inline TwoProdAbstraction{A}(x::T, y::T, p::T, e::T) where
{A<:FloatAbstraction,T<:AbstractFloat} =
    TwoProdAbstraction{A}(A(x), A(y), A(p), A(e))


##################################################### ABSTRACTION DATA ACCESSORS


@inline Base.signbit(x::SEAbstraction) = isone(x.data >> 31)
@inline Base.signbit(x::SETZAbstraction) = isone(x.data >> 31)
@inline Base.signbit(x::SELBTZAbstraction) = isone(x.data >> 31)
@inline Base.signbit(x::SELTZOAbstraction) = isone(x.data >> 31)


@inline unsafe_exponent(x::SEAbstraction) =
    Int((x.data >> 14) & 0x00007FFF) - 16383
@inline unsafe_exponent(x::SETZAbstraction) =
    Int((x.data >> 14) & 0x00007FFF) - 16383
@inline unsafe_exponent(x::SELBTZAbstraction) =
    Int((x.data >> 14) & 0x00007FFF) - 16383
@inline unsafe_exponent(x::SELTZOAbstraction) =
    Int((x.data >> 14) & 0x00007FFF) - 16383


@inline mantissa_trailing_zeros(x::SETZAbstraction) =
    Int(x.data & 0x0000007F)
@inline mantissa_trailing_zeros(x::SELBTZAbstraction) =
    Int(x.data & 0x0000007F)


@inline mantissa_leading_bit(x::SELBTZAbstraction) =
    isone((x.data >> 30) & 0x00000001)
@inline mantissa_leading_bit(x::SELTZOAbstraction) =
    isone((x.data >> 30) & 0x00000001)
@inline mantissa_leading_bits(x::SELBTZAbstraction) =
    Int((x.data >> 7) & 0x0000007F)
@inline mantissa_leading_bits(x::SELTZOAbstraction) =
    Int((x.data >> 7) & 0x0000007F)
@inline mantissa_leading_zeros(x::SELBTZAbstraction) =
    ifelse(mantissa_leading_bit(x), 0, mantissa_leading_bits(x))
@inline mantissa_leading_zeros(x::SELTZOAbstraction) =
    ifelse(mantissa_leading_bit(x), 0, mantissa_leading_bits(x))
@inline mantissa_leading_ones(x::SELBTZAbstraction) =
    ifelse(mantissa_leading_bit(x), mantissa_leading_bits(x), 0)
@inline mantissa_leading_ones(x::SELTZOAbstraction) =
    ifelse(mantissa_leading_bit(x), mantissa_leading_bits(x), 0)


@inline mantissa_trailing_bit(x::SELTZOAbstraction) =
    isone((x.data >> 29) & 0x00000001)
@inline mantissa_trailing_bits(x::SELTZOAbstraction) =
    Int(x.data & 0x0000007F)
@inline mantissa_trailing_zeros(x::SELTZOAbstraction) =
    ifelse(mantissa_trailing_bit(x), 0, mantissa_trailing_bits(x))
@inline mantissa_trailing_ones(x::SELTZOAbstraction) =
    ifelse(mantissa_trailing_bit(x), mantissa_trailing_bits(x), 0)


##################################################### ABSTRACTION CLASSIFICATION


export SELTZOClass, seltzo_classify,
    ZERO, POW2, ALL1, R0R1, R1R0, ONE0, ONE1, TWO0, TWO1, MM01, MM10,
    G00, G01, G10, G11


@enum SELTZOClass begin
    ZERO # e = e_min - 1
    POW2 # ~lb; ~tb; nlb = ntb = p - 1
    ALL1 #  lb;  tb; nlb = ntb = p - 1
    R0R1 # ~lb;  tb; nlb + ntb = p - 1
    R1R0 #  lb; ~tb; nlb + ntb = p - 1
    ONE0 #  lb;  tb; nlb + ntb = p - 2
    ONE1 # ~lb; ~tb; nlb + ntb = p - 2
    TWO0 #  lb;  tb; nlb + ntb = p - 3
    TWO1 # ~lb; ~tb; nlb + ntb = p - 3
    MM01 #  lb; ~tb; nlb + ntb = p - 3
    MM10 # ~lb;  tb; nlb + ntb = p - 3
    G00  # ~lb; ~tb; nlb + ntb < p - 3
    G01  # ~lb;  tb; nlb + ntb < p - 3
    G10  #  lb; ~tb; nlb + ntb < p - 3
    G11  #  lb;  tb; nlb + ntb < p - 3
end


@inline function seltzo_classify(
    x::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}
    _zero = zero(T)
    pos_zero = SELTZOAbstraction(+_zero)
    neg_zero = SELTZOAbstraction(-_zero)
    if (x == pos_zero) | (x == neg_zero)
        return ZERO
    end
    p = precision(T)
    lb = mantissa_leading_bit(x)
    tb = mantissa_trailing_bit(x)
    nlb = mantissa_leading_bits(x)
    ntb = mantissa_trailing_bits(x)
    if nlb == ntb == p - 1
        return (~lb & ~tb) ? POW2 :
               (lb & tb) ? ALL1 :
               throw(DomainError(x, "Invalid SELTZOAbstraction."))
    elseif nlb + ntb == p - 1
        return (~lb & tb) ? R0R1 :
               (lb & ~tb) ? R1R0 :
               throw(DomainError(x, "Invalid SELTZOAbstraction."))
    elseif nlb + ntb == p - 2
        return (lb & tb) ? ONE0 :
               (~lb & ~tb) ? ONE1 :
               throw(DomainError(x, "Invalid SELTZOAbstraction."))
    elseif nlb + ntb == p - 3
        return lb ? (tb ? TWO0 : MM01) : (tb ? MM10 : TWO1)
    elseif 1 < nlb + ntb < p - 3
        return lb ? (tb ? G11 : G10) : (tb ? G01 : G00)
    else
        throw(DomainError(x, "Invalid SELTZOAbstraction."))
    end
end


@inline mantissa_leading_bit(t::SELTZOClass) = (t == ALL1) | (t == R1R0) |
    (t == ONE0) | (t == TWO0) | (t == MM01) | (t == G10) | (t == G11)


@inline mantissa_trailing_bit(t::SELTZOClass) = (t == ALL1) | (t == R0R1) |
    (t == ONE0) | (t == TWO0) | (t == MM10) | (t == G01) | (t == G11)


########################################################## ABSTRACTION UNPACKING


export unpack, unpack_bools, unpack_ints


@inline unpack(x::SEAbstraction) =
    (signbit(x), unsafe_exponent(x))

@inline unpack(x::SEAbstraction, ::Type{T}) where {T<:AbstractFloat} =
    (signbit(x), unsafe_exponent(x))

@inline unpack_bools(x::SEAbstraction) =
    (signbit(x),)

@inline unpack_bools(x::SEAbstraction, ::Type{T}) where {T<:AbstractFloat} =
    (signbit(x),)

@inline unpack_ints(x::SEAbstraction) =
    (unsafe_exponent(x),)

@inline unpack_ints(x::SEAbstraction, ::Type{T}) where {T<:AbstractFloat} =
    (unsafe_exponent(x),)


@inline unpack(x::SETZAbstraction) =
    (signbit(x), unsafe_exponent(x), mantissa_trailing_zeros(x))

@inline function unpack(
    x::SETZAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}
    p = precision(T)
    s = signbit(x)
    e = unsafe_exponent(x)
    f = e - ((p - 1) - mantissa_trailing_zeros(x))
    return (s, e, f)
end

@inline unpack_bools(x::SETZAbstraction) =
    (signbit(x),)

@inline unpack_bools(x::SETZAbstraction, ::Type{T}) where {T<:AbstractFloat} =
    (signbit(x),)

@inline unpack_ints(x::SETZAbstraction) =
    (unsafe_exponent(x), mantissa_trailing_zeros(x))

@inline function unpack_ints(
    x::SETZAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}
    p = precision(T)
    e = unsafe_exponent(x)
    f = e - ((p - 1) - mantissa_trailing_zeros(x))
    return (e, f)
end


@inline unpack(x::SELBTZAbstraction) = (
    signbit(x),
    mantissa_leading_bit(x),
    unsafe_exponent(x),
    mantissa_leading_bits(x),
    mantissa_trailing_zeros(x),
)

@inline function unpack(
    x::SELBTZAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}
    p = precision(T)
    s = signbit(x)
    lb = mantissa_leading_bit(x)
    e = unsafe_exponent(x)
    f = e - (mantissa_leading_bits(x) + 1)
    g = e - ((p - 1) - mantissa_trailing_zeros(x))
    return (s, lb, e, f, g)
end

@inline unpack_bools(x::SELBTZAbstraction) =
    (signbit(x), mantissa_leading_bit(x))

@inline unpack_bools(x::SELBTZAbstraction, ::Type{T}) where {T<:AbstractFloat} =
    (signbit(x), mantissa_leading_bit(x))

@inline unpack_ints(x::SELBTZAbstraction) =
    (unsafe_exponent(x), mantissa_leading_bits(x), mantissa_trailing_zeros(x))

@inline function unpack_ints(
    x::SELBTZAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}
    p = precision(T)
    e = unsafe_exponent(x)
    f = e - (mantissa_leading_bits(x) + 1)
    g = e - ((p - 1) - mantissa_trailing_zeros(x))
    return (e, f, g)
end


@inline unpack(x::SELTZOAbstraction) = (
    signbit(x),
    mantissa_leading_bit(x),
    mantissa_trailing_bit(x),
    unsafe_exponent(x),
    mantissa_leading_bits(x),
    mantissa_trailing_bits(x),
)

@inline function unpack(
    x::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}
    p = precision(T)
    s = signbit(x)
    lb = mantissa_leading_bit(x)
    tb = mantissa_trailing_bit(x)
    e = unsafe_exponent(x)
    f = e - (mantissa_leading_bits(x) + 1)
    g = e - ((p - 1) - mantissa_trailing_bits(x))
    return (s, lb, tb, e, f, g)
end

@inline unpack_bools(x::SELTZOAbstraction) =
    (signbit(x), mantissa_leading_bit(x), mantissa_trailing_bit(x))

@inline unpack_bools(x::SELTZOAbstraction, ::Type{T}) where {T<:AbstractFloat} =
    (signbit(x), mantissa_leading_bit(x), mantissa_trailing_bit(x))

@inline unpack_ints(x::SELTZOAbstraction) =
    (unsafe_exponent(x), mantissa_leading_bits(x), mantissa_trailing_bits(x))

@inline function unpack_ints(
    x::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}
    p = precision(T)
    e = unsafe_exponent(x)
    f = e - (mantissa_leading_bits(x) + 1)
    g = e - ((p - 1) - mantissa_trailing_bits(x))
    return (e, f, g)
end


######################################################### EXHAUSTIVE ENUMERATION


export enumerate_abstractions


@inline _isnormal(x::AbstractFloat) = isfinite(x) & !issubnormal(x)


function enumerate_abstractions(
    ::Type{A},
    ::Type{T},
) where {A<:FloatAbstraction,T<:AbstractFloat}
    U = uinttype(T)
    result = Set{A}()
    for i = typemin(U):typemax(U)
        x = reinterpret(T, i)
        if _isnormal(x)
            push!(result, A(x))
        end
    end
    return sort!(collect(result))
end


function enumerate_abstractions(
    ::Type{SELTZOAbstraction},
    ::Type{T},
    class::SELTZOClass,
) where {T<:AbstractFloat}
    U = uinttype(T)
    result = Set{SELTZOAbstraction}()
    for i = typemin(U):typemax(U)
        x = reinterpret(T, i)
        if _isnormal(x)
            a = SELTZOAbstraction(x)
            if seltzo_classify(a, T) == class
                push!(result, a)
            end
        end
    end
    return sort!(collect(result))
end


@inline function _deinterleave(k::UInt32)
    i = (k >> 0) & 0x55555555
    j = (k >> 1) & 0x55555555
    i = (i | (i >> 1)) & 0x33333333
    j = (j | (j >> 1)) & 0x33333333
    i = (i | (i >> 2)) & 0x0F0F0F0F
    j = (j | (j >> 2)) & 0x0F0F0F0F
    i = (i | (i >> 4)) & 0x00FF00FF
    j = (j | (j >> 4)) & 0x00FF00FF
    i = (i | (i >> 8)) & 0x0000FFFF
    j = (j | (j >> 8)) & 0x0000FFFF
    return (UInt16(i), UInt16(j))
end


function two_sum(x::T, y::T) where {T}
    s = x + y
    x_prime = s - y
    y_prime = s - x_prime
    x_err = x - x_prime
    y_err = y - y_prime
    e = x_err + y_err
    return (s, e)
end


function two_prod(x::T, y::T) where {T}
    p = x * y
    e = fma(x, y, -p)
    return (p, e)
end


function _chunk(
    ::Type{TwoSumAbstraction{A}},
    ::Type{T},
    lo::I,
    hi::I,
) where {A<:FloatAbstraction,T<:AbstractFloat,I<:Integer}
    @assert isbitstype(T)
    @assert 2 * sizeof(T) == sizeof(I)
    result = Set{TwoSumAbstraction{A}}()
    for k = lo:hi
        i, j = _deinterleave(k)
        x = reinterpret(T, i)
        y = reinterpret(T, j)
        s, e = two_sum(x, y)
        if _isnormal(x) & _isnormal(y) & _isnormal(s) & _isnormal(e)
            push!(result, TwoSumAbstraction{A}(x, y, s, e))
        end
    end
    return result
end


function _chunk(
    ::Type{TwoProdAbstraction{A}},
    ::Type{T},
    lo::I,
    hi::I,
) where {A<:FloatAbstraction,T<:AbstractFloat,I<:Integer}
    @assert isbitstype(T)
    @assert 2 * sizeof(T) == sizeof(I)
    result = Set{TwoProdAbstraction{A}}()
    for k = lo:hi
        i, j = _deinterleave(k)
        x = reinterpret(T, i)
        y = reinterpret(T, j)
        p, e = two_prod(x, y)
        if _isnormal(x) & _isnormal(y) & _isnormal(p) & _isnormal(e)
            push!(result, TwoProdAbstraction{A}(x, y, p, e))
        end
    end
    return result
end


function enumerate_abstractions(
    ::Type{TwoSumAbstraction{A}},
    ::Type{T},
) where {A<:FloatAbstraction,T<:AbstractFloat}
    @assert isbitstype(T)
    @assert 2 * sizeof(T) == sizeof(UInt32)
    # Run at least 4 chunks per thread.
    n = trailing_zeros(nextpow(2, clamp(4 * nthreads(), 4, 65536)))
    chunk_size = (0xFFFFFFFF >> n) + 0x00000001
    results = Vector{Set{TwoSumAbstraction{A}}}(undef, 1 << n)
    @threads for chunk_index = 1:(1<<n)
        lo = chunk_size * UInt32(chunk_index - 1)
        hi = chunk_size * UInt32(chunk_index) - 0x00000001
        results[chunk_index] = _chunk(TwoSumAbstraction{A}, T, lo, hi)
    end
    return sort!(collect(union(results...)))
end


function enumerate_abstractions(
    ::Type{TwoProdAbstraction{A}},
    ::Type{T},
) where {A<:FloatAbstraction,T<:AbstractFloat}
    @assert isbitstype(T)
    @assert 2 * sizeof(T) == sizeof(UInt32)
    # Run at least 4 chunks per thread.
    n = trailing_zeros(nextpow(2, clamp(4 * nthreads(), 4, 65536)))
    chunk_size = (0xFFFFFFFF >> n) + 0x00000001
    results = Vector{Set{TwoProdAbstraction{A}}}(undef, 1 << n)
    @threads for chunk_index = 1:(1<<n)
        lo = chunk_size * UInt32(chunk_index - 1)
        hi = chunk_size * UInt32(chunk_index) - 0x00000001
        results[chunk_index] = _chunk(TwoProdAbstraction{A}, T, lo, hi)
    end
    return sort!(collect(union(results...)))
end


function enumerate_abstractions(
    ::Type{TwoSumAbstraction{SELTZOAbstraction}},
    ::Type{T},
    cx::SELTZOClass,
    cy::SELTZOClass,
) where {T<:AbstractFloat}
    U = uinttype(T)
    xs = T[]
    ys = T[]
    for i = typemin(U):typemax(U)
        z = reinterpret(T, i)
        if _isnormal(z)
            cz = seltzo_classify(SELTZOAbstraction(z), T)
            if cx == cz
                push!(xs, z)
            end
            if cy == cz
                push!(ys, z)
            end
        end
    end
    result = Set{TwoSumAbstraction{SELTZOAbstraction}}()
    for x in xs, y in ys
        s, e = two_sum(x, y)
        if _isnormal(s) & _isnormal(e)
            push!(result, TwoSumAbstraction{SELTZOAbstraction}(x, y, s, e))
        end
    end
    return sort!(collect(result))
end


function enumerate_abstractions(
    ::Type{TwoProdAbstraction{SELTZOAbstraction}},
    ::Type{T},
    cx::SELTZOClass,
    cy::SELTZOClass,
) where {T<:AbstractFloat}
    U = uinttype(T)
    xs = T[]
    ys = T[]
    for i = typemin(U):typemax(U)
        z = reinterpret(T, i)
        if _isnormal(z)
            cz = seltzo_classify(SELTZOAbstraction(z), T)
            if cx == cz
                push!(xs, z)
            end
            if cy == cz
                push!(ys, z)
            end
        end
    end
    result = Set{TwoProdAbstraction{SELTZOAbstraction}}()
    for x in xs, y in ys
        p, e = two_prod(x, y)
        if _isnormal(p) & _isnormal(e)
            push!(result, TwoProdAbstraction{SELTZOAbstraction}(x, y, p, e))
        end
    end
    return sort!(collect(result))
end


function _merge(
    src1::AbstractString,
    src2::AbstractString,
    dst::AbstractString,
    ::Type{T},
) where {T}
    @assert isbitstype(T)

    s1 = filesize(src1)
    s2 = filesize(src2)
    if iszero(s1)
        cp(src2, dst)
        return nothing
    elseif iszero(s2)
        cp(src1, dst)
        return nothing
    end

    v = mmap(src1, Vector{T})
    w = mmap(src2, Vector{T})
    m = length(v)
    n = length(w)

    io = open(dst, "w+")
    truncate(io, s1 + s2)
    result = mmap(io, Vector{T})

    i = 1
    j = 1
    k = 1
    while (i <= m) && (j <= n)
        t1 = v[i]
        t2 = w[j]
        if isless(t1, t2)
            result[k] = t1
            i += 1
        elseif isless(t2, t1)
            result[k] = t2
            j += 1
        else
            @assert t1 === t2
            result[k] = t1
            i += 1
            j += 1
        end
        k += 1
    end

    while i <= m
        result[k] = v[i]
        i += 1
        k += 1
    end
    finalize(v)

    while j <= n
        result[k] = w[j]
        j += 1
        k += 1
    end
    finalize(w)

    finalize(result)
    truncate(io, (k - 1) * sizeof(T))
    close(io)
    return nothing
end


function enumerate_abstractions(
    ::Type{TwoSumAbstraction{A}},
    ::Type{T},
    filepath::AbstractString,
    num_chunks::Int=1024,
) where {A<:FloatAbstraction,T<:AbstractFloat}
    @assert !isfile(filepath)
    @assert ispow2(num_chunks)
    n = trailing_zeros(num_chunks)
    chunk_size = (0xFFFFFFFF >> n) + 0x00000001
    mktempdir() do dirpath
        cd(dirpath) do
            @threads for chunk_index = 1:(1<<n)
                lo = chunk_size * UInt32(chunk_index - 1)
                hi = chunk_size * UInt32(chunk_index) - 0x00000001
                open("0-$chunk_index.bin", "w") do io
                    write(io, sort!(collect(_chunk(
                        TwoSumAbstraction{A}, T, lo, hi))))
                end
            end
            for m = 1:n
                @threads for chunk_index = 1:(1<<(n-m))
                    src1 = "$(m - 1)-$(2 * chunk_index - 1).bin"
                    src2 = "$(m - 1)-$(2 * chunk_index - 0).bin"
                    dst = "$m-$chunk_index.bin"
                    _merge(src1, src2, dst, TwoSumAbstraction{A})
                    rm(src1)
                    rm(src2)
                end
            end
        end
        finalpath = joinpath(dirpath, "$n-1.bin")
        @assert isfile(finalpath)
        mv(finalpath, filepath)
    end
    return nothing
end


function enumerate_abstractions(
    ::Type{TwoProdAbstraction{A}},
    ::Type{T},
    filepath::AbstractString,
    num_chunks::Int,
) where {A<:FloatAbstraction,T<:AbstractFloat}
    @assert !isfile(filepath)
    @assert ispow2(num_chunks)
    n = trailing_zeros(num_chunks)
    chunk_size = (0xFFFFFFFF >> n) + 0x00000001
    mktempdir() do dirpath
        cd(dirpath) do
            @threads for chunk_index = 1:(1<<n)
                lo = chunk_size * UInt32(chunk_index - 1)
                hi = chunk_size * UInt32(chunk_index) - 0x00000001
                open("0-$chunk_index.bin", "w") do io
                    write(io, sort!(collect(_chunk(
                        TwoProdAbstraction{A}, T, lo, hi))))
                end
            end
            for m = 1:n
                @threads for chunk_index = 1:(1<<(n-m))
                    src1 = "$(m - 1)-$(2 * chunk_index - 1).bin"
                    src2 = "$(m - 1)-$(2 * chunk_index - 0).bin"
                    dst = "$m-$chunk_index.bin"
                    _merge(src1, src2, dst, TwoProdAbstraction{A})
                    rm(src1)
                    rm(src2)
                end
            end
        end
        finalpath = joinpath(dirpath, "$n-1.bin")
        @assert isfile(finalpath)
        mv(finalpath, filepath)
    end
    return nothing
end


################################################################## OUTPUT LOOKUP


export abstract_outputs, classified_outputs


function abstract_outputs(
    two_sum_abstractions::AbstractVector{TwoSumAbstraction{A}},
    x::A,
    y::A,
) where {A<:FloatAbstraction}
    target = TwoSumAbstraction{A}(x, y, x, y)
    v = view(two_sum_abstractions,
        searchsorted(two_sum_abstractions, target; by=(a -> (a.x, a.y))))
    return [(a.s, a.e) for a in v]
end


function abstract_outputs(
    two_prod_abstractions::AbstractVector{TwoProdAbstraction{A}},
    x::A,
    y::A,
) where {A<:FloatAbstraction}
    target = TwoProdAbstraction{A}(x, y, x, y)
    v = view(two_prod_abstractions,
        searchsorted(two_prod_abstractions, target; by=(a -> (a.x, a.y))))
    return [(a.p, a.e) for a in v]
end


function classified_outputs(
    two_sum_abstractions::AbstractVector{TwoSumAbstraction{SELTZOAbstraction}},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}
    result = Dict{
        Tuple{Bool,SELTZOClass,Bool,SELTZOClass},
        Vector{NTuple{6,Int}}}()
    for (s, e) in abstract_outputs(two_sum_abstractions, x, y)
        ss = signbit(s)
        cs = seltzo_classify(s, T)
        se = signbit(e)
        ce = seltzo_classify(e, T)
        key = (ss, cs, se, ce)
        value = (unpack_ints(s, T)..., unpack_ints(e, T)...)
        if haskey(result, key)
            push!(result[key], value)
        else
            result[key] = [value]
        end
    end
    for (_, v) in result
        sort!(v)
    end
    return result
end


################################################################# LEMMA CHECKING


export LemmaChecker, add_case!, SELBTZRange, SELTZORange


struct LemmaChecker{A<:FloatAbstraction,E<:EFTAbstraction{A},T<:AbstractFloat}
    eft_abstractions::Vector{E}
    x::A
    y::A
    covering_lemmas::Set{String}
    total_counts::Dict{String,Int}
end


function LemmaChecker(
    eft_abstractions::Vector{E},
    x::A,
    y::A,
    ::Type{T},
    total_counts::Dict{String,Int},
) where {A<:FloatAbstraction,E<:EFTAbstraction{A},T<:AbstractFloat}
    return LemmaChecker{A,E,T}(
        eft_abstractions, x, y, Set{String}(), total_counts)
end


struct _LemmaOutputs{A<:FloatAbstraction,T<:AbstractFloat}
    claimed_outputs::Vector{Tuple{A,A}}
end


function (checker::LemmaChecker{A,E,T})(
    state_claims!::F,
) where {A<:FloatAbstraction,E<:EFTAbstraction{A},T<:AbstractFloat,F}
    computed_outputs = abstract_outputs(
        checker.eft_abstractions, checker.x, checker.y)
    if isempty(computed_outputs)
        return false
    end
    lemma = _LemmaOutputs{A,T}(Tuple{A,A}[])
    state_claims!(lemma)
    return computed_outputs == sort!(lemma.claimed_outputs)
end


function (checker::LemmaChecker{A,E,T})(
    state_claims!::F,
    lemma_name::String,
    hypothesis::Bool,
) where {A<:FloatAbstraction,E<:EFTAbstraction{A},T<:AbstractFloat,F}
    if hypothesis
        computed_outputs = abstract_outputs(
            checker.eft_abstractions, checker.x, checker.y)
        if isempty(computed_outputs)
            return nothing
        end
        lemma = _LemmaOutputs{A,T}(Tuple{A,A}[])
        state_claims!(lemma)
        if computed_outputs == sort!(lemma.claimed_outputs)
            push!(checker.covering_lemmas, lemma_name)
            if haskey(checker.total_counts, lemma_name)
                checker.total_counts[lemma_name] += 1
            else
                checker.total_counts[lemma_name] = 1
            end
        else
            println(stderr,
                "ERROR: Claimed outputs of lemma $lemma_name" *
                    " do not match actual computed outputs.")
            println(stderr, "Input 1: $(unpack(checker.x, T)) [$(checker.x)]")
            println(stderr, "Input 2: $(unpack(checker.y, T)) [$(checker.y)]")
            println(stderr, "Claimed outputs:")
            for (r, e) in lemma.claimed_outputs
                println(stderr, "    $(unpack(r, T)), $(unpack(e, T))")
            end
            println(stderr, "Computed outputs:")
            for (r, e) in computed_outputs
                println(stderr, "    $(unpack(r, T)), $(unpack(e, T))")
            end
            flush(stderr)
        end
    end
    return nothing
end


function add_case!(
    lemma::_LemmaOutputs{A,T},
    r::A,
    e::A,
) where {A<:FloatAbstraction,T<:AbstractFloat}
    push!(lemma.claimed_outputs, (r, e))
    return lemma
end


const _BoolRange = Union{Bool,UnitRange{Bool}}
const _IntRange = Union{Int,UnitRange{Int}}


@inline _lemma_range_s(b::Bool) = b:b

@inline _lemma_range_s(r::UnitRange{Bool}) = r


@inline function _lemma_range_e(
    r::UnitRange{Int},
    ::Type{T},
) where {T<:AbstractFloat}
    e_min = exponent(floatmin(T))
    e_max = exponent(floatmax(T))
    return max(r.start, e_min):min(r.stop, e_max)
end

@inline _lemma_range_e(i::Int, ::Type{T}) where {T<:AbstractFloat} =
    _lemma_range_e(i:i, T)


const _SERange = Tuple{_BoolRange,_IntRange}


function add_case!(
    lemma::_LemmaOutputs{SEAbstraction,T},
    (sr_range, er_range)::_SERange,
    e::SEAbstraction
) where {T<:AbstractFloat}
    for sr in _lemma_range_s(sr_range)
        for er in _lemma_range_e(er_range, T)
            r = SEAbstraction(sr, er)
            push!(lemma.claimed_outputs, (r, e))
        end
    end
    return lemma
end


function add_case!(
    lemma::_LemmaOutputs{SEAbstraction,T},
    (sr_range, er_range)::_SERange,
    (se_range, ee_range)::_SERange,
) where {T<:AbstractFloat}
    for sr in _lemma_range_s(sr_range)
        for er in _lemma_range_e(er_range, T)
            for se in _lemma_range_s(se_range)
                for ee in _lemma_range_e(ee_range, T)
                    r = SEAbstraction(sr, er)
                    e = SEAbstraction(se, ee)
                    push!(lemma.claimed_outputs, (r, e))
                end
            end
        end
    end
    return lemma
end


@inline function _lemma_range_t(
    r::UnitRange{Int},
    ::Type{T},
) where {T<:AbstractFloat}
    p = precision(T)
    t_min = exponent(floatmin(T)) - (p - 1)
    t_max = exponent(floatmax(T))
    return max(r.start, t_min):min(r.stop, t_max)
end

@inline _lemma_range_t(i::Int, ::Type{T}) where {T<:AbstractFloat} =
    _lemma_range_t(i:i, T)


const _SETZRange = Tuple{_BoolRange,_IntRange,_IntRange}


function add_case!(
    lemma::_LemmaOutputs{SETZAbstraction,T},
    (sr_range, er_range, fr_range)::_SETZRange,
    e::SETZAbstraction,
) where {T<:AbstractFloat}
    p = precision(T)
    for sr in _lemma_range_s(sr_range)
        for er in _lemma_range_e(er_range, T)
            for fr in _lemma_range_t(fr_range, T)
                r = SETZAbstraction(sr, er, (p - 1) - (er - fr))
                push!(lemma.claimed_outputs, (r, e))
            end
        end
    end
    return lemma
end


function add_case!(
    lemma::_LemmaOutputs{SETZAbstraction,T},
    (sr_range, er_range, fr_range)::_SETZRange,
    (se_range, ee_range, fe_range)::_SETZRange,
) where {T<:AbstractFloat}
    p = precision(T)
    for sr in _lemma_range_s(sr_range)
        for er in _lemma_range_e(er_range, T)
            for fr in _lemma_range_t(fr_range, T)
                for se in _lemma_range_s(se_range)
                    for ee in _lemma_range_e(ee_range, T)
                        for fe in _lemma_range_t(fe_range, T)
                            r = SETZAbstraction(sr, er, (p - 1) - (er - fr))
                            e = SETZAbstraction(se, ee, (p - 1) - (ee - fe))
                            push!(lemma.claimed_outputs, (r, e))
                        end
                    end
                end
            end
        end
    end
    return lemma
end


@inline _to_range(n::Int) = n:n
@inline _to_range(r::UnitRange{Int}) = r


struct SELBTZRange
    s_range::UnitRange{Bool}
    lb_range::UnitRange{Bool}
    e_range::UnitRange{Int}
    f_range::UnitRange{Int}
    g_range::UnitRange{Int}
end


@inline function SELBTZRange(
    s::Bool,
    lb::Int,
    e::_IntRange,
    f::_IntRange,
    g::_IntRange,
)
    if !(iszero(lb) | isone(lb))
        throw(DomainError(lb, "Leading bit must be 0 or 1."))
    end
    return SELBTZRange(s:s, Bool(lb):Bool(lb),
        _to_range(e), _to_range(f), _to_range(g))
end


function add_case!(
    lemma::_LemmaOutputs{SELBTZAbstraction,T},
    r::SELBTZRange,
    e::SELBTZAbstraction,
) where {T<:AbstractFloat}
    p = precision(T)
    for sr in r.s_range
        for lbr in r.lb_range
            for er in _lemma_range_e(r.e_range, T)
                for fr in r.f_range
                    for gr in _lemma_range_t(r.g_range, T)
                        nlbr = (er - fr) - 1
                        ntzr = (p - 1) - (er - gr)
                        push!(lemma.claimed_outputs, (
                            SELBTZAbstraction(sr, lbr, er, nlbr, ntzr), e))
                    end
                end
            end
        end
    end
    return lemma
end


function add_case!(
    lemma::_LemmaOutputs{SELBTZAbstraction,T},
    r::SELBTZRange,
    e::SELBTZRange,
) where {T<:AbstractFloat}
    p = precision(T)
    for sr in r.s_range
        for lbr in r.lb_range
            for er in _lemma_range_e(r.e_range, T)
                for fr in r.f_range
                    for gr in _lemma_range_t(r.g_range, T)
                        for se in e.s_range
                            for lbe in e.lb_range
                                for ee in _lemma_range_e(e.e_range, T)
                                    for fe in e.f_range
                                        for ge in _lemma_range_t(e.g_range, T)
                                            nlbr = (er - fr) - 1
                                            ntzr = (p - 1) - (er - gr)
                                            nlbe = (ee - fe) - 1
                                            ntze = (p - 1) - (ee - ge)
                                            push!(lemma.claimed_outputs, (
                                                SELBTZAbstraction(sr, lbr, er, nlbr, ntzr),
                                                SELBTZAbstraction(se, lbe, ee, nlbe, ntze)))
                                        end
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
    end
    return lemma
end


struct SELTZORange
    s_range::UnitRange{Bool}
    lb_range::UnitRange{Bool}
    tb_range::UnitRange{Bool}
    e_range::UnitRange{Int}
    f_range::UnitRange{Int}
    g_range::UnitRange{Int}
end


@inline function SELTZORange(
    s::Bool,
    lb::Int,
    tb::Int,
    e::_IntRange,
    f::_IntRange,
    g::_IntRange,
)
    if !(iszero(lb) | isone(lb))
        throw(DomainError(lb, "Leading bit must be 0 or 1."))
    end
    if !(iszero(tb) | isone(tb))
        throw(DomainError(tb, "Trailing bit must be 0 or 1."))
    end
    return SELTZORange(s:s, Bool(lb):Bool(lb), Bool(tb):Bool(tb),
        _to_range(e), _to_range(f), _to_range(g))
end


function add_case!(
    lemma::_LemmaOutputs{SELTZOAbstraction,T},
    r::SELTZORange,
    e::SELTZOAbstraction,
) where {T<:AbstractFloat}
    p = precision(T)
    for sr in r.s_range
        for lbr in r.lb_range
            for tbr in r.tb_range
                for er in _lemma_range_e(r.e_range, T)
                    for fr in r.f_range
                        for gr in _lemma_range_t(r.g_range, T)
                            nlbr = (er - fr) - 1
                            ntbr = (p - 1) - (er - gr)
                            push!(lemma.claimed_outputs, (
                                SELTZOAbstraction(sr, lbr, tbr, er, nlbr, ntbr), e))
                        end
                    end
                end
            end
        end
    end
    return lemma
end


function add_case!(
    lemma::_LemmaOutputs{SELTZOAbstraction,T},
    r::SELTZORange,
    e::SELTZORange,
) where {T<:AbstractFloat}
    p = precision(T)
    for sr in r.s_range
        for lbr in r.lb_range
            for tbr in r.tb_range
                for er in _lemma_range_e(r.e_range, T)
                    for fr in r.f_range
                        for gr in _lemma_range_t(r.g_range, T)
                            for se in e.s_range
                                for lbe in e.lb_range
                                    for tbe in e.tb_range
                                        for ee in _lemma_range_e(e.e_range, T)
                                            for fe in e.f_range
                                                for ge in _lemma_range_t(e.g_range, T)
                                                    nlbr = (er - fr) - 1
                                                    ntbr = (p - 1) - (er - gr)
                                                    nlbe = (ee - fe) - 1
                                                    ntbe = (p - 1) - (ee - ge)
                                                    push!(lemma.claimed_outputs, (
                                                        SELTZOAbstraction(sr, lbr, tbr, er, nlbr, ntbr),
                                                        SELTZOAbstraction(se, lbe, tbe, ee, nlbe, ntbe)))
                                                end
                                            end
                                        end
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
    end
    return lemma
end


################################################################################

end # module FloatAbstractions
