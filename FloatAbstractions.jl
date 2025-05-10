module FloatAbstractions

using Base: uinttype, exponent_bias, exponent_mask,
    significand_bits, significand_mask
using Base.Threads: @threads, nthreads

################################################ FLOATING-POINT BIT MANIPULATION


export unsafe_exponent,
    mantissa_leading_bit, mantissa_leading_bits,
    mantissa_leading_zeros, mantissa_leading_ones,
    mantissa_trailing_bit, mantissa_trailing_bits,
    mantissa_trailing_zeros, mantissa_trailing_ones


const _BITS_PER_BYTE = div(64, sizeof(UInt64))
@assert _BITS_PER_BYTE * sizeof(UInt32) == 32
@assert _BITS_PER_BYTE * sizeof(UInt64) == 64


@inline function unsafe_exponent(x::T) where {T}
    raw_exponent = reinterpret(Unsigned, x) & exponent_mask(T)
    raw_exponent >>= significand_bits(T)
    return Int(raw_exponent) - exponent_bias(T)
end


@inline mantissa_leading_bit(x::T) where {T} = !iszero(
    (reinterpret(Unsigned, x) >> (significand_bits(T) - 1)) & one(uinttype(T)))


@inline function mantissa_leading_zeros(x::T) where {T}
    shift = _BITS_PER_BYTE * sizeof(T) - significand_bits(T)
    shifted_mask = significand_mask(T) << shift
    return leading_zeros((reinterpret(Unsigned, x) << shift) | ~shifted_mask)
end


@inline function mantissa_leading_ones(x::T) where {T}
    shift = _BITS_PER_BYTE * sizeof(T) - significand_bits(T)
    shifted_mask = significand_mask(T) << shift
    return leading_ones((reinterpret(Unsigned, x) << shift) & shifted_mask)
end


@inline mantissa_leading_bits(x::T) where {T} = ifelse(
    mantissa_leading_bit(x),
    mantissa_leading_ones(x),
    mantissa_leading_zeros(x))


@inline mantissa_trailing_bit(x::T) where {T} = !iszero(
    reinterpret(Unsigned, x) & one(uinttype(T)))


@inline function mantissa_trailing_zeros(x::T) where {T}
    return trailing_zeros(reinterpret(Unsigned, x) | ~significand_mask(T))
end


@inline function mantissa_trailing_ones(x::T) where {T}
    return trailing_ones(reinterpret(Unsigned, x) & significand_mask(T))
end


@inline mantissa_trailing_bits(x::T) where {T} = ifelse(
    mantissa_trailing_bit(x),
    mantissa_trailing_ones(x),
    mantissa_trailing_zeros(x))


################################################### ABSTRACTION TYPE DEFINITIONS


export SEAbstraction, SETZAbstraction, SELTZOAbstraction,
    TwoSumAbstraction, TwoProdAbstraction


abstract type FloatAbstraction end


# Our packed FloatAbstraction representation assumes that:
# - The exponent fits into a 15-bit signed integer.
# - The number of mantissa bits fits into a 7-bit unsigned integer.
# This just barely accommodates IEEE quadruple precision (binary128) using
# 1 (sign) + 1 (leading bit) + 1 (trailing bit) + 15 (exponent) +
#     7 (leading bit count) + 7 (trailing bit count) = 32 bits.


struct SEAbstraction <: FloatAbstraction
    data::UInt32
end


struct SETZAbstraction <: FloatAbstraction
    data::UInt32
end


struct SELTZOAbstraction <: FloatAbstraction
    data::UInt32
end


struct TwoSumAbstraction{A<:FloatAbstraction}
    x::A
    y::A
    s::A
    e::A
end


struct TwoProdAbstraction{A<:FloatAbstraction}
    x::A
    y::A
    p::A
    e::A
end


####################################################### ABSTRACTION CONSTRUCTORS


@inline function SEAbstraction(x::AbstractFloat)
    s = signbit(x)
    e = unsafe_exponent(x)
    @assert -16383 <= e <= 16384
    return SEAbstraction((UInt32(s) << 31) | (UInt32(e + 16383) << 14))
end


@inline function SETZAbstraction(x::AbstractFloat)
    s = signbit(x)
    e = unsafe_exponent(x)
    @assert -16383 <= e <= 16384
    tz = mantissa_trailing_zeros(x)
    @assert 0 <= tz <= 127
    return SETZAbstraction(
        (UInt32(s) << 31) | (UInt32(e + 16383) << 14) | UInt32(tz))
end


@inline function SELTZOAbstraction(x::AbstractFloat)
    s = signbit(x)
    lb = mantissa_leading_bit(x)
    tb = mantissa_trailing_bit(x)
    e = unsafe_exponent(x)
    @assert -16383 <= e <= 16384
    nlb = mantissa_leading_bits(x)
    @assert 0 <= nlb <= 127
    ntb = mantissa_trailing_bits(x)
    @assert 0 <= ntb <= 127
    return SELTZOAbstraction(
        (UInt32(s) << 31) | (UInt32(lb) << 30) | (UInt32(tb) << 29) |
        (UInt32(e + 16383) << 14) | UInt32(nlb << 7) | UInt32(ntb))
end


@inline TwoSumAbstraction{A}(x::T, y::T, s::T, e::T) where
{A<:FloatAbstraction,T<:AbstractFloat} =
    TwoSumAbstraction{A}(A(x), A(y), A(s), A(e))


@inline TwoProdAbstraction{A}(x::T, y::T, p::T, e::T) where
{A<:FloatAbstraction,T<:AbstractFloat} =
    TwoProdAbstraction{A}(A(x), A(y), A(p), A(e))


##################################################### ABSTRACTION DATA ACCESSORS


@inline Base.signbit(x::SEAbstraction) = isone(x.data >> 31)
@inline Base.signbit(x::SETZAbstraction) = isone(x.data >> 31)
@inline Base.signbit(x::SELTZOAbstraction) = isone(x.data >> 31)


@inline unsafe_exponent(x::SEAbstraction) =
    Int((x.data >> 14) & 0x00007FFF) - 16383
@inline unsafe_exponent(x::SETZAbstraction) =
    Int((x.data >> 14) & 0x00007FFF) - 16383
@inline unsafe_exponent(x::SELTZOAbstraction) =
    Int((x.data >> 14) & 0x00007FFF) - 16383


@inline mantissa_trailing_zeros(x::SETZAbstraction) = Int(x.data & 0x0000007F)


@inline mantissa_leading_bit(x::SELTZOAbstraction) =
    isone((x.data >> 30) & 0x00000001)
@inline mantissa_trailing_bit(x::SELTZOAbstraction) =
    isone((x.data >> 29) & 0x00000001)
@inline mantissa_leading_bits(x::SELTZOAbstraction) =
    Int((x.data >> 7) & 0x0000007F)
@inline mantissa_trailing_bits(x::SELTZOAbstraction) =
    Int(x.data & 0x0000007F)
@inline mantissa_leading_zeros(x::SELTZOAbstraction) =
    ifelse(mantissa_leading_bit(x), 0, mantissa_leading_bits(x))
@inline mantissa_leading_ones(x::SELTZOAbstraction) =
    ifelse(mantissa_leading_bit(x), mantissa_leading_bits(x), 0)
@inline mantissa_trailing_zeros(x::SELTZOAbstraction) =
    ifelse(mantissa_trailing_bit(x), 0, mantissa_trailing_bits(x))
@inline mantissa_trailing_ones(x::SELTZOAbstraction) =
    ifelse(mantissa_trailing_bit(x), mantissa_trailing_bits(x), 0)


########################################################### ABSTRACTION ORDERING


@inline Base.isless(a::SEAbstraction, b::SEAbstraction) =
    isless(a.data, b.data)
@inline Base.isless(a::SETZAbstraction, b::SETZAbstraction) =
    isless(a.data, b.data)
@inline Base.isless(a::SELTZOAbstraction, b::SELTZOAbstraction) =
    isless(a.data, b.data)


@inline Base.isless(a::TwoSumAbstraction{A}, b::TwoSumAbstraction{A}) where
{A<:FloatAbstraction} = isless((a.x, a.y, a.s, a.e), (b.x, b.y, b.s, b.e))
@inline Base.isless(a::TwoProdAbstraction{A}, b::TwoProdAbstraction{A}) where
{A<:FloatAbstraction} = isless((a.x, a.y, a.p, a.e), (b.x, b.y, b.p, b.e))


######################################################### EXHAUSTIVE ENUMERATION


export float_abstractions, two_sum_abstractions, two_prod_abstractions


@inline _isnormal(x::AbstractFloat) = isfinite(x) & !issubnormal(x)


function float_abstractions(::Type{A}, ::Type{T}) where
{A<:FloatAbstraction,T<:AbstractFloat}
    @assert isbitstype(T)
    @assert sizeof(T) == sizeof(UInt16)
    result = Set{A}()
    for i = typemin(UInt16):typemax(UInt16)
        x = reinterpret(T, i)
        if _isnormal(x)
            push!(result, A(x))
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


function two_sum_abstractions(::Type{A}, ::Type{T}) where
{A<:FloatAbstraction,T<:AbstractFloat}
    @assert isbitstype(T)
    @assert 2 * sizeof(T) == sizeof(UInt32)
    # Run at least 4 chunks per thread.
    n = trailing_zeros(nextpow(2, clamp(4 * nthreads(), 4, 65536)))
    chunk_size = (0xFFFFFFFF >> n) + 0x00000001
    results = Vector{Set{TwoSumAbstraction{A}}}(undef, 1 << n)
    @threads :dynamic for chunk_index = 1:(1<<n)
        k_lo = chunk_size * UInt32(chunk_index - 1)
        k_hi = chunk_size * UInt32(chunk_index) - 0x00000001
        result = Set{TwoSumAbstraction{A}}()
        for k = k_lo:k_hi
            i, j = _deinterleave(k)
            x = reinterpret(T, i)
            y = reinterpret(T, j)
            s = x + y
            x_prime = s - y
            y_prime = s - x_prime
            x_err = x - x_prime
            y_err = y - y_prime
            e = x_err + y_err
            if _isnormal(x) & _isnormal(y) & _isnormal(s) & _isnormal(e)
                push!(result, TwoSumAbstraction{A}(x, y, s, e))
            end
        end
        results[chunk_index] = result
    end
    return sort!(collect(union(results...)))
end


function two_prod_abstractions(::Type{A}, ::Type{T}) where
{A<:FloatAbstraction,T<:AbstractFloat}
    @assert isbitstype(T)
    @assert 2 * sizeof(T) == sizeof(UInt32)
    # Run at least 4 chunks per thread.
    n = trailing_zeros(nextpow(2, clamp(4 * nthreads(), 4, 65536)))
    chunk_size = (0xFFFFFFFF >> n) + 0x00000001
    results = Vector{Set{TwoProdAbstraction{A}}}(undef, 1 << n)
    @threads :dynamic for chunk_index = 1:(1<<n)
        k_lo = chunk_size * UInt32(chunk_index - 1)
        k_hi = chunk_size * UInt32(chunk_index) - 0x00000001
        result = Set{TwoProdAbstraction{A}}()
        for k = k_lo:k_hi
            i, j = _deinterleave(k)
            x = reinterpret(T, i)
            y = reinterpret(T, j)
            p = x * y
            e = fma(x, y, -p)
            if _isnormal(x) & _isnormal(y) & _isnormal(p) & _isnormal(e)
                push!(result, TwoProdAbstraction{A}(x, y, p, e))
            end
        end
        results[chunk_index] = result
    end
    return sort!(collect(union(results...)))
end


################################################################################

end # module FloatAbstractions
