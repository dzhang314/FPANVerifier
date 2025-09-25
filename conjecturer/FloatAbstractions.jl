module FloatAbstractions

using Base: uinttype, exponent_bias, exponent_mask,
    significand_bits, significand_mask
using Base.Threads: @threads, nthreads
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


export FloatAbstraction, SEAbstraction, SETZAbstraction, SELTZOAbstraction,
    EFTAbstraction, TwoSumAbstraction, TwoProdAbstraction


# Our packed FloatAbstraction representation assumes that:
# - The exponent fits into a 15-bit signed integer.
# - The number of mantissa bits fits into a 7-bit unsigned integer.
# This just barely accommodates IEEE quadruple precision (binary128) using
# 1 (sign) + 1 (leading bit) + 1 (trailing bit) + 15 (exponent)
# + 7 (leading bit count) + 7 (trailing bit count) = 32 bits.


abstract type FloatAbstraction end


struct SEAbstraction <: FloatAbstraction
    data::UInt32
end


struct SETZAbstraction <: FloatAbstraction
    data::UInt32
end


struct SELTZOAbstraction <: FloatAbstraction
    data::UInt32
end


@inline Base.isless(a::SEAbstraction, b::SEAbstraction) =
    isless(a.data, b.data)
@inline Base.isless(a::SETZAbstraction, b::SETZAbstraction) =
    isless(a.data, b.data)
@inline Base.isless(a::SELTZOAbstraction, b::SELTZOAbstraction) =
    isless(a.data, b.data)


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
    return SETZAbstraction(
        (UInt32(s) << 31) | (UInt32(e + 16383) << 14) | UInt32(tz))
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
        (UInt32(e + 16383) << 14) | UInt32(nlb << 7) | UInt32(ntb))
end


@inline SEAbstraction(x::AbstractFloat) = SEAbstraction(
    signbit(x), unsafe_exponent(x))


@inline SETZAbstraction(x::AbstractFloat) = SETZAbstraction(
    signbit(x), unsafe_exponent(x), mantissa_trailing_zeros(x))


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
        return ((~lb & ~tb) ? POW2 : (lb & tb) ? ALL1 :
                throw(DomainError(x, "Invalid SELTZOAbstraction.")))
    elseif nlb + ntb == p - 1
        return ((~lb & tb) ? R0R1 : (lb & ~tb) ? R1R0 :
                throw(DomainError(x, "Invalid SELTZOAbstraction.")))
    elseif nlb + ntb == p - 2
        return ((lb & tb) ? ONE0 : (~lb & ~tb) ? ONE1 :
                throw(DomainError(x, "Invalid SELTZOAbstraction.")))
    elseif nlb + ntb == p - 3
        return lb ? (tb ? TWO0 : MM01) : (tb ? MM10 : TWO1)
    elseif 1 < nlb + ntb < p - 3
        return lb ? (tb ? G11 : G10) : (tb ? G01 : G00)
    else
        throw(DomainError(x, "Invalid SELTZOAbstraction."))
    end
end


@inline mantissa_leading_bit(t::SELTZOClass) =
    (t == ALL1) | (t == R1R0) | (t == ONE0) | (t == TWO0) |
    (t == MM01) | (t == G10) | (t == G11)


@inline mantissa_trailing_bit(t::SELTZOClass) =
    (t == ALL1) | (t == R0R1) | (t == ONE0) | (t == TWO0) |
    (t == MM10) | (t == G01) | (t == G11)


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


function enumerate_abstractions(::Type{A}, ::Type{T}) where
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


function enumerate_abstractions(::Type{TwoSumAbstraction{A}}, ::Type{T}) where
{A<:FloatAbstraction,T<:AbstractFloat}
    @assert isbitstype(T)
    @assert 2 * sizeof(T) == sizeof(UInt32)
    # Run at least 4 chunks per thread.
    n = trailing_zeros(nextpow(2, clamp(4 * nthreads(), 4, 65536)))
    chunk_size = (0xFFFFFFFF >> n) + 0x00000001
    results = Vector{Set{TwoSumAbstraction{A}}}(undef, 1 << n)
    @threads :dynamic for chunk_index = 1:(1<<n)
        lo = chunk_size * UInt32(chunk_index - 1)
        hi = chunk_size * UInt32(chunk_index) - 0x00000001
        results[chunk_index] = _chunk(TwoSumAbstraction{A}, T, lo, hi)
    end
    return sort!(collect(union(results...)))
end


function enumerate_abstractions(::Type{TwoProdAbstraction{A}}, ::Type{T}) where
{A<:FloatAbstraction,T<:AbstractFloat}
    @assert isbitstype(T)
    @assert 2 * sizeof(T) == sizeof(UInt32)
    # Run at least 4 chunks per thread.
    n = trailing_zeros(nextpow(2, clamp(4 * nthreads(), 4, 65536)))
    chunk_size = (0xFFFFFFFF >> n) + 0x00000001
    results = Vector{Set{TwoProdAbstraction{A}}}(undef, 1 << n)
    @threads :dynamic for chunk_index = 1:(1<<n)
        lo = chunk_size * UInt32(chunk_index - 1)
        hi = chunk_size * UInt32(chunk_index) - 0x00000001
        results[chunk_index] = _chunk(TwoProdAbstraction{A}, T, lo, hi)
    end
    return sort!(collect(union(results...)))
end


function _merge(
    src1::AbstractString,
    src2::AbstractString,
    dst::AbstractString,
    ::Type{T},
    ::Type{I},
) where {T,I}
    @assert isbitstype(T)
    @assert isbitstype(I)
    @assert sizeof(T) == sizeof(I)
    if iszero(filesize(src1))
        cp(src2, dst)
    elseif iszero(filesize(src2))
        cp(src1, dst)
    else
        open(src1, "r") do f1
            open(src2, "r") do f2
                open(dst, "w") do g
                    while (!eof(f1)) && (!eof(f2))
                        i1 = peek(f1, I)
                        i2 = peek(f2, I)
                        t1 = reinterpret(T, i1)
                        t2 = reinterpret(T, i2)
                        if isless(t1, t2)
                            @assert i1 === read(f1, I)
                            write(g, i1)
                        elseif isless(t2, t1)
                            @assert i2 === read(f2, I)
                            write(g, i2)
                        else
                            @assert i1 === read(f1, I)
                            @assert i2 === read(f2, I)
                            @assert i1 === i2
                            write(g, i1)
                        end
                    end
                    while !eof(f1)
                        write(g, read(f1, I))
                    end
                    while !eof(f2)
                        write(g, read(f2, I))
                    end
                end
            end
        end
    end
    return nothing
end


function enumerate_abstractions(
    ::Type{TwoSumAbstraction{A}},
    ::Type{T},
    filename::AbstractString,
    num_chunks::Int=1024,
) where {A<:FloatAbstraction,T<:AbstractFloat}
    @assert !isfile(filename)
    @assert ispow2(num_chunks)
    n = trailing_zeros(num_chunks)
    chunk_size = (0xFFFFFFFF >> n) + 0x00000001
    mktempdir() do dirpath
        cd(dirpath) do
            @threads :dynamic for chunk_index = 1:(1<<n)
                lo = chunk_size * UInt32(chunk_index - 1)
                hi = chunk_size * UInt32(chunk_index) - 0x00000001
                open("0-$chunk_index.bin", "w") do io
                    write(io, sort!(collect(_chunk(
                        TwoSumAbstraction{A}, T, lo, hi))))
                end
            end
            for m = 1:n
                @threads :dynamic for chunk_index = 1:(1<<(n-m))
                    src1 = "$(m - 1)-$(2 * chunk_index - 1).bin"
                    src2 = "$(m - 1)-$(2 * chunk_index - 0).bin"
                    dst = "$m-$chunk_index.bin"
                    _merge(src1, src2, dst, TwoSumAbstraction{A}, UInt128)
                    rm(src1)
                    rm(src2)
                end
            end
        end
        finalpath = joinpath(dirpath, "$n-1.bin")
        @assert isfile(finalpath)
        mv(finalpath, filename)
    end
    return nothing
end


function enumerate_abstractions(
    ::Type{TwoProdAbstraction{A}},
    ::Type{T},
    filename::AbstractString,
    num_chunks::Int,
) where {A<:FloatAbstraction,T<:AbstractFloat}
    @assert !isfile(filename)
    @assert ispow2(num_chunks)
    n = trailing_zeros(num_chunks)
    chunk_size = (0xFFFFFFFF >> n) + 0x00000001
    mktempdir() do dirpath
        cd(dirpath) do
            @threads :dynamic for chunk_index = 1:(1<<n)
                lo = chunk_size * UInt32(chunk_index - 1)
                hi = chunk_size * UInt32(chunk_index) - 0x00000001
                open("0-$chunk_index.bin", "w") do io
                    write(io, sort!(collect(_chunk(
                        TwoProdAbstraction{A}, T, lo, hi))))
                end
            end
            for m = 1:n
                @threads :dynamic for chunk_index = 1:(1<<(n-m))
                    src1 = "$(m - 1)-$(2 * chunk_index - 1).bin"
                    src2 = "$(m - 1)-$(2 * chunk_index - 0).bin"
                    dst = "$m-$chunk_index.bin"
                    _merge(src1, src2, dst, TwoProdAbstraction{A}, UInt128)
                    rm(src1)
                    rm(src2)
                end
            end
        end
        finalpath = joinpath(dirpath, "$n-1.bin")
        @assert isfile(finalpath)
        mv(finalpath, filename)
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


export LemmaChecker, add_case!, SELTZORange


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
    state_claims!::Function,
) where {A<:FloatAbstraction,E<:EFTAbstraction{A},T<:AbstractFloat}
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
    state_claims!::Function,
    lemma_name::String,
    hypothesis::Bool,
) where {A<:FloatAbstraction,E<:EFTAbstraction{A},T<:AbstractFloat}
    if hypothesis
        computed_outputs = abstract_outputs(
            checker.eft_abstractions, checker.x, checker.y)
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


struct SELTZORange
    s_range::UnitRange{Bool}
    lb_range::UnitRange{Bool}
    tb_range::UnitRange{Bool}
    e_range::UnitRange{Int}
    f_range::UnitRange{Int}
    g_range::UnitRange{Int}
end


@inline _to_range(n::Int) = n:n
@inline _to_range(r::UnitRange{Int}) = r


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
    return SELTZORange(
        s:s,
        Bool(lb):Bool(lb),
        Bool(tb):Bool(tb),
        _to_range(e),
        _to_range(f),
        _to_range(g)
    )
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


############################################################### OUTPUT REDUCTION


@inline _combine(i::Int, j::Int) =
    (i + 1 == j) ? (i:j) :
    (j + 1 == i) ? (j:i) : nothing
@inline _combine(i::Int, r::UnitRange{Int}) =
    (i + 1 == r.start) ? (i:r.stop) :
    (r.stop + 1 == i) ? (r.start:i) : nothing
@inline _combine(r::UnitRange{Int}, j::Int) =
    (r.stop + 1 == j) ? (r.start:j) :
    (j + 1 == r.start) ? (j:r.stop) : nothing
@inline _combine(r::UnitRange{Int}, s::UnitRange{Int}) =
    (r.stop + 1 == s.start) ? (r.start:s.stop) :
    (s.stop + 1 == r.start) ? (s.start:r.stop) : nothing


@inline function _combine(s::Tuple, t::Tuple)
    n = length(s)
    @assert n == length(t)
    # Find a unique index k at which s[k] and t[k] differ.
    k = 0
    for i = 1:n
        if s[i] != t[i]
            if k == 0
                k = i
            else
                # s and t differ at more than one index.
                return nothing
            end
        end
    end
    # If we reach this point, then s and t differ only at index k.
    @assert all(xor(i == k, s[i] == t[i]) for i = 1:n)
    # Attempt to combine s[k] with t[k].
    c = _combine(s[k], t[k])
    if isnothing(c)
        return nothing
    end
    # If successful, replace the combined values.
    result_s = Base.setindex(s, c, k)
    result_t = Base.setindex(t, c, k)
    @assert result_s == result_t
    return result_s
end


@inline function _combine!(v::AbstractVector{<:Tuple})
    while true
        found = false
        i = firstindex(v)
        while i < lastindex(v)
            # Try to combine v[i] with v[i+1], v[i+2], ...
            item = v[i]
            combined_indices = BitSet()
            for j = i+1:lastindex(v)
                next = _combine(item, v[j])
                if !isnothing(next)
                    found = true
                    item = next
                    push!(combined_indices, j)
                end
            end
            v[i] = item
            deleteat!(v, combined_indices)
            i += 1
        end
        if !found
            return v
        end
    end
end


####################################################### NEIGHBORHOOD EXPLORATION


export compatible_neighbors


function _neighborhood(x::SELTZOAbstraction, ::Type{T}) where {T<:AbstractFloat}
    result = SELTZOAbstraction[]
    c = seltzo_classify(x, T)
    s, lb, tb, e, nlb, ntb = unpack(x)
    for de = -1:+1
        for dnlb = -1:+1
            for dntb = -1:+1
                try
                    nx = SELTZOAbstraction(
                        s,
                        lb,
                        tb,
                        e + de,
                        nlb + dnlb,
                        ntb + dntb,
                    )
                    if seltzo_classify(nx, T) == c
                        push!(result, nx)
                    end
                catch exception
                    if !(exception isa DomainError)
                        rethrow()
                    end
                end
            end
        end
    end
    return result
end


@inline function _compatible(x::Int, y::Int)
    return (x == y) | (x == y + 1) | (x + 1 == y)
end

@inline function _compatible(x::Int, y::UnitRange{Int})
    return _compatible(x, y.start) & _compatible(x, y.stop)
end

@inline function _compatible(x::UnitRange{Int}, y::Int)
    return _compatible(x.start, y) & _compatible(x.stop, y)
end

@inline function _compatible(x::AbstractUnitRange, y::AbstractUnitRange)
    return _compatible(first(x), first(y)) & _compatible(last(x), last(y))
end

@inline function _compatible(x::Tuple, y::Tuple)
    if length(x) != length(y)
        return false
    end
    for (a, b) in zip(x, y)
        if !_compatible(a, b)
            return false
        end
    end
    return true
end

@inline function _compatible(x::AbstractVector, y::AbstractVector)
    if axes(x) != axes(y)
        return false
    end
    for i in eachindex(x, y)
        if !_compatible(x[i], y[i])
            return false
        end
    end
    return true
end

@inline function _compatible(x::AbstractDict, y::AbstractDict)
    if keys(x) != keys(y)
        return false
    end
    for k in keys(x)
        if !_compatible(x[k], y[k])
            return false
        end
    end
    return true
end


function compatible_neighbors(
    two_sum_abstractions::AbstractVector{TwoSumAbstraction{SELTZOAbstraction}},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T};
    r_max::Int,
) where {T<:AbstractFloat}
    result = Dict{
        Tuple{SELTZOAbstraction,SELTZOAbstraction},
        Dict{Tuple,Vector{Tuple}}}()
    stack = Vector{Tuple{SELTZOAbstraction,SELTZOAbstraction,Int}}()
    rejected = Set{Tuple{SELTZOAbstraction,SELTZOAbstraction}}()
    result[(x, y)] = classified_outputs(two_sum_abstractions, x, y, T)
    push!(stack, (x, y, 1))
    while !isempty(stack)
        sx, sy, r = popfirst!(stack)
        reference_outputs = result[(sx, sy)]
        if r <= r_max
            nsx = _neighborhood(sx, T)
            nsy = _neighborhood(sy, T)
            for nx in nsx, ny in nsy
                if !(((nx, ny) in rejected) || haskey(result, (nx, ny)))
                    neighbor_outputs = classified_outputs(
                        two_sum_abstractions, nx, ny, T)
                    if _compatible(neighbor_outputs, reference_outputs)
                        result[(nx, ny)] = neighbor_outputs
                        if r < r_max
                            push!(stack, (nx, ny, r + 1))
                        end
                    else
                        push!(rejected, (nx, ny))
                    end
                end
            end
        end
    end
    return result
end


################################################################## DEEP INDEXING


@inline _deep_eachindex(::Integer; prefix::Tuple=()) = Tuple[prefix]

@inline _deep_eachindex(::UnitRange; prefix::Tuple=()) =
    Tuple[(prefix..., :start), (prefix..., :stop)]

function _deep_eachindex(
    collection::Union{Tuple,AbstractVector,AbstractDict};
    prefix::Tuple=(),
)
    result = Tuple[]
    for (index, item) in pairs(collection)
        append!(result, _deep_eachindex(item; prefix=(prefix..., index)))
    end
    return result
end


@inline _deep_getindex(x) = x

@inline _deep_getindex(r::UnitRange, field::Symbol) = getfield(r, field)

@inline _deep_getindex(
    collection::Union{Tuple,AbstractVector},
    index::Integer,
    suffix...,
) = _deep_getindex(collection[index], suffix...)

@inline _deep_getindex(
    dictionary::AbstractDict{K,V},
    key::K,
    suffix...,
) where {K,V} = _deep_getindex(dictionary[key], suffix...)


######################################################## SELTZO LEMMA GENERATION


const SELTZO_COEFFICIENT_VECTORS = NTuple{6,Int}[
    (0, 0, 0, 0, 0, 0),
    (1, 0, 0, 0, 0, 0),
    (0, 1, 0, 0, 0, 0),
    (0, 0, 1, 0, 0, 0),
    (0, 0, 0, 1, 0, 0),
    (0, 0, 0, 0, 1, 0),
    (0, 0, 0, 0, 0, 1),
]


function _find_best_seltzo_model(
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    data::AbstractDict{
        Tuple{SELTZOAbstraction,SELTZOAbstraction},
        Dict{Tuple,Vector{Tuple}}},
    deep_indices::AbstractVector{Tuple},
    ::Type{T},
) where {T<:AbstractFloat}

    @assert haskey(data, (x, y))
    Base.require_one_based_indexing(deep_indices)

    input_data = Matrix{Int}(undef, length(data), 6)
    output_data = Matrix{Int}(undef, length(data), length(deep_indices))

    reference_index = nothing
    for (data_index, ((nx, ny), outputs)) in enumerate(data)
        if (nx == x) & (ny == y)
            reference_index = data_index
        end
        ex, fx, gx = unpack_ints(nx, T)
        @inbounds input_data[data_index, 1] = ex
        @inbounds input_data[data_index, 2] = fx
        @inbounds input_data[data_index, 3] = gx
        ey, fy, gy = unpack_ints(ny, T)
        @inbounds input_data[data_index, 4] = ey
        @inbounds input_data[data_index, 5] = fy
        @inbounds input_data[data_index, 6] = gy
        for (output_index, deep_index) in enumerate(deep_indices)
            output_data[data_index, output_index] =
                _deep_getindex(outputs, deep_index...)
        end
    end
    @assert !isnothing(reference_index)

    result = nothing
    for output_index = 1:length(deep_indices)
        best_score = nothing
        best_model = nothing
        for (c1, c2, c3, c4, c5, c6) in SELTZO_COEFFICIENT_VECTORS
            predicted = input_data * [c1, c2, c3, c4, c5, c6]
            actual = output_data[:, output_index]
            c0 = actual[reference_index] - predicted[reference_index]
            predicted .+= c0
            score = (
                # Score each model by the number of correct predictions.
                # Higher is better, so the count is negated.
                -count(predicted .== actual),
                # Among models with the same number of correct predictions,
                # prefer those with fewer nonzero coefficients.
                count(map(!iszero, (c1, c2, c3, c4, c5, c6))),
                # Among models with the same number nonzero coefficients,
                # prefer those with smaller absolute coefficients.
                sum(abs.((c1, c2, c3, c4, c5, c6))),
                # Finally, prefer models with a smaller constant term.
                abs(c0),
            )
            if isnothing(best_score) || score < best_score
                best_score = score
                best_model = (c0, c1, c2, c3, c4, c5, c6)
            end
        end
        trial_result = (best_score, output_index, best_model)
        if isnothing(result) || trial_result < result
            result = trial_result
        end
    end

    # Discard the score and return only the best model and its output index.
    return result[2] => result[3]
end


function _delete_inconsistent_data!(
    data::AbstractDict{
        Tuple{SELTZOAbstraction,SELTZOAbstraction},
        Dict{Tuple,Vector{Tuple}}},
    deep_index::Tuple,
    (c0, c1, c2, c3, c4, c5, c6)::NTuple{7,Int},
    ::Type{T},
) where {T<:AbstractFloat}
    invalid_keys = Tuple{SELTZOAbstraction,SELTZOAbstraction}[]
    for ((nx, ny), outputs) in data
        ex, fx, gx = unpack_ints(nx, T)
        ey, fy, gy = unpack_ints(ny, T)
        predicted =
            c0 + c1 * ex + c2 * fx + c3 * gx + c4 * ey + c5 * fy + c6 * gy
        actual = _deep_getindex(outputs, deep_index...)
        if predicted != actual
            push!(invalid_keys, (nx, ny))
        end
    end
    for key in invalid_keys
        delete!(data, key)
    end
    return data
end


################################################################################


export SELTZOLemma, check_seltzo_lemma, lemma_inputs


struct SELTZOBound
    coefficients::NTuple{6,Int}
    lower_bound::Int
    upper_bound::Int
end


struct SymbolicSELTZOTuple
    s::Bool
    lb::Bool
    tb::Bool
    e::NTuple{7,Int}
    f::NTuple{7,Int}
    g::NTuple{7,Int}
end


struct SymbolicSELTZOPair
    s::Union{Nothing,SymbolicSELTZOTuple}
    e::Union{Nothing,SymbolicSELTZOTuple}
end


struct SELTZOLemma
    sxy::Bool # false -> same_sign, true -> diff_sign
    cx::SELTZOClass
    cy::SELTZOClass
    bounds::Vector{SELTZOBound}
    cases::Vector{SymbolicSELTZOPair}
end


Base.:(==)(a::SELTZOLemma, b::SELTZOLemma) =
    ((a.sxy == b.sxy) & (a.cx == b.cx) & (a.cy == b.cy)) &&
    (a.bounds == b.bounds) && (a.cases == b.cases)


function Base.hash(lemma::SELTZOLemma, h::UInt)
    h = hash(lemma.sxy, h)
    h = hash(lemma.cx, h)
    h = hash(lemma.cy, h)
    h = hash(lemma.bounds, h)
    h = hash(lemma.cases, h)
    return h
end


@inline function _satisfies_bounds(
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    bounds::Vector{SELTZOBound},
    ::Type{T},
) where {T<:AbstractFloat}
    ex, fx, gx = unpack_ints(x, T)
    ey, fy, gy = unpack_ints(y, T)
    for bound in bounds
        c1, c2, c3, c4, c5, c6 = bound.coefficients
        value = c1 * ex + c2 * fx + c3 * gx + c4 * ey + c5 * fy + c6 * gy
        if !(bound.lower_bound <= value <= bound.upper_bound)
            return false
        end
    end
    return true
end


@inline function _evaluate_model(
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    (c0, c1, c2, c3, c4, c5, c6)::NTuple{7,Int},
    ::Type{T},
) where {T<:AbstractFloat}
    ex, fx, gx = unpack_ints(x, T)
    ey, fy, gy = unpack_ints(y, T)
    return c0 + c1 * ex + c2 * fx + c3 * gx + c4 * ey + c5 * fy + c6 * gy
end


function check_seltzo_lemma(
    two_sum_abstractions::AbstractVector{TwoSumAbstraction{SELTZOAbstraction}},
    lemma::SELTZOLemma,
    ::Type{T};
    xs::Union{Nothing,AbstractVector{SELTZOAbstraction}}=nothing,
    ys::Union{Nothing,AbstractVector{SELTZOAbstraction}}=nothing,
) where {T<:AbstractFloat}

    pos_zero = SELTZOAbstraction(+zero(T))
    if isnothing(xs) | isnothing(ys)
        abstract_inputs = enumerate_abstractions(SELTZOAbstraction, T)
        if isnothing(xs)
            xs = filter(x -> seltzo_classify(x, T) == lemma.cx, abstract_inputs)
        end
        if isnothing(ys)
            ys = filter(y -> seltzo_classify(y, T) == lemma.cy, abstract_inputs)
        end
    end

    try
        @threads for x in xs
            sx = signbit(x)
            for y in ys
                sy = signbit(y)
                if xor(sx, sy) == lemma.sxy
                    if _satisfies_bounds(x, y, lemma.bounds, T)
                        checker = _LemmaOutputs{SELTZOAbstraction,T}(
                            Tuple{SELTZOAbstraction,SELTZOAbstraction}[])
                        for case in lemma.cases
                            s_range = if isnothing(case.s)
                                pos_zero
                            else
                                SELTZORange(
                                    xor(sx, case.s.s),
                                    Int(case.s.lb),
                                    Int(case.s.tb),
                                    _evaluate_model(x, y, case.s.e, T),
                                    _evaluate_model(x, y, case.s.f, T),
                                    _evaluate_model(x, y, case.s.g, T),
                                )
                            end
                            e_range = if isnothing(case.e)
                                pos_zero
                            else
                                SELTZORange(
                                    xor(sy, case.e.s),
                                    Int(case.e.lb),
                                    Int(case.e.tb),
                                    _evaluate_model(x, y, case.e.e, T),
                                    _evaluate_model(x, y, case.e.f, T),
                                    _evaluate_model(x, y, case.e.g, T),
                                )
                            end
                            add_case!(checker, s_range, e_range)
                        end
                        actual_outputs = abstract_outputs(
                            two_sum_abstractions, x, y)
                        if actual_outputs != sort!(checker.claimed_outputs)
                            throw(false)
                        end
                    end
                end
            end
        end
    catch exception
        if exception isa CompositeException
            for sub_exception in exception.exceptions
                if sub_exception isa TaskFailedException
                    if sub_exception.task.result isa Bool
                        return sub_exception.task.result
                    elseif sub_exception.task.result isa DomainError
                        return false
                    end
                end
            end
        end
        rethrow()
    end

    return true
end


function lemma_inputs(
    lemma::SELTZOLemma,
    ::Type{T};
    xs::Union{Nothing,AbstractVector{SELTZOAbstraction}}=nothing,
    ys::Union{Nothing,AbstractVector{SELTZOAbstraction}}=nothing,
) where {T<:AbstractFloat}

    if isnothing(xs) | isnothing(ys)
        abstract_inputs = enumerate_abstractions(SELTZOAbstraction, T)
        if isnothing(xs)
            xs = filter(x -> seltzo_classify(x, T) == lemma.cx, abstract_inputs)
        end
        if isnothing(ys)
            ys = filter(y -> seltzo_classify(y, T) == lemma.cy, abstract_inputs)
        end
    end

    result = Tuple{SELTZOAbstraction,SELTZOAbstraction}[]
    for x in xs
        sx = signbit(x)
        for y in ys
            sy = signbit(y)
            if xor(sx, sy) == lemma.sxy
                if _satisfies_bounds(x, y, lemma.bounds, T)
                    push!(result, (x, y))
                end
            end
        end
    end

    return result
end


################################################################################


export find_initial_seltzo_lemma, expand_seltzo_lemma


@inline function _prune_lower_bound(bound::SELTZOBound)
    return SELTZOBound(bound.coefficients, typemin(Int), bound.upper_bound)
end


function _prune_lower_bound(lemma::SELTZOLemma, bound_index::Int)
    @assert bound_index in eachindex(lemma.bounds)
    result = deepcopy(lemma)
    if result.bounds[bound_index].upper_bound == typemax(Int)
        deleteat!(result.bounds, bound_index)
    else
        result.bounds[bound_index] =
            _prune_lower_bound(result.bounds[bound_index])
    end
    return result
end


@inline function _prune_upper_bound(bound::SELTZOBound)
    return SELTZOBound(bound.coefficients, bound.lower_bound, typemax(Int))
end


function _prune_upper_bound(lemma::SELTZOLemma, bound_index::Int)
    @assert bound_index in eachindex(lemma.bounds)
    result = deepcopy(lemma)
    if result.bounds[bound_index].lower_bound == typemin(Int)
        deleteat!(result.bounds, bound_index)
    else
        result.bounds[bound_index] =
            _prune_upper_bound(result.bounds[bound_index])
    end
    return result
end


function _possible_prunings(lemma::SELTZOLemma)
    result = SELTZOLemma[]
    for (bound_index, bound) in pairs(lemma.bounds)
        if bound.lower_bound != typemin(Int)
            push!(result, _prune_lower_bound(lemma, bound_index))
        end
        if bound.upper_bound != typemax(Int)
            push!(result, _prune_upper_bound(lemma, bound_index))
        end
    end
    return result
end


@inline function _weaken_lower_bound(bound::SELTZOBound)
    @assert bound.lower_bound != typemin(Int)
    return SELTZOBound(bound.coefficients,
        bound.lower_bound - 1, bound.upper_bound)
end


function _weaken_lower_bound(lemma::SELTZOLemma, bound_index::Int)
    @assert bound_index in eachindex(lemma.bounds)
    result = deepcopy(lemma)
    result.bounds[bound_index] =
        _weaken_lower_bound(result.bounds[bound_index])
    return result
end


@inline function _weaken_upper_bound(bound::SELTZOBound)
    @assert bound.upper_bound != typemax(Int)
    return SELTZOBound(bound.coefficients,
        bound.lower_bound, bound.upper_bound + 1)
end


function _weaken_upper_bound(lemma::SELTZOLemma, bound_index::Int)
    @assert bound_index in eachindex(lemma.bounds)
    result = deepcopy(lemma)
    result.bounds[bound_index] =
        _weaken_upper_bound(result.bounds[bound_index])
    return result
end


function _possible_strengthenings(lemma::SELTZOLemma)
    result = SELTZOLemma[]
    for (bound_index, bound) in pairs(lemma.bounds)
        if bound.lower_bound != typemin(Int)
            push!(result, _weaken_lower_bound(lemma, bound_index))
        end
        if bound.upper_bound != typemax(Int)
            push!(result, _weaken_upper_bound(lemma, bound_index))
        end
    end
    return result
end


function find_initial_seltzo_lemma(
    two_sum_abstractions::AbstractVector{TwoSumAbstraction{SELTZOAbstraction}},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T};
    r_max::Int,
) where {T<:AbstractFloat}

    data = compatible_neighbors(two_sum_abstractions, x, y, T; r_max)

    deep_indices = only(Set{Vector{Tuple}}(_deep_eachindex.(values(data))))
    models = Dict{Tuple,NTuple{7,Int}}()
    while !isempty(deep_indices)
        output_index, model = _find_best_seltzo_model(
            x, y, data, deep_indices, T)
        models[deep_indices[output_index]] = model
        _delete_inconsistent_data!(data, deep_indices[output_index], model, T)
        deleteat!(deep_indices, output_index)
    end

    deep_indices = only(Set{Vector{Tuple}}(_deep_eachindex.(values(data))))
    models = Dict{Tuple,NTuple{7,Int}}()
    while !isempty(deep_indices)
        output_index, model = _find_best_seltzo_model(
            x, y, data, deep_indices, T)
        models[deep_indices[output_index]] = model
        _delete_inconsistent_data!(data, deep_indices[output_index], model, T)
        deleteat!(deep_indices, output_index)
    end

    cx = seltzo_classify(x, T)
    cy = seltzo_classify(y, T)
    sx, _, _, ex, fx, gx = unpack(x, T)
    sy, _, _, ey, fy, gy = unpack(y, T)

    fx_indeterminate = (cx != POW2) & (cx != ALL1)
    fy_indeterminate = (cy != POW2) & (cy != ALL1)
    gx_indeterminate = (cx == G00) | (cx == G01) | (cx == G10) | (cx == G11)
    gy_indeterminate = (cy == G00) | (cy == G01) | (cy == G10) | (cy == G11)

    lemma_bounds = SELTZOBound[]
    push!(lemma_bounds, SELTZOBound((+1, 0, 0, -1, 0, 0), ex - ey, ex - ey))
    if fx_indeterminate
        push!(lemma_bounds, SELTZOBound((+1, -1, 0, 0, 0, 0), ex - fx, ex - fx))
        push!(lemma_bounds, SELTZOBound((0, +1, 0, -1, 0, 0), fx - ey, fx - ey))
    end
    if gx_indeterminate
        push!(lemma_bounds, SELTZOBound((+1, 0, -1, 0, 0, 0), ex - gx, ex - gx))
        push!(lemma_bounds, SELTZOBound((0, +1, -1, 0, 0, 0), fx - gx, fx - gx))
        push!(lemma_bounds, SELTZOBound((0, 0, +1, -1, 0, 0), gx - ey, gx - ey))
    end
    if fy_indeterminate
        push!(lemma_bounds, SELTZOBound((0, 0, 0, +1, -1, 0), ey - fy, ey - fy))
        push!(lemma_bounds, SELTZOBound((+1, 0, 0, 0, -1, 0), ex - fy, ex - fy))
    end
    if gy_indeterminate
        push!(lemma_bounds, SELTZOBound((0, 0, 0, +1, 0, -1), ey - gy, ey - gy))
        push!(lemma_bounds, SELTZOBound((0, 0, 0, 0, +1, -1), fy - gy, fy - gy))
        push!(lemma_bounds, SELTZOBound((+1, 0, 0, 0, 0, -1), ex - gy, ex - gy))
    end
    if fx_indeterminate & fy_indeterminate
        push!(lemma_bounds, SELTZOBound((0, +1, 0, 0, -1, 0), fx - fy, fx - fy))
    end
    if gx_indeterminate & gy_indeterminate
        push!(lemma_bounds, SELTZOBound((0, 0, +1, 0, 0, -1), gx - gy, gx - gy))
    end

    lemma_cases = SymbolicSELTZOPair[]
    output_classes = unique!(sort!([k[1] for k in keys(models)]))
    for output_class in output_classes
        output_cases = unique!(sort!(
            [k[2] for k in keys(models) if k[1] == output_class]))
        for output_case in output_cases
            (ss, cs, se, ce) = output_class
            s = SymbolicSELTZOTuple(
                xor(ss, signbit(x)),
                mantissa_leading_bit(cs),
                mantissa_trailing_bit(cs),
                models[(output_class, output_case, 1)],
                models[(output_class, output_case, 2)],
                models[(output_class, output_case, 3)],
            )
            e = SymbolicSELTZOTuple(
                xor(se, signbit(y)),
                mantissa_leading_bit(ce),
                mantissa_trailing_bit(ce),
                models[(output_class, output_case, 4)],
                models[(output_class, output_case, 5)],
                models[(output_class, output_case, 6)],
            )
            if s.e == (exponent(floatmin(T)) - 1, 0, 0, 0, 0, 0, 0)
                s = nothing
            end
            if e.e == (exponent(floatmin(T)) - 1, 0, 0, 0, 0, 0, 0)
                e = nothing
            end
            push!(lemma_cases, SymbolicSELTZOPair(s, e))
        end
    end

    return SELTZOLemma(xor(sx, sy), cx, cy, lemma_bounds, lemma_cases)
end


function _same_value(
    abstract_inputs::AbstractVector{Tuple{SELTZOAbstraction,SELTZOAbstraction}},
    bound::SELTZOBound,
    ::Type{T},
) where {T<:AbstractFloat}
    if isempty(abstract_inputs)
        return nothing
    end
    x, y = first(abstract_inputs)
    ex, fx, gx = unpack_ints(x, T)
    ey, fy, gy = unpack_ints(y, T)
    c1, c2, c3, c4, c5, c6 = bound.coefficients
    reference_value = c1 * ex + c2 * fx + c3 * gx + c4 * ey + c5 * fy + c6 * gy
    for (x, y) in abstract_inputs
        ex, fx, gx = unpack_ints(x, T)
        ey, fy, gy = unpack_ints(y, T)
        value = c1 * ex + c2 * fx + c3 * gx + c4 * ey + c5 * fy + c6 * gy
        if value != reference_value
            return nothing
        end
    end
    return reference_value
end


function expand_seltzo_lemma(
    two_sum_abstractions::AbstractVector{TwoSumAbstraction{SELTZOAbstraction}},
    lemma::SELTZOLemma,
    ::Type{T};
    xs::Union{Nothing,AbstractVector{SELTZOAbstraction}}=nothing,
    ys::Union{Nothing,AbstractVector{SELTZOAbstraction}}=nothing
) where {T<:AbstractFloat}

    if isnothing(xs) | isnothing(ys)
        abstract_inputs = enumerate_abstractions(SELTZOAbstraction, T)
        if isnothing(xs)
            xs = filter(x -> seltzo_classify(x, T) == lemma.cx, abstract_inputs)
        end
        if isnothing(ys)
            ys = filter(y -> seltzo_classify(y, T) == lemma.cy, abstract_inputs)
        end
    end

    if !check_seltzo_lemma(two_sum_abstractions, lemma, T; xs, ys)
        return (nothing, nothing)
    end

    result = deepcopy(lemma)

    while true
        found = false
        possible_expansions = shuffle!(vcat(
            _possible_prunings(result),
            _possible_strengthenings(result)))
        for expansion in possible_expansions
            if check_seltzo_lemma(two_sum_abstractions, expansion, T; xs, ys)
                result = expansion
                found = true
                break
            end
        end
        if !found
            break
        end
    end

    input_set = lemma_inputs(result, T; xs, ys)
    for (bound_index, bound) in pairs(result.bounds)
        value = _same_value(input_set, bound, T)
        if !isnothing(value)
            result.bounds[bound_index] =
                SELTZOBound(bound.coefficients, value, value)
        end
    end

    return (result, input_set)
end


################################################################################


export julia_form


const SELTZO_VARIABLE_NAMES = String["ex", "fx", "gx", "ey", "fy", "gy"]
const SELTZO_BOUND_EXPRESSIONS = Dict{Int,String}(
    1 => "1",
    2 => "2",
    3 => "3",
    4 => "4 #= WARNING =#",
    5 => "5 #= WARNING =#",
    6 => "6 #= WARNING =#",
    7 => "7 #= WARNING =#",
    8 => "(p-3)",
    9 => "(p-2)",
    10 => "(p-1)",
    11 => "p",
    12 => "(p+1)",
    13 => "(p+2)",
    14 => "(p+3)",
    15 => "15 #= WARNING =#",
    16 => "16 #= WARNING =#",
    17 => "17 #= WARNING =#",
    18 => "18 #= WARNING =#",
    19 => "19 #= WARNING =#",
    20 => "20 #= WARNING =#",
    21 => "(p+p-1)",
    22 => "22 #= WARNING =#",
    23 => "23 #= WARNING =#",
    24 => "24 #= WARNING =#",
    25 => "25 #= WARNING =#",
)


function julia_form(bound::SELTZOBound)
    result = String[]
    pos_idx = only(findall(==(+1), bound.coefficients))
    neg_idx = only(findall(==(-1), bound.coefficients))
    pos_var = SELTZO_VARIABLE_NAMES[pos_idx]
    neg_var = SELTZO_VARIABLE_NAMES[neg_idx]
    if bound.lower_bound == bound.upper_bound
        bound_val = bound.lower_bound
        if bound_val == 0
            push!(result, "($pos_var == $neg_var)")
        elseif bound_val > 0
            bound_expr = SELTZO_BOUND_EXPRESSIONS[bound_val]
            push!(result, "($pos_var == $neg_var + $bound_expr)")
        elseif bound_val < 0
            bound_expr = SELTZO_BOUND_EXPRESSIONS[-bound_val]
            push!(result, "($pos_var + $bound_expr == $neg_var)")
        end
    else
        if bound.lower_bound != typemin(Int)
            bound_val = bound.lower_bound - 1
            if bound_val == 0
                push!(result, "($pos_var > $neg_var)")
            elseif bound_val > 0
                bound_expr = SELTZO_BOUND_EXPRESSIONS[bound_val]
                push!(result, "($pos_var > $neg_var + $bound_expr)")
            elseif bound_val < 0
                bound_expr = SELTZO_BOUND_EXPRESSIONS[-bound_val]
                push!(result, "($pos_var + $bound_expr > $neg_var)")
            end
        end
        if bound.upper_bound != typemax(Int)
            bound_val = bound.upper_bound + 1
            if bound_val == 0
                push!(result, "($pos_var < $neg_var)")
            elseif bound_val > 0
                bound_expr = SELTZO_BOUND_EXPRESSIONS[bound_val]
                push!(result, "($pos_var < $neg_var + $bound_expr)")
            elseif bound_val < 0
                bound_expr = SELTZO_BOUND_EXPRESSIONS[-bound_val]
                push!(result, "($pos_var + $bound_expr < $neg_var)")
            end
        end
    end
    return result
end


function julia_form((c0, c1, c2, c3, c4, c5, c6)::NTuple{7,Int})
    result = ""
    if c1 == +1
        result *= (isempty(result) ? "ex" : "+ex")
    elseif c1 == -1
        result *= "-ex"
    else
        @assert iszero(c1)
    end
    if c2 == +1
        result *= (isempty(result) ? "fx" : "+fx")
    elseif c2 == -1
        result *= "-fx"
    else
        @assert iszero(c2)
    end
    if c3 == +1
        result *= (isempty(result) ? "gx" : "+gx")
    elseif c3 == -1
        result *= "-gx"
    else
        @assert iszero(c3)
    end
    if c4 == +1
        result *= (isempty(result) ? "ey" : "+ey")
    elseif c4 == -1
        result *= "-ey"
    else
        @assert iszero(c4)
    end
    if c5 == +1
        result *= (isempty(result) ? "fy" : "+fy")
    elseif c5 == -1
        result *= "-fy"
    else
        @assert iszero(c5)
    end
    if c6 == +1
        result *= (isempty(result) ? "gy" : "+gy")
    elseif c6 == -1
        result *= "-gy"
    else
        @assert iszero(c6)
    end
    if c0 > 0
        c0_expr = SELTZO_BOUND_EXPRESSIONS[c0]
        result *= (isempty(result) ? "$c0_expr" : "+$c0_expr")
    elseif c0 < 0
        c0_expr = SELTZO_BOUND_EXPRESSIONS[-c0]
        result *= "-$c0_expr"
    else
        @assert iszero(c0)
    end
    return isempty(result) ? "0" : result
end


function julia_form(t::SymbolicSELTZOTuple, sign_var::AbstractString)
    s_expr = t.s ? ('~' * sign_var) : sign_var
    lb_expr = t.lb ? '1' : '0'
    tb_expr = t.tb ? '1' : '0'
    e_expr = julia_form(t.e)
    f_expr = julia_form(t.f)
    g_expr = julia_form(t.g)
    return "SELTZORange($s_expr, $lb_expr, $tb_expr, $e_expr, $f_expr, $g_expr)"
end


function julia_form(::Nothing, ::AbstractString)
    return "pos_zero"
end


function julia_form(case::SymbolicSELTZOPair)
    s_expr = julia_form(case.s, "sx")
    if isnothing(case.e)
        return "    add_case!(lemma, $s_expr, pos_zero)"
    else
        e_expr = julia_form(case.e, "sy")
        return "    add_case!(lemma, $s_expr, $e_expr)"
    end
end


function julia_form(lemma::SELTZOLemma)
    hypotheses = String[
        lemma.sxy ? "diff_sign" : "same_sign",
        "(cx == $(lemma.cx))",
        "(cy == $(lemma.cy))",
    ]
    for bound in lemma.bounds
        append!(hypotheses, julia_form(bound))
    end
    buffer = IOBuffer()
    lemma_code = "$(lemma.cx)-$(lemma.cy)-$(lemma.sxy ? 'D' : 'S')"
    println(buffer, "checker(\"SELTZO-TwoSum-$lemma_code<#>-X\",")
    println(buffer, "    ", join(hypotheses[1:3], " & ") * " &")
    println(buffer, "    ", join(hypotheses[4:end], " & "))
    println(buffer, ") do lemma")
    for case in lemma.cases
        println(buffer, julia_form(case))
    end
    println(buffer, "end")
    return String(take!(buffer))
end


################################################################################

end # module FloatAbstractions
