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


export SELTZOType, seltzo_classify,
    ZERO, POW2, ALL1, R0R1, R1R0, ONE0, ONE1, TWO0, TWO1, MM01, MM10,
    G00, G01, G10, G11


@enum SELTZOType begin
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


@inline mantissa_leading_bit(t::SELTZOType) =
    (t == ALL1) | (t == R1R0) | (t == ONE0) | (t == TWO0) |
    (t == MM01) | (t == G10) | (t == G11)


@inline mantissa_trailing_bit(t::SELTZOType) =
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


function enumerate_abstractions(::Type{TwoSumAbstraction{A}}, ::Type{T}) where
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
            s, e = two_sum(x, y)
            if _isnormal(x) & _isnormal(y) & _isnormal(s) & _isnormal(e)
                push!(result, TwoSumAbstraction{A}(x, y, s, e))
            end
        end
        results[chunk_index] = result
    end
    return sort!(collect(union(results...)))
end


function two_prod(x::T, y::T) where {T}
    p = x * y
    e = fma(x, y, -p)
    return (p, e)
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
        k_lo = chunk_size * UInt32(chunk_index - 1)
        k_hi = chunk_size * UInt32(chunk_index) - 0x00000001
        result = Set{TwoProdAbstraction{A}}()
        for k = k_lo:k_hi
            i, j = _deinterleave(k)
            x = reinterpret(T, i)
            y = reinterpret(T, j)
            p, e = two_prod(x, y)
            if _isnormal(x) & _isnormal(y) & _isnormal(p) & _isnormal(e)
                push!(result, TwoProdAbstraction{A}(x, y, p, e))
            end
        end
        results[chunk_index] = result
    end
    return sort!(collect(union(results...)))
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
        Tuple{Bool,SELTZOType,Bool,SELTZOType},
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
    coverage_count::Array{Int,0}
    total_counts::Dict{String,Int}
end


function LemmaChecker(
    eft_abstractions::Vector{E},
    x::A,
    y::A,
    ::Type{T},
    total_counts::Dict{String,Int},
) where {A<:FloatAbstraction,E<:EFTAbstraction{A},T<:AbstractFloat}
    return LemmaChecker{A,E,T}(eft_abstractions, x, y, fill(0), total_counts)
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
            checker.coverage_count[] += 1
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


@inline SELTZORange(s::Bool, lb::Bool, tb::Bool, e::Int, f::Int, g::Int) =
    SELTZORange(s:s, lb:lb, tb:tb, e:e, f:f, g:g)


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
                            r = SELTZOAbstraction(sr, lbr, tbr, er, nlbr, ntbr)
                            push!(lemma.claimed_outputs, (r, e))
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
                                                    r = SELTZOAbstraction(sr, lbr, tbr, er, nlbr, ntbr)
                                                    e = SELTZOAbstraction(se, lbe, tbe, ee, nlbe, ntbe)
                                                    push!(lemma.claimed_outputs, (r, e))
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
    for ds = false:true
        for dlb = false:true
            for dtb = false:true
                for de = -1:+1
                    for dnlb = -1:+1
                        for dntb = -1:+1
                            try
                                nx = SELTZOAbstraction(
                                    xor(s, ds),
                                    xor(lb, dlb),
                                    xor(tb, dtb),
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
    r_max::Int=1,
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


export _deep_eachindex, _deep_getindex


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


export _find_best_seltzo_model, _delete_inconsistent_data!, _seltzo_string


const SELTZO_COEFFICIENT_VECTORS = sort!(
    reshape(collect(Iterators.product(ntuple(_ -> -1:+1, Val{6}())...)), :);
    by=v -> (sum(abs.(v)), -2 .* v .^ 2 .- v))


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
        best_score = 0
        best_model = nothing
        for (c1, c2, c3, c4, c5, c6) in SELTZO_COEFFICIENT_VECTORS
            predicted = input_data * [c1, c2, c3, c4, c5, c6]
            actual = output_data[:, output_index]
            c0 = actual[reference_index] - predicted[reference_index]
            predicted .+= c0
            score = count(predicted .== actual)
            if score > best_score
                best_score = score
                best_model = (c0, c1, c2, c3, c4, c5, c6)
            end
        end
        trial_result = (-best_score, output_index, best_model)
        if isnothing(result) || trial_result < result
            result = trial_result
        end
    end
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


function _seltzo_string((c0, c1, c2, c3, c4, c5, c6)::NTuple{7,Int})
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
        result *= (isempty(result) ? "$c0" : "+$c0")
    elseif c0 < 0
        result *= "-$(-c0)"
    else
        @assert iszero(c0)
    end
    return isempty(result) ? "0" : result
end


################################################################################

end # module FloatAbstractions
