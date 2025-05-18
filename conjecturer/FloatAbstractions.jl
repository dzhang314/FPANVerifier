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
# 1 (sign) + 1 (leading bit) + 1 (trailing bit) + 15 (exponent) +
#     7 (leading bit count) + 7 (trailing bit count) = 32 bits.


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


####################################################### ABSTRACTION CONSTRUCTORS


@inline function SEAbstraction(s::Bool, e::Int)
    @assert -16383 <= e <= 16384
    return SEAbstraction((UInt32(s) << 31) | (UInt32(e + 16383) << 14))
end


@inline function SETZAbstraction(s::Bool, e::Int, tz::Int)
    @assert -16383 <= e <= 16384
    @assert 0 <= tz <= 127
    return SETZAbstraction(
        (UInt32(s) << 31) | (UInt32(e + 16383) << 14) | UInt32(tz))
end


@inline function SELTZOAbstraction(
    s::Bool, lb::Bool, tb::Bool,
    e::Int, nlb::Int, ntb::Int,
)
    @assert -16383 <= e <= 16384
    @assert 0 <= nlb <= 127
    @assert 0 <= ntb <= 127
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


################################################################## OUTPUT LOOKUP


export abstract_outputs


function abstract_outputs(
    two_sum_abstractions::AbstractVector{TwoSumAbstraction{A}},
    x::A,
    y::A,
) where {A<:FloatAbstraction}
    target = TwoSumAbstraction{A}(x, y, x, y)
    v = view(two_sum_abstractions, searchsorted(two_sum_abstractions, target;
        by=(a -> (a.x, a.y))))
    return [(a.s, a.e) for a in v]
end


function abstract_outputs(
    two_prod_abstractions::AbstractVector{TwoProdAbstraction{A}},
    x::A,
    y::A,
) where {A<:FloatAbstraction}
    target = TwoProdAbstraction{A}(x, y, x, y)
    v = view(two_prod_abstractions, searchsorted(two_prod_abstractions, target;
        by=(a -> (a.x, a.y))))
    return [(a.p, a.e) for a in v]
end


################################################################# LEMMA CHECKING


export LemmaChecker, add_case!


struct LemmaChecker{A<:FloatAbstraction,E<:EFTAbstraction{A},T<:AbstractFloat}
    eft_abstractions::Vector{E}
    x::A
    y::A
    count::Array{Int,0}
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
    lemma_name::String,
    hypothesis::Bool,
) where {A<:FloatAbstraction,E<:EFTAbstraction{A},T<:AbstractFloat}
    if hypothesis
        computed_outputs = abstract_outputs(
            checker.eft_abstractions, checker.x, checker.y)
        lemma = _LemmaOutputs{A,T}(Tuple{A,A}[])
        state_claims!(lemma)
        if computed_outputs == sort!(lemma.claimed_outputs)
            checker.count[] += 1
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
    return nothing
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
end


############################################################### OUTPUT REDUCTION


export unpack, reduced_outputs


@inline unpack(x::SEAbstraction) =
    (signbit(x), unsafe_exponent(x))

@inline unpack(x::SEAbstraction, ::Type{T}) where {T<:AbstractFloat} =
    (signbit(x), unsafe_exponent(x))


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
    @assert all((i == k) || (s[i] == t[i]) for i = 1:n)
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
    # TODO: Handle non-adjacent combinations.
    while true
        found = false
        i = firstindex(v)
        while i < lastindex(v)
            # Try to combine v[i] with v[i+1], v[i+2], ...
            item = v[i]
            j = i + 1
            while j <= lastindex(v)
                next = _combine(item, v[j])
                # Stop when no further combinations are possible.
                if isnothing(next)
                    break
                end
                found = true
                item = next
                j = j + 1
            end
            # At this point, item represents v[i:j-1] combined.
            v[i] = item
            deleteat!(v, i+1:j-1)
            i = j
        end
        # Repeat until no further combinations are found.
        if !found
            return v
        end
    end
end


@generated function _extract_type(x::Tuple, ::Type{T}) where {T}
    result = Expr[]
    for i in eachindex(x.parameters)
        if x.parameters[i] === T
            push!(result, :(x[$i]))
        end
    end
    return Expr(:tuple, result...)
end


function reduced_outputs(
    eft_abstractions::AbstractVector{E},
    x::A,
    y::A,
    ::Type{T},
) where {A<:FloatAbstraction,E<:EFTAbstraction{A},T<:AbstractFloat}
    outputs = [
        (unpack(r, T)..., unpack(e, T)...)
        for (r, e) in abstract_outputs(eft_abstractions, x, y)
    ]
    result = Dict{Tuple,Vector{Tuple}}()
    for output in outputs
        key = _extract_type(output, Bool)
        value = _extract_type(output, Int)
        if haskey(result, key)
            push!(result[key], value)
        else
            result[key] = [value]
        end
    end
    for (_, values) in result
        _combine!(sort!(values))
    end
    return result
end


####################################################### NEIGHBORHOOD EXPLORATION


export compatible_neighbors


function _neighborhood(x::SELTZOAbstraction)
    result = SELTZOAbstraction[]
    s, lb, tb, e, nlb, ntb = unpack(x)
    for ds = false:true
        for dlb = false:true
            for dtb = false:true
                for de = -1:+1
                    for dnlb = -1:+1
                        for dntb = -1:+1
                            push!(result, SELTZOAbstraction(
                                xor(s, ds),
                                xor(lb, dlb),
                                xor(tb, dtb),
                                e + de,
                                nlb + dnlb,
                                ntb + dntb,
                            ))
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
    # return _compatible(x, y.start) & _compatible(x, y.stop)
    return false
end

@inline function _compatible(x::UnitRange{Int}, y::Int)
    # return _compatible(x.start, y) & _compatible(x.stop, y)
    return false
end

@inline function _compatible(x::UnitRange{Int}, y::UnitRange{Int})
    return _compatible(x.start, y.start) & _compatible(x.stop, y.stop)
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

@inline function _compatible(
    x::AbstractVector{T},
    y::AbstractVector{T},
) where {T}
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

@inline function _compatible(x::Dict{K,V}, y::Dict{K,V}) where {K,V}
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
    eft_abstractions::AbstractVector{E},
    x::A,
    y::A,
    ::Type{T};
    r_max::Int=1,
) where {A<:FloatAbstraction,E<:EFTAbstraction{A},T<:AbstractFloat}
    result = Dict{Tuple{A,A},Dict{Tuple,Vector{Tuple}}}()
    stack = Vector{Tuple{A,A,Int}}()
    rejected = Set{Tuple{A,A}}()
    result[(x, y)] = reduced_outputs(eft_abstractions, x, y, T)
    push!(stack, (x, y, 1))
    while !isempty(stack)
        sx, sy, r = popfirst!(stack)
        reference = result[(sx, sy)]
        if r <= r_max
            nsx = _neighborhood(sx)
            nsy = _neighborhood(sy)
            for nx in nsx, ny in nsy
                if !(((nx, ny) in rejected) || haskey(result, (nx, ny)))
                    neighbor = reduced_outputs(eft_abstractions, nx, ny, T)
                    if _compatible(neighbor, reference)
                        result[(nx, ny)] = neighbor
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


################################################################################

end # module FloatAbstractions
