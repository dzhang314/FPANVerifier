module FloatAbstractions

using Base: exponent_bias, exponent_mask, significand_bits, significand_mask,
    uinttype

using SoftFloats: SoftFloat
import SoftFloats: two_sum, two_prod

################################################ FLOATING-POINT BIT MANIPULATION


export unsafe_exponent,
    mantissa_leading_bit, mantissa_trailing_bit,
    mantissa_leading_zeros, mantissa_trailing_zeros,
    mantissa_leading_ones, mantissa_trailing_ones,
    mantissa_leading_bits, mantissa_trailing_bits

const _AnyFloat = Union{AbstractFloat,SoftFloat}
const _BITS_PER_BYTE = div(Sys.WORD_SIZE, sizeof(UInt))


@inline function unsafe_exponent(x::T) where {T<:AbstractFloat}
    exponent_bits = reinterpret(Unsigned, x) & exponent_mask(T)
    return Int(exponent_bits >> significand_bits(T)) - exponent_bias(T)
end

@inline unsafe_exponent(x::SoftFloat) = ifelse(iszero(x), -16383, exponent(x))


@inline mantissa_leading_bit(x::T) where {T<:AbstractFloat} = !iszero(
    (Base.mantissa(x) >> (significand_bits(T) - 1)) & one(uinttype(T)))

@inline mantissa_leading_bit(x::SoftFloat{P}) where {P} = !iszero(
    (Base.mantissa(x) >> (P - 2)) & one(UInt32))


@inline mantissa_trailing_bit(x::_AnyFloat) = isodd(Base.mantissa(x))


@inline function mantissa_leading_zeros(x::T) where {T<:AbstractFloat}
    _shift = _BITS_PER_BYTE * sizeof(T) - significand_bits(T)
    _shifted_mask = significand_mask(T) << _shift
    return leading_zeros((Base.mantissa(x) << _shift) | ~_shifted_mask)
end

@inline mantissa_leading_zeros(x::SoftFloat{P}) where {P} =
    min(leading_zeros(Base.mantissa(x) << (33 - P)), P - 1)


@inline mantissa_trailing_zeros(x::T) where {T<:AbstractFloat} =
    trailing_zeros(Base.mantissa(x) | ~significand_mask(T))

@inline mantissa_trailing_zeros(x::SoftFloat{P}) where {P} =
    min(trailing_zeros(Base.mantissa(x)), P - 1)


@inline function mantissa_leading_ones(x::T) where {T<:AbstractFloat}
    _shift = _BITS_PER_BYTE * sizeof(T) - significand_bits(T)
    return leading_ones(Base.mantissa(x) << _shift)
end

@inline mantissa_leading_ones(x::SoftFloat{P}) where {P} =
    leading_ones(Base.mantissa(x) << (33 - P))


@inline mantissa_trailing_ones(x::T) where {T<:AbstractFloat} =
    trailing_ones(Base.mantissa(x))

@inline mantissa_trailing_ones(x::SoftFloat{P}) where {P} =
    min(trailing_ones(Base.mantissa(x)), P - 1)


@inline mantissa_leading_bits(x::_AnyFloat) = ifelse(mantissa_leading_bit(x),
    mantissa_leading_ones(x), mantissa_leading_zeros(x))


@inline mantissa_trailing_bits(x::_AnyFloat) = ifelse(mantissa_trailing_bit(x),
    mantissa_trailing_ones(x), mantissa_trailing_zeros(x))


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


@inline SEAbstraction(x::_AnyFloat) = SEAbstraction(
    signbit(x), unsafe_exponent(x))


@inline SETZAbstraction(x::_AnyFloat) = SETZAbstraction(
    signbit(x), unsafe_exponent(x), mantissa_trailing_zeros(x))


@inline SELBTZAbstraction(x::_AnyFloat) = SELBTZAbstraction(
    signbit(x), mantissa_leading_bit(x),
    unsafe_exponent(x), mantissa_leading_bits(x), mantissa_trailing_zeros(x))


@inline SELTZOAbstraction(x::_AnyFloat) = SELTZOAbstraction(
    signbit(x), mantissa_leading_bit(x), mantissa_trailing_bit(x),
    unsafe_exponent(x), mantissa_leading_bits(x), mantissa_trailing_bits(x))


@inline TwoSumAbstraction{A}(x::T, y::T, s::T, e::T) where
{A<:FloatAbstraction,T<:_AnyFloat} =
    TwoSumAbstraction{A}(A(x), A(y), A(s), A(e))


@inline TwoProdAbstraction{A}(x::T, y::T, p::T, e::T) where
{A<:FloatAbstraction,T<:_AnyFloat} =
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
) where {T<:_AnyFloat}
    _zero = zero(T)
    pos_zero = SELTZOAbstraction(_zero)
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


export unpack


@inline unpack(x::SEAbstraction) =
    (signbit(x), unsafe_exponent(x))

@inline unpack(x::SEAbstraction, ::Type{T}) where {T<:_AnyFloat} =
    (signbit(x), unsafe_exponent(x))


@inline unpack(x::SETZAbstraction) =
    (signbit(x), unsafe_exponent(x), mantissa_trailing_zeros(x))

@inline function unpack(x::SETZAbstraction, ::Type{T}) where {T<:_AnyFloat}
    p = precision(T)
    s = signbit(x)
    e = unsafe_exponent(x)
    f = e - ((p - 1) - mantissa_trailing_zeros(x))
    return (s, e, f)
end


@inline unpack(x::SELBTZAbstraction) = (
    signbit(x),
    mantissa_leading_bit(x),
    unsafe_exponent(x),
    mantissa_leading_bits(x),
    mantissa_trailing_zeros(x),
)

@inline function unpack(x::SELBTZAbstraction, ::Type{T}) where {T<:_AnyFloat}
    p = precision(T)
    s = signbit(x)
    lb = mantissa_leading_bit(x)
    e = unsafe_exponent(x)
    f = e - (mantissa_leading_bits(x) + 1)
    g = e - ((p - 1) - mantissa_trailing_zeros(x))
    return (s, lb, e, f, g)
end


@inline unpack(x::SELTZOAbstraction) = (
    signbit(x),
    mantissa_leading_bit(x),
    mantissa_trailing_bit(x),
    unsafe_exponent(x),
    mantissa_leading_bits(x),
    mantissa_trailing_bits(x),
)

@inline function unpack(x::SELTZOAbstraction, ::Type{T}) where {T<:_AnyFloat}
    p = precision(T)
    s = signbit(x)
    lb = mantissa_leading_bit(x)
    tb = mantissa_trailing_bit(x)
    e = unsafe_exponent(x)
    f = e - (mantissa_leading_bits(x) + 1)
    g = e - ((p - 1) - mantissa_trailing_bits(x))
    return (s, lb, tb, e, f, g)
end


######################################################### EXHAUSTIVE ENUMERATION


export compute_value_map, two_sum, two_prod,
    two_sum_abstractions, two_prod_abstractions


function compute_value_map(
    ::Type{A},
    ::Type{SoftFloat{P}},
    e_min::Int,
    e_max::Int,
) where {A<:FloatAbstraction,P}
    _pos_zero = zero(SoftFloat{P})
    _neg_zero = -_pos_zero
    result = Dict{A,Vector{SoftFloat{P}}}()
    result[A(_pos_zero)] = [_pos_zero]
    result[A(_neg_zero)] = [_neg_zero]
    for s = false:true
        for e = e_min:e_max
            for m = (1<<(P-1)):((1<<P)-1)
                x = SoftFloat{P}(s, e, m)
                push!(get!(Vector{SoftFloat{P}}, result, A(x)), x)
            end
        end
    end
    return result
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


function two_sum_abstractions(
    value_map::Dict{A,Vector{T}},
    x::A,
    y::A,
) where {A<:FloatAbstraction,T<:_AnyFloat}
    outputs = Set{UInt64}()
    for a in value_map[x]
        for b in value_map[y]
            s, e = two_sum(a, b)
            push!(outputs, (UInt64(A(s).data) << 32) | UInt64(A(e).data))
        end
    end
    return sort!([
        TwoSumAbstraction{A}(x, y, A((w >> 32) % UInt32), A(w % UInt32))
        for w in outputs])
end


function two_prod_abstractions(
    value_map::Dict{A,Vector{T}},
    x::A,
    y::A,
) where {A<:FloatAbstraction,T<:_AnyFloat}
    outputs = Set{UInt64}()
    for a in value_map[x]
        for b in value_map[y]
            p, e = two_prod(a, b)
            push!(outputs, (UInt64(A(p).data) << 32) | UInt64(A(e).data))
        end
    end
    return sort!([
        TwoProdAbstraction{A}(x, y, A((w >> 32) % UInt32), A(w % UInt32))
        for w in outputs])
end


################################################################## OUTPUT LOOKUP


export abstract_outputs


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


################################################################# LEMMA CHECKING


export LemmaChecker, add_case!, SELBTZRange, SELTZORange


struct LemmaChecker{A<:FloatAbstraction,E<:EFTAbstraction{A},T<:_AnyFloat}
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
) where {A<:FloatAbstraction,E<:EFTAbstraction{A},T<:_AnyFloat}
    return LemmaChecker{A,E,T}(
        eft_abstractions, x, y, Set{String}(), total_counts)
end


struct _LemmaOutputs{A<:FloatAbstraction,T<:_AnyFloat}
    claimed_outputs::Vector{Tuple{A,A}}
end


function (checker::LemmaChecker{A,E,T})(
    state_claims!::F,
) where {A<:FloatAbstraction,E<:EFTAbstraction{A},T<:_AnyFloat,F}
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
) where {A<:FloatAbstraction,E<:EFTAbstraction{A},T<:_AnyFloat,F}
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
            error("Claimed outputs of lemma $lemma_name " *
                "do not match actual computed outputs.")
        end
    end
    return nothing
end


function add_case!(
    lemma::_LemmaOutputs{A,T},
    r::A,
    e::A,
) where {A<:FloatAbstraction,T<:_AnyFloat}
    push!(lemma.claimed_outputs, (r, e))
    return lemma
end


const _BoolRange = Union{Bool,UnitRange{Bool}}
const _IntRange = Union{Int,UnitRange{Int}}
const _SERange = Tuple{_BoolRange,_IntRange}
const _SETZRange = Tuple{_BoolRange,_IntRange,_IntRange}


@inline _to_range(x::T) where {T} = x:x
@inline _to_range(r::UnitRange{T}) where {T} = r


function add_case!(
    lemma::_LemmaOutputs{SEAbstraction,T},
    (sr_range, er_range)::_SERange,
    e::SEAbstraction
) where {T<:_AnyFloat}
    for sr in _to_range(sr_range)
        for er in _to_range(er_range)
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
) where {T<:_AnyFloat}
    for sr in _to_range(sr_range)
        for er in _to_range(er_range)
            for se in _to_range(se_range)
                for ee in _to_range(ee_range)
                    r = SEAbstraction(sr, er)
                    e = SEAbstraction(se, ee)
                    push!(lemma.claimed_outputs, (r, e))
                end
            end
        end
    end
    return lemma
end


function add_case!(
    lemma::_LemmaOutputs{SETZAbstraction,T},
    (sr_range, er_range, fr_range)::_SETZRange,
    e::SETZAbstraction,
) where {T<:_AnyFloat}
    p = precision(T)
    for sr in _to_range(sr_range)
        for er in _to_range(er_range)
            for fr in _to_range(fr_range)
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
) where {T<:_AnyFloat}
    p = precision(T)
    for sr in _to_range(sr_range)
        for er in _to_range(er_range)
            for fr in _to_range(fr_range)
                for se in _to_range(se_range)
                    for ee in _to_range(ee_range)
                        for fe in _to_range(fe_range)
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
) where {T<:_AnyFloat}
    p = precision(T)
    for sr in r.s_range
        for lbr in r.lb_range
            for er in r.e_range
                for fr in r.f_range
                    for gr in r.g_range
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
) where {T<:_AnyFloat}
    p = precision(T)
    for sr in r.s_range
        for lbr in r.lb_range
            for er in r.e_range
                for fr in r.f_range
                    for gr in r.g_range
                        for se in e.s_range
                            for lbe in e.lb_range
                                for ee in e.e_range
                                    for fe in e.f_range
                                        for ge in e.g_range
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
) where {T<:_AnyFloat}
    p = precision(T)
    for sr in r.s_range
        for lbr in r.lb_range
            for tbr in r.tb_range
                for er in r.e_range
                    for fr in r.f_range
                        for gr in r.g_range
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
) where {T<:_AnyFloat}
    p = precision(T)
    for sr in r.s_range
        for lbr in r.lb_range
            for tbr in r.tb_range
                for er in r.e_range
                    for fr in r.f_range
                        for gr in r.g_range
                            for se in e.s_range
                                for lbe in e.lb_range
                                    for tbe in e.tb_range
                                        for ee in e.e_range
                                            for fe in e.f_range
                                                for ge in e.g_range
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
