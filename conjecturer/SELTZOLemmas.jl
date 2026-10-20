push!(LOAD_PATH, @__DIR__)
using FloatAbstractions
using SoftFloats: SoftFloat


const EXIT_INVALID_ARGS = 3
const EXIT_INVALID_CLASS = 4


const SELTZO_CLASS_LIST = """
    Level 0: ZERO, POW2, ALL1
    Level 1: R0R1, R1R0
    Level 2: ONE0, ONE1
    Level 3: TWO0, TWO1, MM01, MM10
    Level 4: G00, G01, G10, G11
"""


if length(ARGS) != 2
    println(stderr,
        "Usage: julia $(basename(PROGRAM_FILE)) CLASS_X CLASS_Y\n" *
            "CLASS_X and CLASS_Y must be one of the following SELTZO classes:\n" *
            SELTZO_CLASS_LIST)
    exit(EXIT_INVALID_ARGS)
end


function parse_seltzo_class(s::AbstractString)
    if uppercase(s) == "ZERO"
        return ZERO
    elseif uppercase(s) == "POW2"
        return POW2
    elseif uppercase(s) == "ALL1"
        return ALL1
    elseif uppercase(s) == "R0R1"
        return R0R1
    elseif uppercase(s) == "R1R0"
        return R1R0
    elseif uppercase(s) == "ONE0"
        return ONE0
    elseif uppercase(s) == "ONE1"
        return ONE1
    elseif uppercase(s) == "TWO0"
        return TWO0
    elseif uppercase(s) == "TWO1"
        return TWO1
    elseif uppercase(s) == "MM01"
        return MM01
    elseif uppercase(s) == "MM10"
        return MM10
    elseif uppercase(s) == "G00"
        return G00
    elseif uppercase(s) == "G01"
        return G01
    elseif uppercase(s) == "G10"
        return G10
    elseif uppercase(s) == "G11"
        return G11
    else
        println(stderr,
            "ERROR: Unrecognized SELTZO class \"$s\".\n" *
                "Valid SELTZO classes are:\n" * SELTZO_CLASS_LIST)
        exit(EXIT_INVALID_CLASS)
    end
end


const CLASS_X = parse_seltzo_class(ARGS[1])
const CLASS_Y = parse_seltzo_class(ARGS[2])
@enum SignCondition SAME_SIGN DIFF_SIGN


include("SELTZO-TwoSum-I.jl")
include("SELTZO-TwoSum-P.jl")
include("SELTZO-TwoSum-A.jl")
include("SELTZO-TwoSum-E.jl")
include("SELTZO-TwoSum-L.jl")
include("SELTZO-TwoSum-T.jl")
include("SELTZO-TwoSum-U.jl")
include("SELTZO-TwoSum-V.jl")
@static if (CLASS_X == ZERO) | (CLASS_Y == ZERO)
    include("SELTZO-TwoSum-Z.jl")
elseif CLASS_X == CLASS_Y
    include(joinpath("seltzo", "SELTZO-TwoSum-$CLASS_X-$CLASS_Y-S.jl"))
    include(joinpath("seltzo", "SELTZO-TwoSum-$CLASS_X-$CLASS_Y-D.jl"))
else
    include(joinpath("seltzo", "SELTZO-TwoSum-$CLASS_X-$CLASS_Y-S.jl"))
    include(joinpath("seltzo", "SELTZO-TwoSum-$CLASS_X-$CLASS_Y-D.jl"))
    include(joinpath("seltzo", "SELTZO-TwoSum-$CLASS_Y-$CLASS_X-S.jl"))
    include(joinpath("seltzo", "SELTZO-TwoSum-$CLASS_Y-$CLASS_X-D.jl"))
end


struct ReservoirSampler{T}
    reservoir::Vector{T}
    population_size::Array{Int,0}

    @inline ReservoirSampler{T}(k::Int) where {T} =
        new{T}(Vector{T}(undef, k), fill(0))
end


function Base.push!(rs::ReservoirSampler{T}, x::T) where {T}
    rs.population_size[] += 1
    if rs.population_size[] <= length(rs.reservoir)
        rs.reservoir[rs.population_size[]] = x
    else
        i = rand(1:rs.population_size[])
        if i <= length(rs.reservoir)
            rs.reservoir[i] = x
        end
    end
    return rs
end


const VAL_CX = Val{CLASS_X}()
const VAL_CY = Val{CLASS_Y}()
const VAL_SS = Val{SAME_SIGN}()
const VAL_DS = Val{DIFF_SIGN}()


function check_seltzo_two_sum_lemmas(
    value_map::Dict{SELTZOAbstraction,Vector{T}},
) where {T}

    abstract_inputs = sort!(collect(keys(value_map)))
    xs = [x for x in abstract_inputs if seltzo_classify(x, T) == CLASS_X]
    ys = [y for y in abstract_inputs if seltzo_classify(y, T) == CLASS_Y]
    case_counts = Dict{String,Int}()
    rs = ReservoirSampler{Tuple{SELTZOAbstraction,SELTZOAbstraction}}(5)

    for x in xs, y in ys
        checker = LemmaChecker(
            two_sum_abstractions(value_map, x, y), x, y, T, case_counts)
        @static if (CLASS_X == ZERO) | (CLASS_Y == ZERO)
            check_seltzo_two_sum_lemmas_z!(checker, x, y, T)
        elseif CLASS_X == CLASS_Y
            check_seltzo_two_sum_lemmas_i!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_p!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_a!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_e!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_l!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_t!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_u!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_v!(checker, x, y, T)
            if signbit(x) == signbit(y)
                check_seltzo_two_sum_lemmas!(checker,
                    VAL_CX, VAL_CY, VAL_SS, x, y, T)
            else
                check_seltzo_two_sum_lemmas!(checker,
                    VAL_CX, VAL_CY, VAL_DS, x, y, T)
            end
        else
            check_seltzo_two_sum_lemmas_i!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_p!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_a!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_e!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_l!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_t!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_u!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_v!(checker, x, y, T)
            if signbit(x) == signbit(y)
                check_seltzo_two_sum_lemmas!(checker,
                    VAL_CX, VAL_CY, VAL_SS, x, y, T)
                check_seltzo_two_sum_lemmas!(checker,
                    VAL_CY, VAL_CX, VAL_SS, x, y, T)
            else
                check_seltzo_two_sum_lemmas!(checker,
                    VAL_CX, VAL_CY, VAL_DS, x, y, T)
                check_seltzo_two_sum_lemmas!(checker,
                    VAL_CY, VAL_CX, VAL_DS, x, y, T)
            end
        end
        if isempty(checker.covering_lemmas)
            # println(stderr,
            #     "ERROR: Abstract SELTZO-TwoSum-$T inputs ($x, $y)" *
            #     " are not covered by any lemmas.")
            push!(rs, (x, y))
        elseif !isone(length(checker.covering_lemmas))
            println(stderr,
                "WARNING: Abstract SELTZO-TwoSum-$T inputs ($x, $y)" *
                    " are covered by multiple lemmas:")
            for name in checker.covering_lemmas
                println(stderr, "    ", name)
            end
        end
    end

    println("SELTZO-TwoSum-$T lemmas:")
    for (name, n) in sort!(collect(case_counts))
        println("    $name: $n")
    end

    println("Unverified cases: $(rs.population_size[])")

    return nothing
end


function main(::Type{SoftFloat{P}}) where {P}
    value_map = compute_value_map(SELTZOAbstraction, SoftFloat{P}, -2, P)
    check_seltzo_two_sum_lemmas(value_map)
    println("Successfully checked all SELTZO-TwoSum-$CLASS_X-$CLASS_Y " *
        "lemmas at precision $P.")
    flush(stdout)
    return nothing
end


if abspath(PROGRAM_FILE) == @__FILE__
    for P = 8:12
        main(SoftFloat{P})
    end
end
