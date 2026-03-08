using BFloat16s: BFloat16
using CRC32c: crc32c

push!(LOAD_PATH, @__DIR__)
using FloatAbstractions


const EXIT_INPUT_FILE_MISSING = 1
const EXIT_INPUT_FILE_MALFORMED = 2
const EXIT_INVALID_ARGS = 3
const EXIT_INVALID_CLASS = 4


@enum SignCondition SAME_SIGN DIFF_SIGN
include("SELTZO-TwoSum-L.jl")
include("SELTZO-TwoSum-POW2-POW2-S.jl")
include("SELTZO-TwoSum-POW2-POW2-D.jl")
include("SELTZO-TwoSum-ALL1-ALL1-S.jl")
include("SELTZO-TwoSum-ALL1-ALL1-D.jl")
include("SELTZO-TwoSum-POW2-ALL1-S.jl")
include("SELTZO-TwoSum-POW2-ALL1-D.jl")
include("SELTZO-TwoSum-ALL1-POW2-S.jl")
include("SELTZO-TwoSum-ALL1-POW2-D.jl")


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


const SELTZO_CLASS_LIST = """
    Level 0: ZERO, POW2, ALL1
    Level 1: R0R1, R1R0
    Level 2: ONE0, ONE1
    Level 3: TWO0, TWO1, MM01, MM10
    Level 4: G00, G01, G10, G11
"""


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


if length(ARGS) != 2
    println(stderr,
        "Usage: julia $(basename(PROGRAM_FILE)) CLASS_X CLASS_Y\n" *
        "CLASS_X and CLASS_Y must be one of the following SELTZO classes:\n" *
        SELTZO_CLASS_LIST)
    exit(EXIT_INVALID_ARGS)
end

const CLASS_X = parse_seltzo_class(ARGS[1])
const CLASS_Y = parse_seltzo_class(ARGS[2])


function check_seltzo_two_sum_lemmas(
    two_sum_abstractions::Vector{TwoSumAbstraction{SELTZOAbstraction}},
    ::Type{T},
) where {T<:AbstractFloat}

    ± = false:true
    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    neg_zero = SELTZOAbstraction(-zero(T))
    abstract_inputs = enumerate_abstractions(SELTZOAbstraction, T)
    case_counts = Dict{String,Int}()
    unverified_counts = Dict{Tuple{SELTZOClass,SELTZOClass},Int}()
    rs = ReservoirSampler{Tuple{SELTZOAbstraction,SELTZOAbstraction}}(5)

    for x in abstract_inputs, y in abstract_inputs

        cx = seltzo_classify(x, T)
        cy = seltzo_classify(y, T)
        if minmax(cx, cy) != minmax(CLASS_X, CLASS_Y)
            continue
        end

        sx, lbx, tbx, ex, fx, gx = unpack(x, T)
        sy, lby, tby, ey, fy, gy = unpack(y, T)

        same_sign = (sx == sy)
        diff_sign = (sx != sy)
        x_zero = (x == pos_zero) | (x == neg_zero)
        y_zero = (y == pos_zero) | (y == neg_zero)
        checker = LemmaChecker(two_sum_abstractions, x, y, T, case_counts)

        if x_zero | y_zero ################################### ZERO LEMMA FAMILY

            checker("SELTZO-TwoSum-Z1-PP",
                (x == pos_zero) & (y == pos_zero)
            ) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            checker("SELTZO-TwoSum-Z1-PN",
                (x == pos_zero) & (y == neg_zero)
            ) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            checker("SELTZO-TwoSum-Z1-NP",
                (x == neg_zero) & (y == pos_zero)
            ) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            checker("SELTZO-TwoSum-Z1-NN",
                (x == neg_zero) & (y == neg_zero)
            ) do lemma
                add_case!(lemma, neg_zero, pos_zero)
            end

            checker("SELTZO-TwoSum-Z2-X",
                y_zero & !x_zero
            ) do lemma
                add_case!(lemma, x, pos_zero)
            end
            checker("SELTZO-TwoSum-Z2-Y",
                x_zero & !y_zero
            ) do lemma
                add_case!(lemma, y, pos_zero)
            end

        else ############################################ NONZERO LEMMA FAMILIES

            # From this point onward, all lemmas implicitly
            # assume that both addends are nonzero.

            checker("SELTZO-TwoSum-I-X",
                (ex > ey + (p + 1)) |
                ((ex == ey + (p + 1)) & ((cy == POW2) | same_sign | (cx != POW2))) |
                ((ex == ey + p) & (cy == POW2) & (same_sign | (cx != POW2)) & (~tbx))
            ) do lemma
                add_case!(lemma, x, y)
            end
            checker("SELTZO-TwoSum-I-Y",
                (ey > ex + (p + 1)) |
                ((ey == ex + (p + 1)) & ((cx == POW2) | same_sign | (cy != POW2))) |
                ((ey == ex + p) & (cx == POW2) & (same_sign | (cy != POW2)) & (~tby))
            ) do lemma
                add_case!(lemma, y, x)
            end

            check_seltzo_two_sum_lemmas_l!(checker, x, y, T)

            @static if CLASS_X == CLASS_Y
                if same_sign
                    check_seltzo_two_sum_lemmas!(checker,
                        Val{CLASS_X}(), Val{CLASS_Y}(), Val{SAME_SIGN}(),
                        x, y, T)
                end
                if diff_sign
                    check_seltzo_two_sum_lemmas!(checker,
                        Val{CLASS_X}(), Val{CLASS_Y}(), Val{DIFF_SIGN}(),
                        x, y, T)
                end
            else
                if same_sign
                    check_seltzo_two_sum_lemmas!(checker,
                        Val{CLASS_X}(), Val{CLASS_Y}(), Val{SAME_SIGN}(),
                        x, y, T)
                    check_seltzo_two_sum_lemmas!(checker,
                        Val{CLASS_Y}(), Val{CLASS_X}(), Val{SAME_SIGN}(),
                        x, y, T)
                end
                if diff_sign
                    check_seltzo_two_sum_lemmas!(checker,
                        Val{CLASS_X}(), Val{CLASS_Y}(), Val{DIFF_SIGN}(),
                        x, y, T)
                    check_seltzo_two_sum_lemmas!(checker,
                        Val{CLASS_Y}(), Val{CLASS_X}(), Val{DIFF_SIGN}(),
                        x, y, T)
                end
            end

        end

        if isempty(checker.covering_lemmas)
            # println(stderr,
            #     "ERROR: Abstract SELTZO-TwoSum-$T inputs ($x, $y)" *
            #     " are not covered by any lemmas.")
            if !isempty(abstract_outputs(two_sum_abstractions, x, y))
                push!(rs, (x, y))
                if haskey(unverified_counts, (cx, cy))
                    unverified_counts[(cx, cy)] += 1
                else
                    unverified_counts[(cx, cy)] = 1
                end
            end
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
        if endswith(name, "-X")
            mirror_name = name[1:end-2] * "-Y"
            @assert haskey(case_counts, mirror_name)
            @assert case_counts[mirror_name] == n
        elseif endswith(name, "-Y")
            mirror_name = name[1:end-2] * "-X"
            @assert haskey(case_counts, mirror_name)
            @assert case_counts[mirror_name] == n
        end
        println("    $name: $n")
    end

    println("Unverified cases: $(rs.population_size[])")
    #=
    for ((cx, cy), case_count) in sort!(collect(unverified_counts))
        println("    ($cx, $cy): $case_count")
    end
    for i = 1:min(rs.population_size[], length(rs.reservoir))
        println("Unverified case $i:")
        x, y = rs.reservoir[i]
        cx = seltzo_classify(x, T)
        cy = seltzo_classify(y, T)
        sx, lbx, tbx, ex, fx, gx = unpack(x, T)
        sy, lby, tby, ey, fy, gy = unpack(y, T)
        sx_str = sx ? '-' : '+'
        sy_str = sy ? '-' : '+'
        println("    $sx_str$cx: (ex = $ex, fx = $fx, gx = $gx) [$x]")
        println("    $sy_str$cy: (ey = $ey, fy = $fy, gy = $gy) [$y]")
        println("    SELTZO Outputs:")
        output_classes = classified_outputs(two_sum_abstractions, x, y, T)
        for ((ss, cs, se, ce), outputs) in output_classes
            ss_str = ss ? '-' : '+'
            se_str = se ? '-' : '+'
            println("        ($ss_str$cs, $se_str$ce): $(length(outputs))")
        end
    end
    flush(stdout)
    =#

    return nothing
end


function main(
    filename::String,
    expected_count::Int,
    expected_crc::UInt32,
    ::Type{T},
) where {T<:AbstractFloat}
    if !isfile(filename)
        println(stderr,
            "ERROR: Input file $filename not found." *
            " Run `julia GenerateAbstractionData.jl` to" *
            " generate the input files for this program.")
        exit(EXIT_INPUT_FILE_MISSING)
    end
    valid = (filesize(filename) ===
             expected_count * sizeof(TwoSumAbstraction{SELTZOAbstraction})) &&
            (open(crc32c, filename) === expected_crc)
    if !valid
        println(stderr,
            "ERROR: Input file $filename is malformed." *
            " Run `julia GenerateAbstractionData.jl` to" *
            " generate the input files for this program.")
        exit(EXIT_INPUT_FILE_MALFORMED)
    end
    two_sum_abstractions =
        Vector{TwoSumAbstraction{SELTZOAbstraction}}(undef, expected_count)
    read!(filename, two_sum_abstractions)
    check_seltzo_two_sum_lemmas(two_sum_abstractions, T)
    println("Successfully checked all SELTZO-TwoSum-$T lemmas.")
    flush(stdout)
    return nothing
end


if abspath(PROGRAM_FILE) == @__FILE__
    main("SELTZO-TwoSum-Float16.bin", 319_985_950, 0xCC55FA4F, Float16)
    main("SELTZO-TwoSum-BFloat16.bin", 1_172_449_766, 0xCB0D263C, BFloat16)
end
