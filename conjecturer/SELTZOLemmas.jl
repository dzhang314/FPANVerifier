using BFloat16s: BFloat16
using CRC32c: crc32c

push!(LOAD_PATH, @__DIR__)
using FloatAbstractions


const EXIT_INPUT_FILE_MISSING = 1
const EXIT_INPUT_FILE_MALFORMED = 2
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
include("SELTZO-TwoSum-L.jl")
include("SELTZO-TwoSum-T.jl")
@static if (CLASS_X == ZERO) | (CLASS_Y == ZERO)
    include("SELTZO-TwoSum-Z.jl")
elseif CLASS_X == CLASS_Y
    include("SELTZO-TwoSum-$CLASS_X-$CLASS_Y-S.jl")
    include("SELTZO-TwoSum-$CLASS_X-$CLASS_Y-D.jl")
else
    include("SELTZO-TwoSum-$CLASS_X-$CLASS_Y-S.jl")
    include("SELTZO-TwoSum-$CLASS_X-$CLASS_Y-D.jl")
    include("SELTZO-TwoSum-$CLASS_Y-$CLASS_X-S.jl")
    include("SELTZO-TwoSum-$CLASS_Y-$CLASS_X-D.jl")
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
    two_sum_abstractions::Vector{TwoSumAbstraction{SELTZOAbstraction}},
    ::Type{T},
) where {T<:AbstractFloat}

    abstract_inputs = enumerate_abstractions(SELTZOAbstraction, T)
    xs = [x for x in abstract_inputs if seltzo_classify(x, T) == CLASS_X]
    ys = [y for y in abstract_inputs if seltzo_classify(y, T) == CLASS_Y]
    case_counts = Dict{String,Int}()
    unverified_counts = Dict{Tuple{SELTZOClass,SELTZOClass},Int}()
    rs = ReservoirSampler{Tuple{SELTZOAbstraction,SELTZOAbstraction}}(5)

    for x in xs, y in ys
        checker = LemmaChecker(two_sum_abstractions, x, y, T, case_counts)
        @static if (CLASS_X == ZERO) | (CLASS_Y == ZERO)
            check_seltzo_two_sum_lemmas_z!(checker, x, y, T)
        elseif CLASS_X == CLASS_Y
            check_seltzo_two_sum_lemmas_i!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_l!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_t!(checker, x, y, T)
            if signbit(x) == signbit(y)
                check_seltzo_two_sum_lemmas!(checker,
                    VAL_CX, VAL_CY, VAL_SS, x, y, T)
            else
                check_seltzo_two_sum_lemmas!(checker,
                    VAL_CX, VAL_CY, VAL_DS, x, y, T)
            end
        else
            check_seltzo_two_sum_lemmas_i!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_l!(checker, x, y, T)
            check_seltzo_two_sum_lemmas_t!(checker, x, y, T)
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


const SELTZO_TWO_SUM_F16_COUNT = Dict{Tuple{SELTZOClass,SELTZOClass},Int}(
    (ZERO, ZERO) => 4, (ZERO, POW2) => 120, (ZERO, ALL1) => 120,
    (ZERO, R0R1) => 1080, (ZERO, R1R0) => 1080, (ZERO, ONE0) => 960,
    (ZERO, ONE1) => 960, (ZERO, TWO0) => 840, (ZERO, TWO1) => 840,
    (ZERO, MM01) => 840, (ZERO, MM10) => 840, (ZERO, G00) => 2520,
    (ZERO, G01) => 2520, (ZERO, G10) => 2520, (ZERO, G11) => 2520,
    (POW2, ZERO) => 120, (POW2, POW2) => 3598, (POW2, ALL1) => 3002,
    (POW2, R0R1) => 28920, (POW2, R1R0) => 30864, (POW2, ONE0) => 25184,
    (POW2, ONE1) => 27512, (POW2, TWO0) => 22190, (POW2, TWO1) => 24066,
    (POW2, MM01) => 23898, (POW2, MM10) => 22778, (POW2, G00) => 189214,
    (POW2, G01) => 183600, (POW2, G10) => 196522, (POW2, G11) => 187968,
    (ALL1, ZERO) => 120, (ALL1, POW2) => 3002, (ALL1, ALL1) => 2894,
    (ALL1, R0R1) => 25514, (ALL1, R1R0) => 26430, (ALL1, ONE0) => 22866,
    (ALL1, ONE1) => 23592, (ALL1, TWO0) => 20036, (ALL1, TWO1) => 20622,
    (ALL1, MM01) => 20524, (ALL1, MM10) => 19994, (ALL1, G00) => 175932,
    (ALL1, G01) => 171324, (ALL1, G10) => 179824, (ALL1, G11) => 175958,
    (R0R1, ZERO) => 1080, (R0R1, POW2) => 28920, (R0R1, ALL1) => 25530,
    (R0R1, R0R1) => 236698, (R0R1, R1R0) => 248284, (R0R1, ONE0) => 209744,
    (R0R1, ONE1) => 222584, (R0R1, TWO0) => 184360, (R0R1, TWO1) => 194836,
    (R0R1, MM01) => 191946, (R0R1, MM10) => 186462, (R0R1, G00) => 1650354,
    (R0R1, G01) => 1603012, (R0R1, G10) => 1699104, (R0R1, G11) => 1639006,
    (R1R0, ZERO) => 1080, (R1R0, POW2) => 30864, (R1R0, ALL1) => 26448,
    (R1R0, R0R1) => 248284, (R1R0, R1R0) => 264114, (R1R0, ONE0) => 217908,
    (R1R0, ONE1) => 236320, (R1R0, TWO0) => 191870, (R1R0, TWO1) => 206650,
    (R1R0, MM01) => 204274, (R1R0, MM10) => 195506, (R1R0, G00) => 1790482,
    (R1R0, G01) => 1723294, (R1R0, G10) => 1851800, (R1R0, G11) => 1777952,
    (ONE0, ZERO) => 960, (ONE0, POW2) => 25184, (ONE0, ALL1) => 22880,
    (ONE0, R0R1) => 209744, (ONE0, R1R0) => 217908, (ONE0, ONE0) => 187552,
    (ONE0, ONE1) => 194584, (ONE0, TWO0) => 164594, (ONE0, TWO1) => 170330,
    (ONE0, MM01) => 169028, (ONE0, MM10) => 164918, (ONE0, G00) => 1515080,
    (ONE0, G01) => 1478844, (ONE0, G10) => 1575626, (ONE0, G11) => 1541240,
    (ONE1, ZERO) => 960, (ONE1, POW2) => 27512, (ONE1, ALL1) => 23592,
    (ONE1, R0R1) => 222584, (ONE1, R1R0) => 236320, (ONE1, ONE0) => 194584,
    (ONE1, ONE1) => 211900, (ONE1, TWO0) => 171508, (ONE1, TWO1) => 185162,
    (ONE1, MM01) => 183060, (ONE1, MM10) => 175266, (ONE1, G00) => 1543740,
    (ONE1, G01) => 1483242, (ONE1, G10) => 1588472, (ONE1, G11) => 1516096,
    (TWO0, ZERO) => 840, (TWO0, POW2) => 22190, (TWO0, ALL1) => 20048,
    (TWO0, R0R1) => 184360, (TWO0, R1R0) => 191870, (TWO0, ONE0) => 164594,
    (TWO0, ONE1) => 171508, (TWO0, TWO0) => 144906, (TWO0, TWO1) => 150092,
    (TWO0, MM01) => 148568, (TWO0, MM10) => 145086, (TWO0, G00) => 1370130,
    (TWO0, G01) => 1333436, (TWO0, G10) => 1420724, (TWO0, G11) => 1389954,
    (TWO1, ZERO) => 840, (TWO1, POW2) => 24066, (TWO1, ALL1) => 20636,
    (TWO1, R0R1) => 194836, (TWO1, R1R0) => 206650, (TWO1, ONE0) => 170330,
    (TWO1, ONE1) => 185162, (TWO1, TWO0) => 150092, (TWO1, TWO1) => 161978,
    (TWO1, MM01) => 160036, (TWO1, MM10) => 153370, (TWO1, G00) => 1408642,
    (TWO1, G01) => 1345132, (TWO1, G10) => 1442722, (TWO1, G11) => 1366012,
    (MM01, ZERO) => 840, (MM01, POW2) => 23898, (MM01, ALL1) => 20524,
    (MM01, R0R1) => 191946, (MM01, R1R0) => 204274, (MM01, ONE0) => 169028,
    (MM01, ONE1) => 183060, (MM01, TWO0) => 148568, (MM01, TWO1) => 160036,
    (MM01, MM01) => 158086, (MM01, MM10) => 151348, (MM01, G00) => 1449938,
    (MM01, G01) => 1379840, (MM01, G10) => 1494336, (MM01, G11) => 1423572,
    (MM10, ZERO) => 840, (MM10, POW2) => 22778, (MM10, ALL1) => 20006,
    (MM10, R0R1) => 186462, (MM10, R1R0) => 195506, (MM10, ONE0) => 164918,
    (MM10, ONE1) => 175266, (MM10, TWO0) => 145086, (MM10, TWO1) => 153370,
    (MM10, MM01) => 151348, (MM10, MM10) => 147002, (MM10, G00) => 1343632,
    (MM10, G01) => 1304688, (MM10, G10) => 1379058, (MM10, G11) => 1327960,
    (G00, ZERO) => 2520, (G00, POW2) => 189214, (G00, ALL1) => 176044,
    (G00, R0R1) => 1650354, (G00, R1R0) => 1790482, (G00, ONE0) => 1515080,
    (G00, ONE1) => 1543740, (G00, TWO0) => 1370130, (G00, TWO1) => 1408642,
    (G00, MM01) => 1449938, (G00, MM10) => 1343632, (G00, G00) => 12948362,
    (G00, G01) => 12680768, (G00, G10) => 13248914, (G00, G11) => 12835284,
    (G01, ZERO) => 2520, (G01, POW2) => 183600, (G01, ALL1) => 171354,
    (G01, R0R1) => 1603012, (G01, R1R0) => 1723294, (G01, ONE0) => 1478844,
    (G01, ONE1) => 1483242, (G01, TWO0) => 1333436, (G01, TWO1) => 1345132,
    (G01, MM01) => 1379840, (G01, MM10) => 1304688, (G01, G00) => 12680768,
    (G01, G01) => 12391310, (G01, G10) => 13033710, (G01, G11) => 12622398,
    (G10, ZERO) => 2520, (G10, POW2) => 196522, (G10, ALL1) => 179936,
    (G10, R0R1) => 1699104, (G10, R1R0) => 1851800, (G10, ONE0) => 1575626,
    (G10, ONE1) => 1588472, (G10, TWO0) => 1420724, (G10, TWO1) => 1442722,
    (G10, MM01) => 1494336, (G10, MM10) => 1379058, (G10, G00) => 13248914,
    (G10, G01) => 13033710, (G10, G10) => 13756850, (G10, G11) => 13481136,
    (G11, ZERO) => 2520, (G11, POW2) => 187968, (G11, ALL1) => 175988,
    (G11, R0R1) => 1639006, (G11, R1R0) => 1777952, (G11, ONE0) => 1541240,
    (G11, ONE1) => 1516096, (G11, TWO0) => 1389954, (G11, TWO1) => 1366012,
    (G11, MM01) => 1423572, (G11, MM10) => 1327960, (G11, G00) => 12835284,
    (G11, G01) => 12622398, (G11, G10) => 13481136, (G11, G11) => 13164090,
)


const SELTZO_TWO_SUM_F16_CRC = Dict{Tuple{SELTZOClass,SELTZOClass},UInt32}(
    (ZERO, ZERO) => 0x488B0E21, (ZERO, POW2) => 0x0E376E38, (ZERO, ALL1) => 0xCFE5C64A,
    (ZERO, R0R1) => 0x181FBCA3, (ZERO, R1R0) => 0x31912C3D, (ZERO, ONE0) => 0xFA51E0B4,
    (ZERO, ONE1) => 0x7F17598C, (ZERO, TWO0) => 0x22FE8C71, (ZERO, TWO1) => 0xF9997F08,
    (ZERO, MM01) => 0x6BDC22A6, (ZERO, MM10) => 0xB0BBD1DF, (ZERO, G00) => 0xF9EE83B6,
    (ZERO, G01) => 0x50BC18E5, (ZERO, G10) => 0xAEA7C3E1, (ZERO, G11) => 0x07F558B2,
    (POW2, ZERO) => 0xE4E81CB5, (POW2, POW2) => 0x3874A8BC, (POW2, ALL1) => 0xC71DBA95,
    (POW2, R0R1) => 0xC68C9424, (POW2, R1R0) => 0x524C5D83, (POW2, ONE0) => 0x6A4BEBFC,
    (POW2, ONE1) => 0xACECD3E4, (POW2, TWO0) => 0x13A6D73C, (POW2, TWO1) => 0x6BBA6FF6,
    (POW2, MM01) => 0x211CCC1A, (POW2, MM10) => 0x41E57787, (POW2, G00) => 0x78E4D294,
    (POW2, G01) => 0x73C8F3D9, (POW2, G10) => 0xECB272CA, (POW2, G11) => 0xE2561BC8,
    (ALL1, ZERO) => 0x703A87D0, (ALL1, POW2) => 0x3CD7CED5, (ALL1, ALL1) => 0x97B9AB6C,
    (ALL1, R0R1) => 0x61B42DCB, (ALL1, R1R0) => 0xD9989AD8, (ALL1, ONE0) => 0x3B4BC896,
    (ALL1, ONE1) => 0x43242126, (ALL1, TWO0) => 0x78B61E8D, (ALL1, TWO1) => 0x3CCBED99,
    (ALL1, MM01) => 0xD727CB42, (ALL1, MM10) => 0xAEC57FA4, (ALL1, G00) => 0x7FF6E009,
    (ALL1, G01) => 0x61076EA8, (ALL1, G10) => 0xBEABF592, (ALL1, G11) => 0x6054D116,
    (R0R1, ZERO) => 0x43906D41, (R0R1, POW2) => 0xB633B93A, (R0R1, ALL1) => 0x481959A8,
    (R0R1, R0R1) => 0xAEC94493, (R0R1, R1R0) => 0x11633378, (R0R1, ONE0) => 0x4FF0D580,
    (R0R1, ONE1) => 0x6BED5380, (R0R1, TWO0) => 0xFE80EE6B, (R0R1, TWO1) => 0xC842FF29,
    (R0R1, MM01) => 0xFD60DC56, (R0R1, MM10) => 0x6F634A55, (R0R1, G00) => 0xF52094EF,
    (R0R1, G01) => 0x08D25B1F, (R0R1, G10) => 0x32F6F62F, (R0R1, G11) => 0x50557ABB,
    (R1R0, ZERO) => 0x4F49C3E1, (R1R0, POW2) => 0x92B4847A, (R1R0, ALL1) => 0x3C61BDE9,
    (R1R0, R0R1) => 0xE819B883, (R1R0, R1R0) => 0xF6A9B655, (R1R0, ONE0) => 0x1C372501,
    (R1R0, ONE1) => 0xDE6BADA5, (R1R0, TWO0) => 0x87981B6F, (R1R0, TWO1) => 0xFD389F3B,
    (R1R0, MM01) => 0x2243A1F7, (R1R0, MM10) => 0xE305E70D, (R1R0, G00) => 0x78C3075F,
    (R1R0, G01) => 0xEB80FAFF, (R1R0, G10) => 0xB2C875AA, (R1R0, G11) => 0xE9085F23,
    (ONE0, ZERO) => 0x341D9E9A, (ONE0, POW2) => 0x99430FCE, (ONE0, ALL1) => 0xF227A6F8,
    (ONE0, R0R1) => 0xE997AD2E, (ONE0, R1R0) => 0x1C0800F5, (ONE0, ONE0) => 0x3679AFB6,
    (ONE0, ONE1) => 0x7202DBE9, (ONE0, TWO0) => 0x1D4028D4, (ONE0, TWO1) => 0x90849604,
    (ONE0, MM01) => 0x228F5ED7, (ONE0, MM10) => 0xFEDF33BB, (ONE0, G00) => 0xC0EEEEB2,
    (ONE0, G01) => 0xD7C063DE, (ONE0, G10) => 0xAA2EDAC1, (ONE0, G11) => 0x50A3E935,
    (ONE1, ZERO) => 0xDF5004C6, (ONE1, POW2) => 0x8267DD7F, (ONE1, ALL1) => 0x1563818F,
    (ONE1, R0R1) => 0xCEAECFF6, (ONE1, R1R0) => 0xA38F9A80, (ONE1, ONE0) => 0xE4393536,
    (ONE1, ONE1) => 0xF11C4986, (ONE1, TWO0) => 0x96B742DA, (ONE1, TWO1) => 0x0F3E88DC,
    (ONE1, MM01) => 0x78B8F200, (ONE1, MM10) => 0x5495F882, (ONE1, G00) => 0x407EFC0C,
    (ONE1, G01) => 0x25605C6D, (ONE1, G10) => 0x4C59469E, (ONE1, G11) => 0xA5D64BBA,
    (TWO0, ZERO) => 0x6F59769B, (TWO0, POW2) => 0xAADB4204, (TWO0, ALL1) => 0xCBBDB031,
    (TWO0, R0R1) => 0xAD979239, (TWO0, R1R0) => 0xEECD98BA, (TWO0, ONE0) => 0xF2989320,
    (TWO0, ONE1) => 0x05D94755, (TWO0, TWO0) => 0x33F5AB69, (TWO0, TWO1) => 0x71056230,
    (TWO0, MM01) => 0x45523548, (TWO0, MM10) => 0x9FD21BB7, (TWO0, G00) => 0x7C28F011,
    (TWO0, G01) => 0x1253CCB3, (TWO0, G10) => 0x5855B1D7, (TWO0, G11) => 0xFCB5BC0D,
    (TWO1, ZERO) => 0x8DF9A149, (TWO1, POW2) => 0xCCB3F5DA, (TWO1, ALL1) => 0x5194F2EB,
    (TWO1, R0R1) => 0xD39156D4, (TWO1, R1R0) => 0x7D3BDC76, (TWO1, ONE0) => 0x99EFA4C2,
    (TWO1, ONE1) => 0xA47AA16D, (TWO1, TWO0) => 0xAC5A7F9A, (TWO1, TWO1) => 0xC1CAD615,
    (TWO1, MM01) => 0xA0B7FF22, (TWO1, MM10) => 0xA22DE8A5, (TWO1, G00) => 0x8EF24D75,
    (TWO1, G01) => 0x564650B2, (TWO1, G10) => 0x9C3334B8, (TWO1, G11) => 0xB743C20C,
    (MM01, ZERO) => 0xCD9D167A, (MM01, POW2) => 0xC323546F, (MM01, ALL1) => 0xC25ABF01,
    (MM01, R0R1) => 0x8ED83060, (MM01, R1R0) => 0xC9B5EEB8, (MM01, ONE0) => 0x665183A5,
    (MM01, ONE1) => 0x65A6045F, (MM01, TWO0) => 0xFD359D55, (MM01, TWO1) => 0x0711944B,
    (MM01, MM01) => 0xD79135FA, (MM01, MM10) => 0xC02BA7C1, (MM01, G00) => 0xAD4C6807,
    (MM01, G01) => 0xE7058DBA, (MM01, G10) => 0xD142C6A1, (MM01, G11) => 0x17D339E6,
    (MM10, ZERO) => 0x2F3DC1A8, (MM10, POW2) => 0x99CEA90A, (MM10, ALL1) => 0xE59586A8,
    (MM10, R0R1) => 0x1BF76119, (MM10, R1R0) => 0x97B7169F, (MM10, ONE0) => 0xF22FC415,
    (MM10, ONE1) => 0x24A43D66, (MM10, TWO0) => 0x8C1E3058, (MM10, TWO1) => 0xB5028CB1,
    (MM10, MM01) => 0xEEC67850, (MM10, MM10) => 0x92489C0A, (MM10, G00) => 0xF8FF123F,
    (MM10, G01) => 0x0508ACDC, (MM10, G10) => 0xB2F50CB4, (MM10, G11) => 0xA30F8BA6,
    (G00, ZERO) => 0x9E0EB07A, (G00, POW2) => 0xC2B633A2, (G00, ALL1) => 0x733121BB,
    (G00, R0R1) => 0x5DEC9051, (G00, R1R0) => 0x5E2E6ED0, (G00, ONE0) => 0x0F056E26,
    (G00, ONE1) => 0x03155F30, (G00, TWO0) => 0x9FBB345C, (G00, TWO1) => 0x56C88033,
    (G00, MM01) => 0xE0A066B3, (G00, MM10) => 0xEFA24276, (G00, G00) => 0xF511CCBA,
    (G00, G01) => 0x8B9E5988, (G00, G10) => 0xB1367297, (G00, G11) => 0x908A8367,
    (G01, ZERO) => 0x0328D1B4, (G01, POW2) => 0x2FCD4D1F, (G01, ALL1) => 0xFC38C694,
    (G01, R0R1) => 0x87380674, (G01, R1R0) => 0x8FE28D7D, (G01, ONE0) => 0x9514DC64,
    (G01, ONE1) => 0xA36000FF, (G01, TWO0) => 0x1F672C44, (G01, TWO1) => 0x82C40E23,
    (G01, MM01) => 0xC5FAD61D, (G01, MM10) => 0x9D69BC3A, (G01, G00) => 0xF896AC7B,
    (G01, G01) => 0x82917C57, (G01, G10) => 0x7E8AD9D3, (G01, G11) => 0x0731C7A3,
    (G10, ZERO) => 0xA1AE0517, (G10, POW2) => 0x2FF28857, (G10, ALL1) => 0x1BA2E99A,
    (G10, R0R1) => 0x33D88FD3, (G10, R1R0) => 0x49B17154, (G10, ONE0) => 0xAA415C3C,
    (G10, ONE1) => 0x33C1D304, (G10, TWO0) => 0xAFBB25EB, (G10, TWO1) => 0x943B43A3,
    (G10, MM01) => 0xDDD9FC1B, (G10, MM10) => 0x6CC30C8E, (G10, G00) => 0xE3B58F2E,
    (G10, G01) => 0xBE74713D, (G10, G10) => 0xF056D21A, (G10, G11) => 0x42BF9610,
    (G11, ZERO) => 0x3C8864D9, (G11, POW2) => 0x68DA90C1, (G11, ALL1) => 0x15B2B500,
    (G11, R0R1) => 0x704C13C0, (G11, R1R0) => 0x7C2339E0, (G11, ONE0) => 0xDE83C120,
    (G11, ONE1) => 0x098D7940, (G11, TWO0) => 0xB708783F, (G11, TWO1) => 0xD4327879,
    (G11, MM01) => 0x00146C8D, (G11, MM10) => 0xAF2DA49B, (G11, G00) => 0x4ED0BAFB,
    (G11, G01) => 0x963D9374, (G11, G10) => 0x06737381, (G11, G11) => 0xD9089177,
)


const SELTZO_TWO_SUM_BF16_COUNT = Dict{Tuple{SELTZOClass,SELTZOClass},Int}(
    (ZERO, ZERO) => 4, (ZERO, POW2) => 1016, (ZERO, ALL1) => 1016,
    (ZERO, R0R1) => 6096, (ZERO, R1R0) => 6096, (ZERO, ONE0) => 5080,
    (ZERO, ONE1) => 5080, (ZERO, TWO0) => 4064, (ZERO, TWO1) => 4064,
    (ZERO, MM01) => 4064, (ZERO, MM10) => 4064, (ZERO, G00) => 6096,
    (ZERO, G01) => 6096, (ZERO, G10) => 6096, (ZERO, G11) => 6096,
    (POW2, ZERO) => 1016, (POW2, POW2) => 258062, (POW2, ALL1) => 257748,
    (POW2, R0R1) => 1547162, (POW2, R1R0) => 1547828, (POW2, ONE0) => 1289140,
    (POW2, ONE1) => 1289880, (POW2, TWO0) => 1031364, (POW2, TWO1) => 1031892,
    (POW2, MM01) => 1031832, (POW2, MM10) => 1031540, (POW2, G00) => 1696856,
    (POW2, G01) => 1698936, (POW2, G10) => 1708532, (POW2, G11) => 1710276,
    (ALL1, ZERO) => 1016, (ALL1, POW2) => 257748, (ALL1, ALL1) => 257694,
    (ALL1, R0R1) => 1545990, (ALL1, R1R0) => 1546294, (ALL1, ONE0) => 1288372,
    (ALL1, ONE1) => 1288620, (ALL1, TWO0) => 1030706, (ALL1, TWO1) => 1030880,
    (ALL1, MM01) => 1030848, (ALL1, MM10) => 1030714, (ALL1, G00) => 1701132,
    (ALL1, G01) => 1700622, (ALL1, G10) => 1708836, (ALL1, G11) => 1708394,
    (R0R1, ZERO) => 6096, (R0R1, POW2) => 1547162, (R0R1, ALL1) => 1546000,
    (R0R1, R0R1) => 9278136, (R0R1, R1R0) => 9280298, (R0R1, ONE0) => 7731384,
    (R0R1, ONE1) => 7734020, (R0R1, TWO0) => 6185298, (R0R1, TWO1) => 6187190,
    (R0R1, MM01) => 6186486, (R0R1, MM10) => 6185944, (R0R1, G00) => 10260346,
    (R0R1, G01) => 10248536, (R0R1, G10) => 10317344, (R0R1, G11) => 10310734,
    (R1R0, ZERO) => 6096, (R1R0, POW2) => 1547828, (R1R0, ALL1) => 1546306,
    (R1R0, R0R1) => 9280298, (R1R0, R1R0) => 9283704, (R1R0, ONE0) => 7732980,
    (R1R0, ONE1) => 7736790, (R1R0, TWO0) => 6186646, (R1R0, TWO1) => 6189328,
    (R1R0, MM01) => 6188736, (R1R0, MM10) => 6187388, (R1R0, G00) => 10294648,
    (R1R0, G01) => 10301624, (R1R0, G10) => 10358458, (R1R0, G11) => 10358970,
    (ONE0, ZERO) => 5080, (ONE0, POW2) => 1289140, (ONE0, ALL1) => 1288380,
    (ONE0, R0R1) => 7731384, (ONE0, R1R0) => 7732980, (ONE0, ONE0) => 6443022,
    (ONE0, ONE1) => 6444356, (ONE0, TWO0) => 5154476, (ONE0, TWO1) => 5155482,
    (ONE0, MM01) => 5155194, (ONE0, MM10) => 5154624, (ONE0, G00) => 8582950,
    (ONE0, G01) => 8591430, (ONE0, G10) => 8652740, (ONE0, G11) => 8639416,
    (ONE1, ZERO) => 5080, (ONE1, POW2) => 1289880, (ONE1, ALL1) => 1288620,
    (ONE1, R0R1) => 7734020, (ONE1, R1R0) => 7736790, (ONE1, ONE0) => 6444356,
    (ONE1, ONE1) => 6447846, (ONE1, TWO0) => 5155744, (ONE1, TWO1) => 5158134,
    (ONE1, MM01) => 5157648, (ONE1, MM10) => 5156452, (ONE1, G00) => 8545690,
    (ONE1, G01) => 8542742, (ONE1, G10) => 8596590, (ONE1, G11) => 8603348,
    (TWO0, ZERO) => 4064, (TWO0, POW2) => 1031364, (TWO0, ALL1) => 1030712,
    (TWO0, R0R1) => 6185298, (TWO0, R1R0) => 6186646, (TWO0, ONE0) => 5154476,
    (TWO0, ONE1) => 5155744, (TWO0, TWO0) => 4123796, (TWO0, TWO1) => 4124574,
    (TWO0, MM01) => 4124242, (TWO0, MM10) => 4123876, (TWO0, G00) => 6912220,
    (TWO0, G01) => 6908086, (TWO0, G10) => 6946452, (TWO0, G11) => 6940618,
    (TWO1, ZERO) => 4064, (TWO1, POW2) => 1031892, (TWO1, ALL1) => 1030888,
    (TWO1, R0R1) => 6187190, (TWO1, R1R0) => 6189328, (TWO1, ONE0) => 5155482,
    (TWO1, ONE1) => 5158134, (TWO1, TWO0) => 4124574, (TWO1, TWO1) => 4126464,
    (TWO1, MM01) => 4126024, (TWO1, MM10) => 4125134, (TWO1, G00) => 6890414,
    (TWO1, G01) => 6876678, (TWO1, G10) => 6928904, (TWO1, G11) => 6916014,
    (MM01, ZERO) => 4064, (MM01, POW2) => 1031832, (MM01, ALL1) => 1030848,
    (MM01, R0R1) => 6186486, (MM01, R1R0) => 6188736, (MM01, ONE0) => 5155194,
    (MM01, ONE1) => 5157648, (MM01, TWO0) => 4124242, (MM01, TWO1) => 4126024,
    (MM01, MM01) => 4125588, (MM01, MM10) => 4124746, (MM01, G00) => 6921576,
    (MM01, G01) => 6905684, (MM01, G10) => 6950740, (MM01, G11) => 6935288,
    (MM10, ZERO) => 4064, (MM10, POW2) => 1031540, (MM10, ALL1) => 1030720,
    (MM10, R0R1) => 6185944, (MM10, R1R0) => 6187388, (MM10, ONE0) => 5154624,
    (MM10, ONE1) => 5156452, (MM10, TWO0) => 4123876, (MM10, TWO1) => 4125134,
    (MM10, MM01) => 4124746, (MM10, MM10) => 4124364, (MM10, G00) => 6890670,
    (MM10, G01) => 6878450, (MM10, G10) => 6925484, (MM10, G11) => 6920876,
    (G00, ZERO) => 6096, (G00, POW2) => 1696856, (G00, ALL1) => 1701152,
    (G00, R0R1) => 10260346, (G00, R1R0) => 10294648, (G00, ONE0) => 8582950,
    (G00, ONE1) => 8545690, (G00, TWO0) => 6912220, (G00, TWO1) => 6890414,
    (G00, MM01) => 6921576, (G00, MM10) => 6890670, (G00, G00) => 12891372,
    (G00, G01) => 12963532, (G00, G10) => 13052736, (G00, G11) => 13030748,
    (G01, ZERO) => 6096, (G01, POW2) => 1698936, (G01, ALL1) => 1700628,
    (G01, R0R1) => 10248536, (G01, R1R0) => 10301624, (G01, ONE0) => 8591430,
    (G01, ONE1) => 8542742, (G01, TWO0) => 6908086, (G01, TWO1) => 6876678,
    (G01, MM01) => 6905684, (G01, MM10) => 6878450, (G01, G00) => 12963532,
    (G01, G01) => 12912348, (G01, G10) => 13109418, (G01, G11) => 13050112,
    (G10, ZERO) => 6096, (G10, POW2) => 1708532, (G10, ALL1) => 1708856,
    (G10, R0R1) => 10317344, (G10, R1R0) => 10358458, (G10, ONE0) => 8652740,
    (G10, ONE1) => 8596590, (G10, TWO0) => 6946452, (G10, TWO1) => 6928904,
    (G10, MM01) => 6950740, (G10, MM10) => 6925484, (G10, G00) => 13052736,
    (G10, G01) => 13109418, (G10, G10) => 13157836, (G10, G11) => 13192212,
    (G11, ZERO) => 6096, (G11, POW2) => 1710276, (G11, ALL1) => 1708400,
    (G11, R0R1) => 10310734, (G11, R1R0) => 10358970, (G11, ONE0) => 8639416,
    (G11, ONE1) => 8603348, (G11, TWO0) => 6940618, (G11, TWO1) => 6916014,
    (G11, MM01) => 6935288, (G11, MM10) => 6920876, (G11, G00) => 13030748,
    (G11, G01) => 13050112, (G11, G10) => 13192212, (G11, G11) => 13109248,
)


const SELTZO_TWO_SUM_BF16_CRC = Dict{Tuple{SELTZOClass,SELTZOClass},UInt32}(
    (ZERO, ZERO) => 0x881352C7, (ZERO, POW2) => 0x3D22E451, (ZERO, ALL1) => 0xEC0A95D3,
    (ZERO, R0R1) => 0x7F3A90D6, (ZERO, R1R0) => 0x1DF763E6, (ZERO, ONE0) => 0x5682AABB,
    (ZERO, ONE1) => 0x548BA8CA, (ZERO, TWO0) => 0x59160F5E, (ZERO, TWO1) => 0xFEECB2E1,
    (ZERO, MM01) => 0x3BBF9BCB, (ZERO, MM10) => 0x9C452674, (ZERO, G00) => 0xF4210CB9,
    (ZERO, G01) => 0xD59A5DA9, (ZERO, G10) => 0xB757AE99, (ZERO, G11) => 0x96ECFF89,
    (POW2, ZERO) => 0x7C87284F, (POW2, POW2) => 0x8440A843, (POW2, ALL1) => 0x184CBBF5,
    (POW2, R0R1) => 0x290032BC, (POW2, R1R0) => 0xDB14C87D, (POW2, ONE0) => 0xCFC704EF,
    (POW2, ONE1) => 0x3E9FEC03, (POW2, TWO0) => 0x8249EDDC, (POW2, TWO1) => 0x011978C5,
    (POW2, MM01) => 0xE22D2FCD, (POW2, MM10) => 0x17871471, (POW2, G00) => 0xCAD635DC,
    (POW2, G01) => 0x21DE7CF7, (POW2, G10) => 0x8F6BDFE0, (POW2, G11) => 0xB4F78582,
    (ALL1, ZERO) => 0x708D6558, (ALL1, POW2) => 0x0AFF0A0B, (ALL1, ALL1) => 0x07EB93E4,
    (ALL1, R0R1) => 0x0E32C9F8, (ALL1, R1R0) => 0x182EC4AD, (ALL1, ONE0) => 0x3A485DF8,
    (ALL1, ONE1) => 0xBE689442, (ALL1, TWO0) => 0xB4ACA823, (ALL1, TWO1) => 0x73A78B7E,
    (ALL1, MM01) => 0xC274483D, (ALL1, MM10) => 0x91C37E73, (ALL1, G00) => 0x3CF8DD79,
    (ALL1, G01) => 0x20DFA0BE, (ALL1, G10) => 0x652DF300, (ALL1, G11) => 0xE43AD6AD,
    (R0R1, ZERO) => 0x8CC2FAFC, (R0R1, POW2) => 0x0F0D0D1A, (R0R1, ALL1) => 0x66D51709,
    (R0R1, R0R1) => 0xFB2029A2, (R0R1, R1R0) => 0x6AC54301, (R0R1, ONE0) => 0xCE213864,
    (R0R1, ONE1) => 0x2E0A339E, (R0R1, TWO0) => 0x0958D00F, (R0R1, TWO1) => 0x560A1DCC,
    (R0R1, MM01) => 0x174D6DE4, (R0R1, MM10) => 0x65C071BB, (R0R1, G00) => 0xCA6E6444,
    (R0R1, G01) => 0x42C66231, (R0R1, G10) => 0x1FFB6A19, (R0R1, G11) => 0x1F0F465C,
    (R1R0, ZERO) => 0xA3D1F876, (R1R0, POW2) => 0x5F8711E0, (R1R0, ALL1) => 0x4E4C9F1C,
    (R1R0, R0R1) => 0x6048CF03, (R1R0, R1R0) => 0xEEB0F24D, (R1R0, ONE0) => 0x5B7D3707,
    (R1R0, ONE1) => 0xB1229EC2, (R1R0, TWO0) => 0xB120E669, (R1R0, TWO1) => 0x982D61BB,
    (R1R0, MM01) => 0xCC7348B9, (R1R0, MM10) => 0xAECD768F, (R1R0, G00) => 0x228DB7CE,
    (R1R0, G01) => 0x2F8F2B89, (R1R0, G10) => 0x30A7D622, (R1R0, G11) => 0xA485C67B,
    (ONE0, ZERO) => 0xA67C62D8, (ONE0, POW2) => 0xF57D14C7, (ONE0, ALL1) => 0xF9F024AA,
    (ONE0, R0R1) => 0xA235B178, (ONE0, R1R0) => 0x588BBA0D, (ONE0, ONE0) => 0x203DD5E4,
    (ONE0, ONE1) => 0x5A98DCC4, (ONE0, TWO0) => 0x9308499F, (ONE0, TWO1) => 0x992F13AD,
    (ONE0, MM01) => 0x3CF6E6E0, (ONE0, MM10) => 0xD341D4FD, (ONE0, G00) => 0x25ED8CA5,
    (ONE0, G01) => 0xE65AAD57, (ONE0, G10) => 0x78E45D37, (ONE0, G11) => 0x289E503D,
    (ONE1, ZERO) => 0xCC354975, (ONE1, POW2) => 0x15CED992, (ONE1, ALL1) => 0xC2245DE7,
    (ONE1, R0R1) => 0xACBBA706, (ONE1, R1R0) => 0x43BAB925, (ONE1, ONE0) => 0xE96AED24,
    (ONE1, ONE1) => 0xB92EA3BB, (ONE1, TWO0) => 0xF8357141, (ONE1, TWO1) => 0x1A748766,
    (ONE1, MM01) => 0x5F7A14E3, (ONE1, MM10) => 0x4BCDAC1F, (ONE1, G00) => 0x1F4D8138,
    (ONE1, G01) => 0x187A5C10, (ONE1, G10) => 0xB736E3D0, (ONE1, G11) => 0x26A595BA,
    (TWO0, ZERO) => 0xB6E8E5E8, (TWO0, POW2) => 0xA5B5CCBF, (TWO0, ALL1) => 0x00F7A82E,
    (TWO0, R0R1) => 0x2A875455, (TWO0, R1R0) => 0x6343AEFF, (TWO0, ONE0) => 0x1C9D8E00,
    (TWO0, ONE1) => 0x13D47025, (TWO0, TWO0) => 0x4EF6CECE, (TWO0, TWO1) => 0xF53E4D3C,
    (TWO0, MM01) => 0x48EC3499, (TWO0, MM10) => 0x61CB567A, (TWO0, G00) => 0x555D702F,
    (TWO0, G01) => 0xF780E3E5, (TWO0, G10) => 0xD6113A14, (TWO0, G11) => 0xB95F2D7B,
    (TWO1, ZERO) => 0x03F21AEB, (TWO1, POW2) => 0x9A381876, (TWO1, ALL1) => 0xD4DA68E4,
    (TWO1, R0R1) => 0xDA94933F, (TWO1, R1R0) => 0xD2E64699, (TWO1, ONE0) => 0x02F8D5FC,
    (TWO1, ONE1) => 0xA71FCB50, (TWO1, TWO0) => 0x2F2FAC5B, (TWO1, TWO1) => 0x22B76758,
    (TWO1, MM01) => 0x93EFD52A, (TWO1, MM10) => 0x41AF0664, (TWO1, G00) => 0x00AA8575,
    (TWO1, G01) => 0x38F24EEB, (TWO1, G10) => 0x9AC5B708, (TWO1, G11) => 0xDC2FEADA,
    (MM01, ZERO) => 0x26BA9D46, (MM01, POW2) => 0xEAAB63F3, (MM01, ALL1) => 0x32BF3DBF,
    (MM01, R0R1) => 0x951EFEB4, (MM01, R1R0) => 0x57F4510B, (MM01, ONE0) => 0x0AF029A4,
    (MM01, ONE1) => 0x28CC2C80, (MM01, TWO0) => 0x66DA41F1, (MM01, TWO1) => 0x0FFF0278,
    (MM01, MM01) => 0x2E089AC8, (MM01, MM10) => 0x0231AAEF, (MM01, G00) => 0x65BC4DC4,
    (MM01, G01) => 0xA63AE56D, (MM01, G10) => 0xB7916011, (MM01, G11) => 0xCAA3C4C2,
    (MM10, ZERO) => 0x93A06245, (MM10, POW2) => 0xECDAE3DA, (MM10, ALL1) => 0xA94FCEAC,
    (MM10, R0R1) => 0x85421536, (MM10, R1R0) => 0x2DBEC245, (MM10, ONE0) => 0x94C410E5,
    (MM10, ONE1) => 0xD860BCAD, (MM10, TWO0) => 0x7C811B00, (MM10, TWO1) => 0x8B32FF99,
    (MM10, MM01) => 0xEA152A2E, (MM10, MM10) => 0xF11E9FD9, (MM10, G00) => 0x3EA64305,
    (MM10, G01) => 0x6ACAB491, (MM10, G10) => 0x0AE6362F, (MM10, G11) => 0x64116C4A,
    (G00, ZERO) => 0x13E09170, (G00, POW2) => 0x73E21C03, (G00, ALL1) => 0xF5E56EED,
    (G00, R0R1) => 0x648228DF, (G00, R1R0) => 0xAF5F5F85, (G00, ONE0) => 0x65561733,
    (G00, ONE1) => 0x802548CF, (G00, TWO0) => 0x07F52AC4, (G00, TWO1) => 0x45E055A0,
    (G00, MM01) => 0x20B93723, (G00, MM10) => 0xC93B9D84, (G00, G00) => 0x89D034E6,
    (G00, G01) => 0xD62AC59E, (G00, G10) => 0x5E5FA99A, (G00, G11) => 0xE3FB04CD,
    (G01, ZERO) => 0x091190F6, (G01, POW2) => 0x1D74D43A, (G01, ALL1) => 0x42404726,
    (G01, R0R1) => 0x810A1689, (G01, R1R0) => 0x5EEBE525, (G01, ONE0) => 0x944867EA,
    (G01, ONE1) => 0x7FD71B89, (G01, TWO0) => 0xA81D26D2, (G01, TWO1) => 0x5657273B,
    (G01, MM01) => 0xC4738253, (G01, MM10) => 0xECB573AC, (G01, G00) => 0xBE5223CB,
    (G01, G01) => 0x8EEF52C0, (G01, G10) => 0x1A01C563, (G01, G11) => 0xA7F1400D,
    (G10, ZERO) => 0x2602927C, (G10, POW2) => 0x0D6D83CD, (G10, ALL1) => 0x2BCF6245,
    (G10, R0R1) => 0x8C402E8F, (G10, R1R0) => 0x7B274733, (G10, ONE0) => 0x5201F7BC,
    (G10, ONE1) => 0xBD9A5F28, (G10, TWO0) => 0x6E27DAD0, (G10, TWO1) => 0xD2CD8118,
    (G10, MM01) => 0xA5BCEFB9, (G10, MM10) => 0x80998972, (G10, G00) => 0x243D8A68,
    (G10, G01) => 0x6512943D, (G10, G10) => 0x9CE3FF91, (G10, G11) => 0xE8D30231,
    (G11, ZERO) => 0x3CF393FA, (G11, POW2) => 0x6FF98086, (G11, ALL1) => 0xDE16FF61,
    (G11, R0R1) => 0x40661CC3, (G11, R1R0) => 0x073BD7D7, (G11, ONE0) => 0x2047B96F,
    (G11, ONE1) => 0x0C442147, (G11, TWO0) => 0xBD924619, (G11, TWO1) => 0x390CA1D3,
    (G11, MM01) => 0x74580EE2, (G11, MM10) => 0x75798E30, (G11, G00) => 0xC3BCE639,
    (G11, G01) => 0x17FDC9F4, (G11, G10) => 0xDD1D0AAE, (G11, G11) => 0xCB9E19DC,
)


function main(
    ::Type{T},
    expected_count_dict::Dict{Tuple{SELTZOClass,SELTZOClass},Int},
    expected_crc_dict::Dict{Tuple{SELTZOClass,SELTZOClass},UInt32},
) where {T<:AbstractFloat}
    filename = "SELTZO-TwoSum-$T-$CLASS_X-$CLASS_Y.bin"
    if !isfile(filename)
        println(stderr,
            "ERROR: Input file $filename not found." *
            " Run `julia GenerateAbstractionData.jl` to" *
            " generate the input files for this program.")
        exit(EXIT_INPUT_FILE_MISSING)
    end
    expected_count = expected_count_dict[(CLASS_X, CLASS_Y)]
    expected_crc = expected_crc_dict[(CLASS_X, CLASS_Y)]
    valid = (filesize(filename) ==
             expected_count * sizeof(TwoSumAbstraction{SELTZOAbstraction})) &&
            (open(crc32c, filename) == expected_crc)
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
    println("Successfully checked $(filename[1:end-4]) lemmas.")
    flush(stdout)
    return nothing
end


if abspath(PROGRAM_FILE) == @__FILE__
    main(Float16, SELTZO_TWO_SUM_F16_COUNT, SELTZO_TWO_SUM_F16_CRC)
    main(BFloat16, SELTZO_TWO_SUM_BF16_COUNT, SELTZO_TWO_SUM_BF16_CRC)
end
