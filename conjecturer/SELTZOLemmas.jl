using BFloat16s: BFloat16
using CRC32c: crc32c

push!(LOAD_PATH, @__DIR__)
using FloatAbstractions


struct ReservoirSampler{T}
    reservoir::Vector{T}
    count::Array{Int,0}

    @inline ReservoirSampler{T}(k::Int) where {T} =
        new{T}(Vector{T}(undef, k), fill(0))
end


function Base.push!(rs::ReservoirSampler{T}, x::T) where {T}
    rs.count[] += 1
    if rs.count[] <= length(rs.reservoir)
        rs.reservoir[rs.count[]] = x
    else
        i = rand(1:rs.count[])
        if i <= length(rs.reservoir)
            rs.reservoir[i] = x
        end
    end
    return rs
end


function check_seltzo_two_sum_lemmas(
    two_sum_abstractions::Vector{TwoSumAbstraction{SELTZOAbstraction}},
    ::Type{T},
) where {T<:AbstractFloat}

    ± = false:true
    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    neg_zero = SELTZOAbstraction(-zero(T))
    abstract_inputs = enumerate_abstractions(SELTZOAbstraction, T)
    lemma_counts = Dict{String,Int}()
    rs = ReservoirSampler{Tuple{SELTZOAbstraction,SELTZOAbstraction}}(5)

    for x in abstract_inputs, y in abstract_inputs

        sx, lbx, lby, ex, fx, gx = unpack(x, T)
        sy, tbx, tby, ey, fy, gy = unpack(y, T)
        f0x = ex - (mantissa_leading_ones(x) + 1)
        f0y = ey - (mantissa_leading_ones(y) + 1)
        f1x = ex - (mantissa_leading_zeros(x) + 1)
        f1y = ey - (mantissa_leading_zeros(y) + 1)
        g0x = ex - ((p - 1) - mantissa_trailing_ones(x))
        g0y = ey - ((p - 1) - mantissa_trailing_ones(y))
        g1x = ex - ((p - 1) - mantissa_trailing_zeros(x))
        g1y = ey - ((p - 1) - mantissa_trailing_zeros(y))
        same_sign = (sx == sy)
        diff_sign = (sx != sy)
        x_zero = (x == pos_zero) | (x == neg_zero)
        y_zero = (y == pos_zero) | (y == neg_zero)
        checker = LemmaChecker(two_sum_abstractions, x, y, T, lemma_counts)

        #! format: off
        if x_zero | y_zero ############################### LEMMA FAMILY SELTZO-Z

            # Lemmas in Family SELTZO-Z (for "zero")
            # when one or both addends are zero.

            # Lemma SELTZO-Z1: Both addends are zero.
            checker("SELTZO-Z1-PP", (x == pos_zero) & (y == pos_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            checker("SELTZO-Z1-PN", (x == pos_zero) & (y == neg_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            checker("SELTZO-Z1-NP", (x == neg_zero) & (y == pos_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            checker("SELTZO-Z1-NN", (x == neg_zero) & (y == neg_zero)) do lemma
                add_case!(lemma, neg_zero, pos_zero)
            end

            # Lemma SELTZO-Z2: One addend is zero.
            checker("SELTZO-Z2-X", y_zero & !x_zero) do lemma
                add_case!(lemma, x, pos_zero)
            end
            checker("SELTZO-Z2-Y", x_zero & !y_zero) do lemma
                add_case!(lemma, y, pos_zero)
            end

        else ############################################ NONZERO LEMMA FAMILIES

            # From this point onward, all lemmas implicitly
            # assume that both addends are nonzero.

            ##################################################### LEMMA SELTZO-I

            # Lemmas in Family SELTZO-I (for "identical") apply
            # to addends unchanged by the TwoSum algorithm.

            checker("SELTZO-I-X",
                (ex > ey + (p+1)) |
                ((ex == ey + (p+1)) & ((ey == g1y) | same_sign | (ex > g1x))) |
                ((ex == ey + p) & (ey == g1y) & (same_sign | (ex > g1x)) & (ex < g1x + (p-1)))
            ) do lemma
                add_case!(lemma, x, y)
            end
            checker("SELTZO-I-Y",
                (ey > ex + (p+1)) |
                ((ey == ex + (p+1)) & ((ex == g1x) | same_sign | (ey > g1y))) |
                ((ey == ex + p) & (ex == g1x) & (same_sign | (ey > g1y)) & (ey < g1y + (p-1)))
            ) do lemma
                add_case!(lemma, y, x)
            end

        end
        #! format: on

        if iszero(checker.count[])
            # println(stderr,
            #     "ERROR: Abstract SELTZO-TwoSum-$T inputs ($x, $y)" *
            #     " are not covered by any lemmas.")
            if length(abstract_outputs(two_sum_abstractions, x, y)) > 2
                push!(rs, (x, y))
            end
        elseif !isone(checker.count[])
            println(stderr,
                "WARNING: Abstract SELTZO-TwoSum-$T inputs ($x, $y)" *
                " are covered by multiple lemmas.")
        end
    end

    println("SELTZO-TwoSum-$T lemmas:")
    for (name, n) in sort!(collect(lemma_counts))
        println("    $name: $n")
    end
    println("Unverified cases: $(rs.count[])")
    for i = 1:min(rs.count[], length(rs.reservoir))
        println("Unverified case $i:")
        x, y = rs.reservoir[i]
        sx, lbx, lby, ex, fx, gx = unpack(x, T)
        sy, tbx, tby, ey, fy, gy = unpack(y, T)
        println("    SELTZO Input 1: ",
            "(sx = $sx, lbx = $lbx, lby = $lby, ",
            "ex = $ex, fx = $fx, gx = $gx) [$x]")
        println("    SELTZO Input 2: ",
            "(sy = $sy, tbx = $tbx, tby = $tby, ",
            "ey = $ey, fy = $fy, gy = $gy) [$y]")
        println("    SELTZO Outputs:")
        for (k, vs) in condense(abstract_outputs(two_sum_abstractions, x, y), T)
            ss, lbs, tbs, se, lbe, tbe = k
            for v in vs
                es, fs, gs, ee, fe, ge = v
                println("        ",
                    "(ss = $ss, lbs = $lbs, tbs = $tbs, ",
                    "es = $es, fs = $fs, gs = $gs), ",
                    "(se = $se, lbe = $lbe, tbe = $tbe, ",
                    "ee = $ee, fe = $fe, ge = $ge)")
            end
        end
    end
    flush(stdout)

    return nothing
end


const EXIT_INPUT_FILE_MISSING = 1
const EXIT_INPUT_FILE_MALFORMED = 2


function main(
    file_name::String,
    expected_count::Int,
    expected_crc::UInt32,
    ::Type{T},
) where {T<:AbstractFloat}

    if !isfile(file_name)
        println(stderr,
            "ERROR: Input file $file_name not found." *
            " Run `julia GenerateAbstractionData.jl` to" *
            " generate the input files for this program.")
        exit(EXIT_INPUT_FILE_MISSING)
    end
    valid = (filesize(file_name) ===
             expected_count * sizeof(TwoSumAbstraction{SELTZOAbstraction})) &&
            (open(crc32c, file_name) === expected_crc)
    if !valid
        println(stderr,
            "ERROR: Input file $file_name is malformed." *
            " Run `julia GenerateAbstractionData.jl` to" *
            " generate the input files for this program.")
        exit(EXIT_INPUT_FILE_MALFORMED)
    end
    two_sum_abstractions =
        Vector{TwoSumAbstraction{SELTZOAbstraction}}(undef, expected_count)
    read!(file_name, two_sum_abstractions)
    check_seltzo_two_sum_lemmas(two_sum_abstractions, T)
    println("Successfully checked all SELTZO-TwoSum-$T lemmas.")
    flush(stdout)

    return nothing
end


if abspath(PROGRAM_FILE) == @__FILE__
    main("SELTZO-TwoSum-Float16.bin", 319_985_950, 0xCC55FA4F, Float16)
    # main("SELTZO-TwoSum-BFloat16.bin", 1_172_449_766, 0xCB0D263C, BFloat16)
end
