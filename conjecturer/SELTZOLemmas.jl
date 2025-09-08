using BFloat16s: BFloat16
using CRC32c: crc32c

push!(LOAD_PATH, @__DIR__)
using FloatAbstractions


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
    unverified_counts = Dict{Tuple{SELTZOType,SELTZOType},Int}()
    rs = ReservoirSampler{Tuple{SELTZOAbstraction,SELTZOAbstraction}}(5)

    for x in abstract_inputs, y in abstract_inputs

        cx = seltzo_classify(x, T)
        cy = seltzo_classify(y, T)
        sx, lbx, tbx, ex, fx, gx = unpack(x, T)
        sy, lby, tby, ey, fy, gy = unpack(y, T)

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
                ((ex == ey + (p+1)) & ((cy == POW2) | same_sign | (cx != POW2))) |
                ((ex == ey + p) & (cy == POW2) & (same_sign | (cx != POW2)) & (~tbx))
            ) do lemma
                add_case!(lemma, x, y)
            end
            checker("SELTZO-I-Y",
                (ey > ex + (p+1)) |
                ((ey == ex + (p+1)) & ((cx == POW2) | same_sign | (cy != POW2))) |
                ((ey == ex + p) & (cx == POW2) & (same_sign | (cy != POW2)) & (~tby))
            ) do lemma
                add_case!(lemma, y, x)
            end

            checker("SELTZO-1-X",
                diff_sign & lbx & (~tbx) & lby & (~tby) &
                (ex == fx + 2) & (fx > ey + 1 > gx) & (ex > fy + p) & (fy + 1 == gy)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, ~lbx, tbx, ex, fx, gx), SELTZORange(~sy, ~lby, tby, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, lbx, tbx, ex, fx, gx), SELTZORange(~sy, ~lby, tby, gy, gy-p, gy))
            end
            checker("SELTZO-1-Y",
                diff_sign & lby & (~tby) & lbx & (~tbx) &
                (ey == fy + 2) & (fy > ex + 1 > gy) & (ey > fx + p) & (fx + 1 == gx)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, ~lby, tby, ey, fy, gy), SELTZORange(~sx, ~lbx, tbx, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, lby, tby, ey, fy, gy), SELTZORange(~sx, ~lbx, tbx, gx, gx-p, gx))
            end

            checker("SELTZO-2-X",
                same_sign & (~lbx) & (~tby) & (ex > ey + 1) & (fx < fy) & (gx < gy)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, lbx, tbx, ex, ey, gx), pos_zero)
            end
            checker("SELTZO-2-Y",
                same_sign & (~lby) & (~tbx) & (ey > ex + 1) & (fy < fx) & (gy < gx)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, lby, tby, ey, ex, gy), pos_zero)
            end

        end
        #! format: on

        if iszero(checker.coverage_count[])
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
        elseif !isone(checker.coverage_count[])
            println(stderr,
                "WARNING: Abstract SELTZO-TwoSum-$T inputs ($x, $y)" *
                " are covered by multiple lemmas.")
        end
    end

    println("SELTZO-TwoSum-$T lemmas:")
    for (name, n) in sort!(collect(lemma_counts))
        println("    $name: $n")
    end
    println("Unverified cases: $(rs.population_size[])")
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
