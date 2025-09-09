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
                (ex > ey + (p+1)) |
                ((ex == ey + (p+1)) & ((cy == POW2) | same_sign | (cx != POW2))) |
                ((ex == ey + p) & (cy == POW2) & (same_sign | (cx != POW2)) & (~tbx))
            ) do lemma
                add_case!(lemma, x, y)
            end
            checker("SELTZO-TwoSum-I-Y",
                (ey > ex + (p+1)) |
                ((ey == ex + (p+1)) & ((cx == POW2) | same_sign | (cy != POW2))) |
                ((ey == ex + p) & (cx == POW2) & (same_sign | (cy != POW2)) & (~tby))
            ) do lemma
                add_case!(lemma, y, x)
            end

            ####################################################################

            # Sum of two powers of two (equal exponent case).
            checker("SELTZO-TwoSum-POW2-POW2-SE",
                same_sign & (cx == POW2) & (cy == POW2) & (ex == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fx+1, gx+1), pos_zero)
            end

            # Sum of two powers of two (adjacent case).
            checker("SELTZO-TwoSum-POW2-POW2-SA-X",
                same_sign & (cx == POW2) & (cy == POW2) & (ex == ey + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey-1, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-POW2-SA-Y",
                same_sign & (cy == POW2) & (cx == POW2) & (ey == ex + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex-1, ex), pos_zero)
            end

            # Sum of two powers of two (general case).
            checker("SELTZO-TwoSum-POW2-POW2-SG-X",
                same_sign & (cx == POW2) & (cy == POW2) &
                (ex > ey + 1) & (ex < ey + p - 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-POW2-SG-Y",
                same_sign & (cy == POW2) & (cx == POW2) &
                (ey > ex + 1) & (ey < ex + p - 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, ex), pos_zero)
            end

            # Sum of two powers of two (boundary case).
            checker("SELTZO-TwoSum-POW2-POW2-SB-X",
                same_sign & (cx == POW2) & (cy == POW2) & (ex == ey + p - 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey+1), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-POW2-SB-Y",
                same_sign & (cy == POW2) & (cx == POW2) & (ey == ex + p - 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex+1), pos_zero)
            end

            ####################################################################

            # Difference of two powers of two (equal exponent case).
            checker("SELTZO-TwoSum-POW2-POW2-DE",
                diff_sign & (cx == POW2) & (cy == POW2) & (ex == ey)
            ) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end

            # Difference of two powers of two (adjacent case).
            checker("SELTZO-TwoSum-POW2-POW2-DA-X",
                diff_sign & (cx == POW2) & (cy == POW2) & (ex == ey + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, fx-1, gx-1), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-POW2-DA-Y",
                diff_sign & (cy == POW2) & (cx == POW2) & (ey == ex + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, fy-1, gy-1), pos_zero)
            end

            # Difference of two powers of two (general case).
            checker("SELTZO-TwoSum-POW2-POW2-DG-X",
                diff_sign & (cx == POW2) & (cy == POW2) &
                (ex > ey + 1) & (ex < ey + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey-1, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-POW2-DG-Y",
                diff_sign & (cy == POW2) & (cx == POW2) &
                (ey > ex + 1) & (ey < ex + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex-1, ex), pos_zero)
            end

            # Difference of two powers of two (boundary case).
            checker("SELTZO-TwoSum-POW2-POW2-DB-X",
                diff_sign & (cx == POW2) & (cy == POW2) & (ex == ey + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fx-1, gx-1), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-POW2-DB-Y",
                diff_sign & (cy == POW2) & (cx == POW2) & (ey == ex + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fy-1, gy-1), pos_zero)
            end

            ####################################################################

            checker("SELTZO-TwoSum-R1R0-ONE1-D1-X",
                diff_sign & (cx == R1R0) & (cy == ONE1) &
                (ex > fy + (p-1)) & (ey > fx + 1)
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sx, 1, 0, ex, ey, gx),
                    SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-R1R0-ONE1-D1-Y",
                diff_sign & (cy == R1R0) & (cx == ONE1) &
                (ey > fx + (p-1)) & (ex > fy + 1)
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sy, 1, 0, ey, ex, gy),
                    SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-POW2-ALL1-S1-X",
                same_sign & (cx == POW2) & (cy == ALL1) &
                (ex > ey + 2) & (ex < ey + p)
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sx, 0, 0, ex, ey+1, ey+1),
                    SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-POW2-ALL1-S1-Y",
                same_sign & (cy == POW2) & (cx == ALL1) &
                (ey > ex + 2) & (ey < ex + p)
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sy, 0, 0, ey, ex+1, ex+1),
                    SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
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
