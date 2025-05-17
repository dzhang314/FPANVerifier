using BFloat16s
using CRC32c

push!(LOAD_PATH, @__DIR__)
using FloatAbstractions


function check_se_two_sum_lemmas(
    two_sum_abstractions::Vector{TwoSumAbstraction{SEAbstraction}},
    ::Type{T},
) where {T<:AbstractFloat}

    ± = false:true
    p = precision(T)
    pos_zero = SEAbstraction(+zero(T))
    neg_zero = SEAbstraction(-zero(T))
    abstract_inputs = enumerate_abstractions(SEAbstraction, T)
    lemma_counts = Dict{String,Int}()

    for x in abstract_inputs, y in abstract_inputs

        sx = signbit(x)
        sy = signbit(y)
        ex = unsafe_exponent(x)
        ey = unsafe_exponent(y)
        same_sign = (sx == sy)
        diff_sign = (sx != sy)
        x_zero = (x == pos_zero) | (x == neg_zero)
        y_zero = (y == pos_zero) | (y == neg_zero)
        checker = LemmaChecker(two_sum_abstractions, x, y, T, lemma_counts)

        #! format: off
        if x_zero | y_zero ################################### LEMMA FAMILY SE-Z

            # Lemmas in Family SE-Z (for "zero") apply
            # when one or both addends are zero.

            # Lemma SE-Z1: Both addends are zero.
            checker("SE-Z1-PP", (x == pos_zero) & (y == pos_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            checker("SE-Z1-PN", (x == pos_zero) & (y == neg_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            checker("SE-Z1-NP", (x == neg_zero) & (y == pos_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            checker("SE-Z1-NN", (x == neg_zero) & (y == neg_zero)) do lemma
                add_case!(lemma, neg_zero, pos_zero)
            end

            # Lemma SE-Z2: One addend is zero.
            checker("SE-Z2-X", y_zero & !x_zero) do lemma
                add_case!(lemma, x, pos_zero)
            end
            checker("SE-Z2-Y", x_zero & !y_zero) do lemma
                add_case!(lemma, y, pos_zero)
            end

        else ############################################ NONZERO LEMMA FAMILIES

            # From this point onward, all lemmas implicitly
            # assume that both addends are nonzero.

            ################################################## LEMMA FAMILY SE-I

            # Lemmas in Family SE-I (for "identical") apply
            # to addends unchanged by the TwoSum algorithm.

            checker("SE-I-X", (ex > ey + (p+1)) | ((ex == ey + (p+1)) & same_sign)) do lemma
                add_case!(lemma, x, y)
            end
            checker("SE-I-Y", (ey > ex + (p+1)) | ((ey == ex + (p+1)) & same_sign)) do lemma
                add_case!(lemma, y, x)
            end

            ################################################## LEMMA FAMILY SE-S

            # Lemmas in Family SE-S apply to addends with the same sign.

            checker("SE-S1-X", same_sign & (ex == ey + p)) do lemma
                add_case!(lemma, (sx, ex:ex+1), (!sy, ey-(p-1):ex-p))
                add_case!(lemma, x            , y                   )
            end
            checker("SE-S1-Y", same_sign & (ey == ex + p)) do lemma
                add_case!(lemma, (sy, ey:ey+1), (!sx, ex-(p-1):ey-p))
                add_case!(lemma, y            , x                   )
            end

            checker("SE-S2-X", same_sign & (ex == ey + (p-1))) do lemma
                add_case!(lemma, (sx, ex:ex+1), pos_zero          )
                add_case!(lemma, (sx, ex:ex+1), (±, ey-(p-1):ex-p))
            end
            checker("SE-S2-Y", same_sign & (ey == ex + (p-1))) do lemma
                add_case!(lemma, (sy, ey:ey+1), pos_zero          )
                add_case!(lemma, (sy, ey:ey+1), (±, ex-(p-1):ey-p))
            end

            checker("SE-S3-X", same_sign & (ex == ey + (p-2))) do lemma
                add_case!(lemma, (sx, ex:ex+1), pos_zero                )
                add_case!(lemma, (sx, ex:ex+1), (!sy, ey-(p-1):ex-p    ))
                add_case!(lemma, (sx, ex     ), ( sy, ey-(p-1):ex-p    ))
                add_case!(lemma, (sx, ex+1   ), ( sy, ey-(p-1):ex-(p-1)))
            end
            checker("SE-S3-Y", same_sign & (ey == ex + (p-2))) do lemma
                add_case!(lemma, (sy, ey:ey+1), pos_zero                )
                add_case!(lemma, (sy, ey:ey+1), (!sx, ex-(p-1):ey-p    ))
                add_case!(lemma, (sy, ey     ), ( sx, ex-(p-1):ey-p    ))
                add_case!(lemma, (sy, ey+1   ), ( sx, ex-(p-1):ey-(p-1)))
            end

            checker("SE-S4-X", same_sign & (ex > ey) & (ex < ey + (p-2))) do lemma
                add_case!(lemma, (sx, ex:ex+1), pos_zero              )
                add_case!(lemma, (sx, ex     ), (±, ey-(p-1):ex-p    ))
                add_case!(lemma, (sx, ex+1   ), (±, ey-(p-1):ex-(p-1)))
            end
            checker("SE-S4-Y", same_sign & (ey > ex) & (ey < ex + (p-2))) do lemma
                add_case!(lemma, (sy, ey:ey+1), pos_zero              )
                add_case!(lemma, (sy, ey     ), (±, ex-(p-1):ey-p    ))
                add_case!(lemma, (sy, ey+1   ), (±, ex-(p-1):ey-(p-1)))
            end

            checker("SE-S5", same_sign & (ex == ey)) do lemma
                add_case!(lemma, (sx, ex+1), pos_zero)
                add_case!(lemma, (sx, ex+1), (±, ex-(p-1)))
            end

            ################################################## LEMMA FAMILY SE-D

            # Lemmas in Family SE-D apply to addends with different signs.

            checker("SE-D1-X", diff_sign & (ex == ey + (p+1))) do lemma
                add_case!(lemma, (sx, ex-1), (!sy, ey-(p-1):ex-(p+2)))
                add_case!(lemma, x         , y                       )
            end
            checker("SE-D1-Y", diff_sign & (ey == ex + (p+1))) do lemma
                add_case!(lemma, (sy, ey-1), (!sx, ex-(p-1):ey-(p+2)))
                add_case!(lemma, y         , x                       )
            end

            checker("SE-D2-X", diff_sign & (ex == ey + p)) do lemma
                add_case!(lemma, (sx, ex-1), pos_zero                )
                add_case!(lemma, (sx, ex-1), ( sy, ey-(p-1):ex-(p+2)))
                add_case!(lemma, (sx, ex-1), (!sy, ey-(p-1):ex-(p+1)))
                add_case!(lemma, (sx, ex  ), (!sy, ey-(p-1):ex-p    ))
                add_case!(lemma, x         , y                       )
            end
            checker("SE-D2-Y", diff_sign & (ey == ex + p)) do lemma
                add_case!(lemma, (sy, ey-1), pos_zero                )
                add_case!(lemma, (sy, ey-1), ( sx, ex-(p-1):ey-(p+2)))
                add_case!(lemma, (sy, ey-1), (!sx, ex-(p-1):ey-(p+1)))
                add_case!(lemma, (sy, ey  ), (!sx, ex-(p-1):ey-p    ))
                add_case!(lemma, y         , x                       )
            end

            checker("SE-D3-X", diff_sign & (ex > ey + 1) & (ex < ey + p)) do lemma
                add_case!(lemma, (sx, ex-1:ex), pos_zero              )
                add_case!(lemma, (sx, ex-1   ), (±, ey-(p-1):ex-(p+1)))
                add_case!(lemma, (sx, ex     ), (±, ey-(p-1):ex-p    ))
            end
            checker("SE-D3-Y", diff_sign & (ey > ex + 1) & (ey < ex + p)) do lemma
                add_case!(lemma, (sy, ey-1:ey), pos_zero              )
                add_case!(lemma, (sy, ey-1   ), (±, ex-(p-1):ey-(p+1)))
                add_case!(lemma, (sy, ey     ), (±, ex-(p-1):ey-p    ))
            end

            checker("SE-D4-X", diff_sign & (ex == ey + 1)) do lemma
                add_case!(lemma, (sx, ex-p:ex), pos_zero )
                add_case!(lemma, (sx, ex     ), (±, ex-p))
            end
            checker("SE-D4-Y", diff_sign & (ey == ex + 1)) do lemma
                add_case!(lemma, (sy, ey-p:ey), pos_zero )
                add_case!(lemma, (sy, ey     ), (±, ey-p))
            end

            checker("SE-D5", diff_sign & (ex == ey)) do lemma
                add_case!(lemma, pos_zero          , pos_zero)
                add_case!(lemma, (±, ex-(p-1):ex-1), pos_zero)
            end

        end
        #! format: on

        if iszero(checker.count[])
            println(stderr,
                "ERROR: Abstract SE-TwoSum-$T inputs ($x, $y)" *
                " are not covered by any lemmas.")
        elseif !isone(checker.count[])
            println(stderr,
                "WARNING: Abstract SE-TwoSum-$T inputs ($x, $y)" *
                " are covered by multiple lemmas.")
        end
    end

    println("SE-TwoSum-$T lemmas:")
    for (name, n) in sort!(collect(lemma_counts))
        println("    $name: $n")
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
             expected_count * sizeof(TwoSumAbstraction{SEAbstraction})) &&
            (open(crc32c, file_name) === expected_crc)
    if !valid
        println(stderr,
            "ERROR: Input file $file_name is malformed." *
            " Run `julia GenerateAbstractionData.jl` to" *
            " generate the input files for this program.")
        exit(EXIT_INPUT_FILE_MALFORMED)
    end
    two_sum_abstractions =
        Vector{TwoSumAbstraction{SEAbstraction}}(undef, expected_count)
    read!(file_name, two_sum_abstractions)
    check_se_two_sum_lemmas(two_sum_abstractions, T)
    println("Successfully checked all SE-TwoSum-$T lemmas.")
    flush(stdout)

end


if abspath(PROGRAM_FILE) == @__FILE__
    main("SE-TwoSum-Float16.bin", 38_638, 0x18557287, Float16)
    main("SE-TwoSum-BFloat16.bin", 548_026, 0xB20B9481, BFloat16)
end
