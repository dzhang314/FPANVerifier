using BFloat16s
using CRC32c

push!(LOAD_PATH, @__DIR__)
using FloatAbstractions


function check_se_two_sum_lemmas(
    eft_abstractions::Vector{TwoSumAbstraction{SEAbstraction}},
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
        checker = LemmaChecker(eft_abstractions, x, y, T, lemma_counts)

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

        @assert isone(checker.count[])
    end

    println("SE-TwoSum-$T lemmas:")
    for (name, n) in sort!(collect(lemma_counts))
        println("    $name: $n")
    end
    flush(stdout)

    return nothing
end


try

    @assert isfile("SE-TwoSum-Float16.bin")
    @assert filesize("SE-TwoSum-Float16.bin") ===
            38_638 * sizeof(TwoSumAbstraction{SEAbstraction})
    @assert open(crc32c, "SE-TwoSum-Float16.bin") === 0x18557287
    se_two_sum_f16_abstractions =
        Vector{TwoSumAbstraction{SEAbstraction}}(undef, 38_638)
    read!("SE-TwoSum-Float16.bin", se_two_sum_f16_abstractions)
    check_se_two_sum_lemmas(se_two_sum_f16_abstractions, Float16)
    println("Successfully checked all SE-TwoSum-Float16 lemmas.")
    flush(stdout)

    @assert isfile("SE-TwoSum-BFloat16.bin")
    @assert filesize("SE-TwoSum-BFloat16.bin") ===
            548_026 * sizeof(TwoSumAbstraction{SEAbstraction})
    @assert open(crc32c, "SE-TwoSum-BFloat16.bin") === 0xB20B9481
    se_two_sum_bf16_abstractions =
        Vector{TwoSumAbstraction{SEAbstraction}}(undef, 548_026)
    read!("SE-TwoSum-BFloat16.bin", se_two_sum_bf16_abstractions)
    check_se_two_sum_lemmas(se_two_sum_bf16_abstractions, BFloat16)
    println("Successfully checked all SE-TwoSum-BFloat16 lemmas.")
    flush(stdout)

catch e
    if e isa AssertionError
        println("Run `julia GenerateAbstractionData.jl` to" *
                " generate the input data for this program.")
        exit(1)
    else
        rethrow()
    end
end
