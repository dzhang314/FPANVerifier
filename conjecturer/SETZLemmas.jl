using BFloat16s: BFloat16
using CRC32c: crc32c

push!(LOAD_PATH, @__DIR__)
using FloatAbstractions


const EXIT_INPUT_FILE_MISSING = 1
const EXIT_INPUT_FILE_MALFORMED = 2


function check_setz_two_sum_lemmas(
    two_sum_abstractions::Vector{TwoSumAbstraction{SETZAbstraction}},
    ::Type{T},
) where {T<:AbstractFloat}

    ± = false:true
    p = precision(T)
    pos_zero = SETZAbstraction(+zero(T))
    neg_zero = SETZAbstraction(-zero(T))
    abstract_inputs = enumerate_abstractions(SETZAbstraction, T)
    lemma_counts = Dict{String,Int}()

    for x in abstract_inputs, y in abstract_inputs

        sx, ex, fx = unpack(x, T)
        sy, ey, fy = unpack(y, T)
        same_sign = (sx == sy)
        diff_sign = (sx != sy)
        x_zero = (x == pos_zero) | (x == neg_zero)
        y_zero = (y == pos_zero) | (y == neg_zero)
        checker = LemmaChecker(two_sum_abstractions, x, y, T, lemma_counts)

        #! format: off
        if x_zero | y_zero ################################## LEMMA FAMILY Z (2)

            checker("SETZ-TwoSum-Z1-P", x_zero & y_zero & ((x == pos_zero) | (y == pos_zero))) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            checker("SETZ-TwoSum-Z1-N", (x == neg_zero) & (y == neg_zero)) do lemma
                add_case!(lemma, neg_zero, pos_zero)
            end

            checker("SETZ-TwoSum-Z2-X", y_zero & !x_zero) do lemma
                add_case!(lemma, x, pos_zero)
            end
            checker("SETZ-TwoSum-Z2-Y", x_zero & !y_zero) do lemma
                add_case!(lemma, y, pos_zero)
            end

        else ############################################ NONZERO LEMMA FAMILIES

            checker("SETZ-TwoSum-I-X",
                (ex > ey + (p+1)) |
                ((ex == ey + (p+1)) & (same_sign | (ex > fx) | (ey == fy))) |
                ((ex == ey + p) & (same_sign | (ex > fx)) & (ey == fy) & (ex < fx + (p-1)))
            ) do lemma
                add_case!(lemma, x, y)
            end
            checker("SETZ-TwoSum-I-Y",
                (ey > ex + (p+1)) |
                ((ey == ex + (p+1)) & (same_sign | (ey > fy) | (ex == fx))) |
                ((ey == ex + p) & (same_sign | (ey > fy)) & (ex == fx) & (ey < fy + (p-1)))
            ) do lemma
                add_case!(lemma, y, x)
            end

            checker("SETZ-TwoSum-LS-X", same_sign & (ex > ey) & (fx < fy) & (ex < fx + (p-1))) do lemma
                add_case!(lemma, (sx, ex:ex+1, fx), pos_zero)
            end
            checker("SETZ-TwoSum-LS-Y", same_sign & (ey > ex) & (fy < fx) & (ey < fy + (p-1))) do lemma
                add_case!(lemma, (sy, ey:ey+1, fy), pos_zero)
            end

            checker("SETZ-TwoSum-LSA0-X", same_sign & (ex > ey) & (fx < fy) & (ex == fx + (p-1)) & (ey > fy)) do lemma
                add_case!(lemma, (sx, ex  , fx     ), pos_zero)
                add_case!(lemma, (sx, ex+1, fx+2:ey), (± , fx, fx))
                add_case!(lemma, (sx, ex+1, ex+1   ), (sy, fx, fx))
            end
            checker("SETZ-TwoSum-LSA0-Y", same_sign & (ey > ex) & (fy < fx) & (ey == fy + (p-1)) & (ex > fx)) do lemma
                add_case!(lemma, (sy, ey  , fy     ), pos_zero)
                add_case!(lemma, (sy, ey+1, fy+2:ex), (± , fy, fy))
                add_case!(lemma, (sy, ey+1, ey+1   ), (sx, fy, fy))
            end

            checker("SETZ-TwoSum-LSA1-X", same_sign & (ex > ey) & (fx < fy) & (ex == fx + (p-1)) & (ey == fy)) do lemma
                add_case!(lemma, (sx, ex  , fx       ), pos_zero)
                add_case!(lemma, (sx, ex+1, fx+2:ey-1), ( sy, fx, fx))
                add_case!(lemma, (sx, ex+1, fx+2:ey  ), (~sy, fx, fx))
                add_case!(lemma, (sx, ex+1, ex+1     ), ( sy, fx, fx))
            end
            checker("SETZ-TwoSum-LSA1-Y", same_sign & (ey > ex) & (fy < fx) & (ey == fy + (p-1)) & (ex == fx)) do lemma
                add_case!(lemma, (sy, ey  , fy       ), pos_zero)
                add_case!(lemma, (sy, ey+1, fy+2:ex-1), ( sx, fy, fy))
                add_case!(lemma, (sy, ey+1, fy+2:ex  ), (~sx, fy, fy))
                add_case!(lemma, (sy, ey+1, ey+1     ), ( sx, fy, fy))
            end

            checker("SETZ-TwoSum-LSB0-X", same_sign & (ex > ey + 1) & (fx == fy)) do lemma
                add_case!(lemma, (sx, ex  , fx+1:ex-1), pos_zero)
                add_case!(lemma, (sx, ex+1, fx+1:ey  ), pos_zero)
                add_case!(lemma, (sx, ex+1, ex+1     ), pos_zero)
            end
            checker("SETZ-TwoSum-LSB0-Y", same_sign & (ey > ex + 1) & (fy == fx)) do lemma
                add_case!(lemma, (sy, ey  , fy+1:ey-1), pos_zero)
                add_case!(lemma, (sy, ey+1, fy+1:ex  ), pos_zero)
                add_case!(lemma, (sy, ey+1, ey+1     ), pos_zero)
            end

            checker("SETZ-TwoSum-LSB1-X", same_sign & (ex == ey + 1) & (fx == fy)) do lemma
                add_case!(lemma, (sx, ex  , fx+1:ex-2), pos_zero)
                add_case!(lemma, (sx, ex+1, fx+1:ey  ), pos_zero)
                add_case!(lemma, (sx, ex+1, ex+1     ), pos_zero)
            end
            checker("SETZ-TwoSum-LSB1-Y", same_sign & (ey == ex + 1) & (fy == fx)) do lemma
                add_case!(lemma, (sy, ey  , fy+1:ey-2), pos_zero)
                add_case!(lemma, (sy, ey+1, fy+1:ex  ), pos_zero)
                add_case!(lemma, (sy, ey+1, ey+1     ), pos_zero)
            end

            checker("SETZ-TwoSum-LSB2", same_sign & (ex == ey) & (fx == fy)) do lemma
                add_case!(lemma, (sx, ex+1, fx+1   ), pos_zero)
                add_case!(lemma, (sx, ex+1, fx+2:ex), pos_zero)
            end

            checker("SETZ-TwoSum-LD-X", diff_sign & (ex > ey + 1) & (fx < fy)) do lemma
                add_case!(lemma, (sx, ex-1:ex, fx), pos_zero)
            end
            checker("SETZ-TwoSum-LD-Y", diff_sign & (ey > ex + 1) & (fy < fx)) do lemma
                add_case!(lemma, (sy, ey-1:ey, fy), pos_zero)
            end

            checker("SETZ-TwoSum-LDA-X", diff_sign & (ex > ey + 1) & (fx == fy)) do lemma
                add_case!(lemma, (sx, ex-1, fx+1:ey), pos_zero)
                add_case!(lemma, (sx, ex  , fx+1:ex), pos_zero)
            end
            checker("SETZ-TwoSum-LDA-Y", diff_sign & (ey > ex + 1) & (fy == fx)) do lemma
                add_case!(lemma, (sy, ey-1, fy+1:ex), pos_zero)
                add_case!(lemma, (sy, ey  , fy+1:ey), pos_zero)
            end

            checker("SETZ-TwoSum-LDB-X", diff_sign & (ex == ey + 1) & (fx < fy)) do lemma
                add_case!(lemma, (sx, fy:ex, fx), pos_zero)
            end
            checker("SETZ-TwoSum-LDB-Y", diff_sign & (ey == ex + 1) & (fy < fx)) do lemma
                add_case!(lemma, (sy, fx:ey, fy), pos_zero)
            end

            checker("SETZ-TwoSum-LDC0-X", diff_sign & (ex == ey) & (fx < fy) & (ey > fy + 1)) do lemma
                add_case!(lemma, (±, fx:ex-1, fx), pos_zero)
            end
            checker("SETZ-TwoSum-LDC0-Y", diff_sign & (ey == ex) & (fy < fx) & (ex > fx + 1)) do lemma
                add_case!(lemma, (±, fy:ey-1, fy), pos_zero)
            end

            checker("SETZ-TwoSum-LDC1-X", diff_sign & (ex == ey) & (fx < fy) & (ey == fy + 1)) do lemma
                add_case!(lemma, (±, fx:ex-2, fx), pos_zero)
            end
            checker("SETZ-TwoSum-LDC1-Y", diff_sign & (ey == ex) & (fy < fx) & (ex == fx + 1)) do lemma
                add_case!(lemma, (±, fy:ey-2, fy), pos_zero)
            end

            checker("SETZ-TwoSum-LDC2-X", diff_sign & (ex == ey) & (fx < fy) & (ey == fy)) do lemma
                add_case!(lemma, (sx, fx:ex-1, fx), pos_zero)
            end
            checker("SETZ-TwoSum-LDC2-Y", diff_sign & (ey == ex) & (fy < fx) & (ex == fx)) do lemma
                add_case!(lemma, (sy, fy:ey-1, fy), pos_zero)
            end

            checker("SETZ-TwoSum-LDAB-X", diff_sign & (ex == ey + 1) & (fx == fy)) do lemma
                for k = fx+1:ex-1
                    add_case!(lemma, (sx, k, fx+1:k), pos_zero)
                end
                add_case!(lemma, (sx, ex, fx+1:ex-2), pos_zero)
                add_case!(lemma, (sx, ex,      ex  ), pos_zero)
            end
            checker("SETZ-TwoSum-LDAB-Y", diff_sign & (ey == ex + 1) & (fy == fx)) do lemma
                for k = fy+1:ey-1
                    add_case!(lemma, (sy, k, fy+1:k), pos_zero)
                end
                add_case!(lemma, (sy, ey, fy+1:ey-2), pos_zero)
                add_case!(lemma, (sy, ey,      ey  ), pos_zero)
            end

            checker("SETZ-TwoSum-LDAC", diff_sign & (ex == ey) & (fx == fy)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
                for k = fx+1:ex-1
                    add_case!(lemma, (±, k, fx+1:k), pos_zero)
                end
            end

            checker("SETZ-TwoSum-CS-X", same_sign & (ex > ey) & (fx > fy) & (ex < fy + (p-1)) & (fx < ey + 1) & (ex > fx + 1)) do lemma
                add_case!(lemma, (sx, ex:ex+1, fy), pos_zero)
            end
            checker("SETZ-TwoSum-CS-Y", same_sign & (ey > ex) & (fy > fx) & (ey < fx + (p-1)) & (fy < ex + 1) & (ey > fy + 1)) do lemma
                add_case!(lemma, (sy, ey:ey+1, fx), pos_zero)
            end

            checker("SETZ-TwoSum-CSA0-X", same_sign & (ex > ey) & (fx > fy) & (ex == fy + (p-1)) & (fx < ey)) do lemma
                add_case!(lemma, (sx, ex  , fy     ), pos_zero)
                add_case!(lemma, (sx, ex+1, fy+2:ey), ( ± , fy, fy))
                add_case!(lemma, (sx, ex+1, ex+1   ), ( sy, fy, fy))
            end
            checker("SETZ-TwoSum-CSA0-Y", same_sign & (ey > ex) & (fy > fx) & (ey == fx + (p-1)) & (fy < ex)) do lemma
                add_case!(lemma, (sy, ey  , fx     ), pos_zero)
                add_case!(lemma, (sy, ey+1, fx+2:ex), ( ± , fx, fx))
                add_case!(lemma, (sy, ey+1, ey+1   ), ( sx, fx, fx))
            end

            checker("SETZ-TwoSum-CSA1-X", same_sign & (ex > ey + 1) & (fx > fy) & (ex == fy + (p-1)) & (fx == ey)) do lemma
                add_case!(lemma, (sx, ex  , fy       ), pos_zero)
                add_case!(lemma, (sx, ex+1, fy+2:ey-1), ( sy, fy, fy))
                add_case!(lemma, (sx, ex+1, fy+2:ey  ), (~sy, fy, fy))
                add_case!(lemma, (sx, ex+1, ex+1     ), ( sy, fy, fy))
            end
            checker("SETZ-TwoSum-CSA1-Y", same_sign & (ey > ex + 1) & (fy > fx) & (ey == fx + (p-1)) & (fy == ex)) do lemma
                add_case!(lemma, (sy, ey  , fx       ), pos_zero)
                add_case!(lemma, (sy, ey+1, fx+2:ex-1), ( sx, fx, fx))
                add_case!(lemma, (sy, ey+1, fx+2:ex  ), (~sx, fx, fx))
                add_case!(lemma, (sy, ey+1, ey+1     ), ( sx, fx, fx))
            end

            checker("SETZ-TwoSum-CSB-X", same_sign & ((ex == ey) | ((ex == ey + 1) & (fx == ey))) & (fx > fy) & (ex < fy + (p-1))) do lemma
                add_case!(lemma, (sx, ex+1, fy), pos_zero)
            end
            checker("SETZ-TwoSum-CSB-Y", same_sign & ((ey == ex) | ((ey == ex + 1) & (fy == ex))) & (fy > fx) & (ey < fx + (p-1))) do lemma
                add_case!(lemma, (sy, ey+1, fx), pos_zero)
            end

            checker("SETZ-TwoSum-CSAB0-X", same_sign & (ex == ey) & (fx > fy) & (ex == fy + (p-1)) & (fx < ey)) do lemma
                add_case!(lemma, (sx, ex+1, fy+2:ex), (±, fy, fy))
            end
            checker("SETZ-TwoSum-CSAB0-Y", same_sign & (ey == ex) & (fy > fx) & (ey == fx + (p-1)) & (fy < ex)) do lemma
                add_case!(lemma, (sy, ey+1, fx+2:ey), (±, fx, fx))
            end

            checker("SETZ-TwoSum-CSAB1-X", same_sign & ((ex == ey) | (ex == ey + 1)) & (ex == fy + (p-1)) & (fx == ey)) do lemma
                add_case!(lemma, (sx, ex+1, fy+2:ey-1), ( ± , fy, fy))
                add_case!(lemma, (sx, ex+1,      ey  ), (~sy, fy, fy))
                add_case!(lemma, (sx, ex+1, ex+1     ), ( sy, fy, fy))
            end
            checker("SETZ-TwoSum-CSAB1-Y", same_sign & ((ey == ex) | (ey == ex + 1)) & (ey == fx + (p-1)) & (fy == ex)) do lemma
                add_case!(lemma, (sy, ey+1, fx+2:ex-1), ( ± , fx, fx))
                add_case!(lemma, (sy, ey+1,      ex  ), (~sx, fx, fx))
                add_case!(lemma, (sy, ey+1, ey+1     ), ( sx, fx, fx))
            end

            checker("SETZ-TwoSum-CD0-X", diff_sign & (ex > ey + 1) & (fx > fy) & (ex < fy + p) & (fx < ey + 1)) do lemma
                add_case!(lemma, (sx, ex-1:ex, fy), pos_zero)
            end
            checker("SETZ-TwoSum-CD0-Y", diff_sign & (ey > ex + 1) & (fy > fx) & (ey < fx + p) & (fy < ex + 1)) do lemma
                add_case!(lemma, (sy, ey-1:ey, fx), pos_zero)
            end

            checker("SETZ-TwoSum-CD1-X", diff_sign & (ex == ey + 1) & (fx > fy) & (ex < fy + p) & (fx < ey)) do lemma
                add_case!(lemma, (sx, fx:ex, fy), pos_zero)
            end
            checker("SETZ-TwoSum-CD1-Y", diff_sign & (ey == ex + 1) & (fy > fx) & (ey < fx + p) & (fy < ex)) do lemma
                add_case!(lemma, (sy, fy:ey, fx), pos_zero)
            end

            checker("SETZ-TwoSum-CD2-X", diff_sign & (ex == ey + 1) & (fx > fy) & (fx == ey)) do lemma
                add_case!(lemma, (sx, ex-1, fy), pos_zero)
            end
            checker("SETZ-TwoSum-CD2-Y", diff_sign & (ey == ex + 1) & (fy > fx) & (fy == ex)) do lemma
                add_case!(lemma, (sy, ey-1, fx), pos_zero)
            end

            checker("SETZ-TwoSum-T0-X", (same_sign | (ex > fx)) & (ex < fy + p) & (fx > ey)) do lemma
                add_case!(lemma, (sx, ex, fy), pos_zero)
            end
            checker("SETZ-TwoSum-T0-Y", (same_sign | (ey > fy)) & (ey < fx + p) & (fy > ex)) do lemma
                add_case!(lemma, (sy, ey, fx), pos_zero)
            end

            checker("SETZ-TwoSum-T1-X", diff_sign & (ex == fx) & (ex < fy + (p+1)) & (fx > ey + 1)) do lemma
                add_case!(lemma, (sx, ex-1, fy), pos_zero)
            end
            checker("SETZ-TwoSum-T1-Y", diff_sign & (ey == fy) & (ey < fx + (p+1)) & (fy > ex + 1)) do lemma
                add_case!(lemma, (sy, ey-1, fx), pos_zero)
            end

            checker("SETZ-TwoSum-T2-X", diff_sign & (ex == fx) & (fx == ey + 1) & (ey > fy)) do lemma
                add_case!(lemma, (sx, fy:ex-2, fy), pos_zero)
            end
            checker("SETZ-TwoSum-T2-Y", diff_sign & (ey == fy) & (fy == ex + 1) & (ex > fx)) do lemma
                add_case!(lemma, (sy, fx:ey-2, fx), pos_zero)
            end

            checker("SETZ-TwoSum-T3-X", diff_sign & (ex == fx) & (fx == ey + 1) & (ey == fy)) do lemma
                add_case!(lemma, (sx, ex-1, fy), pos_zero)
            end
            checker("SETZ-TwoSum-T3-Y", diff_sign & (ey == fy) & (fy == ex + 1) & (ex == fx)) do lemma
                add_case!(lemma, (sy, ey-1, fx), pos_zero)
            end

            checker("SETZ-TwoSum-1-X", (same_sign | (ex > fx)) & (ex > fy + p) & (fx > ey + 1) & (ex < ey + (p+1))) do lemma
                add_case!(lemma, (sx, ex, ex-(p-1):ey-1), (~sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex, ex-(p-1):ey  ), ( sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex,          ey+1), (~sy, fy:ex-(p+1), fy))
            end
            checker("SETZ-TwoSum-1-Y", (same_sign | (ey > fy)) & (ey > fx + p) & (fy > ex + 1) & (ey < ex + (p+1))) do lemma
                add_case!(lemma, (sy, ey, ey-(p-1):ex-1), (~sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey, ey-(p-1):ex  ), ( sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey,          ex+1), (~sx, fx:ey-(p+1), fx))
            end

            checker("SETZ-TwoSum-1A-X", same_sign & (ex > fy + p) & (fx == ey + 1)) do lemma
                add_case!(lemma, (sx, ex  , ex-(p-1):ey-1), (~sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  , ex-(p-1):ey  ), ( sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  , ey+2    :ex-1), (~sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), (~sy, fy:ex-(p+1), fy))
            end
            checker("SETZ-TwoSum-1A-Y", same_sign & (ey > fx + p) & (fy == ex + 1)) do lemma
                add_case!(lemma, (sy, ey  , ey-(p-1):ex-1), (~sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  , ey-(p-1):ex  ), ( sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  , ex+2    :ey-1), (~sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), (~sx, fx:ey-(p+1), fx))
            end

            checker("SETZ-TwoSum-1B-X", diff_sign & (ex > fy + p) & (fx == ey + 1)) do lemma
                add_case!(lemma, (sx, ex, ex-(p-1):ey-1), (~sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex, ex-(p-1):ey  ), ( sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex, ey+2    :ex  ), (~sy, fy:ex-(p+1), fy))
            end
            checker("SETZ-TwoSum-1B-Y", diff_sign & (ey > fx + p) & (fy == ex + 1)) do lemma
                add_case!(lemma, (sy, ey, ey-(p-1):ex-1), (~sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey, ey-(p-1):ex  ), ( sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey, ex+2    :ey  ), (~sx, fx:ey-(p+1), fx))
            end

            checker("SETZ-TwoSum-1C-X", (same_sign | (ex > fx)) & (ex == fy + p) & (fx > ey + 1) & (ex < ey + p)) do lemma
                add_case!(lemma, (sx, ex, ex-(p-2):ey-1), (~sy, fy, fy))
                add_case!(lemma, (sx, ex, ex-(p-2):ey  ), ( sy, fy, fy))
                add_case!(lemma, (sx, ex,          ey+1), (~sy, fy, fy))
            end
            checker("SETZ-TwoSum-1C-Y", (same_sign | (ey > fy)) & (ey == fx + p) & (fy > ex + 1) & (ey < ex + p)) do lemma
                add_case!(lemma, (sy, ey, ey-(p-2):ex-1), (~sx, fx, fx))
                add_case!(lemma, (sy, ey, ey-(p-2):ex  ), ( sx, fx, fx))
                add_case!(lemma, (sy, ey,          ex+1), (~sx, fx, fx))
            end

            checker("SETZ-TwoSum-1D0-X", diff_sign & (ex == fx) & (ex > fy + (p+1)) & (ex < ey + (p+2))) do lemma
                add_case!(lemma, (sx, ex-1, ex-p:ey-1), (~sy, fy:ex-(p+2), fy))
                add_case!(lemma, (sx, ex-1, ex-p:ey  ), ( sy, fy:ex-(p+2), fy))
                add_case!(lemma, (sx, ex-1,      ey+1), (~sy, fy:ex-(p+2), fy))
            end
            checker("SETZ-TwoSum-1D0-Y", diff_sign & (ey == fy) & (ey > fx + (p+1)) & (ey < ex + (p+2))) do lemma
                add_case!(lemma, (sy, ey-1, ey-p:ex-1), (~sx, fx:ey-(p+2), fx))
                add_case!(lemma, (sy, ey-1, ey-p:ex  ), ( sx, fx:ey-(p+2), fx))
                add_case!(lemma, (sy, ey-1,      ex+1), (~sx, fx:ey-(p+2), fx))
            end

            checker("SETZ-TwoSum-1D1-X", diff_sign & (ex == fx) & (ex == fy + (p+1)) & (ex < ey + (p+1))) do lemma
                add_case!(lemma, (sx, ex-1, ex-(p-1):ey-1), (~sy, fy, fy))
                add_case!(lemma, (sx, ex-1, ex-(p-1):ey  ), ( sy, fy, fy))
                add_case!(lemma, (sx, ex-1,          ey+1), (~sy, fy, fy))
            end
            checker("SETZ-TwoSum-1D1-Y", diff_sign & (ey == fy) & (ey == fx + (p+1)) & (ey < ex + (p+1))) do lemma
                add_case!(lemma, (sy, ey-1, ey-(p-1):ex-1), (~sx, fx, fx))
                add_case!(lemma, (sy, ey-1, ey-(p-1):ex  ), ( sx, fx, fx))
                add_case!(lemma, (sy, ey-1,          ex+1), (~sx, fx, fx))
            end

            checker("SETZ-TwoSum-1AC-X", same_sign & (ex == fy + p) & (fx == ey + 1)) do lemma
                add_case!(lemma, (sx, ex  , ex-(p-2):ey-1), (~sy, fy, fy))
                add_case!(lemma, (sx, ex  , ex-(p-2):ey  ), ( sy, fy, fy))
                add_case!(lemma, (sx, ex  , ey+2    :ex-1), (~sy, fy, fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), (~sy, fy, fy))
            end
            checker("SETZ-TwoSum-1AC-Y", same_sign & (ey == fx + p) & (fy == ex + 1)) do lemma
                add_case!(lemma, (sy, ey  , ey-(p-2):ex-1), (~sx, fx, fx))
                add_case!(lemma, (sy, ey  , ey-(p-2):ex  ), ( sx, fx, fx))
                add_case!(lemma, (sy, ey  , ex+2    :ey-1), (~sx, fx, fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), (~sx, fx, fx))
            end

            checker("SETZ-TwoSum-1BC-X", diff_sign & (ex == fy + p) & (fx == ey + 1) & (ex > fx)) do lemma
                add_case!(lemma, (sx, ex, ex-(p-2):ey-1), (~sy, fy, fy))
                add_case!(lemma, (sx, ex, ex-(p-2):ey  ), ( sy, fy, fy))
                add_case!(lemma, (sx, ex, ey+2    :ex  ), (~sy, fy, fy))
            end
            checker("SETZ-TwoSum-1BC-Y", diff_sign & (ey == fx + p) & (fy == ex + 1) & (ey > fy)) do lemma
                add_case!(lemma, (sy, ey, ey-(p-2):ex-1), (~sx, fx, fx))
                add_case!(lemma, (sy, ey, ey-(p-2):ex  ), ( sx, fx, fx))
                add_case!(lemma, (sy, ey, ex+2    :ey  ), (~sx, fx, fx))
            end

            checker("SETZ-TwoSum-2-X", same_sign & (ex > fy + p) & (fx < ey)) do lemma
                add_case!(lemma, (sx, ex  , ex-(p-1):ex-1), ( ± , fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex+1, ex-(p-2):ey  ), ( ± , fy:ex-p    , fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), ( sy, fy:ex-p    , fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), (~sy, fy:ex-(p+1), fy))
            end
            checker("SETZ-TwoSum-2-Y", same_sign & (ey > fx + p) & (fy < ex)) do lemma
                add_case!(lemma, (sy, ey  , ey-(p-1):ey-1), ( ± , fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey+1, ey-(p-2):ex  ), ( ± , fx:ey-p    , fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), ( sx, fx:ey-p    , fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), (~sx, fx:ey-(p+1), fx))
            end

            checker("SETZ-TwoSum-2A-X", same_sign & (ex > fy + p) & (fx == ey)) do lemma
                add_case!(lemma, (sx, ex  , ex-(p-1):ey-1), ( ± , fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  ,          ey  ), (~sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  , ey+1    :ex-1), ( sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex+1, ex-(p-2):ey-1), ( sy, fy:ex-p    , fy))
                add_case!(lemma, (sx, ex+1, ex-(p-2):ey  ), (~sy, fy:ex-p    , fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), ( sy, fy:ex-p    , fy))
            end
            checker("SETZ-TwoSum-2A-Y", same_sign & (ey > fx + p) & (fy == ex)) do lemma
                add_case!(lemma, (sy, ey  , ey-(p-1):ex-1), ( ± , fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  ,          ex  ), (~sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  , ex+1    :ey-1), ( sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey+1, ey-(p-2):ex-1), ( sx, fx:ey-p    , fx))
                add_case!(lemma, (sy, ey+1, ey-(p-2):ex  ), (~sx, fx:ey-p    , fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), ( sx, fx:ey-p    , fx))
            end

            checker("SETZ-TwoSum-2B0-X", same_sign & (ex == fy + p) & (fx < ey) & (ex > ey + 1)) do lemma
                add_case!(lemma, (sx, ex  , ex-(p-2):ex-1), (±, fy, fy))
                add_case!(lemma, (sx, ex+1, ex-(p-2):ey  ), (±, fy, fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), (±, fy, fy))
            end
            checker("SETZ-TwoSum-2B0-Y", same_sign & (ey == fx + p) & (fy < ex) & (ey > ex + 1)) do lemma
                add_case!(lemma, (sy, ey  , ey-(p-2):ey-1), (±, fx, fx))
                add_case!(lemma, (sy, ey+1, ey-(p-2):ex  ), (±, fx, fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), (±, fx, fx))
            end

            checker("SETZ-TwoSum-2B1-X", same_sign & (ex == fy + p) & (fx + 1 < ey) & (ex == ey + 1)) do lemma
                add_case!(lemma, (sx, ex  , ex-(p-2):ex-2), (±, fy, fy))
                add_case!(lemma, (sx, ex+1, ex-(p-2):ey  ), (±, fy, fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), (±, fy, fy))
            end
            checker("SETZ-TwoSum-2B1-Y", same_sign & (ey == fx + p) & (fy + 1 < ex) & (ey == ex + 1)) do lemma
                add_case!(lemma, (sy, ey  , ey-(p-2):ey-2), (±, fx, fx))
                add_case!(lemma, (sy, ey+1, ey-(p-2):ex  ), (±, fx, fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), (±, fx, fx))
            end

            checker("SETZ-TwoSum-2B2-X", same_sign & (ex == fy + p) & (fx + 1 == ey) & (ex == ey + 1)) do lemma
                add_case!(lemma, (sx, ex  , ex-(p-2):ex-3), (± , fy, fy))
                add_case!(lemma, (sx, ex  ,          ex-2), (sy, fy, fy))
                add_case!(lemma, (sx, ex+1, ex-(p-2):ey  ), (± , fy, fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), (± , fy, fy))
            end
            checker("SETZ-TwoSum-2B2-Y", same_sign & (ey == fx + p) & (fy + 1 == ex) & (ey == ex + 1)) do lemma
                add_case!(lemma, (sy, ey  , ey-(p-2):ey-3), (± , fx, fx))
                add_case!(lemma, (sy, ey  ,          ey-2), (sx, fx, fx))
                add_case!(lemma, (sy, ey+1, ey-(p-2):ex  ), (± , fx, fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), (± , fx, fx))
            end

            checker("SETZ-TwoSum-2AB0-X", same_sign & (ex == fy + p) & (fx == ey) & (ex > ey + 1)) do lemma
                add_case!(lemma, (sx, ex:ex+1, ex-(p-2):ey-1), ( sy, fy, fy))
                add_case!(lemma, (sx, ex:ex+1, ex-(p-2):ey  ), (~sy, fy, fy))
                add_case!(lemma, (sx, ex     , ey+1    :ex-1), ( sy, fy, fy))
                add_case!(lemma, (sx, ex+1   , ex+1         ), ( sy, fy, fy))
            end
            checker("SETZ-TwoSum-2AB0-Y", same_sign & (ey == fx + p) & (fy == ex) & (ey > ex + 1)) do lemma
                add_case!(lemma, (sy, ey:ey+1, ey-(p-2):ex-1), ( sx, fx, fx))
                add_case!(lemma, (sy, ey:ey+1, ey-(p-2):ex  ), (~sx, fx, fx))
                add_case!(lemma, (sy, ey     , ex+1    :ey-1), ( sx, fx, fx))
                add_case!(lemma, (sy, ey+1   , ey+1         ), ( sx, fx, fx))
            end

            checker("SETZ-TwoSum-2AB1-X", same_sign & (ex == fy + p) & (fx == ey) & (ex == ey + 1)) do lemma
                add_case!(lemma, (sx, ex+1, ex-(p-2):ey-1), ( ± , fy, fy))
                add_case!(lemma, (sx, ex+1,          ey  ), (~sy, fy, fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), ( sy, fy, fy))
            end
            checker("SETZ-TwoSum-2AB1-Y", same_sign & (ey == fx + p) & (fy == ex) & (ey == ex + 1)) do lemma
                add_case!(lemma, (sy, ey+1, ey-(p-2):ex-1), ( ± , fx, fx))
                add_case!(lemma, (sy, ey+1,          ex  ), (~sx, fx, fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), ( sx, fx, fx))
            end

            checker("SETZ-TwoSum-3-X", diff_sign & (ex > fy + (p+1)) & (fx < ey)) do lemma
                add_case!(lemma, (sx, ex-1, ex-p    :ey  ), ( ± , fy:ex-(p+2), fy))
                add_case!(lemma, (sx, ex  , ex-(p-1):ex-1), ( ± , fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  ,          ex  ), ( sy, fy:ex-(p+2), fy))
                add_case!(lemma, (sx, ex  ,          ex  ), (~sy, fy:ex-(p+1), fy))
            end
            checker("SETZ-TwoSum-3-Y", diff_sign & (ey > fx + (p+1)) & (fy < ex)) do lemma
                add_case!(lemma, (sy, ey-1, ey-p    :ex  ), ( ± , fx:ey-(p+2), fx))
                add_case!(lemma, (sy, ey  , ey-(p-1):ey-1), ( ± , fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  ,          ey  ), ( sx, fx:ey-(p+2), fx))
                add_case!(lemma, (sy, ey  ,          ey  ), (~sx, fx:ey-(p+1), fx))
            end

            checker("SETZ-TwoSum-3A-X", diff_sign & (ex > fy + (p+1)) & (fx == ey)) do lemma
                add_case!(lemma, (sx, ex-1, ex-p    :ey-1), ( ± , fy:ex-(p+2), fy))
                add_case!(lemma, (sx, ex-1,          ey  ), (~sy, fy:ex-(p+2), fy))
                add_case!(lemma, (sx, ex  , ex-(p-1):ey-1), ( ± , fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  ,          ey  ), (~sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  , ey+1    :ex-1), ( sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  ,          ex  ), ( sy, fy:ex-(p+2), fy))
            end
            checker("SETZ-TwoSum-3A-Y", diff_sign & (ey > fx + (p+1)) & (fy == ex)) do lemma
                add_case!(lemma, (sy, ey-1, ey-p    :ex-1), ( ± , fx:ey-(p+2), fx))
                add_case!(lemma, (sy, ey-1,          ex  ), (~sx, fx:ey-(p+2), fx))
                add_case!(lemma, (sy, ey  , ey-(p-1):ex-1), ( ± , fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  ,          ex  ), (~sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  , ex+1    :ey-1), ( sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  ,          ey  ), ( sx, fx:ey-(p+2), fx))
            end

            checker("SETZ-TwoSum-3B-X", diff_sign & (ex == fy + (p+1)) & (fx < ey)) do lemma
                add_case!(lemma, (sx, ex-1, ex-(p-1):ey), (±, fy, fy))
                add_case!(lemma, (sx, ex  , ex-(p-1):ex), (±, fy, fy))
            end
            checker("SETZ-TwoSum-3B-Y", diff_sign & (ey == fx + (p+1)) & (fy < ex)) do lemma
                add_case!(lemma, (sy, ey-1, ey-(p-1):ex), (±, fx, fx))
                add_case!(lemma, (sy, ey  , ey-(p-1):ey), (±, fx, fx))
            end

            checker("SETZ-TwoSum-3C0-X", diff_sign & (ex == fy + p) & (fx < ey) & (ex > ey + 1)) do lemma
                add_case!(lemma, (sx, ex-1, fy           ), pos_zero)
                add_case!(lemma, (sx, ex  , ex-(p-2):ex-1), ( ± , fy, fy))
                add_case!(lemma, (sx, ex  ,          ex  ), (~sy, fy, fy))
            end
            checker("SETZ-TwoSum-3C0-Y", diff_sign & (ey == fx + p) & (fy < ex) & (ey > ex + 1)) do lemma
                add_case!(lemma, (sy, ey-1, fx           ), pos_zero)
                add_case!(lemma, (sy, ey  , ey-(p-2):ey-1), ( ± , fx, fx))
                add_case!(lemma, (sy, ey  ,          ey  ), (~sx, fx, fx))
            end

            checker("SETZ-TwoSum-3C1-X", diff_sign & (ex == fy + p) & (fx + 1 < ey) & (ex == ey + 1)) do lemma
                add_case!(lemma, (sx, fx:ex-1, fy           ), pos_zero)
                add_case!(lemma, (sx, ex     , ex-(p-2):ex-2), ( ± , fy, fy))
                add_case!(lemma, (sx, ex     ,          ex  ), (~sy, fy, fy))
            end
            checker("SETZ-TwoSum-3C1-Y", diff_sign & (ey == fx + p) & (fy + 1 < ex) & (ey == ex + 1)) do lemma
                add_case!(lemma, (sy, fy:ey-1, fx           ), pos_zero)
                add_case!(lemma, (sy, ey     , ey-(p-2):ey-2), ( ± , fx, fx))
                add_case!(lemma, (sy, ey     ,          ey  ), (~sx, fx, fx))
            end

            checker("SETZ-TwoSum-3C2-X", diff_sign & (ex == fy + p) & (fx + 1 == ey) & (ex == ey + 1)) do lemma
                add_case!(lemma, (sx, fx:ex-1, fy           ), pos_zero)
                add_case!(lemma, (sx, ex     , ex-(p-2):ex-3), ( ± , fy, fy))
                add_case!(lemma, (sx, ex     ,          ex-2), ( sy, fy, fy))
                add_case!(lemma, (sx, ex     ,          ex  ), (~sy, fy, fy))
            end
            checker("SETZ-TwoSum-3C2-Y", diff_sign & (ey == fx + p) & (fy + 1 == ex) & (ey == ex + 1)) do lemma
                add_case!(lemma, (sy, fy:ey-1, fx           ), pos_zero)
                add_case!(lemma, (sy, ey     , ey-(p-2):ey-3), ( ± , fx, fx))
                add_case!(lemma, (sy, ey     ,          ey-2), ( sx, fx, fx))
                add_case!(lemma, (sy, ey     ,          ey  ), (~sx, fx, fx))
            end

            checker("SETZ-TwoSum-3AB-X", diff_sign & (ex == fy + (p+1)) & (fx == ey)) do lemma
                add_case!(lemma, (sx, ex-1:ex, ex-(p-1):ey-1), ( sy, fy, fy))
                add_case!(lemma, (sx, ex-1:ex, ex-(p-1):ey  ), (~sy, fy, fy))
                add_case!(lemma, (sx, ex     , ey+1    :ex  ), ( sy, fy, fy))
            end
            checker("SETZ-TwoSum-3AB-Y", diff_sign & (ey == fx + (p+1)) & (fy == ex)) do lemma
                add_case!(lemma, (sy, ey-1:ey, ey-(p-1):ex-1), ( sx, fx, fx))
                add_case!(lemma, (sy, ey-1:ey, ey-(p-1):ex  ), (~sx, fx, fx))
                add_case!(lemma, (sy, ey     , ex+1    :ey  ), ( sx, fx, fx))
            end

            checker("SETZ-TwoSum-3AC-X", diff_sign & (ex == fy + p) & (fx == ey) & (ex > ey + 1)) do lemma
                add_case!(lemma, (sx, ex-1, fy           ), pos_zero)
                add_case!(lemma, (sx, ex  , ex-(p-2):ey-1), ( sy, fy, fy))
                add_case!(lemma, (sx, ex  , ex-(p-2):ey  ), (~sy, fy, fy))
                add_case!(lemma, (sx, ex  , ey+1    :ex-1), ( sy, fy, fy))
            end
            checker("SETZ-TwoSum-3AC-Y", diff_sign & (ey == fx + p) & (fy == ex) & (ey > ex + 1)) do lemma
                add_case!(lemma, (sy, ey-1, fx           ), pos_zero)
                add_case!(lemma, (sy, ey  , ey-(p-2):ex-1), ( sx, fx, fx))
                add_case!(lemma, (sy, ey  , ey-(p-2):ex  ), (~sx, fx, fx))
                add_case!(lemma, (sy, ey  , ex+1    :ey-1), ( sx, fx, fx))
            end

        end
        #! format: on

        if isempty(checker.covering_lemmas)
            println(stderr,
                "ERROR: Abstract SETZ-TwoSum-$T inputs ($x, $y)" *
                    " are not covered by any lemmas.")
        elseif !isone(length(checker.covering_lemmas))
            println(stderr,
                "WARNING: Abstract SETZ-TwoSum-$T inputs ($x, $y)" *
                    " are covered by multiple lemmas.")
        end
    end

    println("SETZ-TwoSum-$T lemmas:")
    for (name, n) in sort!(collect(lemma_counts))
        println("    $name: $n")
    end
    flush(stdout)

    return nothing
end


function main(
    ::Type{T},
    expected_count::Int,
    expected_crc::UInt32,
) where {T<:AbstractFloat}
    filename = "SETZ-TwoSum-$T.bin"
    filepath = joinpath("data", filename)
    if !isfile(filepath)
        println(stderr,
            "ERROR: Input file $filename not found." *
                " Run `julia GenerateAbstractionData.jl` to" *
                " generate the input files for this program.")
        exit(EXIT_INPUT_FILE_MISSING)
    end
    expected_size = expected_count * sizeof(TwoSumAbstraction{SETZAbstraction})
    valid = (filesize(filepath) == expected_size) &&
        (open(crc32c, filepath) == expected_crc)
    if !valid
        println(stderr,
            "ERROR: Input file $filename is malformed." *
                " Run `julia GenerateAbstractionData.jl` to" *
                " generate the input files for this program.")
        exit(EXIT_INPUT_FILE_MALFORMED)
    end
    two_sum_abstractions =
        Vector{TwoSumAbstraction{SETZAbstraction}}(undef, expected_count)
    read!(filepath, two_sum_abstractions)
    check_setz_two_sum_lemmas(two_sum_abstractions, T)
    println("Successfully checked all SETZ-TwoSum-$T lemmas.")
    flush(stdout)
    return nothing
end


if abspath(PROGRAM_FILE) == @__FILE__
    main(Float16, 3_833_700, 0x66E6D552)
    main(BFloat16, 26_618_866, 0x1DB442CF)
end
