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
        println("WARNING: Unrecognized SELTZO class $s will be ignored.")
        return nothing
    end
end


const CLASS_X = length(ARGS) >= 1 ? parse_seltzo_class(ARGS[1]) : nothing
const CLASS_Y = length(ARGS) >= 2 ? parse_seltzo_class(ARGS[2]) : nothing


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
        @static if (!isnothing(CLASS_X)) && (!isnothing(CLASS_Y))
            if minmax(cx, cy) != minmax(CLASS_X, CLASS_Y)
                continue
            end
        elseif !isnothing(CLASS_X)
            if (cx != CLASS_X) && (cy != CLASS_X)
                continue
            end
        end

        sx, lbx, tbx, ex, fx, gx = unpack(x, T)
        sy, lby, tby, ey, fy, gy = unpack(y, T)

        same_sign = (sx == sy)
        diff_sign = (sx != sy)
        x_zero = (x == pos_zero) | (x == neg_zero)
        y_zero = (y == pos_zero) | (y == neg_zero)
        checker = LemmaChecker(two_sum_abstractions, x, y, T, case_counts)

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

            ##################################################### LEMMA FAMILY L

            # Lemmas in family L apply to situations where the smaller addend
            # fits entirely inside the leading bits of the larger addend.

            # Larger addend is a power of two (general case).
            checker("SELTZO-TwoSum-LS-POW2-G-X",
                same_sign & (cx == POW2) & (~tby) &
                (ex > ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-LS-POW2-G-Y",
                same_sign & (cy == POW2) & (~tbx) &
                (ey > ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gx), pos_zero)
            end

            # Larger addend is a power of two (adjacent case 1).
            checker("SELTZO-TwoSum-LS-POW2-A1-X",
                same_sign & (cx == POW2) & lby & (~tby) &
                (ex == ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-LS-POW2-A1-Y",
                same_sign & (cy == POW2) & lbx & (~tbx) &
                (ey == ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx, gx), pos_zero)
            end

            # Larger addend is a power of two (adjacent case 2).
            checker("SELTZO-TwoSum-LS-POW2-A2-X",
                same_sign & (cx == POW2) & (~lby) & (~tby) &
                (ex == ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey-1, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-LS-POW2-A2-Y",
                same_sign & (cy == POW2) & (~lbx) & (~tbx) &
                (ey == ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex-1, gx), pos_zero)
            end

            # Larger addend has trailing zeros (general case).
            checker("SELTZO-TwoSum-LS-T0-G-X",
                same_sign & (~lbx) & (~tbx) & (cx != POW2) & (~tby) &
                (ex > ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-LS-T0-G-Y",
                same_sign & (~lby) & (~tby) & (cy != POW2) & (~tbx) &
                (ey > ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gy), pos_zero)
            end

            # Larger addend has trailing zeros (adjacent case 1).
            checker("SELTZO-TwoSum-LS-T0-A1-X",
                same_sign & (~lbx) & (~tbx) & (cx != POW2) & lby & (~tby) &
                (ex == ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-LS-T0-A1-Y",
                same_sign & (~lby) & (~tby) & (cy != POW2) & lbx & (~tbx) &
                (ey == ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx, gy), pos_zero)
            end

            # Larger addend has trailing zeros (adjacent case 2).
            checker("SELTZO-TwoSum-LS-T0-A2-X",
                same_sign & (~lbx) & (~tbx) & (cx != POW2) & (~lby) & (~tby) &
                (ex == ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey-1, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-LS-T0-A2-Y",
                same_sign & (~lby) & (~tby) & (cy != POW2) & (~lbx) & (~tbx) &
                (ey == ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex-1, gy), pos_zero)
            end

            # Larger addend has trailing ones (general case).
            checker("SELTZO-TwoSum-LS-T1-G-X",
                same_sign & (~lbx) & tbx & (~tby) &
                (ex > ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-LS-T1-G-Y",
                same_sign & (~lby) & tby & (~tbx) &
                (ey > ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, gy), pos_zero)
            end

            # Larger addend has trailing ones (adjacent case 1).
            checker("SELTZO-TwoSum-LS-T1-A1-X",
                same_sign & (~lbx) & tbx & lby & (~tby) &
                (ex == ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-LS-T1-A1-Y",
                same_sign & (~lby) & tby & lbx & (~tbx) &
                (ey == ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx, gy), pos_zero)
            end

            # Larger addend has trailing ones (adjacent case 2).
            checker("SELTZO-TwoSum-LS-T1-A2-X",
                same_sign & (~lbx) & tbx & (~lby) & (~tby) &
                (ex == ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey-1, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-LS-T1-A2-Y",
                same_sign & (~lby) & tby & (~lbx) & (~tbx) &
                (ey == ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex-1, gy), pos_zero)
            end

            # Larger addend is an all-ones number (general case).
            checker("SELTZO-TwoSum-LD-ALL1-G-X",
                diff_sign & (cx == ALL1) & (~tby) &
                (ex > ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-LD-ALL1-G-Y",
                diff_sign & (cy == ALL1) & (~tbx) &
                (ey > ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, gx), pos_zero)
            end

            # Larger addend is an all-ones number (adjacent case 1).
            checker("SELTZO-TwoSum-LD-ALL1-A1-X",
                diff_sign & (cx == ALL1) & lby & (~tby) &
                (ex == ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-LD-ALL1-A1-Y",
                diff_sign & (cy == ALL1) & lbx & (~tbx) &
                (ey == ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx, gx), pos_zero)
            end

            # Larger addend is an all-ones number (adjacent case 2).
            checker("SELTZO-TwoSum-LD-ALL1-A2-X",
                diff_sign & (cx == ALL1) & (~lby) & (~tby) &
                (ex == ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey-1, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-LD-ALL1-A2-Y",
                diff_sign & (cy == ALL1) & (~lbx) & (~tbx) &
                (ey == ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex-1, gx), pos_zero)
            end

            # Larger addend has trailing zeros (general case).
            checker("SELTZO-TwoSum-LD-T0-G-X",
                diff_sign & lbx & (~tbx) & (~tby) &
                (ex > ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-LD-T0-G-Y",
                diff_sign & lby & (~tby) & (~tbx) &
                (ey > ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, gy), pos_zero)
            end

            # Larger addend has trailing zeros (adjacent case 1).
            checker("SELTZO-TwoSum-LD-T0-A1-X",
                diff_sign & lbx & (~tbx) & lby & (~tby) &
                (ex == ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fy, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-LD-T0-A1-Y",
                diff_sign & lby & (~tby) & lbx & (~tbx) &
                (ey == ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fx, gy), pos_zero)
            end

            # Larger addend has trailing zeros (adjacent case 2).
            checker("SELTZO-TwoSum-LD-T0-A2-X",
                diff_sign & lbx & (~tbx) & (~lby) & (~tby) &
                (ex == ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey-1, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-LD-T0-A2-Y",
                diff_sign & lby & (~tby) & (~lbx) & (~tbx) &
                (ey == ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex-1, gy), pos_zero)
            end

            # Larger addend has trailing ones (general case).
            checker("SELTZO-TwoSum-LD-T1-G-X",
                diff_sign & lbx & tbx & (cx != ALL1) & (~tby) &
                (ex > ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-LD-T1-G-Y",
                diff_sign & lby & tby & (cy != ALL1) & (~tbx) &
                (ey > ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, gy), pos_zero)
            end

            # Larger addend has trailing ones (adjacent case 1).
            checker("SELTZO-TwoSum-LD-T1-A1-X",
                diff_sign & lbx & tbx & (cx != ALL1) & lby & (~tby) &
                (ex == ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-LD-T1-A1-Y",
                diff_sign & lby & tby & (cy != ALL1) & lbx & (~tbx) &
                (ey == ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx, gy), pos_zero)
            end

            # Larger addend has trailing ones (adjacent case 2).
            checker("SELTZO-TwoSum-LD-T1-A2-X",
                diff_sign & lbx & tbx & (cx != ALL1) & (~lby) & (~tby) &
                (ex == ey + 1) & (gy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey-1, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-LD-T1-A2-Y",
                diff_sign & lby & tby & (cy != ALL1) & (~lbx) & (~tbx) &
                (ey == ex + 1) & (gx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex-1, gy), pos_zero)
            end

            ########################################### LEMMA FAMILY POW2-POW2-S

            # Sum of two powers of two (equal exponent case).
            checker("SELTZO-TwoSum-POW2-POW2-SE",
                same_sign & (cx == POW2) & (cy == POW2) &
                (ex == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fx+1, gx+1), pos_zero)
            end

            # Sum of two powers of two (boundary case).
            checker("SELTZO-TwoSum-POW2-POW2-SB-X",
                same_sign & (cx == POW2) & (cy == POW2) &
                (ex == ey + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey+1), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-POW2-SB-Y",
                same_sign & (cy == POW2) & (cx == POW2) &
                (ey == ex + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex+1), pos_zero)
            end

            # Remaining POW2-POW2-S lemmas have been subsumed by L lemmas.

            ########################################### LEMMA FAMILY POW2-POW2-D

            # Difference of two powers of two (equal exponent case).
            checker("SELTZO-TwoSum-POW2-POW2-DE",
                diff_sign & (cx == POW2) & (cy == POW2) &
                (ex == ey)
            ) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end

            # Difference of two powers of two (adjacent case).
            checker("SELTZO-TwoSum-POW2-POW2-DA-X",
                diff_sign & (cx == POW2) & (cy == POW2) &
                (ex == ey + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, fx-1, gx-1), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-POW2-DA-Y",
                diff_sign & (cy == POW2) & (cx == POW2) &
                (ey == ex + 1)
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
                diff_sign & (cx == POW2) & (cy == POW2) &
                (ex == ey + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fx-1, gx-1), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-POW2-DB-Y",
                diff_sign & (cy == POW2) & (cx == POW2) &
                (ey == ex + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fy-1, gy-1), pos_zero)
            end

            ########################################### LEMMA FAMILY ALL1-ALL1-S

            checker("SELTZO-TwoSum-ALL1-ALL1-SE",
                same_sign & (cx == ALL1) & (cy == ALL1) &
                (ex == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex+1, fx+1, gx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-ALL1-ALL1-SA-X",
                same_sign & (cx == ALL1) & (cy == ALL1) &
                (ex == ey + 1)
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sx, 0, 1, ex+1, ey, ey+1),
                    SELTZORange(sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-ALL1-ALL1-SA-Y",
                same_sign & (cy == ALL1) & (cx == ALL1) &
                (ey == ex + 1)
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sy, 0, 1, ey+1, ex, ex+1),
                    SELTZORange(sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-ALL1-ALL1-SG-X",
                same_sign & (cx == ALL1) & (cy == ALL1) &
                (ex > ey + 1) & (ex < ey + (p-1))
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sx, 0, 1, ex+1, ey, ey+1),
                    SELTZORange(sy, 1, 0, fx, fy, fy+1))
            end
            checker("SELTZO-TwoSum-ALL1-ALL1-SG-Y",
                same_sign & (cy == ALL1) & (cx == ALL1) &
                (ey > ex + 1) & (ey < ex + (p-1))
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sy, 0, 1, ey+1, ex, ex+1),
                    SELTZORange(sx, 1, 0, fy, fx, fx+1))
            end

            checker("SELTZO-TwoSum-ALL1-ALL1-SB1-X",
                same_sign & (cx == ALL1) & (cy == ALL1) &
                (ex == ey + (p-1))
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sx, 0, 0, ex+1, fx+1, gx+1),
                    SELTZORange(sy, 1, 0, fx, fy, fy+1))
            end
            checker("SELTZO-TwoSum-ALL1-ALL1-SB1-Y",
                same_sign & (cy == ALL1) & (cx == ALL1) &
                (ey == ex + (p-1))
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sy, 0, 0, ey+1, fy+1, gy+1),
                    SELTZORange(sx, 1, 0, fy, fx, fx+1))
            end

            checker("SELTZO-TwoSum-ALL1-ALL1-SB2-X",
                same_sign & (cx == ALL1) & (cy == ALL1) &
                (ex == ey + p)
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sx, 0, 0, ex+1, fx+1, gx+1),
                    SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-ALL1-ALL1-SB2-Y",
                same_sign & (cy == ALL1) & (cx == ALL1) &
                (ey == ex + p)
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sy, 0, 0, ey+1, fy+1, gy+1),
                    SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            ########################################### LEMMA FAMILY ALL1-ALL1-D

            checker("SELTZO-TwoSum-ALL1-ALL1-DE",
                diff_sign & (cx == ALL1) & (cy == ALL1) &
                (ex == ey)
            ) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end

            checker("SELTZO-TwoSum-ALL1-ALL1-DA1-X",
                diff_sign & (cx == ALL1) & (cy == ALL1) &
                (ex == ey + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fx-1, gx-1), pos_zero)
            end
            checker("SELTZO-TwoSum-ALL1-ALL1-DA1-Y",
                diff_sign & (cy == ALL1) & (cx == ALL1) &
                (ey == ex + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fy-1, gy-1), pos_zero)
            end

            checker("SELTZO-TwoSum-ALL1-ALL1-DA2-X",
                diff_sign & (cx == ALL1) & (cy == ALL1) &
                (ex == ey + 2)
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sx, 0, 1, ex, ey, ey+1),
                    SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-ALL1-ALL1-DA2-Y",
                diff_sign & (cy == ALL1) & (cx == ALL1) &
                (ey == ex + 2)
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sy, 0, 1, ey, ex, ex+1),
                    SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-ALL1-ALL1-DG-X",
                diff_sign & (cx == ALL1) & (cy == ALL1) &
                (ex > ey + 2) & (ex < ey + p)
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sx, 1, 1, ex, ey+1, ey+1),
                    SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-ALL1-ALL1-DG-Y",
                diff_sign & (cy == ALL1) & (cx == ALL1) &
                (ey > ex + 2) & (ey < ex + p)
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sy, 1, 1, ey, ex+1, ex+1),
                    SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-ALL1-ALL1-DB-X",
                diff_sign & (cx == ALL1) & (cy == ALL1) &
                (ex == ey + p)
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sx, 1, 0, ex, ey+1, ey+2),
                    SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-ALL1-ALL1-DB-Y",
                diff_sign & (cy == ALL1) & (cx == ALL1) &
                (ey == ex + p)
            ) do lemma
                add_case!(lemma,
                    SELTZORange(sy, 1, 0, ey, ex+1, ex+2),
                    SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            ####################################################################

            checker("SELTZO-TwoSum-POW2-ALL1-SE",
                same_sign & (cx == POW2) & (cy == ALL1) &
                (ex == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex+1, ey-1, ey), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end

            checker("SELTZO-TwoSum-POW2-ALL1-SA1-X",
                same_sign & (cx == POW2) & (cy == ALL1) &
                (ex == ey + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fx+1, gx+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-POW2-ALL1-SA1-Y",
                same_sign & (cy == POW2) & (cx == ALL1) &
                (ey == ex + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fy+1, gy+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-POW2-ALL1-SA2-X",
                same_sign & (cx == POW2) & (cy == ALL1) &
                (ex == ey + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ey+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-POW2-ALL1-SA2-Y",
                same_sign & (cy == POW2) & (cx == ALL1) &
                (ey == ex + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ex+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-POW2-ALL1-SG-X",
                same_sign & (cx == POW2) & (cy == ALL1) &
                (ex > ey + 2) & (ex < ey + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey+1, ey+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-POW2-ALL1-SG-Y",
                same_sign & (cy == POW2) & (cx == ALL1) &
                (ey > ex + 2) & (ey < ex + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex+1, ex+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-POW2-ALL1-SB-X",
                same_sign & (cx == POW2) & (cy == ALL1) &
                (ex == ey + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey+1, ey+2), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-POW2-ALL1-SB-Y",
                same_sign & (cy == POW2) & (cx == ALL1) &
                (ey == ex + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex+1, ex+2), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            ####################################################################

            checker("SELTZO-TwoSum-POW2-ALL1-DE",
                diff_sign & (cx == POW2) & (cy == ALL1) & (ex == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(~sx, 1, 0, ex-1, fx, fx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-ALL1-DA1-X",
                diff_sign & (cx == POW2) & (cy == ALL1) & (ex == ey + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, fx, fx-p, fx), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-ALL1-DA1-Y",
                diff_sign & (cy == POW2) & (cx == ALL1) & (ey == ex + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, fy, fy-p, fy), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-ALL1-DA2-X",
                diff_sign & (cx == POW2) & (cy == ALL1) & (ex == ey + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, fx-1, gx-1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-POW2-ALL1-DA2-Y",
                diff_sign & (cy == POW2) & (cx == ALL1) & (ey == ex + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, fy-1, gy-1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-POW2-ALL1-DG-X",
                diff_sign & (cx == POW2) & (cy == ALL1) &
                (ex > ey + 2) & (ex < ey + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, ey+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-POW2-ALL1-DG-Y",
                diff_sign & (cy == POW2) & (cx == ALL1) &
                (ey > ex + 2) & (ey < ex + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, ex+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-POW2-ALL1-DB-X",
                diff_sign & (cx == POW2) & (cy == ALL1) & (ex == ey + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ex-1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-POW2-ALL1-DB-Y",
                diff_sign & (cy == POW2) & (cx == ALL1) & (ey == ex + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ey-1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            ####################################################################

            checker("SELTZO-TwoSum-ALL1-POW2-SE",
                same_sign & (cx == ALL1) & (cy == POW2) &
                (ex == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex+1, ey-1, ey), SELTZORange(~sy, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-ALL1-POW2-SG-X",
                same_sign & (cx == ALL1) & (cy == POW2) &
                (ex > ey) & (ex < ey + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, ey), SELTZORange(~sy, 0, 0, fx+1, fx-(p-1), fx+1))
            end
            checker("SELTZO-TwoSum-ALL1-POW2-SG-Y",
                same_sign & (cy == ALL1) & (cx == POW2) &
                (ey > ex) & (ey < ex + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, ex), SELTZORange(~sx, 0, 0, fy+1, fy-(p-1), fy+1))
            end

            checker("SELTZO-TwoSum-ALL1-POW2-SB1-X",
                same_sign & (cx == ALL1) & (cy == POW2) &
                (ex == ey + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey-1, ex+1), SELTZORange(sy, 0, 0, fx+1, fx-(p-1), fx+1))
            end
            checker("SELTZO-TwoSum-ALL1-POW2-SB1-Y",
                same_sign & (cy == ALL1) & (cx == POW2) &
                (ey == ex + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex-1, ey+1), SELTZORange(sx, 0, 0, fy+1, fy-(p-1), fy+1))
            end

            checker("SELTZO-TwoSum-ALL1-POW2-SB2-X",
                same_sign & (cx == ALL1) & (cy == POW2) &
                (ex == ey + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fx+1, gx+1), pos_zero)
            end
            checker("SELTZO-TwoSum-ALL1-POW2-SB2-Y",
                same_sign & (cy == ALL1) & (cx == POW2) &
                (ey == ex + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fy+1, gy+1), pos_zero)
            end

            checker("SELTZO-TwoSum-ALL1-POW2-SB3-X",
                same_sign & (cx == ALL1) & (cy == POW2) &
                (ex == ey + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fx+1, gx+1), SELTZORange(~sy, 0, 0, fx, fx-p, fx))
            end
            checker("SELTZO-TwoSum-ALL1-POW2-SB3-Y",
                same_sign & (cy == ALL1) & (cx == POW2) &
                (ey == ex + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fy+1, gy+1), SELTZORange(~sx, 0, 0, fy, fy-p, fy))
            end

            ####################################################################

            checker("SELTZO-TwoSum-ALL1-POW2-DE",
                diff_sign & (cx == ALL1) & (cy == POW2) & (ex == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fx, fx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-ALL1-POW2-DB1-X",
                diff_sign & (cx == ALL1) & (cy == POW2) &
                (ex == ey + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ey+1), pos_zero)
            end
            checker("SELTZO-TwoSum-ALL1-POW2-DB1-Y",
                diff_sign & (cy == ALL1) & (cx == POW2) &
                (ey == ex + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ex+1), pos_zero)
            end

            checker("SELTZO-TwoSum-ALL1-POW2-DB2-X",
                diff_sign & (cx == ALL1) & (cy == POW2) &
                (ex == ey + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey+1, ey+2), SELTZORange(~sy, 0, 0, ey, ey-p, ey))
            end
            checker("SELTZO-TwoSum-ALL1-POW2-DB2-Y",
                diff_sign & (cy == ALL1) & (cx == POW2) &
                (ey == ex + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex+1, ex+2), SELTZORange(~sx, 0, 0, ex, ex-p, ex))
            end

            ####################################################################

            checker("SELTZO-TwoSum-R1R0-ONE1-D1-X",
                diff_sign & (cx == R1R0) & (cy == ONE1) &
                (ex > fy + (p-1)) & (ey > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-R1R0-ONE1-D1-Y",
                diff_sign & (cy == R1R0) & (cx == ONE1) &
                (ey > fx + (p-1)) & (ex > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-R1R0-ALL1-D1-X",
                diff_sign & (cx == R1R0) & (cy == ALL1) &
                (ex > ey + 2) & (ey + 1 > gx)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey+1, gx), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-R1R0-ALL1-D1-Y",
                diff_sign & (cy == R1R0) & (cx == ALL1) &
                (ey > ex + 2) & (ex + 1 > gy)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex+1, gy), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-R0R1-POW2-S1-X",
                same_sign & (cx == R0R1) & (cy == POW2) &
                (ex == ey + 1) & (ex == fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex-p, ex), pos_zero)
            end
            checker("SELTZO-TwoSum-R0R1-POW2-S1-Y",
                same_sign & (cy == R0R1) & (cx == POW2) &
                (ey == ex + 1) & (ey == fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey-p, ey), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE0-POW2-S1-X",
                same_sign & (cx == ONE0) & (cy == POW2) &
                (fx == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex-p, ex), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE0-POW2-S1-Y",
                same_sign & (cy == ONE0) & (cx == POW2) &
                (fy == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey-p, ey), pos_zero)
            end

            checker("SELTZO-TwoSum-R0R1-R1R0-S1-X",
                same_sign & (cx == R0R1) & (cy == R1R0) &
                (ex == ey + 2) & (ey == fx + 1) & (fx == fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx+1, gx-1), pos_zero)
            end
            checker("SELTZO-TwoSum-R0R1-R1R0-S1-Y",
                same_sign & (cy == R0R1) & (cx == R1R0) &
                (ey == ex + 2) & (ex == fy + 1) & (fy == fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy+1, gy-1), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE1-R1R0-D1-X",
                diff_sign & (cx == ONE1) & (cy == R1R0) &
                (fx == ey) & (ex == gy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey-1, ex-(p-1)), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE1-R1R0-D1-Y",
                diff_sign & (cy == ONE1) & (cx == R1R0) &
                (fy == ex) & (ey == gx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex-1, ey-(p-1)), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-R1R0-S1-X",
                same_sign & (cx == POW2) & (cy == R1R0) &
                (ex == ey + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ex-(p-1), ex-(p-2)), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-POW2-R1R0-S1-Y",
                same_sign & (cy == POW2) & (cx == R1R0) &
                (ey == ex + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ey-(p-1), ey-(p-2)), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-R0R1-R1R0-S2-X",
                same_sign & (cx == R0R1) & (cy == R1R0) &
                (ex > ey + 1) & (fx == fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey+1), pos_zero)
            end
            checker("SELTZO-TwoSum-R0R1-R1R0-S2-Y",
                same_sign & (cy == R0R1) & (cx == R1R0) &
                (ey > ex + 1) & (fy == fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex+1), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-ONE1-S1-X",
                same_sign & (cx == POW2) & (cy == ONE1) &
                (ex == ey + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey+1, ey+2), SELTZORange(~sy, 1, 0, ey-1, fy-1, fy))
            end
            checker("SELTZO-TwoSum-POW2-ONE1-S1-Y",
                same_sign & (cy == POW2) & (cx == ONE1) &
                (ey == ex + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex+1, ex+2), SELTZORange(~sx, 1, 0, ex-1, fx-1, fx))
            end

            checker("SELTZO-TwoSum-ALL1-R1R0-S1-X",
                same_sign & (cx == ALL1) & (cy == R1R0) &
                (ex > ey) & (ex < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, gy), SELTZORange(~sy, 0, 0, fx+1, fx-(p-1), fx+1))
            end
            checker("SELTZO-TwoSum-ALL1-R1R0-S1-Y",
                same_sign & (cy == ALL1) & (cx == R1R0) &
                (ey > ex) & (ey < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, gx), SELTZORange(~sx, 0, 0, fy+1, fy-(p-1), fy+1))
            end

            checker("SELTZO-TwoSum-POW2-ONE1-S2-X",
                same_sign & (cx == POW2) & (cy == ONE1) &
                (ex == ey + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey+1), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-POW2-ONE1-S2-Y",
                same_sign & (cy == POW2) & (cx == ONE1) &
                (ey == ex + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex+1), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ALL1-R1R0-D1-X",
                diff_sign & (cx == ALL1) & (cy == R1R0) &
                (ex == ey + (p-1)) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey+1, ey+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-ALL1-R1R0-D1-Y",
                diff_sign & (cy == ALL1) & (cx == R1R0) &
                (ey == ex + (p-1)) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex+1, ex+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-POW2-R1R0-S2-X",
                same_sign & (cx == POW2) & (cy == R1R0) &
                (ex > ey + 2) & (ex < ey + p) & (ex > fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey+1, ey+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-POW2-R1R0-S2-Y",
                same_sign & (cy == POW2) & (cx == R1R0) &
                (ey > ex + 2) & (ey < ex + p) & (ey > fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex+1, ex+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-R1R0-ONE1-S1-X",
                same_sign & (cx == R1R0) & (cy == ONE1) &
                (ex == ey + p) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex-p, ex), SELTZORange(~sy, 1, 0, ey-1, fy-1, gy))
            end
            checker("SELTZO-TwoSum-R1R0-ONE1-S1-Y",
                same_sign & (cy == R1R0) & (cx == ONE1) &
                (ey == ex + p) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey-p, ey), SELTZORange(~sx, 1, 0, ex-1, fx-1, gx))
            end

            checker("SELTZO-TwoSum-ONE0-R0R1-D1-X",
                diff_sign & (cx == ONE0) & (cy == R0R1) &
                (ex == ey + (p-1)) & (ex < fx + (p-2)) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey+1), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-ONE0-R0R1-D1-Y",
                diff_sign & (cy == ONE0) & (cx == R0R1) &
                (ey == ex + (p-1)) & (ey < fy + (p-2)) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex+1), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-R1R0-R1R0-D1-X",
                diff_sign & (cx == R1R0) & (cy == R1R0) &
                (ex == ey + p) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, gx, gx), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-R1R0-R1R0-D1-Y",
                diff_sign & (cy == R1R0) & (cx == R1R0) &
                (ey == ex + p) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, gy, gy), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-R0R1-R1R0-S3-X",
                same_sign & (cx == R0R1) & (cy == R1R0) &
                (ex > fx + 2) & (fx + 1 > ey) & (ex < fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, gx, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-R0R1-R1R0-S3-Y",
                same_sign & (cy == R0R1) & (cx == R1R0) &
                (ey > fy + 2) & (fy + 1 > ex) & (ey < fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, gy, gx), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE1-R1R0-D2-X",
                diff_sign & (cx == ONE1) & (cy == R1R0) &
                (ey > fx) & (ex > fy + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, gx), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-ONE1-R1R0-D2-Y",
                diff_sign & (cy == ONE1) & (cx == R1R0) &
                (ex > fy) & (ey > fx + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, gy), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-R1R0-ONE1-D2-X",
                diff_sign & (cx == R1R0) & (cy == ONE1) &
                (ex == ey + p) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx+1, gx), SELTZORange(~sy, 1, 0, ey-1, fy-1, gy))
            end
            checker("SELTZO-TwoSum-R1R0-ONE1-D2-Y",
                diff_sign & (cy == R1R0) & (cx == ONE1) &
                (ey == ex + p) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy+1, gy), SELTZORange(~sx, 1, 0, ex-1, fx-1, gx))
            end

            checker("SELTZO-TwoSum-ALL1-ONE1-S1-X",
                same_sign & (cx == ALL1) & (cy == ONE1) &
                (ex == ey + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ex-(p-1), ex+1), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-ALL1-ONE1-S1-Y",
                same_sign & (cy == ALL1) & (cx == ONE1) &
                (ey == ex + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ey-(p-1), ey+1), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ONE1-ONE1-D1-X",
                diff_sign & (cx == ONE1) & (cy == ONE1) &
                (ey == fx) & (ex > fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex-p, ex), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-ONE1-ONE1-D1-Y",
                diff_sign & (cy == ONE1) & (cx == ONE1) &
                (ex == fy) & (ey > fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey-p, ey), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-MM10-POW2-S1-X",
                same_sign & (cx == MM10) & (cy == POW2) &
                (ex == ey + 1) & (ex == fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, gx, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-MM10-POW2-S1-Y",
                same_sign & (cy == MM10) & (cx == POW2) &
                (ey == ex + 1) & (ey == fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, gy, gy), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-ONE0-S1-X",
                same_sign & (cx == POW2) & (cy == ONE0) &
                (ex > ey + 1) & (ex < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-ONE0-S1-Y",
                same_sign & (cy == POW2) & (cx == ONE0) &
                (ey > ex + 1) & (ey < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-ONE1-ALL1-D1-X",
                diff_sign & (cx == ONE1) & (cy == ALL1) &
                (ex == ey + 2) & (ey > fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, fx, fx), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-ONE1-ALL1-D1-Y",
                diff_sign & (cy == ONE1) & (cx == ALL1) &
                (ey == ex + 2) & (ex > fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, fy, fy), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-POW2-R0R1-D1-X",
                diff_sign & (cx == POW2) & (cy == R0R1) &
                (ex == ey + (p+1)) & (ey > fy + 2) & (ey < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ex-1), SELTZORange(~sy, 1, 0, ey-1, fy, ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-R0R1-D1-Y",
                diff_sign & (cy == POW2) & (cx == R0R1) &
                (ey == ex + (p+1)) & (ex > fx + 2) & (ex < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ey-1), SELTZORange(~sx, 1, 0, ex-1, fx, ex-(p-1)))
            end

            checker("SELTZO-TwoSum-R0R1-R0R1-D1-X",
                diff_sign & (cx == R0R1) & (cy == R0R1) &
                (ex == ey + (p-1)) & (ex == fx + (p-2)) & (ey < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fx), SELTZORange(sy, 1, 0, fy, ey-p, ey-(p-1)))
            end
            checker("SELTZO-TwoSum-R0R1-R0R1-D1-Y",
                diff_sign & (cy == R0R1) & (cx == R0R1) &
                (ey == ex + (p-1)) & (ey == fy + (p-2)) & (ex < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fy), SELTZORange(sx, 1, 0, fx, ex-p, ex-(p-1)))
            end

            checker("SELTZO-TwoSum-R1R0-ONE1-S2-X",
                same_sign & (cx == R1R0) & (cy == ONE1) &
                (ex > fy + p-2) & (gx == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ex-(p-1), ex+1), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-R1R0-ONE1-S2-Y",
                same_sign & (cy == R1R0) & (cx == ONE1) &
                (ey > fx + p-2) & (gy == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ey-(p-1), ey+1), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ONE1-R1R0-D3-X",
                diff_sign & (cx == ONE1) & (cy == R1R0) &
                (fx == ey) & (ex > fy + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fx-1, gx), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-ONE1-R1R0-D3-Y",
                diff_sign & (cy == ONE1) & (cx == R1R0) &
                (fy == ex) & (ey > fx + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fy-1, gy), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-POW2-R0R1-D2-X",
                diff_sign & (cx == POW2) & (cy == R0R1) &
                (ex == ey + (p+1)) & (ey == fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ex-1), SELTZORange(~sy, 0, 0, ey-1, ey-(p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-R0R1-D2-Y",
                diff_sign & (cy == POW2) & (cx == R0R1) &
                (ey == ex + (p+1)) & (ex == fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ey-1), SELTZORange(~sx, 0, 0, ex-1, ex-(p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-POW2-R0R1-D3-X",
                diff_sign & (cx == POW2) & (cy == R0R1) &
                (ex > ey + 1) & (ex < ey + p) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey-1, ey), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-POW2-R0R1-D3-Y",
                diff_sign & (cy == POW2) & (cx == R0R1) &
                (ey > ex + 1) & (ey < ex + p) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex-1, ex), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ALL1-TWO1-S1-X",
                same_sign & (cx == ALL1) & (cy == TWO1) &
                (ex == ey + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, ex+1), SELTZORange(sy, 1, 0, fy, fy-2, fy-1))
            end
            checker("SELTZO-TwoSum-ALL1-TWO1-S1-Y",
                same_sign & (cy == ALL1) & (cx == TWO1) &
                (ey == ex + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, ey+1), SELTZORange(sx, 1, 0, fx, fx-2, fx-1))
            end

            checker("SELTZO-TwoSum-ONE1-TWO1-D1-X",
                diff_sign & (cx == ONE1) & (cy == TWO1) &
                (ex == fy + p) & (fx == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ex-p, ex-(p-1)), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-ONE1-TWO1-D1-Y",
                diff_sign & (cy == ONE1) & (cx == TWO1) &
                (ey == fx + p) & (fy == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ey-p, ey-(p-1)), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-MM01-ONE1-D1-X",
                diff_sign & (cx == MM01) & (cy == ONE1) &
                (ex == ey + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, gx), SELTZORange(~sy, 1, 0, ey-1, fy-1, gy))
            end
            checker("SELTZO-TwoSum-MM01-ONE1-D1-Y",
                diff_sign & (cy == MM01) & (cx == ONE1) &
                (ey == ex + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, gy), SELTZORange(~sx, 1, 0, ex-1, fx-1, gx))
            end

            checker("SELTZO-TwoSum-POW2-G01-D1-X",
                diff_sign & (cx == POW2) & (cy == G01) &
                (ex == ey + (p+1)) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ex-1), SELTZORange(~sy, 1, 0, ey-1, fy, ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-G01-D1-Y",
                diff_sign & (cy == POW2) & (cx == G01) &
                (ey == ex + (p+1)) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ey-1), SELTZORange(~sx, 1, 0, ex-1, fx, ex-(p-1)))
            end

            checker("SELTZO-TwoSum-POW2-ONE0-S2-X",
                same_sign & (cx == POW2) & (cy == ONE0) &
                (ex == ey + 2) & (ex == fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey+1), SELTZORange(sy, 0, 0, fx-1, fx-(p+1), fx-1))
            end
            checker("SELTZO-TwoSum-POW2-ONE0-S2-Y",
                same_sign & (cy == POW2) & (cx == ONE0) &
                (ey == ex + 2) & (ey == fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex+1), SELTZORange(sx, 0, 0, fy-1, fy-(p+1), fy-1))
            end

            checker("SELTZO-TwoSum-POW2-R0R1-S1-X",
                same_sign & (cx == POW2) & (cy == R0R1) &
                (ex > ey + 1) & (ex < fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gy), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-R0R1-S1-Y",
                same_sign & (cy == POW2) & (cx == R0R1) &
                (ey > ex + 1) & (ey < fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gx), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-R0R1-ONE1-S1-X",
                same_sign & (cx == R0R1) & (cy == ONE1) &
                (ex == ey + 1) & (ex == fx + (p-1)) & (ey == fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex-2, ex-(p-3)), pos_zero)
            end
            checker("SELTZO-TwoSum-R0R1-ONE1-S1-Y",
                same_sign & (cy == R0R1) & (cx == ONE1) &
                (ey == ex + 1) & (ey == fy + (p-1)) & (ex == fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey-2, ey-(p-3)), pos_zero)
            end

            checker("SELTZO-TwoSum-R0R1-ONE1-D1-X",
                diff_sign & (cx == R0R1) & (cy == ONE1) &
                (ex == ey + (p-1)) & (fx == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex-p, ex), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-R0R1-ONE1-D1-Y",
                diff_sign & (cy == R0R1) & (cx == ONE1) &
                (ey == ex + (p-1)) & (fy == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey-p, ey), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-R1R0-R0R1-D1-X",
                diff_sign & (cx == R1R0) & (cy == R0R1) &
                (ex == ey + p) & (ex > gx + 1) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, gx, gx), SELTZORange(~sy, 1, 0, ey-1, fy-1, fy))
            end
            checker("SELTZO-TwoSum-R1R0-R0R1-D1-Y",
                diff_sign & (cy == R1R0) & (cx == R0R1) &
                (ey == ex + p) & (ey > gy + 1) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, gy, gy), SELTZORange(~sx, 1, 0, ex-1, fx-1, fx))
            end

            checker("SELTZO-TwoSum-G01-POW2-S1-X",
                same_sign & (cx == G01) & (cy == POW2) &
                (ex == ey) & (ex < gx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fx, gx), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-G01-POW2-S1-Y",
                same_sign & (cy == G01) & (cx == POW2) &
                (ey == ex) & (ey < gy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fy, gy), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-G10-MM10-D1-X",
                diff_sign & (cx == G10) & (cy == MM10) &
                (ex == ey + (p-1)) & (ey == gy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, gx), SELTZORange(sy, 0, 0, gy+1, gy-1, gy-2))
            end
            checker("SELTZO-TwoSum-G10-MM10-D1-Y",
                diff_sign & (cy == G10) & (cx == MM10) &
                (ey == ex + (p-1)) & (ex == gx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, gy), SELTZORange(sx, 0, 0, gx+1, gx-1, gx-2))
            end

            checker("SELTZO-TwoSum-MM01-R1R0-S1-X",
                same_sign & (cx == MM01) & (cy == R1R0) &
                (ex < ey + (p-3)) & (ey == fx) & (ex > fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, gx, gx), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-MM01-R1R0-S1-Y",
                same_sign & (cy == MM01) & (cx == R1R0) &
                (ey < ex + (p-3)) & (ex == fy) & (ey > fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, gy, gy), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-POW2-R1R0-D1-X",
                diff_sign & (cx == POW2) & (cy == R1R0) &
                (ex == ey + (p-1)) & (ey == fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-R1R0-D1-Y",
                diff_sign & (cy == POW2) & (cx == R1R0) &
                (ey == ex + (p-1)) & (ex == fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ex), pos_zero)
            end

            checker("SELTZO-TwoSum-R1R0-R1R0-D2-X",
                diff_sign & (cx == R1R0) & (cy == R1R0) &
                (ex == ey + 2) & (ey == fx + 1) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, ey), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-R1R0-R1R0-D2-Y",
                diff_sign & (cy == R1R0) & (cx == R1R0) &
                (ey == ex + 2) & (ex == fy + 1) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, ex), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-POW2-ONE1-S3-X",
                same_sign & (cx == POW2) & (cy == ONE1) &
                (ex < ey + (p-1)) & (ex > fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, ey), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-POW2-ONE1-S3-Y",
                same_sign & (cy == POW2) & (cx == ONE1) &
                (ey < ex + (p-1)) & (ey > fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, ex), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ONE1-ONE1-D2-X",
                diff_sign & (cx == ONE1) & (cy == ONE1) &
                (ey == fx + 2) & (ex > fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fx+1, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-ONE1-ONE1-D2-Y",
                diff_sign & (cy == ONE1) & (cx == ONE1) &
                (ex == fy + 2) & (ey > fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fy+1, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-R1R0-MM10-D1-X",
                diff_sign & (cx == R1R0) & (cy == MM10) &
                (ex == ey + (p-1)) & (ex > fx + 2) & (ey == fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx+1, gx), SELTZORange(sy, 0, 0, fy, fy-2, fy-2))
            end
            checker("SELTZO-TwoSum-R1R0-MM10-D1-Y",
                diff_sign & (cy == R1R0) & (cx == MM10) &
                (ey == ex + (p-1)) & (ey > fy + 2) & (ex == fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy+1, gy), SELTZORange(sx, 0, 0, fx, fx-2, fx-2))
            end

            checker("SELTZO-TwoSum-ONE1-ONE1-D3-X",
                diff_sign & (cx == ONE1) & (cy == ONE1) &
                (fx == ey) & (ex == fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ex-(p+1), ex-1), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE1-ONE1-D3-Y",
                diff_sign & (cy == ONE1) & (cx == ONE1) &
                (fy == ex) & (ey == fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ey-(p+1), ey-1), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE1-G10-D1-X",
                diff_sign & (cx == ONE1) & (cy == G10) &
                (ex > fy + (p+1)) & (ey > fx) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, gx), SELTZORange(~sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, gx), SELTZORange(~sy, 0, 0, fy, gy, gy))
            end
            checker("SELTZO-TwoSum-ONE1-G10-D1-Y",
                diff_sign & (cy == ONE1) & (cx == G10) &
                (ey > fx + (p+1)) & (ex > fy) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, gy), SELTZORange(~sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, gy), SELTZORange(~sx, 0, 0, fx, gx, gx))
            end

            checker("SELTZO-TwoSum-POW2-R0R1-D4-X",
                diff_sign & (cx == POW2) & (cy == R0R1) &
                (ex == ey + (p+1)) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ex-1), SELTZORange(~sy, 1, 0, ey-1, fy-1, fy))
            end
            checker("SELTZO-TwoSum-POW2-R0R1-D4-Y",
                diff_sign & (cy == POW2) & (cx == R0R1) &
                (ey == ex + (p+1)) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ey-1), SELTZORange(~sx, 1, 0, ex-1, fx-1, fx))
            end

            checker("SELTZO-TwoSum-ONE1-ALL1-D2-X",
                diff_sign & (cx == ONE1) & (cy == ALL1) &
                (ey == fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey-1, ey), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-ONE1-ALL1-D2-Y",
                diff_sign & (cy == ONE1) & (cx == ALL1) &
                (ex == fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex-1, ex), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-POW2-R1R0-D2-X",
                diff_sign & (cx == POW2) & (cy == R1R0) &
                (ex == ey + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ex-1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-POW2-R1R0-D2-Y",
                diff_sign & (cy == POW2) & (cx == R1R0) &
                (ey == ex + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ey-1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-G10-POW2-S1-X",
                same_sign & (cx == G10) & (cy == POW2) &
                (ex < ey + (p-1)) & (gx > ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-G10-POW2-S1-Y",
                same_sign & (cy == G10) & (cx == POW2) &
                (ey < ex + (p-1)) & (gy > ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex), pos_zero)
            end

            checker("SELTZO-TwoSum-R1R0-ONE1-D3-X",
                diff_sign & (cx == R1R0) & (cy == ONE1) &
                (fx + 1 > ey) & (ex > fx + 2) & (ex < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx+1, fy), pos_zero)
            end
            checker("SELTZO-TwoSum-R1R0-ONE1-D3-Y",
                diff_sign & (cy == R1R0) & (cx == ONE1) &
                (fy + 1 > ex) & (ey > fy + 2) & (ey < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy+1, fx), pos_zero)
            end

            checker("SELTZO-TwoSum-R0R1-POW2-S2-X",
                same_sign & (cx == R0R1) & (cy == POW2) &
                (ex == ey) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ex-(p-1), ex+1), SELTZORange(sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-R0R1-POW2-S2-Y",
                same_sign & (cy == R0R1) & (cx == POW2) &
                (ey == ex) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ey-(p-1), ey+1), SELTZORange(sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-R1R0-ONE1-S3-X",
                same_sign & (cx == R1R0) & (cy == ONE1) &
                (ex == fy + (p-1)) & (fx > ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy+1), pos_zero)
            end
            checker("SELTZO-TwoSum-R1R0-ONE1-S3-Y",
                same_sign & (cy == R1R0) & (cx == ONE1) &
                (ey == fx + (p-1)) & (fy > ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE1-POW2-D1-X",
                diff_sign & (cx == ONE1) & (cy == POW2) &
                (ex == ey + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx-1, fx), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE1-POW2-D1-Y",
                diff_sign & (cy == ONE1) & (cx == POW2) &
                (ey == ex + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy-1, fy), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE0-R1R0-D1-X",
                diff_sign & (cx == ONE0) & (cy == R1R0) &
                (ex == ey + p) & (ex == fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-ONE0-R1R0-D1-Y",
                diff_sign & (cy == ONE0) & (cx == R1R0) &
                (ey == ex + p) & (ey == fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-TWO1-ONE1-D1-X",
                diff_sign & (cx == TWO1) & (cy == ONE1) &
                (ey == fx) & (ex > fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx-1, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-TWO1-ONE1-D1-Y",
                diff_sign & (cy == TWO1) & (cx == ONE1) &
                (ex == fy) & (ey > fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy-1, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-TWO1-ONE1-D2-X",
                diff_sign & (cx == TWO1) & (cy == ONE1) &
                 (ey + 1 == fx) & (ex > fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, gx+1), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-TWO1-ONE1-D2-Y",
                diff_sign & (cy == TWO1) & (cx == ONE1) &
                 (ex + 1 == fy) & (ey > fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, gy+1), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ALL1-R1R0-D2-X",
                diff_sign & (cx == ALL1) & (cy == R1R0) &
                (ex == ey) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-(p-1), fx-(p-1), gx-(p-1)), pos_zero)
            end
            checker("SELTZO-TwoSum-ALL1-R1R0-D2-Y",
                diff_sign & (cy == ALL1) & (cx == R1R0) &
                (ey == ex) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-(p-1), fy-(p-1), gy-(p-1)), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-R0R1-S2-X",
                same_sign & (cx == POW2) & (cy == R0R1) &
                (ex == ey + p) & (ey == fx) & (ey > fy + 2) & (ey < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx+1, fx+2), SELTZORange(~sy, 1, 0, ey-1, fy, ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-R0R1-S2-Y",
                same_sign & (cy == POW2) & (cx == R0R1) &
                (ey == ex + p) & (ex == fy) & (ex > fx + 2) & (ex < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy+1, fy+2), SELTZORange(~sx, 1, 0, ex-1, fx, ex-(p-1)))
            end

            checker("SELTZO-TwoSum-POW2-G00-S1-X",
                same_sign & (cx == POW2) & (cy == G00) &
                (ex == gy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gy+2:fy), SELTZORange(sy, 0, 0, fx, fx-p, fx))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gy+2:fy-1), SELTZORange(~sy, 0, 0, fx, fx-p, fx))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy+1), SELTZORange(~sy, 0, 0, fx, fx-p, fx))
            end
            checker("SELTZO-TwoSum-POW2-G00-S1-Y",
                same_sign & (cy == POW2) & (cx == G00) &
                (ey == gx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gx+2:fx), SELTZORange(sx, 0, 0, fy, fy-p, fy))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gx+2:fx-1), SELTZORange(~sx, 0, 0, fy, fy-p, fy))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx+1), SELTZORange(~sx, 0, 0, fy, fy-p, fy))
            end

            checker("SELTZO-TwoSum-POW2-R0R1-S3-X",
                same_sign & (cx == POW2) & (cy == R0R1) &
                (ex == ey + p) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ex-(p-1), ex-(p-2)), SELTZORange(~sy, 1, 0, ey-1, ey-p, ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-R0R1-S3-Y",
                same_sign & (cy == POW2) & (cx == R0R1) &
                (ey == ex + p) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ey-(p-1), ey-(p-2)), SELTZORange(~sx, 1, 0, ex-1, ex-p, ex-(p-1)))
            end

            checker("SELTZO-TwoSum-R0R1-POW2-S3-X",
                same_sign & (cx == R0R1) & (cy == POW2) &
                (ex == ey) & (ex < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fx+1, gx), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-R0R1-POW2-S3-Y",
                same_sign & (cy == R0R1) & (cx == POW2) &
                (ey == ex) & (ey < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fy+1, gy), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-ALL1-ONE1-D1-X",
                diff_sign & (cx == ALL1) & (cy == ONE1) &
                (ex == ey) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fy, fx+1), pos_zero)
            end
            checker("SELTZO-TwoSum-ALL1-ONE1-D1-Y",
                diff_sign & (cy == ALL1) & (cx == ONE1) &
                (ey == ex) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fx, fy+1), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-R0R1-S4-X",
                same_sign & (cx == POW2) & (cy == R0R1) &
                (ex == ey + (p-1)) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey+1), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-POW2-R0R1-S4-Y",
                same_sign & (cy == POW2) & (cx == R0R1) &
                (ey == ex + (p-1)) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex+1), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-POW2-G11-S1-X",
                same_sign & (cx == POW2) & (cy == G11) &
                (ex > ey + 1) & (ex == gy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, gy+1:fy), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-G11-S1-Y",
                same_sign & (cy == POW2) & (cx == G11) &
                (ey > ex + 1) & (ey == gx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, gx+1:fx), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-MM10-POW2-S2-X",
                same_sign & (cx == MM10) & (cy == POW2) &
                (ex == ey) & (ex == gx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fx, gx+1), SELTZORange(sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-MM10-POW2-S2-Y",
                same_sign & (cy == MM10) & (cx == POW2) &
                (ey == ex) & (ey == gy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fy, gy+1), SELTZORange(sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-ONE1-ONE1-D4-X",
                diff_sign & (cx == ONE1) & (cy == ONE1) &
                (ex < ey + (p-1)) & (fx > ey) & (ex > fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx-1, ey), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-ONE1-ONE1-D4-Y",
                diff_sign & (cy == ONE1) & (cx == ONE1) &
                (ey < ex + (p-1)) & (fy > ex) & (ey > fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy-1, ex), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-POW2-TWO1-D1-X",
                diff_sign & (cx == POW2) & (cy == TWO1) &
                (ex == ey + 1) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ey-1, fy, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-TWO1-D1-Y",
                diff_sign & (cy == POW2) & (cx == TWO1) &
                (ey == ex + 1) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ex-1, fx, gx), pos_zero)
            end

            checker("SELTZO-TwoSum-MM01-ONE1-S1-X",
                same_sign & (cx == MM01) & (cy == ONE1) &
                (ey == fx + 1) & (ex > fy + (p-2)) & (ex < fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fx-1, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-MM01-ONE1-S1-Y",
                same_sign & (cy == MM01) & (cx == ONE1) &
                (ex == fy + 1) & (ey > fx + (p-2)) & (ey < fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fy-1, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-POW2-R0R1-D5-X",
                diff_sign & (cx == POW2) & (cy == R0R1) &
                (ex == ey + 1) & (ex == fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-2, ex-(p+1), ex-p), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-R0R1-D5-Y",
                diff_sign & (cy == POW2) & (cx == R0R1) &
                (ey == ex + 1) & (ey == fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-2, ey-(p+1), ey-p), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-TWO1-S1-X",
                same_sign & (cx == POW2) & (cy == TWO1) &
                (ex < ey + (p-1)) & (ex > fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, ey), SELTZORange(sy, 1, 0, fy, fy-2, fy-1))
            end
            checker("SELTZO-TwoSum-POW2-TWO1-S1-Y",
                same_sign & (cy == POW2) & (cx == TWO1) &
                (ey < ex + (p-1)) & (ey > fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, ex), SELTZORange(sx, 1, 0, fx, fx-2, fx-1))
            end

            checker("SELTZO-TwoSum-POW2-R0R1-D6-X",
                diff_sign & (cx == POW2) & (cy == R0R1) &
                (ex == ey + 1) & (ex > fy + 3) & (ex < fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ey-1, fy, ey-(p-1)), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-R0R1-D6-Y",
                diff_sign & (cy == POW2) & (cx == R0R1) &
                (ey == ex + 1) & (ey > fx + 3) & (ey < fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ex-1, fx, ex-(p-1)), pos_zero)
            end

            checker("SELTZO-TwoSum-ALL1-R1R0-D3-X",
                diff_sign & (cx == ALL1) & (cy == R1R0) &
                (ex == ey) & (ey < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, fy, ey-p, ey-(p-1)), pos_zero)
            end
            checker("SELTZO-TwoSum-ALL1-R1R0-D3-Y",
                diff_sign & (cy == ALL1) & (cx == R1R0) &
                (ey == ex) & (ex < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, fx, ex-p, ex-(p-1)), pos_zero)
            end

            checker("SELTZO-TwoSum-TWO1-R1R0-D1-X",
                diff_sign & (cx == TWO1) & (cy == R1R0) &
                (ex > fy + p) & (ey + 1 == fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx-1, gx), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-TWO1-R1R0-D1-Y",
                diff_sign & (cy == TWO1) & (cx == R1R0) &
                (ey > fx + p) & (ex + 1 == fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy-1, gy), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-TWO1-R1R0-D2-X",
                diff_sign & (cx == TWO1) & (cy == R1R0) &
                (ex > fy + p) & (ey + 2 == fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, gx+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-TWO1-R1R0-D2-Y",
                diff_sign & (cy == TWO1) & (cx == R1R0) &
                (ey > fx + p) & (ex + 2 == fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, gy+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-R1R0-R1R0-D3-X",
                diff_sign & (cx == R1R0) & (cy == R1R0) &
                (ex > fy + p) & (ex < ey + p) & (fx > ey) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx+1, ey+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-R1R0-R1R0-D3-Y",
                diff_sign & (cy == R1R0) & (cx == R1R0) &
                (ey > fx + p) & (ey < ex + p) & (fy > ex) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy+1, ex+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-R1R0-ONE1-S4-X",
                same_sign & (cx == R1R0) & (cy == ONE1) &
                (ey > fx + 1) & (ex < fx + (p-1)) & (ex > fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey-1, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-R1R0-ONE1-S4-Y",
                same_sign & (cy == R1R0) & (cx == ONE1) &
                (ex > fy + 1) & (ey < fy + (p-1)) & (ey > fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex-1, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ONE1-R0R1-D1-X",
                diff_sign & (cx == ONE1) & (cy == R0R1) &
                (ex == ey) & (ex < fx + (p-2)) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, fx-1, fy-1, fy), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE1-R0R1-D1-Y",
                diff_sign & (cy == ONE1) & (cx == R0R1) &
                (ey == ex) & (ey < fy + (p-2)) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, fy-1, fx-1, fx), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-G00-D1-X",
                diff_sign & (cx == POW2) & (cy == G00) &
                (ex == ey + 1) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ey-1, fy, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-G00-D1-Y",
                diff_sign & (cy == POW2) & (cx == G00) &
                (ey == ex + 1) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ex-1, fx, gx), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE1-G00-S1-X",
                same_sign & (cx == ONE1) & (cy == G00) &
                (fx > ey) & (ex > fy + p) & (ex < ey + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey), SELTZORange(sy, 0, 0, fy, gy:fy-2, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey), SELTZORange(sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey), SELTZORange(sy, 1, 0, fy, gy+1:fy-2, gy))
            end
            checker("SELTZO-TwoSum-ONE1-G00-S1-Y",
                same_sign & (cy == ONE1) & (cx == G00) &
                (fy > ex) & (ey > fx + p) & (ey < ex + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex), SELTZORange(sx, 0, 0, fx, gx:fx-2, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex), SELTZORange(sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex), SELTZORange(sx, 1, 0, fx, gx+1:fx-2, gx))
            end

            checker("SELTZO-TwoSum-POW2-R0R1-S5-X",
                same_sign & (cx == POW2) & (cy == R0R1) &
                (ex > ey + 1) & (ex < ey + (p-1)) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, ey), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-POW2-R0R1-S5-Y",
                same_sign & (cy == POW2) & (cx == R0R1) &
                (ey > ex + 1) & (ey < ex + (p-1)) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, ex), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-POW2-MM10-D1-X",
                diff_sign & (cx == POW2) & (cy == MM10) &
                (ex == ey + (p+1)) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ex-(p+1), ex-1), SELTZORange(~sy, 1, 0, ey-1, fy, ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-MM10-D1-Y",
                diff_sign & (cy == POW2) & (cx == MM10) &
                (ey == ex + (p+1)) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ey-(p+1), ey-1), SELTZORange(~sx, 1, 0, ex-1, fx, ex-(p-1)))
            end

            checker("SELTZO-TwoSum-R1R0-R1R0-S1-X",
                same_sign & (cx == R1R0) & (cy == R1R0) &
                (ey == fx) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ex-(p-1), ex+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-R1R0-R1R0-S1-Y",
                same_sign & (cy == R1R0) & (cx == R1R0) &
                (ex == fy) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ey-(p-1), ey+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-ONE1-ONE1-S1-X",
                same_sign & (cx == ONE1) & (cy == ONE1) &
                (ex == ey + 1) & (ey == fx + 1) & (ex < fy + (p-1)) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ey+1, ex-3, fy), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE1-ONE1-S1-Y",
                same_sign & (cy == ONE1) & (cx == ONE1) &
                (ey == ex + 1) & (ex == fy + 1) & (ey < fx + (p-1)) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ex+1, ey-3, fx), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-MM01-S1-X",
                same_sign & (cx == POW2) & (cy == MM01) &
                (ex == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, ex-(p-2)), SELTZORange(sy, 0, 0, fx, fx-p, fx))
            end
            checker("SELTZO-TwoSum-POW2-MM01-S1-Y",
                same_sign & (cy == POW2) & (cx == MM01) &
                (ey == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, ey-(p-2)), SELTZORange(sx, 0, 0, fy, fy-p, fy))
            end

            checker("SELTZO-TwoSum-POW2-R1R0-D3-X",
                diff_sign & (cx == POW2) & (cy == R1R0) &
                (ex < ey + (p+1)) & (ex > fy + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, ey+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-POW2-R1R0-D3-Y",
                diff_sign & (cy == POW2) & (cx == R1R0) &
                (ey < ex + (p+1)) & (ey > fx + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, ex+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-POW2-ONE1-D1-X",
                diff_sign & (cx == POW2) & (cy == ONE1) &
                (ex == ey + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ey-1, fy-1, fy), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-ONE1-D1-Y",
                diff_sign & (cy == POW2) & (cx == ONE1) &
                (ey == ex + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ex-1, fx-1, fx), pos_zero)
            end

            checker("SELTZO-TwoSum-R1R0-R0R1-D2-X",
                diff_sign & (cx == R1R0) & (cy == R0R1) &
                (ex == ey) & (fx + 1 > fy) & (ex > fx + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fx+1, ex-(p-1)), pos_zero)
            end
            checker("SELTZO-TwoSum-R1R0-R0R1-D2-Y",
                diff_sign & (cy == R1R0) & (cx == R0R1) &
                (ey == ex) & (fy + 1 > fx) & (ey > fy + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fy+1, ey-(p-1)), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-MM10-S1-X",
                same_sign & (cx == POW2) & (cy == MM10) &
                (ex > fy + p) & (ex < ey + (p-1)) & (ey == gy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, ey), SELTZORange(sy, 0, 0, gy+1, gy-1, gy-2))
            end
            checker("SELTZO-TwoSum-POW2-MM10-S1-Y",
                same_sign & (cy == POW2) & (cx == MM10) &
                (ey > fx + p) & (ey < ex + (p-1)) & (ex == gx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, ex), SELTZORange(sx, 0, 0, gx+1, gx-1, gx-2))
            end

            checker("SELTZO-TwoSum-R1R0-R1R0-D4-X",
                diff_sign & (cx == R1R0) & (cy == R1R0) &
                (ex == ey + 1) & (ex > fx + 2) & (fx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fx, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-R1R0-R1R0-D4-Y",
                diff_sign & (cy == R1R0) & (cx == R1R0) &
                (ey == ex + 1) & (ey > fy + 2) & (fy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fy, gx), pos_zero)
            end

            checker("SELTZO-TwoSum-ALL1-ONE1-S2-X",
                same_sign & (cx == ALL1) & (cy == ONE1) &
                (ex > ey) & (ex < fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, fy), SELTZORange(~sy, 0, 0, fx+1, fx-(p-1), fx+1))
            end
            checker("SELTZO-TwoSum-ALL1-ONE1-S2-Y",
                same_sign & (cy == ALL1) & (cx == ONE1) &
                (ey > ex) & (ey < fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, fx), SELTZORange(~sx, 0, 0, fy+1, fy-(p-1), fy+1))
            end

            checker("SELTZO-TwoSum-POW2-ONE1-D2-X",
                diff_sign & (cx == POW2) & (cy == ONE1) &
                (ex > fy + p) & (ex < ey + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey-1, ey), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-POW2-ONE1-D2-Y",
                diff_sign & (cy == POW2) & (cx == ONE1) &
                (ey > fx + p) & (ey < ex + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex-1, ex), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ONE0-ONE0-D1-X",
                diff_sign & (cx == ONE0) & (cy == ONE0) &
                (ex == ey + p) & (ex < fx + (p-2)) & (ey < fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey+2), SELTZORange(~sy, 0, 0, fy, ey-(p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-ONE0-ONE0-D1-Y",
                diff_sign & (cy == ONE0) & (cx == ONE0) &
                (ey == ex + p) & (ey < fy + (p-2)) & (ex < fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex+2), SELTZORange(~sx, 0, 0, fx, ex-(p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-G00-R1R0-D1-X",
                diff_sign & (cx == G00) & (cy == R1R0) &
                (fx == ey + 2) & (ex > fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx-1:fx, gx), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-G00-R1R0-D1-Y",
                diff_sign & (cy == G00) & (cx == R1R0) &
                (fy == ex + 2) & (ey > fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy-1:fy, gy), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-R1R0-R1R0-D5-X",
                diff_sign & (cx == R1R0) & (cy == R1R0) &
                (ex == fx + 2) & (ex > fy + p) & (ex < ey + p) & (ey < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-R1R0-R1R0-D5-Y",
                diff_sign & (cy == R1R0) & (cx == R1R0) &
                (ey == fy + 2) & (ey > fx + p) & (ey < ex + p) & (ex < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-POW2-R0R1-D7-X",
                diff_sign & (cx == POW2) & (cy == R0R1) &
                (ex > ey + 2) & (ex < fy + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, gy), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-R0R1-D7-Y",
                diff_sign & (cy == POW2) & (cx == R0R1) &
                (ey > ex + 2) & (ey < fx + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, gx), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-R1R0-R0R1-S1-X",
                same_sign & (cx == R1R0) & (cy == R0R1) &
                (ex == fy + (p-1)) & (ey > fx + 1) & (ex < fx + (p-2)) & (ey < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex+1, ey-1, gy+1), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-R1R0-R0R1-S1-Y",
                same_sign & (cy == R1R0) & (cx == R0R1) &
                (ey == fx + (p-1)) & (ex > fy + 1) & (ey < fy + (p-2)) & (ex < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey+1, ex-1, gx+1), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-POW2-MM10-D2-X",
                diff_sign & (cx == POW2) & (cy == MM10) &
                (ex == ey + 1) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ey-1, fy, ey-(p-1)), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-MM10-D2-Y",
                diff_sign & (cy == POW2) & (cx == MM10) &
                (ey == ex + 1) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ex-1, fx, ex-(p-1)), pos_zero)
            end

            checker("SELTZO-TwoSum-R0R1-POW2-D1-X",
                diff_sign & (cx == R0R1) & (cy == POW2) &
                (ex == ey) & (ex - fx < p-1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, fx, ex-p, ex-(p-1)), pos_zero)
            end
            checker("SELTZO-TwoSum-R0R1-POW2-D1-Y",
                diff_sign & (cy == R0R1) & (cx == POW2) &
                (ey == ex) & (ey - fy < p-1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, fy, ey-p, ey-(p-1)), pos_zero)
            end

            checker("SELTZO-TwoSum-MM10-POW2-S3-X",
                same_sign & (cx == MM10) & (cy == POW2) &
                (ex == ey) & (ex - fx < p-3)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fx, gx), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-MM10-POW2-S3-Y",
                same_sign & (cy == MM10) & (cx == POW2) &
                (ey == ex) & (ey - fy < p-3)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fy, gy), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-ONE0-R1R0-D2-X",
                diff_sign & (cx == ONE0) & (cy == R1R0) &
                (ex == ey) & (fx + 1 < fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, fy, fx, ex-(p-1)), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE0-R1R0-D2-Y",
                diff_sign & (cy == ONE0) & (cx == R1R0) &
                (ey == ex) & (fy + 1 < fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, fx, fy, ey-(p-1)), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-ONE1-D3-X",
                diff_sign & (cx == POW2) & (cy == ONE1) &
                (ex == ey + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ex-(p+1), ex-1), SELTZORange(~sy, 1, 0, ey-1, fy-1, fy))
            end
            checker("SELTZO-TwoSum-POW2-ONE1-D3-Y",
                diff_sign & (cy == POW2) & (cx == ONE1) &
                (ey == ex + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ey-(p+1), ey-1), SELTZORange(~sx, 1, 0, ex-1, fx-1, fx))
            end

            checker("SELTZO-TwoSum-ONE1-R0R1-D2-X",
                diff_sign & (cx == ONE1) & (cy == R0R1) &
                (fx == ey) & (ex < fy + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fy, gy), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-ONE1-R0R1-D2-Y",
                diff_sign & (cy == ONE1) & (cx == R0R1) &
                (fy == ex) & (ey < fx + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fx, gx), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-ONE0-POW2-D1-X",
                diff_sign & (cx == ONE0) & (cy == POW2) &
                (ex == ey + (p-1)) & (ex == fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ex-(p-2), ex-(p-3)), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE0-POW2-D1-Y",
                diff_sign & (cy == ONE0) & (cx == POW2) &
                (ey == ex + (p-1)) & (ey == fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ey-(p-2), ey-(p-3)), pos_zero)
            end

            checker("SELTZO-TwoSum-R1R0-POW2-S1-X",
                same_sign & (cx == R1R0) & (cy == POW2) &
                (ex < ey + (p-1))  & (fx > ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-R1R0-POW2-S1-Y",
                same_sign & (cy == R1R0) & (cx == POW2) &
                (ey < ex + (p-1))  & (fy > ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex), pos_zero)
            end

            checker("SELTZO-TwoSum-R1R0-G10-D1-X",
                diff_sign & (cx == R1R0) & (cy == G10) &
                (ex == ey + 2) & (ey == fx + 1) & (ex == gy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gy+2:fy-1), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy+1), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gy+2:fy), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-R1R0-G10-D1-Y",
                diff_sign & (cy == R1R0) & (cx == G10) &
                (ey == ex + 2) & (ex == fy + 1) & (ey == gx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gx+2:fx-1), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx+1), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gx+2:fx), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-POW2-MM01-D1-X",
                diff_sign & (cx == POW2) & (cy == MM01) &
                (ex > fy + (p+1)) & (ex < ey + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, ey+1), SELTZORange(~sy, 1, 0, fy, fy-2, fy-1))
            end
            checker("SELTZO-TwoSum-POW2-MM01-D1-Y",
                diff_sign & (cy == POW2) & (cx == MM01) &
                (ey > fx + (p+1)) & (ey < ex + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, ex+1), SELTZORange(~sx, 1, 0, fx, fx-2, fx-1))
            end

            checker("SELTZO-TwoSum-TWO1-TWO1-D1-X",
                diff_sign & (cx == TWO1) & (cy == TWO1) &
                (ex == fy + (p-1)) & (fx == ey + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx-1, ex-(p-2)), SELTZORange(~sy, 0, 0, fy-1, fy-(p+1), fy-1))
            end
            checker("SELTZO-TwoSum-TWO1-TWO1-D1-Y",
                diff_sign & (cy == TWO1) & (cx == TWO1) &
                (ey == fx + (p-1)) & (fy == ex + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy-1, ey-(p-2)), SELTZORange(~sx, 0, 0, fx-1, fx-(p+1), fx-1))
            end

            checker("SELTZO-TwoSum-TWO1-TWO1-D2-X",
                diff_sign & (cx == TWO1) & (cy == TWO1) &
                (ex == fy + (p-1)) & (fx == ey) & (ex < fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx-2, ex-(p-2)), SELTZORange(~sy, 0, 0, fy-1, fy-(p+1), fy-1))
            end
            checker("SELTZO-TwoSum-TWO1-TWO1-D2-Y",
                diff_sign & (cy == TWO1) & (cx == TWO1) &
                (ey == fx + (p-1)) & (fy == ex) & (ey < fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy-2, ey-(p-2)), SELTZORange(~sx, 0, 0, fx-1, fx-(p+1), fx-1))
            end

            checker("SELTZO-TwoSum-R1R0-G00-S1-X",
                same_sign & (cx == R1R0) & (cy == G00) &
                (ex == gy + (p-1)) & (gx == ey) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fy, fy), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fy+1, fy+1), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-R1R0-G00-S1-Y",
                same_sign & (cy == R1R0) & (cx == G00) &
                (ey == gx + (p-1)) & (gy == ex) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fx, fx), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fx+1, fx+1), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-MM01-ONE1-S2-X",
                same_sign & (cx == MM01) & (cy == ONE1) &
                (ex == fy + (p-1)) & (fx == ey) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx-2, fy+1), pos_zero)
            end
            checker("SELTZO-TwoSum-MM01-ONE1-S2-Y",
                same_sign & (cy == MM01) & (cx == ONE1) &
                (ey == fx + (p-1)) & (fy == ex) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy-2, fx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE1-POW2-D2-X",
                diff_sign & (cx == ONE1) & (cy == POW2) &
                (ex < ey + (p-1)) & (ey < fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx-1, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE1-POW2-D2-Y",
                diff_sign & (cy == ONE1) & (cx == POW2) &
                (ey < ex + (p-1)) & (ex < fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy-1, ex), pos_zero)
            end

            checker("SELTZO-TwoSum-R1R0-POW2-D1-X",
                diff_sign & (cx == R1R0) & (cy == POW2) &
                (fx + 1 > ey) & (ex < ey + (p-1)) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, gx, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-R1R0-POW2-D1-Y",
                diff_sign & (cy == R1R0) & (cx == POW2) &
                (fy + 1 > ex) & (ey < ex + (p-1)) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, gy, ex), pos_zero)
            end

            checker("SELTZO-TwoSum-R1R0-ONE1-S5-X",
                same_sign & (cx == R1R0) & (cy == ONE1) &
                (ex == fx + (p-1)) & (fx == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx-1, ex), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-R1R0-ONE1-S5-Y",
                same_sign & (cy == R1R0) & (cx == ONE1) &
                (ey == fy + (p-1)) & (fy == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy-1, ey), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-POW2-TWO1-S2-X",
                same_sign & (cx == POW2) & (cy == TWO1) &
                (ex == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy+1), SELTZORange(~sy, 0, 0, fx, fx-p, fx))
            end
            checker("SELTZO-TwoSum-POW2-TWO1-S2-Y",
                same_sign & (cy == POW2) & (cx == TWO1) &
                (ey == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx+1), SELTZORange(~sx, 0, 0, fy, fy-p, fy))
            end

            checker("SELTZO-TwoSum-POW2-G11-D1-X",
                diff_sign & (cx == POW2) & (cy == G11) &
                (ex == ey + 2) & (ey < gy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, fy, gy), SELTZORange(~sy, 0, 0, fx-1, fx-(p+1), fx-1))
            end
            checker("SELTZO-TwoSum-POW2-G11-D1-Y",
                diff_sign & (cy == POW2) & (cx == G11) &
                (ey == ex + 2) & (ex < gx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, fx, gx), SELTZORange(~sx, 0, 0, fy-1, fy-(p+1), fy-1))
            end

            checker("SELTZO-TwoSum-POW2-TWO1-D2-X",
                diff_sign & (cx == POW2) & (cy == TWO1) &
                (ex == fy + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ey), SELTZORange(~sy, 0, 0, fy-1, fy-(p+1), fy-1))
            end
            checker("SELTZO-TwoSum-POW2-TWO1-D2-Y",
                diff_sign & (cy == POW2) & (cx == TWO1) &
                (ey == fx + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ex), SELTZORange(~sx, 0, 0, fx-1, fx-(p+1), fx-1))
            end

            checker("SELTZO-TwoSum-POW2-TWO1-S3-X",
                same_sign & (cx == POW2) & (cy == TWO1) &
                (ex == fy + p) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx+2), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-POW2-TWO1-S3-Y",
                same_sign & (cy == POW2) & (cx == TWO1) &
                (ey == fx + p) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy+2), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-TWO0-R0R1-D1-X",
                diff_sign & (cx == TWO0) & (cy == R0R1) &
                (ex == ey) & (ex > fx + 2) & (fx > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fx, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-TWO0-R0R1-D1-Y",
                diff_sign & (cy == TWO0) & (cx == R0R1) &
                (ey == ex) & (ey > fy + 2) & (fy > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fy, gx), pos_zero)
            end

            checker("SELTZO-TwoSum-MM01-ONE1-S3-X",
                same_sign & (cx == MM01) & (cy == ONE1) &
                (ex > fy + (p-2)) & (fx + 1 < ey) & (ex < fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey-1, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-MM01-ONE1-S3-Y",
                same_sign & (cy == MM01) & (cx == ONE1) &
                (ey > fx + (p-2)) & (fy + 1 < ex) & (ey < fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex-1, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-G00-R1R0-S1-X",
                same_sign & (cx == G00) & (cy == R1R0) &
                (ex < ey + p) & (ey + 1 < gx) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey+1), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-G00-R1R0-S1-Y",
                same_sign & (cy == G00) & (cx == R1R0) &
                (ey < ex + p) & (ex + 1 < gy) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex+1), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-POW2-ONE1-D4-X",
                diff_sign & (cx == POW2) & (cy == ONE1) &
                (ex > ey + 2) & (ex < fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, fy), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-ONE1-D4-Y",
                diff_sign & (cy == POW2) & (cx == ONE1) &
                (ey > ex + 2) & (ey < fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, fx), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE0-ONE1-D1-X",
                diff_sign & (cx == ONE0) & (cy == ONE1) &
                (ex == ey) & (fx == fy) & (ex > fx + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fx+1, ex-(p-1)), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE0-ONE1-D1-Y",
                diff_sign & (cy == ONE0) & (cx == ONE1) &
                (ey == ex) & (fy == fx) & (ey > fy + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fy+1, ey-(p-1)), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE0-ONE1-D2-X",
                diff_sign & (cx == ONE0) & (cy == ONE1) &
                (ex == ey) & (ey > fy + 2) & (fx < fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fy, ex-(p-1)), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE0-ONE1-D2-Y",
                diff_sign & (cy == ONE0) & (cx == ONE1) &
                (ey == ex) & (ex > fx + 2) & (fy < fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fx, ey-(p-1)), pos_zero)
            end

            checker("SELTZO-TwoSum-G10-ONE1-D1-X",
                diff_sign & (cx == G10) & (cy == ONE1) &
                (ey == gx) & (fx == gx + 2) & (fx > fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx+1), SELTZORange(sy, 0, 0, fy, fy-p, fy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx-1), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-G10-ONE1-D1-Y",
                diff_sign & (cy == G10) & (cx == ONE1) &
                (ex == gy) & (fy == gy + 2) & (fy > fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy+1), SELTZORange(sx, 0, 0, fx, fx-p, fx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy-1), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ONE0-ALL1-D1-X",
                diff_sign & (cx == ONE0) & (cy == ALL1) &
                (ex == ey + p) & (ex == fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-ONE0-ALL1-D1-Y",
                diff_sign & (cy == ONE0) & (cx == ALL1) &
                (ey == ex + p) & (ey == fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-TWO0-POW2-S1-X",
                same_sign & (cx == TWO0) & (cy == POW2) &
                (fx == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx-1, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-TWO0-POW2-S1-Y",
                same_sign & (cy == TWO0) & (cx == POW2) &
                (fy == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy-1, gy), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-ONE1-D5-X",
                diff_sign & (cx == POW2) & (cy == ONE1) &
                (ex == fy + p) & (ey < fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-ONE1-D5-Y",
                diff_sign & (cy == POW2) & (cx == ONE1) &
                (ey == fx + p) & (ex < fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ex), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-G01-D2-X",
                diff_sign & (cx == POW2) & (cy == G01) &
                (ex == ey + 1) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ey-1, fy, fx), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-G01-D2-Y",
                diff_sign & (cy == POW2) & (cx == G01) &
                (ey == ex + 1) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ex-1, fx, fy), pos_zero)
            end

            checker("SELTZO-TwoSum-MM01-ONE1-S4-X",
                same_sign & (cx == MM01) & (cy == ONE1) &
                (ey == fx) & (ey == fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, gx-1, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-MM01-ONE1-S4-Y",
                same_sign & (cy == MM01) & (cx == ONE1) &
                (ex == fy) & (ex == fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, gy-1, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ONE1-TWO1-D2-X",
                diff_sign & (cx == ONE1) & (cy == TWO1) &
                (ex > fy + p) & (ey < fx) & (ex < ey + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx-1, ey), SELTZORange(sy, 1, 0, fy, gy-1, gy))
            end
            checker("SELTZO-TwoSum-ONE1-TWO1-D2-Y",
                diff_sign & (cy == ONE1) & (cx == TWO1) &
                (ey > fx + p) & (ex < fy) & (ey < ex + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy-1, ex), SELTZORange(sx, 1, 0, fx, gx-1, gx))
            end

            checker("SELTZO-TwoSum-MM01-ONE1-S5-X",
                same_sign & (cx == MM01) & (cy == ONE1) &
                (ex == fy + p) & (ey + 1 < fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-MM01-ONE1-S5-Y",
                same_sign & (cy == MM01) & (cx == ONE1) &
                (ey == fx + p) & (ex + 1 < fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-R1R0-G01-D1-X",
                diff_sign & (cx == R1R0) & (cy == G01) &
                (ex == ey) & (ex == fx + 2) & (fx > fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy, fx-(p-3)), pos_zero)
            end
            checker("SELTZO-TwoSum-R1R0-G01-D1-Y",
                diff_sign & (cy == R1R0) & (cx == G01) &
                (ey == ex) & (ey == fy + 2) & (fy > fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx, fy-(p-3)), pos_zero)
            end

            checker("SELTZO-TwoSum-R1R0-POW2-D2-X",
                diff_sign & (cx == R1R0) & (cy == POW2) &
                (ex == ey) & (2 < ex - fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fx, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-R1R0-POW2-D2-Y",
                diff_sign & (cy == R1R0) & (cx == POW2) &
                (ey == ex) & (2 < ey - fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fy, gy), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-TWO0-D1-X",
                diff_sign & (cx == POW2) & (cy == TWO0) &
                (ex < ey + (p+1)) & (ex > gy + (p+2)) & (ey == gy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, ey+1), SELTZORange(~sy, 1, 0, fy, gy-1, gy-2))
            end
            checker("SELTZO-TwoSum-POW2-TWO0-D1-Y",
                diff_sign & (cy == POW2) & (cx == TWO0) &
                (ey < ex + (p+1)) & (ey > gx + (p+2)) & (ex == gx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, ex+1), SELTZORange(~sx, 1, 0, fx, gx-1, gx-2))
            end

            checker("SELTZO-TwoSum-R1R0-R1R0-S2-X",
                same_sign & (cx == R1R0) & (cy == R1R0) &
                (ex < fx + (p-1)) & (fx < ey) & (fy + (p-1) < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, gx), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-R1R0-R1R0-S2-Y",
                same_sign & (cy == R1R0) & (cx == R1R0) &
                (ey < fy + (p-1)) & (fy < ex) & (fx + (p-1) < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, gy), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-POW2-G10-D1-X",
                diff_sign & (cx == POW2) & (cy == G10) &
                (ex > fy + (p+1)) & (ex < ey + (p+1)) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, ey+1), SELTZORange(~sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, ey+1), SELTZORange(~sy, 0, 0, fy, gy, gy))
            end
            checker("SELTZO-TwoSum-POW2-G10-D1-Y",
                diff_sign & (cy == POW2) & (cx == G10) &
                (ey > fx + (p+1)) & (ey < ex + (p+1)) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, ex+1), SELTZORange(~sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, ex+1), SELTZORange(~sx, 0, 0, fx, gx, gx))
            end

            checker("SELTZO-TwoSum-TWO1-R0R1-D1-X",
                diff_sign & (cx == TWO1) & (cy == R0R1) &
                (ex == ey + (p-1)) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-TWO1-R0R1-D1-Y",
                diff_sign & (cy == TWO1) & (cx == R0R1) &
                (ey == ex + (p-1)) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-R1R0-R0R1-S2-X",
                same_sign & (cx == R1R0) & (cy == R0R1) &
                (ex == ey + p) & (ex < fx + (p-1)) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, ey+2), SELTZORange(~sy, 1, 0, ey-1, fy-1, fy))
            end
            checker("SELTZO-TwoSum-R1R0-R0R1-S2-Y",
                same_sign & (cy == R1R0) & (cx == R0R1) &
                (ey == ex + p) & (ey < fy + (p-1)) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, ex+2), SELTZORange(~sx, 1, 0, ex-1, fx-1, fx))
            end

            checker("SELTZO-TwoSum-ONE0-POW2-S2-X",
                same_sign & (cx == ONE0) & (cy == POW2) &
                (ey > fx) & (ex + 1 > ey) & (ex < fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey-1, fx), SELTZORange(~sy, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end
            checker("SELTZO-TwoSum-ONE0-POW2-S2-Y",
                same_sign & (cy == ONE0) & (cx == POW2) &
                (ex > fy) & (ey + 1 > ex) & (ey < fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex-1, fy), SELTZORange(~sx, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end

            checker("SELTZO-TwoSum-TWO1-POW2-S1-X",
                same_sign & (cx == TWO1) & (cy == POW2) &
                (ex == ey) & (ex < fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, gy+1, fx, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-TWO1-POW2-S1-Y",
                same_sign & (cy == TWO1) & (cx == POW2) &
                (ey == ex) & (ey < fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, gx+1, fy, gy), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE0-R0R1-S1-X",
                same_sign & (cx == ONE0) & (cy == R0R1) &
                (ex > fy + (p+1)) & (ex < ey + (p-2)) & (ex == fx + (p-2)) & (ey < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex+1, ey-1, ey), SELTZORange(~sy, 1, 0, ex-p, fy, ey-(p-1)))
            end
            checker("SELTZO-TwoSum-ONE0-R0R1-S1-Y",
                same_sign & (cy == ONE0) & (cx == R0R1) &
                (ey > fx + (p+1)) & (ey < ex + (p-2)) & (ey == fy + (p-2)) & (ex < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey+1, ex-1, ex), SELTZORange(~sx, 1, 0, ey-p, fx, ex-(p-1)))
            end

            checker("SELTZO-TwoSum-MM01-R1R0-S2-X",
                same_sign & (cx == MM01) & (cy == R1R0) &
                (ex > fy + (p-1)) & (ey > fx) & (ex < fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, gx), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-MM01-R1R0-S2-Y",
                same_sign & (cy == MM01) & (cx == R1R0) &
                (ey > fx + (p-1)) & (ex > fy) & (ey < fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, gy), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-ALL1-TWO1-D1-X",
                diff_sign & (cx == ALL1) & (cy == TWO1) &
                (ex == ey) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fy, fx+1), pos_zero)
            end
            checker("SELTZO-TwoSum-ALL1-TWO1-D1-Y",
                diff_sign & (cy == ALL1) & (cx == TWO1) &
                (ey == ex) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fx, fy+1), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-G01-S1-X",
                same_sign & (cx == POW2) & (cy == G01) &
                (ex == ey + p) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx+1, fx+2), SELTZORange(~sy, 1, 0, ey-1, fy, ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-G01-S1-Y",
                same_sign & (cy == POW2) & (cx == G01) &
                (ey == ex + p) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy+1, fy+2), SELTZORange(~sx, 1, 0, ex-1, fx, ex-(p-1)))
            end

            checker("SELTZO-TwoSum-POW2-R1R0-S3-X",
                same_sign & (cx == POW2) & (cy == R1R0) &
                (ex == ey + 2) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ex-1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-POW2-R1R0-S3-Y",
                same_sign & (cy == POW2) & (cx == R1R0) &
                (ey == ex + 2) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ey-1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-MM01-R0R1-D1-X",
                diff_sign & (cx == MM01) & (cy == R0R1) &
                (ex == ey + p) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, gx), SELTZORange(~sy, 1, 0, ey-1, fy-1, fy))
            end
            checker("SELTZO-TwoSum-MM01-R0R1-D1-Y",
                diff_sign & (cy == MM01) & (cx == R0R1) &
                (ey == ex + p) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, gy), SELTZORange(~sx, 1, 0, ex-1, fx-1, fx))
            end

            checker("SELTZO-TwoSum-POW2-TWO1-S4-X",
                same_sign & (cx == POW2) & (cy == TWO1) &
                (ex == ey + p) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ex-(p-1), ex-(p-2)), SELTZORange(~sy, 1, 0, ey-1, fy, gy))
            end
            checker("SELTZO-TwoSum-POW2-TWO1-S4-Y",
                same_sign & (cy == POW2) & (cx == TWO1) &
                (ey == ex + p) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ey-(p-1), ey-(p-2)), SELTZORange(~sx, 1, 0, ex-1, fx, gx))
            end

            checker("SELTZO-TwoSum-POW2-ONE0-S3-X",
                same_sign & (cx == POW2) & (cy == ONE0) &
                (ex > ey + 2) & (ex < ey + p) & (ey == fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey+1, ey+1), SELTZORange(~sy, 1, 0, fy, fy-2, fy-1))
            end
            checker("SELTZO-TwoSum-POW2-ONE0-S3-Y",
                same_sign & (cy == POW2) & (cx == ONE0) &
                (ey > ex + 2) & (ey < ex + p) & (ex == fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex+1, ex+1), SELTZORange(~sx, 1, 0, fx, fx-2, fx-1))
            end

            checker("SELTZO-TwoSum-POW2-R0R1-D8-X",
                diff_sign & (cx == POW2) & (cy == R0R1) &
                (ex == ey + 1) & (ey == fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, gy, fx, fx), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-R0R1-D8-Y",
                diff_sign & (cy == POW2) & (cx == R0R1) &
                (ey == ex + 1) & (ex == fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, gx, fy, fy), pos_zero)
            end

            checker("SELTZO-TwoSum-R1R0-ONE1-D4-X",
                diff_sign & (cx == R1R0) & (cy == ONE1) &
                (fx + 1 == ey) & (ex > fy + p-1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, gx, gx+1), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-R1R0-ONE1-D4-Y",
                diff_sign & (cy == R1R0) & (cx == ONE1) &
                (fy + 1 == ex) & (ey > fx + p-1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, gy, gy+1), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ALL1-R1R0-S2-X",
                same_sign & (cx == ALL1) & (cy == R1R0) &
                (ex == ey + (p-1)) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, ex+1), SELTZORange(sy, 1, 0, fx, fy, gy))
            end
            checker("SELTZO-TwoSum-ALL1-R1R0-S2-Y",
                same_sign & (cy == ALL1) & (cx == R1R0) &
                (ey == ex + (p-1)) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, ey+1), SELTZORange(sx, 1, 0, fy, fx, gx))
            end

            checker("SELTZO-TwoSum-POW2-ONE0-D1-X",
                diff_sign & (cx == POW2) & (cy == ONE0) &
                (ex == ey + 2) & (ey < fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, fy, fy), SELTZORange(~sy, 0, 0, fx-1, fx-(p+1), fx-1))
            end
            checker("SELTZO-TwoSum-POW2-ONE0-D1-Y",
                diff_sign & (cy == POW2) & (cx == ONE0) &
                (ey == ex + 2) & (ex < fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, fx, fx), SELTZORange(~sx, 0, 0, fy-1, fy-(p+1), fy-1))
            end

            checker("SELTZO-TwoSum-POW2-MM01-S2-X",
                same_sign & (cx == POW2) & (cy == MM01) &
                (ex == ey + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx+1, fx+2), SELTZORange(~sy, 1, 0, fy, fy-2, fy-1))
            end
            checker("SELTZO-TwoSum-POW2-MM01-S2-Y",
                same_sign & (cy == POW2) & (cx == MM01) &
                (ey == ex + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy+1, fy+2), SELTZORange(~sx, 1, 0, fx, fx-2, fx-1))
            end

            checker("SELTZO-TwoSum-ONE0-ONE1-D3-X",
                diff_sign & (cx == ONE0) & (cy == ONE1) &
                (ex == ey + (p-1)) & (fx == ey + 1) & (ex == fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx+1), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-ONE0-ONE1-D3-Y",
                diff_sign & (cy == ONE0) & (cx == ONE1) &
                (ey == ex + (p-1)) & (fy == ex + 1) & (ey == fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy+1), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ALL1-TWO1-S2-X",
                same_sign & (cx == ALL1) & (cy == TWO1) &
                (ex > ey) & (ex < fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, gy), SELTZORange(~sy, 0, 0, fx+1, fx-(p-1), fx+1))
            end
            checker("SELTZO-TwoSum-ALL1-TWO1-S2-Y",
                same_sign & (cy == ALL1) & (cx == TWO1) &
                (ey > ex) & (ey < fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, gx), SELTZORange(~sx, 0, 0, fy+1, fy-(p-1), fy+1))
            end

            checker("SELTZO-TwoSum-ONE1-ONE1-D5-X",
                diff_sign & (cx == ONE1) & (cy == ONE1) &
                (ex == ey + 1) & (fx + 1 < fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-2, fy-1, fx), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE1-ONE1-D5-Y",
                diff_sign & (cy == ONE1) & (cx == ONE1) &
                (ey == ex + 1) & (fy + 1 < fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-2, fx-1, fy), pos_zero)
            end

            checker("SELTZO-TwoSum-TWO1-ALL1-D1-X",
                diff_sign & (cx == TWO1) & (cy == ALL1) &
                (ex < ey + p) & (fx > ey + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-TWO1-ALL1-D1-Y",
                diff_sign & (cy == TWO1) & (cx == ALL1) &
                (ey < ex + p) & (fy > ex + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-ONE1-MM01-S1-X",
                same_sign & (cx == ONE1) & (cy == MM01) &
                (fx > ey) & (ex == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy+1), SELTZORange(sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-ONE1-MM01-S1-Y",
                same_sign & (cy == ONE1) & (cx == MM01) &
                (fy > ex) & (ey == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx+1), SELTZORange(sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-POW2-G00-D2-X",
                diff_sign & (cx == POW2) & (cy == G00) &
                (ex == ey + 1) & (ey == fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ey-1, gy:fy-1, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-G00-D2-Y",
                diff_sign & (cy == POW2) & (cx == G00) &
                (ey == ex + 1) & (ex == fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ex-1, gx:fx-1, gx), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-G10-D2-X",
                diff_sign & (cx == POW2) & (cy == G10) &
                (ex == fy + (p-1)) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, fy), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, fy+1), SELTZORange(sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-POW2-G10-D2-Y",
                diff_sign & (cy == POW2) & (cx == G10) &
                (ey == fx + (p-1)) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, fx), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, fx+1), SELTZORange(sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-POW2-MM01-D2-X",
                diff_sign & (cx == POW2) & (cy == MM01) &
                (ex == fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, fx+1), SELTZORange(sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-POW2-MM01-D2-Y",
                diff_sign & (cy == POW2) & (cx == MM01) &
                (ey == fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, fy+1), SELTZORange(sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-ONE1-POW2-S1-X",
                same_sign & (cx == ONE1) & (cy == POW2) &
                (ex == ey) & (ey < fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fx, fx), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE1-POW2-S1-Y",
                same_sign & (cy == ONE1) & (cx == POW2) &
                (ey == ex) & (ex < fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fy, fy), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-TWO1-D3-X",
                diff_sign & (cx == POW2) & (cy == TWO1) &
                (ex < ey + p) & (ex > fy + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey-1, ey), SELTZORange(sy, 1, 0, fy, gy-1, gy))
            end
            checker("SELTZO-TwoSum-POW2-TWO1-D3-Y",
                diff_sign & (cy == POW2) & (cx == TWO1) &
                (ey < ex + p) & (ey > fx + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex-1, ex), SELTZORange(sx, 1, 0, fx, gx-1, gx))
            end

            checker("SELTZO-TwoSum-ALL1-R1R0-S3-X",
                same_sign & (cx == ALL1) & (cy == R1R0) &
                (ex == ey) & (ex < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex+1, fy, gy), SELTZORange(~sy, 0, 0, fx+1, fx-(p-1), fx+1))
            end
            checker("SELTZO-TwoSum-ALL1-R1R0-S3-Y",
                same_sign & (cy == ALL1) & (cx == R1R0) &
                (ey == ex) & (ey < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey+1, fx, gx), SELTZORange(~sx, 0, 0, fy+1, fy-(p-1), fy+1))
            end

            checker("SELTZO-TwoSum-POW2-G01-D3-X",
                diff_sign & (cx == POW2) & (cy == G01) &
                (ex == ey + 1) & (ey == fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ey-1, gy:fy-1, fx), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-G01-D3-Y",
                diff_sign & (cy == POW2) & (cx == G01) &
                (ey == ex + 1) & (ex == fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ex-1, gx:fx-1, fy), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-ONE0-D2-X",
                diff_sign & (cx == POW2) & (cy == ONE0) &
                (ex == ey + (p+1)) & (ey < fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ex-1), SELTZORange(~sy, 0, 0, fy, ey-(p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-ONE0-D2-Y",
                diff_sign & (cy == POW2) & (cx == ONE0) &
                (ey == ex + (p+1)) & (ex < fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ey-1), SELTZORange(~sx, 0, 0, fx, ex-(p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-POW2-MM10-S2-X",
                same_sign & (cx == POW2) & (cy == MM10) &
                (ex > ey + 1) & (ex < fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gy), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-MM10-S2-Y",
                same_sign & (cy == POW2) & (cx == MM10) &
                (ey > ex + 1) & (ey < fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gx), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-ALL1-G00-D1-X",
                diff_sign & (cx == ALL1) & (cy == G00) &
                (ex == ey) & (ey == fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, gy-1, fx+1), pos_zero)
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, gy+1:fy-1, fx+1), pos_zero)
            end
            checker("SELTZO-TwoSum-ALL1-G00-D1-Y",
                diff_sign & (cy == ALL1) & (cx == G00) &
                (ey == ex) & (ex == fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, gx-1, fy+1), pos_zero)
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, gx+1:fx-1, fy+1), pos_zero)
            end

            checker("SELTZO-TwoSum-R1R0-ONE1-S6-X",
                same_sign & (cx == R1R0) & (cy == ONE1) &
                (ex > ey) & (fx + 1 == fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-R1R0-ONE1-S6-Y",
                same_sign & (cy == R1R0) & (cx == ONE1) &
                (ey > ex) & (fy + 1 == fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, ex), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE1-G00-D1-X",
                diff_sign & (cx == ONE1) & (cy == G00) &
                (fx == ey) & (ex == gy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fy, gy+1:fy), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE1-G00-D1-Y",
                diff_sign & (cy == ONE1) & (cx == G00) &
                (fy == ex) & (ey == gx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fx, gx+1:fx), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE1-MM01-D1-X",
                diff_sign & (cx == ONE1) & (cy == MM01) &
                (fx == ey) & (ex == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fx-1, fy+1), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE1-MM01-D1-Y",
                diff_sign & (cy == ONE1) & (cx == MM01) &
                (fy == ex) & (ey == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fy-1, fx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-R1R0-ALL1-S1-X",
                same_sign & (cx == R1R0) & (cy == ALL1) &
                (fx + 1 == ey) & (ex < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, gx, gx), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-R1R0-ALL1-S1-Y",
                same_sign & (cy == R1R0) & (cx == ALL1) &
                (fy + 1 == ex) & (ey < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, gy, gy), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-ALL1-ONE1-D2-X",
                diff_sign & (cx == ALL1) & (cy == ONE1) &
                (ex == ey) & (ey == fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, fy-1, fx+1), pos_zero)
            end
            checker("SELTZO-TwoSum-ALL1-ONE1-D2-Y",
                diff_sign & (cy == ALL1) & (cx == ONE1) &
                (ey == ex) & (ex == fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, fx-1, fy+1), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-TWO1-D4-X",
                diff_sign & (cx == POW2) & (cy == TWO1) &
                (ey == fy + 2) & (ex == ey + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ey-1, gy, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-TWO1-D4-Y",
                diff_sign & (cy == POW2) & (cx == TWO1) &
                (ex == fx + 2) & (ey == ex + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ex-1, gx, gx), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-MM10-D3-X",
                diff_sign & (cx == POW2) & (cy == MM10) &
                (ex == ey + 1) & (ey == fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ey-1, gy, fx), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-MM10-D3-Y",
                diff_sign & (cy == POW2) & (cx == MM10) &
                (ey == ex + 1) & (ex == fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ex-1, gx, fy), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-G10-D3-X",
                diff_sign & (cx == POW2) & (cy == G10) &
                (ex == gy + (p+2)) & (2 < fy - gy)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, fx+1:fy-1), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, fy+1), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, fx+1:fy), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, fx+1:fy-1), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, fy+1), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, fx+1:fy-1), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, fy+1), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-POW2-G10-D3-Y",
                diff_sign & (cy == POW2) & (cx == G10) &
                (ey == gx + (p+2)) & (2 < fx - gx)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, fy+1:fx-1), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, fx+1), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, fy+1:fx), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, fy+1:fx-1), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, fx+1), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, fy+1:fx-1), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, fx+1), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-R1R0-G00-S2-X",
                same_sign & (cx == R1R0) & (cy == G00) &
                (fx + 1 == ey) & (ex < fy + (p-3)) & (ex == gy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fy+1, fy+1), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fy, gy+2:fy-1), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fy, gy+2:fy), SELTZORange(sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-R1R0-G00-S2-Y",
                same_sign & (cy == R1R0) & (cx == G00) &
                (fy + 1 == ex) & (ey < fx + (p-3)) & (ey == gx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fx+1, fx+1), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fx, gx+2:fx-1), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fx, gx+2:fx), SELTZORange(sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-G01-POW2-D1-X",
                diff_sign & (cx == G01) & (cy == POW2) &
                (ex == ey + 1) & (ex == gx + (p-3)) & (fx + 1 == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ey, gx:fx-1, gx-2), pos_zero)
            end
            checker("SELTZO-TwoSum-G01-POW2-D1-Y",
                diff_sign & (cy == G01) & (cx == POW2) &
                (ey == ex + 1) & (ey == gy + (p-3)) & (fy + 1 == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ex, gy:fy-1, gy-2), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-R0R1-S6-X",
                same_sign & (cx == POW2) & (cy == R0R1) &
                (ex > ey + 1) & (ex < ey + (p-2)) & (ex == fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, gy+1), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-R0R1-S6-Y",
                same_sign & (cy == POW2) & (cx == R0R1) &
                (ey > ex + 1) & (ey < ex + (p-2)) & (ey == fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, gx+1), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-ALL1-G00-D2-X",
                diff_sign & (cx == ALL1) & (cy == G00) &
                (ex == ey) & (ex > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fy, fx+1), pos_zero)
            end
            checker("SELTZO-TwoSum-ALL1-G00-D2-Y",
                diff_sign & (cy == ALL1) & (cx == G00) &
                (ey == ex) & (ey > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fx, fy+1), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-ONE1-D6-X",
                diff_sign & (cx == POW2) & (cy == ONE1) &
                (ex == ey + 2) & (ex < fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, ey-1, fy), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-ONE1-D6-Y",
                diff_sign & (cy == POW2) & (cx == ONE1) &
                (ey == ex + 2) & (ey < fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, ex-1, fx), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-G10-S1-X",
                same_sign & (cx == POW2) & (cy == G10) &
                (ex == gy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gy+2:fy), SELTZORange(~sy, 0, 0, fx, fx-p, fx))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gy+2:fy-1), SELTZORange(sy, 0, 0, fx, fx-p, fx))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy+1), SELTZORange(sy, 0, 0, fx, fx-p, fx))
            end
            checker("SELTZO-TwoSum-POW2-G10-S1-Y",
                same_sign & (cy == POW2) & (cx == G10) &
                (ey == gx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gx+2:fx), SELTZORange(~sx, 0, 0, fy, fy-p, fy))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gx+2:fx-1), SELTZORange(sx, 0, 0, fy, fy-p, fy))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx+1), SELTZORange(sx, 0, 0, fy, fy-p, fy))
            end

            checker("SELTZO-TwoSum-R1R0-R0R1-S3-X",
                same_sign & (cx == R1R0) & (cy == R0R1) &
                (ex == ey + p) & (ex == fx + (p-1)) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, ex), SELTZORange(~sy, 1, 0, ey-1, fy-1, fy))
            end
            checker("SELTZO-TwoSum-R1R0-R0R1-S3-Y",
                same_sign & (cy == R1R0) & (cx == R0R1) &
                (ey == ex + p) & (ey == fy + (p-1)) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, ey), SELTZORange(~sx, 1, 0, ex-1, fx-1, fx))
            end

            checker("SELTZO-TwoSum-ONE1-G00-S2-X",
                same_sign & (cx == ONE1) & (cy == G00) &
                (ex == ey + 1) & (ex == fx + 2) & (fx > fy + 1) & (ex == gy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx-1, gy+1:fy-1), pos_zero)
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx-1, fy+1), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE1-G00-S2-Y",
                same_sign & (cy == ONE1) & (cx == G00) &
                (ey == ex + 1) & (ey == fy + 2) & (fy > fx + 1) & (ey == gx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy-1, gx+1:fx-1), pos_zero)
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy-1, fx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE1-ONE1-D6-X",
                diff_sign & (cx == ONE1) & (cy == ONE1) &
                (ex == ey + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx-1, fx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-ONE1-ONE1-D6-Y",
                diff_sign & (cy == ONE1) & (cx == ONE1) &
                (ey == ex + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy-1, fy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-TWO1-R1R0-D3-X",
                diff_sign & (cx == TWO1) & (cy == R1R0) &
                (ex == ey + 2) & (fx < fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, gy, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-TWO1-R1R0-D3-Y",
                diff_sign & (cy == TWO1) & (cx == R1R0) &
                (ey == ex + 2) & (fy < fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, gx, gy), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE1-R0R1-D3-X",
                diff_sign & (cx == ONE1) & (cy == R0R1) &
                (ex < ey + (p-1)) & (fx == ey + 1) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, ey), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-ONE1-R0R1-D3-Y",
                diff_sign & (cy == ONE1) & (cx == R0R1) &
                (ey < ex + (p-1)) & (fy == ex + 1) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, ex), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-R1R0-R1R0-S3-X",
                same_sign & (cx == R1R0) & (cy == R1R0) &
                (ex == ey + p) & (ex == fx + (p-1)) & (fx == ey + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, ex), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-R1R0-R1R0-S3-Y",
                same_sign & (cy == R1R0) & (cx == R1R0) &
                (ey == ex + p) & (ey == fy + (p-1)) & (fy == ex + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, ey), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-G11-POW2-S1-X",
                same_sign & (cx == G11) & (cy == POW2) &
                (fx == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, gx:fx-1, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-G11-POW2-S1-Y",
                same_sign & (cy == G11) & (cx == POW2) &
                (fy == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, gy:fy-1, gy), pos_zero)
            end

            checker("SELTZO-TwoSum-ALL1-R1R0-S4-X",
                same_sign & (cx == ALL1) & (cy == R1R0) &
                (ex < ey + (p-1)) & (ex > fy + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex+1, ey, ey+1), SELTZORange(sy, 1, 0, fx, fy, gy))
            end
            checker("SELTZO-TwoSum-ALL1-R1R0-S4-Y",
                same_sign & (cy == ALL1) & (cx == R1R0) &
                (ey < ex + (p-1)) & (ey > fx + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey+1, ex, ex+1), SELTZORange(sx, 1, 0, fy, fx, gx))
            end

            checker("SELTZO-TwoSum-ONE1-TWO1-S1-X",
                same_sign & (cx == ONE1) & (cy == TWO1) &
                (ex < ey + (p-1)) & (fx > ey) & (ex > fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey), SELTZORange(sy, 1, 0, fy, gy-1, gy))
            end
            checker("SELTZO-TwoSum-ONE1-TWO1-S1-Y",
                same_sign & (cy == ONE1) & (cx == TWO1) &
                (ey < ex + (p-1)) & (fy > ex) & (ey > fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex), SELTZORange(sx, 1, 0, fx, gx-1, gx))
            end

            checker("SELTZO-TwoSum-POW2-G01-S2-X",
                same_sign & (cx == POW2) & (cy == G01) &
                (ex == ey + 1) & (ey < gy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey-1, gy), SELTZORange(~sy, 0, 0, fx, fx-p, fx))
            end
            checker("SELTZO-TwoSum-POW2-G01-S2-Y",
                same_sign & (cy == POW2) & (cx == G01) &
                (ey == ex + 1) & (ex < gx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex-1, gx), SELTZORange(~sx, 0, 0, fy, fy-p, fy))
            end

            checker("SELTZO-TwoSum-ONE1-TWO1-D3-X",
                diff_sign & (cx == ONE1) & (cy == TWO1) &
                (fx == ey) & (ex == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fy, fy), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE1-TWO1-D3-Y",
                diff_sign & (cy == ONE1) & (cx == TWO1) &
                (fy == ex) & (ey == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fx, fx), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-G00-D3-X",
                diff_sign & (cx == POW2) & (cy == G00) &
                (ex == ey + (p+1)) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ex-1), SELTZORange(~sy, 1, 0, ey-1, fy, gy))
            end
            checker("SELTZO-TwoSum-POW2-G00-D3-Y",
                diff_sign & (cy == POW2) & (cx == G00) &
                (ey == ex + (p+1)) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ey-1), SELTZORange(~sx, 1, 0, ex-1, fx, gx))
            end

            checker("SELTZO-TwoSum-ONE1-MM01-S2-X",
                same_sign & (cx == ONE1) & (cy == MM01) &
                (ex < ey + p) & (fx > ey + 1) & (ex > fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey+1), SELTZORange(~sy, 1, 0, fy, gy-1, gy))
            end
            checker("SELTZO-TwoSum-ONE1-MM01-S2-Y",
                same_sign & (cy == ONE1) & (cx == MM01) &
                (ey < ex + p) & (fy > ex + 1) & (ey > fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex+1), SELTZORange(~sx, 1, 0, fx, gx-1, gx))
            end

            checker("SELTZO-TwoSum-POW2-G00-D4-X",
                diff_sign & (cx == POW2) & (cy == G00) &
                (ex == ey + 2) & (ex < gy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, ey-1, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-G00-D4-Y",
                diff_sign & (cy == POW2) & (cx == G00) &
                (ey == ex + 2) & (ey < gx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, ex-1, gx), pos_zero)
            end

            checker("SELTZO-TwoSum-G10-G00-D1-X",
                diff_sign & (cx == G10) & (cy == G00) &
                (ex == ey + (p-1)) & (fy == gy + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, gx), SELTZORange(sy, 0, 0, fy, gy:gy+1, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, gx), SELTZORange(sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, gx), SELTZORange(sy, 1, 0, fy, gy+1, gy))
            end
            checker("SELTZO-TwoSum-G10-G00-D1-Y",
                diff_sign & (cy == G10) & (cx == G00) &
                (ey == ex + (p-1)) & (fx == gx + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, gy), SELTZORange(sx, 0, 0, fx, gx:gx+1, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, gy), SELTZORange(sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, gy), SELTZORange(sx, 1, 0, fx, gx+1, gx))
            end

            checker("SELTZO-TwoSum-POW2-G00-S2-X",
                same_sign & (cx == POW2) & (cy == G00) &
                (ex < ey + (p-1)) & (ex > fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, ey), SELTZORange(sy, 0, 0, fy, gy:fy-2, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, ey), SELTZORange(sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, ey), SELTZORange(sy, 1, 0, fy, gy+1:fy-2, gy))
            end
            checker("SELTZO-TwoSum-POW2-G00-S2-Y",
                same_sign & (cy == POW2) & (cx == G00) &
                (ey < ex + (p-1)) & (ey > fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, ex), SELTZORange(sx, 0, 0, fx, gx:fx-2, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, ex), SELTZORange(sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, ex), SELTZORange(sx, 1, 0, fx, gx+1:fx-2, gx))
            end

            checker("SELTZO-TwoSum-TWO1-G10-D1-X",
                diff_sign & (cx == TWO1) & (cy == G10) &
                (ex == fx + (p-3)) & (fx == fy + 1) & (ey > fy + 2) & (fy == gy + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, gx-1), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, gx), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, gx-1), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, fx+1), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-TWO1-G10-D1-Y",
                diff_sign & (cy == TWO1) & (cx == G10) &
                (ey == fy + (p-3)) & (fy == fx + 1) & (ex > fx + 2) & (fx == gx + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, gy-1), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, gy), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, gy-1), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, fy+1), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-POW2-G00-S3-X",
                same_sign & (cx == POW2) & (cy == G00) &
                (ex == ey + p) & (ey == fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx+1, fx+2), SELTZORange(~sy, 0, 0, fx-1, gy:fy-1, gy))
            end
            checker("SELTZO-TwoSum-POW2-G00-S3-Y",
                same_sign & (cy == POW2) & (cx == G00) &
                (ey == ex + p) & (ex == fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy+1, fy+2), SELTZORange(~sx, 0, 0, fy-1, gx:fx-1, gx))
            end

            checker("SELTZO-TwoSum-G01-POW2-S2-X",
                same_sign & (cx == G01) & (cy == POW2) &
                (ex == ey) & (ex == gx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fx, gx+1:fx), SELTZORange(sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-G01-POW2-S2-Y",
                same_sign & (cy == G01) & (cx == POW2) &
                (ey == ex) & (ey == gy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fy, gy+1:fy), SELTZORange(sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-POW2-MM01-S3-X",
                same_sign & (cx == POW2) & (cy == MM01) &
                (ex < ey + p) & (ex > fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey+1, ey+1), SELTZORange(~sy, 1, 0, fy, gy-1, gy))
            end
            checker("SELTZO-TwoSum-POW2-MM01-S3-Y",
                same_sign & (cy == POW2) & (cx == MM01) &
                (ey < ex + p) & (ey > fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex+1, ex+1), SELTZORange(~sx, 1, 0, fx, gx-1, gx))
            end

            checker("SELTZO-TwoSum-TWO1-ONE1-D3-X",
                diff_sign & (cx == TWO1) & (cy == ONE1) &
                (ex < ey + (p-1)) & (fx > ey + 1) & (ex > fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-TWO1-ONE1-D3-Y",
                diff_sign & (cy == TWO1) & (cx == ONE1) &
                (ey < ex + (p-1)) & (fy > ex + 1) & (ey > fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-POW2-MM10-S3-X",
                same_sign & (cx == POW2) & (cy == MM10) &
                (ex == ey + p) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx+1, fx+2), SELTZORange(~sy, 1, 0, fx-1, fy, fx-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-MM10-S3-Y",
                same_sign & (cy == POW2) & (cx == MM10) &
                (ey == ex + p) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy+1, fy+2), SELTZORange(~sx, 1, 0, fy-1, fx, fy-(p-1)))
            end

            checker("SELTZO-TwoSum-R0R1-R1R0-D1-X",
                diff_sign & (cx == R0R1) & (cy == R1R0) &
                (ex == ey + 1) & (ex == fx + (p-1)) & (fx < fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, gy, fx, fx), pos_zero)
            end
            checker("SELTZO-TwoSum-R0R1-R1R0-D1-Y",
                diff_sign & (cy == R0R1) & (cx == R1R0) &
                (ey == ex + 1) & (ey == fy + (p-1)) & (fy < fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, gx, fy, fy), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-R0R1-S7-X",
                same_sign & (cx == POW2) & (cy == R0R1) &
                (ex < ey + (p-1)) & (ey < fy + (p-1)) & (ex > fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, ey), SELTZORange(sy, 1, 0, fy, ey-p, ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-R0R1-S7-Y",
                same_sign & (cy == POW2) & (cx == R0R1) &
                (ey < ex + (p-1)) & (ex < fx + (p-1)) & (ey > fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, ex), SELTZORange(sx, 1, 0, fx, ex-p, ex-(p-1)))
            end

            checker("SELTZO-TwoSum-G10-R0R1-D1-X",
                diff_sign & (cx == G10) & (cy == R0R1) &
                (ex == ey + p) & (ey == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, gx), SELTZORange(~sy, 1, 0, ey-1, fy-1, fy))
            end
            checker("SELTZO-TwoSum-G10-R0R1-D1-Y",
                diff_sign & (cy == G10) & (cx == R0R1) &
                (ey == ex + p) & (ex == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, gy), SELTZORange(~sx, 1, 0, ex-1, fx-1, fx))
            end

            checker("SELTZO-TwoSum-POW2-G10-S2-X",
                same_sign & (cx == POW2) & (cy == G10) &
                (ex < ey + p) & (ex > fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey+1, ey+1), SELTZORange(~sy, 0, 0, fy, gy:fy-2, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey+1, ey+1), SELTZORange(~sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey+1, ey+1), SELTZORange(~sy, 1, 0, fy, gy+1:fy-2, gy))
            end
            checker("SELTZO-TwoSum-POW2-G10-S2-Y",
                same_sign & (cy == POW2) & (cx == G10) &
                (ey < ex + p) & (ey > fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex+1, ex+1), SELTZORange(~sx, 0, 0, fx, gx:fx-2, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex+1, ex+1), SELTZORange(~sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex+1, ex+1), SELTZORange(~sx, 1, 0, fx, gx+1:fx-2, gx))
            end

            checker("SELTZO-TwoSum-ALL1-G00-S1-X",
                same_sign & (cx == ALL1) & (cy == G00) &
                (ex > ey) & (ex < gy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, gy), SELTZORange(~sy, 0, 0, fx+1, fx-(p-1), fx+1))
            end
            checker("SELTZO-TwoSum-ALL1-G00-S1-Y",
                same_sign & (cy == ALL1) & (cx == G00) &
                (ey > ex) & (ey < gx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, gx), SELTZORange(~sx, 0, 0, fy+1, fy-(p-1), fy+1))
            end

            checker("SELTZO-TwoSum-MM01-R1R0-D1-X",
                diff_sign & (cx == MM01) & (cy == R1R0) &
                (ex > fy + p) & (ex < ey + p) & (fx > ey + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-MM01-R1R0-D1-Y",
                diff_sign & (cy == MM01) & (cx == R1R0) &
                (ey > fx + p) & (ey < ex + p) & (fy > ex + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-POW2-TWO1-D5-X",
                diff_sign & (cx == POW2) & (cy == TWO1) &
                (ex == ey + (p+1)) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ex-1), SELTZORange(~sy, 1, 0, ey-1, fy, gy))
            end
            checker("SELTZO-TwoSum-POW2-TWO1-D5-Y",
                diff_sign & (cy == POW2) & (cx == TWO1) &
                (ey == ex + (p+1)) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ey-1), SELTZORange(~sx, 1, 0, ex-1, fx, gx))
            end

            checker("SELTZO-TwoSum-ONE1-ALL1-D3-X",
                diff_sign & (cx == ONE1) & (cy == ALL1) &
                (ex < ey + p) & (fx > ey + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx-1, ey+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-ONE1-ALL1-D3-Y",
                diff_sign & (cy == ONE1) & (cx == ALL1) &
                (ey < ex + p) & (fy > ex + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy-1, ex+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-ONE0-POW2-S3-X",
                same_sign & (cx == ONE0) & (cy == POW2) &
                (ex == ey + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx-1, fx), SELTZORange(~sy, 0, 0, ey, fy, ey))
            end
            checker("SELTZO-TwoSum-ONE0-POW2-S3-Y",
                same_sign & (cy == ONE0) & (cx == POW2) &
                (ey == ex + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy-1, fy), SELTZORange(~sx, 0, 0, ex, fx, ex))
            end

            checker("SELTZO-TwoSum-POW2-G01-D4-X",
                diff_sign & (cx == POW2) & (cy == G01) &
                (ex == ey + (p+1)) & (ey == fy + 2) & (ey == gy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ex-1), SELTZORange(~sy, 0, 0, ey-1, gy:fy-1, gy-1))
            end
            checker("SELTZO-TwoSum-POW2-G01-D4-Y",
                diff_sign & (cy == POW2) & (cx == G01) &
                (ey == ex + (p+1)) & (ex == fx + 2) & (ex == gx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ey-1), SELTZORange(~sx, 0, 0, ex-1, gx:fx-1, gx-1))
            end

            checker("SELTZO-TwoSum-G10-G00-D2-X",
                diff_sign & (cx == G10) & (cy == G00) &
                (ex > gy + (p+2)) & (ey > gx) & (ex == fx + 2) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, gx), SELTZORange(sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, gx), SELTZORange(sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, gx), SELTZORange(sy, 0, 0, fy, gy, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, gx), SELTZORange(sy, 0, 0, fy, gy, gy))
            end
            checker("SELTZO-TwoSum-G10-G00-D2-Y",
                diff_sign & (cy == G10) & (cx == G00) &
                (ey > gx + (p+2)) & (ex > gy) & (ey == fy + 2) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, gy), SELTZORange(sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, gy), SELTZORange(sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, gy), SELTZORange(sx, 0, 0, fx, gx, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, gy), SELTZORange(sx, 0, 0, fx, gx, gx))
            end

            checker("SELTZO-TwoSum-R0R1-R0R1-D2-X",
                diff_sign & (cx == R0R1) & (cy == R0R1) &
                (ex > ey + 1) & (fx + 1 == ey) & (ex == fy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, gy, gy+1), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-R0R1-R0R1-D2-Y",
                diff_sign & (cy == R0R1) & (cx == R0R1) &
                (ey > ex + 1) & (fy + 1 == ex) & (ey == fx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, gx, gx+1), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-POW2-G01-S3-X",
                same_sign & (cx == POW2) & (cy == G01) &
                (ex == ey + 2) & (ex == gy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gy+2:fy), SELTZORange(sy, 0, 0, fx-1, fx-(p+1), fx-1))
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, gy+2:fy-1), SELTZORange(sy, 0, 0, fx-1, fx-(p+1), fx-1))
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy+1), SELTZORange(sy, 0, 0, fx-1, fx-(p+1), fx-1))
            end
            checker("SELTZO-TwoSum-POW2-G01-S3-Y",
                same_sign & (cy == POW2) & (cx == G01) &
                (ey == ex + 2) & (ey == gx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gx+2:fx), SELTZORange(sx, 0, 0, fy-1, fy-(p+1), fy-1))
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, gx+2:fx-1), SELTZORange(sx, 0, 0, fy-1, fy-(p+1), fy-1))
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx+1), SELTZORange(sx, 0, 0, fy-1, fy-(p+1), fy-1))
            end

            checker("SELTZO-TwoSum-ONE1-G10-D2-X",
                diff_sign & (cx == ONE1) & (cy == G10) &
                (fx == ey) & (ex == gy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fx-1, gy+1:fy-1), pos_zero)
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fx-1, fy+1), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE1-G10-D2-Y",
                diff_sign & (cy == ONE1) & (cx == G10) &
                (fy == ex) & (ey == gx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fy-1, gx+1:fx-1), pos_zero)
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fy-1, fx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-R1R0-ONE1-D5-X",
                diff_sign & (cx == R1R0) & (cy == ONE1) &
                (ex == ey + (p-1)) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, gx, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-R1R0-ONE1-D5-Y",
                diff_sign & (cy == R1R0) & (cx == ONE1) &
                (ey == ex + (p-1)) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, gy, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-R1R0-R0R1-S4-X",
                same_sign & (cx == R1R0) & (cy == R0R1) &
                (ex == ey + p) & (ex == fx + (p-1)) & (ey == fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, ex), SELTZORange(~sy, 1, 0, ey-1, fy, fy-1))
            end
            checker("SELTZO-TwoSum-R1R0-R0R1-S4-Y",
                same_sign & (cy == R1R0) & (cx == R0R1) &
                (ey == ex + p) & (ey == fy + (p-1)) & (ex == fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, ey), SELTZORange(~sx, 1, 0, ex-1, fx, fx-1))
            end

            checker("SELTZO-TwoSum-POW2-G00-S4-X",
                same_sign & (cx == POW2) & (cy == G00) &
                (ex == ey + (p-1)) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey+1), SELTZORange(sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey+1), SELTZORange(sy, 0, 0, fy, gy, gy))
            end
            checker("SELTZO-TwoSum-POW2-G00-S4-Y",
                same_sign & (cy == POW2) & (cx == G00) &
                (ey == ex + (p-1)) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex+1), SELTZORange(sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex+1), SELTZORange(sx, 0, 0, fx, gx, gx))
            end

            checker("SELTZO-TwoSum-G00-ONE1-D1-X",
                diff_sign & (cx == G00) & (cy == ONE1) &
                (ex > fy + (p-1)) & (gx == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, gx+1:fx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-G00-ONE1-D1-Y",
                diff_sign & (cy == G00) & (cx == ONE1) &
                (ey > fx + (p-1)) & (gy == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, gy+1:fy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-TWO1-TWO1-D3-X",
                diff_sign & (cx == TWO1) & (cy == TWO1) &
                (fx > ey + 1) & (ex == fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy+1), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-TWO1-TWO1-D3-Y",
                diff_sign & (cy == TWO1) & (cx == TWO1) &
                (fy > ex + 1) & (ey == fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx+1), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-MM10-POW2-D1-X",
                diff_sign & (cx == MM10) & (cy == POW2) &
                (ex == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, fx, gx-1, fy+1), pos_zero)
            end
            checker("SELTZO-TwoSum-MM10-POW2-D1-Y",
                diff_sign & (cy == MM10) & (cx == POW2) &
                (ey == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, fy, gy-1, fx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE1-G00-S3-X",
                same_sign & (cx == ONE1) & (cy == G00) &
                (ex == ey + p) & (ex < fx + (p-2)) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, ey+2), SELTZORange(~sy, 1, 0, ey-1, fy, gy))
            end
            checker("SELTZO-TwoSum-ONE1-G00-S3-Y",
                same_sign & (cy == ONE1) & (cx == G00) &
                (ey == ex + p) & (ey < fy + (p-2)) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, ex+2), SELTZORange(~sx, 1, 0, ex-1, fx, gx))
            end

            checker("SELTZO-TwoSum-ALL1-MM01-S1-X",
                same_sign & (cx == ALL1) & (cy == MM01) &
                (ex > ey) & (fy + (p-3) > ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, gy), SELTZORange(~sy, 0, 0, fx+1, fx-(p-1), fx+1))
            end
            checker("SELTZO-TwoSum-ALL1-MM01-S1-Y",
                same_sign & (cy == ALL1) & (cx == MM01) &
                (ey > ex) & (fx + (p-3) > ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, gx), SELTZORange(~sx, 0, 0, fy+1, fy-(p-1), fy+1))
            end

            checker("SELTZO-TwoSum-POW2-ONE0-D3-X",
                diff_sign & (cx == POW2) & (cy == ONE0) &
                (ex == ey + 1) & (ey < fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, fy, fx, fx), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-ONE0-D3-Y",
                diff_sign & (cy == POW2) & (cx == ONE0) &
                (ey == ex + 1) & (ex < fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, fx, fy, fy), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-G11-D2-X",
                diff_sign & (cx == POW2) & (cy == G11) &
                (ex == ey + 1) & (ey == gy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, fy, gy:fy-2, fx), pos_zero)
                add_case!(lemma, SELTZORange(sx, 1, 0, fy, gy-2, fx), pos_zero)
                add_case!(lemma, SELTZORange(sx, 1, 0, fy, gy+1:fy-2, fx), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-G11-D2-Y",
                diff_sign & (cy == POW2) & (cx == G11) &
                (ey == ex + 1) & (ex == gx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, fx, gx:fx-2, fy), pos_zero)
                add_case!(lemma, SELTZORange(sy, 1, 0, fx, gx-2, fy), pos_zero)
                add_case!(lemma, SELTZORange(sy, 1, 0, fx, gx+1:fx-2, fy), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-G01-S4-X",
                same_sign & (cx == POW2) & (cy == G01) &
                (ex > ey + 1) & (ex < gy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gy), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-G01-S4-Y",
                same_sign & (cy == POW2) & (cx == G01) &
                (ey > ex + 1) & (ey < gx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gx), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-POW2-TWO0-D2-X",
                diff_sign & (cx == POW2) & (cy == TWO0) &
                (ex == ey + (p+1)) & (ey < fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ex-1), SELTZORange(~sy, 1, 0, fy, gy-1, ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-TWO0-D2-Y",
                diff_sign & (cy == POW2) & (cx == TWO0) &
                (ey == ex + (p+1)) & (ex < fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ey-1), SELTZORange(~sx, 1, 0, fx, gx-1, ex-(p-1)))
            end

            checker("SELTZO-TwoSum-MM01-POW2-S1-X",
                same_sign & (cx == MM01) & (cy == POW2) &
                (ex < ey + (p-1)) & (fx > ey + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-MM01-POW2-S1-Y",
                same_sign & (cy == MM01) & (cx == POW2) &
                (ey < ex + (p-1)) & (fy > ex + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-R0R1-D9-X",
                diff_sign & (cx == POW2) & (cy == R0R1) &
                (ex < ey + p) & (ey < fy + (p-1)) & (fy + (p+1) < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey-1, ey), SELTZORange(sy, 1, 0, fy, ey-p, ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-R0R1-D9-Y",
                diff_sign & (cy == POW2) & (cx == R0R1) &
                (ey < ex + p) & (ex < fx + (p-1)) & (fx + (p+1) < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex-1, ex), SELTZORange(sx, 1, 0, fx, ex-p, ex-(p-1)))
            end

            checker("SELTZO-TwoSum-POW2-ONE1-D7-X",
                diff_sign & (cx == POW2) & (cy == ONE1) &
                (ex == ey + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fx-1, ex-1), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-POW2-ONE1-D7-Y",
                diff_sign & (cy == POW2) & (cx == ONE1) &
                (ey == ex + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fy-1, ey-1), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-G00-ONE1-D2-X",
                diff_sign & (cx == G00) & (cy == ONE1) &
                (fx + 1 < ey) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey-1, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-G00-ONE1-D2-Y",
                diff_sign & (cy == G00) & (cx == ONE1) &
                (fy + 1 < ex) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex-1, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-MM01-ONE1-D2-X",
                diff_sign & (cx == MM01) & (cy == ONE1) &
                (ex == ey + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-MM01-ONE1-D2-Y",
                diff_sign & (cy == MM01) & (cx == ONE1) &
                (ey == ex + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ONE0-ONE1-S1-X",
                same_sign & (cx == ONE0) & (cy == ONE1) &
                (ex == ey + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx-1, fx), SELTZORange(~sy, 1, 0, ey-1, fy-1, fy))
            end
            checker("SELTZO-TwoSum-ONE0-ONE1-S1-Y",
                same_sign & (cy == ONE0) & (cx == ONE1) &
                (ey == ex + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy-1, fy), SELTZORange(~sx, 1, 0, ex-1, fx-1, fx))
            end

            checker("SELTZO-TwoSum-TWO0-POW2-S2-X",
                same_sign & (cx == TWO0) & (cy == POW2) &
                (ex < fx + (p-3)) & (fx + 1 == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, gx, gx), SELTZORange(~sy, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end
            checker("SELTZO-TwoSum-TWO0-POW2-S2-Y",
                same_sign & (cy == TWO0) & (cx == POW2) &
                (ey < fy + (p-3)) & (fy + 1 == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, gy, gy), SELTZORange(~sx, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end

            checker("SELTZO-TwoSum-ONE1-ALL1-D4-X",
                diff_sign & (cx == ONE1) & (cy == ALL1) &
                (ex == ey + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, fx, fy+1, fy+1), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE1-ALL1-D4-Y",
                diff_sign & (cy == ONE1) & (cx == ALL1) &
                (ey == ex + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, fy, fx+1, fx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-R1R0-G00-S3-X",
                same_sign & (cx == R1R0) & (cy == G00) &
                (ex + 1 > ey) & (fx + 1 < ey) & (ex < gy + (p-2)) & (fx + 1 > fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey-1, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-R1R0-G00-S3-Y",
                same_sign & (cy == R1R0) & (cx == G00) &
                (ey + 1 > ex) & (fy + 1 < ex) & (ey < gx + (p-2)) & (fy + 1 > fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex-1, gx), pos_zero)
            end

            checker("SELTZO-TwoSum-ALL1-G10-S1-X",
                same_sign & (cx == ALL1) & (cy == G10) &
                (ex > ey) & (ex < gy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, gy), SELTZORange(~sy, 0, 0, fx+1, fx-(p-1), fx+1))
            end
            checker("SELTZO-TwoSum-ALL1-G10-S1-Y",
                same_sign & (cy == ALL1) & (cx == G10) &
                (ey > ex) & (ey < gx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, gx), SELTZORange(~sx, 0, 0, fy+1, fy-(p-1), fy+1))
            end

            checker("SELTZO-TwoSum-TWO1-TWO1-D4-X",
                diff_sign & (cx == TWO1) & (cy == TWO1) &
                (fx > ey + 1) & (fy + (p-2) > ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-TWO1-TWO1-D4-Y",
                diff_sign & (cy == TWO1) & (cx == TWO1) &
                (fy > ex + 1) & (fx + (p-2) > ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, gx), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-TWO1-D6-X",
                diff_sign & (cx == POW2) & (cy == TWO1) &
                (ex > ey + 2) & (fy + (p-1) > ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-TWO1-D6-Y",
                diff_sign & (cy == POW2) & (cx == TWO1) &
                (ey > ex + 2) & (fx + (p-1) > ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, gx), pos_zero)
            end

            checker("SELTZO-TwoSum-TWO1-R1R0-D4-X",
                diff_sign & (cx == TWO1) & (cy == R1R0) &
                (fx == ey) & (fy + (p+1) < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, gx-1, gx), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-TWO1-R1R0-D4-Y",
                diff_sign & (cy == TWO1) & (cx == R1R0) &
                (fy == ex) & (fx + (p+1) < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, gy-1, gy), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-ONE1-ONE1-S2-X",
                same_sign & (cx == ONE1) & (cy == ONE1) &
                (ex < ey + (p-1)) & (fx > ey) & (fy + (p-1) < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-ONE1-ONE1-S2-Y",
                same_sign & (cy == ONE1) & (cx == ONE1) &
                (ey < ex + (p-1)) & (fy > ex) & (fx + (p-1) < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-POW2-TWO0-S1-X",
                same_sign & (cx == POW2) & (cy == TWO0) &
                (ex > ey + 1) & (fy + (p-2) > ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gy), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-TWO0-S1-Y",
                same_sign & (cy == POW2) & (cx == TWO0) &
                (ey > ex + 1) & (fx + (p-2) > ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gx), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-R0R1-ONE1-S2-X",
                same_sign & (cx == R0R1) & (cy == ONE1) &
                (ex < ey + (p-1)) & (ex > fx + 2) & (fx + 1 > ey) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, gx, ey), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-R0R1-ONE1-S2-Y",
                same_sign & (cy == R0R1) & (cx == ONE1) &
                (ey < ex + (p-1)) & (ey > fy + 2) & (fy + 1 > ex) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, gy, ex), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ONE1-R1R0-D4-X",
                diff_sign & (cx == ONE1) & (cy == R1R0) &
                (ex < ey + p) & (fx > ey + 1) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx-1, ey+1), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-ONE1-R1R0-D4-Y",
                diff_sign & (cy == ONE1) & (cx == R1R0) &
                (ey < ex + p) & (fy > ex + 1) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy-1, ex+1), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-ONE1-R0R1-D4-X",
                diff_sign & (cx == ONE1) & (cy == R0R1) &
                (ex < ey + (p-1)) & (fx > ey) & (ey < fy + (p-1)) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx-1, ey), SELTZORange(sy, 1, 0, fy, ey-p, ey-(p-1)))
            end
            checker("SELTZO-TwoSum-ONE1-R0R1-D4-Y",
                diff_sign & (cy == ONE1) & (cx == R0R1) &
                (ey < ex + (p-1)) & (fy > ex) & (ex < fx + (p-1)) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy-1, ex), SELTZORange(sx, 1, 0, fx, ex-p, ex-(p-1)))
            end

            checker("SELTZO-TwoSum-POW2-G00-D5-X",
                diff_sign & (cx == POW2) & (cy == G00) &
                (ex > ey + 2) & (ex < gy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-G00-D5-Y",
                diff_sign & (cy == POW2) & (cx == G00) &
                (ey > ex + 2) & (ey < gx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, gx), pos_zero)
            end

            checker("SELTZO-TwoSum-MM01-POW2-D1-X",
                diff_sign & (cx == MM01) & (cy == POW2) &
                (ex < ey + (p-1)) & (fx > ey + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-MM01-POW2-D1-Y",
                diff_sign & (cy == MM01) & (cx == POW2) &
                (ey < ex + (p-1)) & (fy > ex + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE1-R0R1-S1-X",
                same_sign & (cx == ONE1) & (cy == R0R1) &
                (ex < ey + (p-1)) & (fx > ey) & (ey > fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-ONE1-R0R1-S1-Y",
                same_sign & (cy == ONE1) & (cx == R0R1) &
                (ey < ex + (p-1)) & (fy > ex) & (ex > fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-POW2-G00-D6-X",
                diff_sign & (cx == POW2) & (cy == G00) &
                (fy + (p-1) == ex) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, fy+1), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, fy), SELTZORange(sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-POW2-G00-D6-Y",
                diff_sign & (cy == POW2) & (cx == G00) &
                (fx + (p-1) == ey) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, fx+1), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, fx), SELTZORange(sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-ONE0-ONE1-D4-X",
                diff_sign & (cx == ONE0) & (cy == ONE1) &
                (ex == ey + (p-1)) & (ex < fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey+1), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-ONE0-ONE1-D4-Y",
                diff_sign & (cy == ONE0) & (cx == ONE1) &
                (ey == ex + (p-1)) & (ey < fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex+1), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-G10-R1R0-D1-X",
                diff_sign & (cx == G10) & (cy == R1R0) &
                (ex > fx + 2) & (fx > ey + 1) & (ey + 1 > gx) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, gx), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx+1, gx), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-G10-R1R0-D1-Y",
                diff_sign & (cy == G10) & (cx == R1R0) &
                (ey > fy + 2) & (fy > ex + 1) & (ex + 1 > gy) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, gy), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy+1, gy), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-R1R0-TWO1-S1-X",
                same_sign & (cx == R1R0) & (cy == TWO1) &
                (ex > fx + (p-3)) & (fx == fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, ey), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-R1R0-TWO1-S1-Y",
                same_sign & (cy == R1R0) & (cx == TWO1) &
                (ey > fy + (p-3)) & (fy == fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, ex), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-TWO1-MM01-D1-X",
                diff_sign & (cx == TWO1) & (cy == MM01) &
                (fx > ey + 1) & (fy + (p-1) == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy+1), SELTZORange(sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-TWO1-MM01-D1-Y",
                diff_sign & (cy == TWO1) & (cx == MM01) &
                (fy > ex + 1) & (fx + (p-1) == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx+1), SELTZORange(sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-G10-R0R1-S1-X",
                same_sign & (cx == G10) & (cy == R0R1) &
                (ex > ey + (p-1)) & (ey > fy + (p-3)) & (fx < fy + (p+3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fx), SELTZORange(~sy, 1, 0, ey-1, fy, fy-1))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fx-1), SELTZORange(~sy, 1, 0, ey-1, fy, fy-1))
            end
            checker("SELTZO-TwoSum-G10-R0R1-S1-Y",
                same_sign & (cy == G10) & (cx == R0R1) &
                (ey > ex + (p-1)) & (ex > fx + (p-3)) & (fy < fx + (p+3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fy), SELTZORange(~sx, 1, 0, ex-1, fx, fx-1))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fy-1), SELTZORange(~sx, 1, 0, ex-1, fx, fx-1))
            end

            checker("SELTZO-TwoSum-POW2-G11-D3-X",
                diff_sign & (cx == POW2) & (cy == G11) &
                (ex == ey + 1) & (ey < gy + (p-2)) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, fy, gy, fx), pos_zero)
                add_case!(lemma, SELTZORange(sx, 1, 0, fy, gy-1, fx), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-G11-D3-Y",
                diff_sign & (cy == POW2) & (cx == G11) &
                (ey == ex + 1) & (ex < gx + (p-2)) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, fx, gx, fy), pos_zero)
                add_case!(lemma, SELTZORange(sy, 1, 0, fx, gx-1, fy), pos_zero)
            end

            checker("SELTZO-TwoSum-ALL1-R1R0-S5-X",
                same_sign & (cx == ALL1) & (cy == R1R0) &
                (ex == ey + (p-3)) & (ey == fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, ey), SELTZORange(sy, 0, 0, fy, fx-(p-1), fy))
            end
            checker("SELTZO-TwoSum-ALL1-R1R0-S5-Y",
                same_sign & (cy == ALL1) & (cx == R1R0) &
                (ey == ex + (p-3)) & (ex == fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, ex), SELTZORange(sx, 0, 0, fx, fy-(p-1), fx))
            end

            checker("SELTZO-TwoSum-G11-POW2-D1-X",
                diff_sign & (cx == G11) & (cy == POW2) &
                (ex == ey) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fx, fy+1), pos_zero)
            end
            checker("SELTZO-TwoSum-G11-POW2-D1-Y",
                diff_sign & (cy == G11) & (cx == POW2) &
                (ey == ex) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fy, fx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE1-R1R0-D5-X",
                diff_sign & (cx == ONE1) & (cy == R1R0) &
                (fx > ey + 1) & (fy + p > ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx-1, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE1-R1R0-D5-Y",
                diff_sign & (cy == ONE1) & (cx == R1R0) &
                (fy > ex + 1) & (fx + p > ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy-1, gx), pos_zero)
            end

            checker("SELTZO-TwoSum-G11-R1R0-D1-X",
                diff_sign & (cx == G11) & (cy == R1R0) &
                (ex == ey + p) & (ex < gx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey+2), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-G11-R1R0-D1-Y",
                diff_sign & (cy == G11) & (cx == R1R0) &
                (ey == ex + p) & (ey < gy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex+2), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-POW2-G00-D7-X",
                diff_sign & (cx == POW2) & (cy == G00) &
                (ex == ey + p) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fx-1, ex-1), SELTZORange(sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fx-1, ex-1), SELTZORange(sy, 0, 0, fy, gy, gy))
            end
            checker("SELTZO-TwoSum-POW2-G00-D7-Y",
                diff_sign & (cy == POW2) & (cx == G00) &
                (ey == ex + p) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fy-1, ey-1), SELTZORange(sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fy-1, ey-1), SELTZORange(sx, 0, 0, fx, gx, gx))
            end

            checker("SELTZO-TwoSum-ONE1-POW2-S2-X",
                same_sign & (cx == ONE1) & (cy == POW2) &
                (ex < ey + (p-1)) & (fx > ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE1-POW2-S2-Y",
                same_sign & (cy == ONE1) & (cx == POW2) &
                (ey < ex + (p-1)) & (fy > ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE1-TWO1-D4-X",
                diff_sign & (cx == ONE1) & (cy == TWO1) &
                (fx + 2 == ey) & (fy + (p+1) < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fx+1, fx), SELTZORange(sy, 1, 0, fy, gy-1, gy))
            end
            checker("SELTZO-TwoSum-ONE1-TWO1-D4-Y",
                diff_sign & (cy == ONE1) & (cx == TWO1) &
                (fy + 2 == ex) & (fx + (p+1) < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fy+1, fy), SELTZORange(sx, 1, 0, fx, gx-1, gx))
            end

            checker("SELTZO-TwoSum-POW2-TWO1-D7-X",
                diff_sign & (cx == POW2) & (cy == TWO1) &
                (ex == ey + 2) & (ey < fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, ey-1, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-TWO1-D7-Y",
                diff_sign & (cy == POW2) & (cx == TWO1) &
                (ey == ex + 2) & (ex < fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, ex-1, gx), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-R0R1-S8-X",
                same_sign & (cx == POW2) & (cy == R0R1) &
                (ex == ey + 1) & (ey > fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey-1, ey), SELTZORange(sy, 0, 0, fx, fx-p, fx))
            end
            checker("SELTZO-TwoSum-POW2-R0R1-S8-Y",
                same_sign & (cy == POW2) & (cx == R0R1) &
                (ey == ex + 1) & (ex > fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex-1, ex), SELTZORange(sx, 0, 0, fy, fy-p, fy))
            end

            checker("SELTZO-TwoSum-POW2-G00-S5-X",
                same_sign & (cx == POW2) & (cy == G00) &
                (ex == ey + p) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx+1, fx+2), SELTZORange(~sy, 1, 0, fx-1, fy, gy))
            end
            checker("SELTZO-TwoSum-POW2-G00-S5-Y",
                same_sign & (cy == POW2) & (cx == G00) &
                (ey == ex + p) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy+1, fy+2), SELTZORange(~sx, 1, 0, fy-1, fx, gx))
            end

            checker("SELTZO-TwoSum-TWO1-ONE0-D1-X",
                diff_sign & (cx == TWO1) & (cy == ONE0) &
                (ex == ey + 1) & (fx > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, fx, gx-1, ey-(p-1)), pos_zero)
            end
            checker("SELTZO-TwoSum-TWO1-ONE0-D1-Y",
                diff_sign & (cy == TWO1) & (cx == ONE0) &
                (ey == ex + 1) & (fy > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, fy, gy-1, ex-(p-1)), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-MM10-D4-X",
                diff_sign & (cx == POW2) & (cy == MM10) &
                (ex > ey + 2) & (fy + (p-1) == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, fy), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-MM10-D4-Y",
                diff_sign & (cy == POW2) & (cx == MM10) &
                (ey > ex + 2) & (fx + (p-1) == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, fx), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-G10-ONE1-S1-X",
                same_sign & (cx == G10) & (cy == ONE1) &
                (fx == ey) & (fx == gx + 2) & (fy + (p-1) < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, gx-1, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx-1, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-G10-ONE1-S1-Y",
                same_sign & (cy == G10) & (cx == ONE1) &
                (fy == ex) & (fy == gy + 2) & (fx + (p-1) < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, gy-1, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy-1, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-G00-POW2-S1-X",
                same_sign & (cx == G00) & (cy == POW2) &
                (ex < ey + (p-1)) & (ey < gx)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-G00-POW2-S1-Y",
                same_sign & (cy == G00) & (cx == POW2) &
                (ey < ex + (p-1)) & (ex < gy)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE0-R1R0-D3-X",
                diff_sign & (cx == ONE0) & (cy == R1R0) &
                (ex == ey + p) & (ex < fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey+2), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-ONE0-R1R0-D3-Y",
                diff_sign & (cy == ONE0) & (cx == R1R0) &
                (ey == ex + p) & (ey < fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex+2), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-ONE0-POW2-D2-X",
                diff_sign & (cx == ONE0) & (cy == POW2) &
                (ex < ey + (p-1)) & (fx > ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE0-POW2-D2-Y",
                diff_sign & (cy == ONE0) & (cx == POW2) &
                (ey < ex + (p-1)) & (fy > ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, ex), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-TWO1-D8-X",
                diff_sign & (cx == POW2) & (cy == TWO1) &
                (ex == ey + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fx-1, ex-1), SELTZORange(sy, 1, 0, fy, gy-1, gy))
            end
            checker("SELTZO-TwoSum-POW2-TWO1-D8-Y",
                diff_sign & (cy == POW2) & (cx == TWO1) &
                (ey == ex + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fy-1, ey-1), SELTZORange(sx, 1, 0, fx, gx-1, gx))
            end

            checker("SELTZO-TwoSum-ONE0-ONE1-S2-X",
                same_sign & (cx == ONE0) & (cy == ONE1) &
                (fx == ey) & (fy + (p-2) > ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fy, fy), SELTZORange(~sy, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end
            checker("SELTZO-TwoSum-ONE0-ONE1-S2-Y",
                same_sign & (cy == ONE0) & (cx == ONE1) &
                (fy == ex) & (fx + (p-2) > ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fx, fx), SELTZORange(~sx, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end

            checker("SELTZO-TwoSum-ONE1-R1R0-D6-X",
                diff_sign & (cx == ONE1) & (cy == R1R0) &
                (fx == ey + 1) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex-p, ex), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-ONE1-R1R0-D6-Y",
                diff_sign & (cy == ONE1) & (cx == R1R0) &
                (fy == ex + 1) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey-p, ey), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-POW2-TWO1-D9-X",
                diff_sign & (cx == POW2) & (cy == TWO1) &
                (ex == ey + (p+1)) & (ey == fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ex-1), SELTZORange(~sy, 0, 0, ey-1, gy, gy))
            end
            checker("SELTZO-TwoSum-POW2-TWO1-D9-Y",
                diff_sign & (cy == POW2) & (cx == TWO1) &
                (ey == ex + (p+1)) & (ex == fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ey-1), SELTZORange(~sx, 0, 0, ex-1, gx, gx))
            end

            checker("SELTZO-TwoSum-ONE1-TWO1-D5-X",
                diff_sign & (cx == ONE1) & (cy == TWO1) &
                (fx + 1 == ey) & (fy + (p+1) < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fx-1, fx), SELTZORange(sy, 1, 0, fy, gy-1, gy))
            end
            checker("SELTZO-TwoSum-ONE1-TWO1-D5-Y",
                diff_sign & (cy == ONE1) & (cx == TWO1) &
                (fy + 1 == ex) & (fx + (p+1) < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fy-1, fy), SELTZORange(sx, 1, 0, fx, gx-1, gx))
            end

            checker("SELTZO-TwoSum-POW2-R0R1-S9-X",
                same_sign & (cx == POW2) & (cy == R0R1) &
                (ex == ey + 1) & (ey > fy + 2) & (fy + p > ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey-1, gy), SELTZORange(~sy, 0, 0, fx, fx-p, fx))
            end
            checker("SELTZO-TwoSum-POW2-R0R1-S9-Y",
                same_sign & (cy == POW2) & (cx == R0R1) &
                (ey == ex + 1) & (ex > fx + 2) & (fx + p > ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex-1, gx), SELTZORange(~sx, 0, 0, fy, fy-p, fy))
            end

            checker("SELTZO-TwoSum-R1R0-R0R1-D3-X",
                diff_sign & (cx == R1R0) & (cy == R0R1) &
                (ex == ey + (p-1)) & (ex > fx + 2) & (ey < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, gx, gx), SELTZORange(sy, 1, 0, fy, ey-p, ey-(p-1)))
            end
            checker("SELTZO-TwoSum-R1R0-R0R1-D3-Y",
                diff_sign & (cy == R1R0) & (cx == R0R1) &
                (ey == ex + (p-1)) & (ey > fy + 2) & (ex < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, gy, gy), SELTZORange(sx, 1, 0, fx, ex-p, ex-(p-1)))
            end

            checker("SELTZO-TwoSum-R1R0-G00-S4-X",
                same_sign & (cx == R1R0) & (cy == G00) &
                (ex < fx + (p-1)) & (fx + 2 == ey) & (fy + (p-1) < ex) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, gx, gx), SELTZORange(sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, gx, gx), SELTZORange(sy, 0, 0, fy, gy, gy))
            end
            checker("SELTZO-TwoSum-R1R0-G00-S4-Y",
                same_sign & (cy == R1R0) & (cx == G00) &
                (ey < fy + (p-1)) & (fy + 2 == ex) & (fx + (p-1) < ey) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, gy, gy), SELTZORange(sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, gy, gy), SELTZORange(sx, 0, 0, fx, gx, gx))
            end

            checker("SELTZO-TwoSum-G00-POW2-D1-X",
                diff_sign & (cx == G00) & (cy == POW2) &
                (ex == ey + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-G00-POW2-D1-Y",
                diff_sign & (cy == G00) & (cx == POW2) &
                (ey == ex + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, gy), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-G11-S2-X",
                same_sign & (cx == POW2) & (cy == G11) &
                (ex > ey + 1) & (ex < gy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gy), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-G11-S2-Y",
                same_sign & (cy == POW2) & (cx == G11) &
                (ey > ex + 1) & (ey < gx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gx), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-G11-POW2-S2-X",
                same_sign & (cx == G11) & (cy == POW2) &
                (ex + 1 > ey) & (fx + 1 < ey) & (ex < gx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey-1, gx), SELTZORange(~sy, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end
            checker("SELTZO-TwoSum-G11-POW2-S2-Y",
                same_sign & (cy == G11) & (cx == POW2) &
                (ey + 1 > ex) & (fy + 1 < ex) & (ey < gy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex-1, gy), SELTZORange(~sx, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end

            checker("SELTZO-TwoSum-R1R0-G10-S1-X",
                same_sign & (cx == R1R0) & (cy == G10) &
                (ex < fx + (p-1)) & (fx + 1 < ey) & (fy == gy + 2) & (ex == gy + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex+1, ey, gx), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 0, 1, ex+1, ey, gx), SELTZORange(sy, 1, 0, fy-1, gy-1, gy))
            end
            checker("SELTZO-TwoSum-R1R0-G10-S1-Y",
                same_sign & (cy == R1R0) & (cx == G10) &
                (ey < fy + (p-1)) & (fy + 1 < ex) & (fx == gx + 2) & (ey == gx + (p+1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey+1, ex, gy), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 0, 1, ey+1, ex, gy), SELTZORange(sx, 1, 0, fx-1, gx-1, gx))
            end

            checker("SELTZO-TwoSum-POW2-R0R1-D10-X",
                diff_sign & (cx == POW2) & (cy == R0R1) &
                (ex == ey + 2) & (ey < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, ey-1, gy), SELTZORange(~sy, 0, 0, fx-1, fx-(p+1), fx-1))
            end
            checker("SELTZO-TwoSum-POW2-R0R1-D10-Y",
                diff_sign & (cy == POW2) & (cx == R0R1) &
                (ey == ex + 2) & (ex < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, ex-1, gx), SELTZORange(~sx, 0, 0, fy-1, fy-(p+1), fy-1))
            end

            checker("SELTZO-TwoSum-POW2-G00-D8-X",
                diff_sign & (cx == POW2) & (cy == G00) &
                (ex == ey + p) & (fy == gy + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fx-1, ex-1), SELTZORange(sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fx-1, ex-1), SELTZORange(sy, 0, 0, fy, gy, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fx-1, ex-1), SELTZORange(sy, 0, 0, fy, gy+1, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fx-1, ex-1), SELTZORange(sy, 1, 0, fy, gy+1, gy))
            end
            checker("SELTZO-TwoSum-POW2-G00-D8-Y",
                diff_sign & (cy == POW2) & (cx == G00) &
                (ey == ex + p) & (fx == gx + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fy-1, ey-1), SELTZORange(sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fy-1, ey-1), SELTZORange(sx, 0, 0, fx, gx, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fy-1, ey-1), SELTZORange(sx, 0, 0, fx, gx+1, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fy-1, ey-1), SELTZORange(sx, 1, 0, fx, gx+1, gx))
            end

            checker("SELTZO-TwoSum-TWO1-POW2-S2-X",
                same_sign & (cx == TWO1) & (cy == POW2) &
                (ex < ey + (p-1)) & (fx > ey + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-TWO1-POW2-S2-Y",
                same_sign & (cy == TWO1) & (cx == POW2) &
                (ey < ex + (p-1)) & (fy > ex + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex), pos_zero)
            end

            checker("SELTZO-TwoSum-R1R0-TWO1-S2-X",
                same_sign & (cx == R1R0) & (cy == TWO1) &
                (fx + 1 == ey) & (fy + (p-2) == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fy+1, fy+1), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-R1R0-TWO1-S2-Y",
                same_sign & (cy == R1R0) & (cx == TWO1) &
                (fy + 1 == ex) & (fx + (p-2) == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fx+1, fx+1), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-POW2-G00-S6-X",
                same_sign & (cx == POW2) & (cy == G00) &
                (ex == ey + (p-1)) & (fy == gy + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey+1), SELTZORange(sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey+1), SELTZORange(sy, 0, 0, fy, gy, gy))
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey+1), SELTZORange(sy, 0, 0, fy, gy+1, gy))
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey+1), SELTZORange(sy, 1, 0, fy, gy+1, gy))
            end
            checker("SELTZO-TwoSum-POW2-G00-S6-Y",
                same_sign & (cy == POW2) & (cx == G00) &
                (ey == ex + (p-1)) & (fx == gx + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex+1), SELTZORange(sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex+1), SELTZORange(sx, 0, 0, fx, gx, gx))
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex+1), SELTZORange(sx, 0, 0, fx, gx+1, gx))
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex+1), SELTZORange(sx, 1, 0, fx, gx+1, gx))
            end

            checker("SELTZO-TwoSum-G00-R1R0-D2-X",
                diff_sign & (cx == G00) & (cy == R1R0) &
                (fx == ey + 3) & (fx == gx + 2) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fx), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fx-1), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-G00-R1R0-D2-Y",
                diff_sign & (cy == G00) & (cx == R1R0) &
                (fy == ex + 3) & (fy == gy + 2) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fy), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fy-1), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-ONE1-R1R0-S1-X",
                same_sign & (cx == ONE1) & (cy == R1R0) &
                (ex < fx + (p-2)) & (fx == ey + 2) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fx-1), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-ONE1-R1R0-S1-Y",
                same_sign & (cy == ONE1) & (cx == R1R0) &
                (ey < fy + (p-2)) & (fy == ex + 2) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fy-1), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-ALL1-ONE1-S3-X",
                same_sign & (cx == ALL1) & (cy == ONE1) &
                (ex > ey) & (fy + (p-2) == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, ey), SELTZORange(sy, 0, 0, fx+1, fx-(p-1), fx+1))
            end
            checker("SELTZO-TwoSum-ALL1-ONE1-S3-Y",
                same_sign & (cy == ALL1) & (cx == ONE1) &
                (ey > ex) & (fx + (p-2) == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, ex), SELTZORange(sx, 0, 0, fy+1, fy-(p-1), fy+1))
            end

            checker("SELTZO-TwoSum-MM10-POW2-D2-X",
                diff_sign & (cx == MM10) & (cy == POW2) &
                (ex == ey + p) & (ex < fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey+2), SELTZORange(~sy, 0, 0, ey, fy, ey))
            end
            checker("SELTZO-TwoSum-MM10-POW2-D2-Y",
                diff_sign & (cy == MM10) & (cx == POW2) &
                (ey == ex + p) & (ey < fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex+2), SELTZORange(~sx, 0, 0, ex, fx, ex))
            end

            checker("SELTZO-TwoSum-G10-R0R1-D2-X",
                diff_sign & (cx == G10) & (cy == R0R1) &
                (ex == ey + p) & (ey > fy + 2) & (ey < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, gx), SELTZORange(~sy, 1, 0, ey-1, fy, ey-(p-1)))
            end
            checker("SELTZO-TwoSum-G10-R0R1-D2-Y",
                diff_sign & (cy == G10) & (cx == R0R1) &
                (ey == ex + p) & (ex > fx + 2) & (ex < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, gy), SELTZORange(~sx, 1, 0, ex-1, fx, ex-(p-1)))
            end

            checker("SELTZO-TwoSum-POW2-G01-D5-X",
                diff_sign & (cx == POW2) & (cy == G01) &
                (ex == ey + 2) & (ex < gy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, ey-1, gy), SELTZORange(~sy, 0, 0, fx-1, fx-(p+1), fx-1))
            end
            checker("SELTZO-TwoSum-POW2-G01-D5-Y",
                diff_sign & (cy == POW2) & (cx == G01) &
                (ey == ex + 2) & (ey < gx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, ex-1, gx), SELTZORange(~sx, 0, 0, fy-1, fy-(p+1), fy-1))
            end

            checker("SELTZO-TwoSum-ONE1-TWO1-D6-X",
                diff_sign & (cx == ONE1) & (cy == TWO1) &
                (fx > ey + 1) & (fy + (p-1) == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx-1, fy+1), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-ONE1-TWO1-D6-Y",
                diff_sign & (cy == ONE1) & (cx == TWO1) &
                (fy > ex + 1) & (fx + (p-1) == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy-1, fx+1), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-POW2-G01-S5-X",
                same_sign & (cx == POW2) & (cy == G01) &
                (ex < ey + 2) & (fy == gy + 2) & (ex > gy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey-1, fy-1), SELTZORange(sy, 0, 0, fx, fx-p, fx))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey-1, fy), SELTZORange(sy, 0, 0, fx, fx-p, fx))
            end
            checker("SELTZO-TwoSum-POW2-G01-S5-Y",
                same_sign & (cy == POW2) & (cx == G01) &
                (ey < ex + 2) & (fx == gx + 2) & (ey > gx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex-1, fx-1), SELTZORange(sx, 0, 0, fy, fy-p, fy))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex-1, fx), SELTZORange(sx, 0, 0, fy, fy-p, fy))
            end

            checker("SELTZO-TwoSum-R1R0-POW2-D3-X",
                diff_sign & (cx == R1R0) & (cy == POW2) &
                (ex > ey + 1) & (ex < ey + (p-1)) & (ex == fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-R1R0-POW2-D3-Y",
                diff_sign & (cy == R1R0) & (cx == POW2) &
                (ey > ex + 1) & (ey < ex + (p-1)) & (ey == fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex), pos_zero)
            end

            checker("SELTZO-TwoSum-TWO0-R1R0-D1-X",
                diff_sign & (cx == TWO0) & (cy == R1R0) &
                (ex == ey + p) & (ex < fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey+2), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-TWO0-R1R0-D1-Y",
                diff_sign & (cy == TWO0) & (cx == R1R0) &
                (ey == ex + p) & (ey < fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex+2), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-POW2-G10-D4-X",
                diff_sign & (cx == POW2) & (cy == G10) &
                (fy + (p+1) == ex) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, fx+1), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, fx+1), SELTZORange(sy, 1, 0, fy-1, gy-1, gy))
            end
            checker("SELTZO-TwoSum-POW2-G10-D4-Y",
                diff_sign & (cy == POW2) & (cx == G10) &
                (fx + (p+1) == ey) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, fy+1), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, fy+1), SELTZORange(sx, 1, 0, fx-1, gx-1, gx))
            end

            checker("SELTZO-TwoSum-TWO1-R1R0-S1-X",
                same_sign & (cx == TWO1) & (cy == R1R0) &
                (ex < ey + p) & (fx > ey + 2) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey+1), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-TWO1-R1R0-S1-Y",
                same_sign & (cy == TWO1) & (cx == R1R0) &
                (ey < ex + p) & (fy > ex + 2) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex+1), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-ONE1-MM01-D2-X",
                diff_sign & (cx == ONE1) & (cy == MM01) &
                (fx < ey) & (fy + (p+1) < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, fx), SELTZORange(~sy, 1, 0, fy, gy-1, gy))
            end
            checker("SELTZO-TwoSum-ONE1-MM01-D2-Y",
                diff_sign & (cy == ONE1) & (cx == MM01) &
                (fy < ex) & (fx + (p+1) < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, fy), SELTZORange(~sx, 1, 0, fx, gx-1, gx))
            end

            checker("SELTZO-TwoSum-R1R0-G00-S5-X",
                same_sign & (cx == R1R0) & (cy == G00) &
                (ex == ey + (p-1)) & (ex > fx + (p-2)) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx-1, ex), SELTZORange(sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx-1, ex), SELTZORange(sy, 0, 0, fy, gy, gy))
            end
            checker("SELTZO-TwoSum-R1R0-G00-S5-Y",
                same_sign & (cy == R1R0) & (cx == G00) &
                (ey == ex + (p-1)) & (ey > fy + (p-2)) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy-1, ey), SELTZORange(sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy-1, ey), SELTZORange(sx, 0, 0, fx, gx, gx))
            end

            checker("SELTZO-TwoSum-POW2-G00-S7-X",
                same_sign & (cx == POW2) & (cy == G00) &
                (ey > fy + 2) & (fy + p == ex) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx+2), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx+2), SELTZORange(~sy, 1, 0, fx-1, gy-1, gy))
            end
            checker("SELTZO-TwoSum-POW2-G00-S7-Y",
                same_sign & (cy == POW2) & (cx == G00) &
                (ex > fx + 2) & (fx + p == ey) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy+2), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy+2), SELTZORange(~sx, 1, 0, fy-1, gx-1, gx))
            end

            checker("SELTZO-TwoSum-ONE1-R1R0-S2-X",
                same_sign & (cx == ONE1) & (cy == R1R0) &
                (ex == ey + 1) & (ex < fx + (p-2)) & (ey > fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fx, fx), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-ONE1-R1R0-S2-Y",
                same_sign & (cy == ONE1) & (cx == R1R0) &
                (ey == ex + 1) & (ey < fy + (p-2)) & (ex > fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fy, fy), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-R1R0-ONE1-S7-X",
                same_sign & (cx == R1R0) & (cy == ONE1) &
                (ex + 1 > ey) & (fx + 1 < ey) & (fy + (p-2) > ex) & (fx + 1 > fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey-1, fy), pos_zero)
            end
            checker("SELTZO-TwoSum-R1R0-ONE1-S7-Y",
                same_sign & (cy == R1R0) & (cx == ONE1) &
                (ey + 1 > ex) & (fy + 1 < ex) & (fx + (p-2) > ey) & (fy + 1 > fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex-1, fx), pos_zero)
            end

            checker("SELTZO-TwoSum-G11-ONE1-S1-X",
                same_sign & (cx == G11) & (cy == ONE1) &
                (fx == ey) & (fx == gx + 2) & (ey == fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex-p, ex), pos_zero)
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx-1, fx-1), pos_zero)
            end
            checker("SELTZO-TwoSum-G11-ONE1-S1-Y",
                same_sign & (cy == G11) & (cx == ONE1) &
                (fy == ex) & (fy == gy + 2) & (ex == fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey-p, ey), pos_zero)
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy-1, fy-1), pos_zero)
            end

            checker("SELTZO-TwoSum-G00-R0R1-D1-X",
                diff_sign & (cx == G00) & (cy == R0R1) &
                (ex < ey + (p-1)) & (ey < gx) & (ey > fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-G00-R0R1-D1-Y",
                diff_sign & (cy == G00) & (cx == R0R1) &
                (ey < ex + (p-1)) & (ex < gy) & (ex > fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-R0R1-POW2-S4-X",
                same_sign & (cx == R0R1) & (cy == POW2) &
                (ex == ey + p) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, gx, gx), SELTZORange(~sy, 0, 0, ey, fy, ey))
            end
            checker("SELTZO-TwoSum-R0R1-POW2-S4-Y",
                same_sign & (cy == R0R1) & (cx == POW2) &
                (ey == ex + p) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, gy, gy), SELTZORange(~sx, 0, 0, ex, fx, ex))
            end

            checker("SELTZO-TwoSum-R1R0-TWO1-S3-X",
                same_sign & (cx == R1R0) & (cy == TWO1) &
                (ex < ey + (p-1)) & (fx == ey) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx-1, fx), SELTZORange(sy, 1, 0, fy, gy-1, gy))
            end
            checker("SELTZO-TwoSum-R1R0-TWO1-S3-Y",
                same_sign & (cy == R1R0) & (cx == TWO1) &
                (ey < ex + (p-1)) & (fy == ex) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy-1, fy), SELTZORange(sx, 1, 0, fx, gx-1, gx))
            end

            checker("SELTZO-TwoSum-ONE0-TWO1-S1-X",
                same_sign & (cx == ONE0) & (cy == TWO1) &
                (ex < fx + (p-3)) & (fx < ey) & (fy + (p-3) == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey-1, fy), SELTZORange(sy, 0, 0, gy-1, gy-(p+1), gy-1))
            end
            checker("SELTZO-TwoSum-ONE0-TWO1-S1-Y",
                same_sign & (cy == ONE0) & (cx == TWO1) &
                (ey < fy + (p-3)) & (fy < ex) & (fx + (p-3) == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex-1, fx), SELTZORange(sx, 0, 0, gx-1, gx-(p+1), gx-1))
            end

            checker("SELTZO-TwoSum-R1R0-G01-S1-X",
                same_sign & (cx == R1R0) & (cy == G01) &
                (fx + 1 == ey) & (fy + (p-1) < ex) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ex-(p-1), ex+1), SELTZORange(sy, 0, 0, fy, gy-1, fx-(p-2)))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ex-(p-1), ex+1), SELTZORange(sy, 1, 0, fy, gy, fx-(p-2)))
            end
            checker("SELTZO-TwoSum-R1R0-G01-S1-Y",
                same_sign & (cy == R1R0) & (cx == G01) &
                (fy + 1 == ex) & (fx + (p-1) < ey) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ey-(p-1), ey+1), SELTZORange(sx, 0, 0, fx, gx-1, fy-(p-2)))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ey-(p-1), ey+1), SELTZORange(sx, 1, 0, fx, gx, fy-(p-2)))
            end

            checker("SELTZO-TwoSum-POW2-MM10-D5-X",
                diff_sign & (cx == POW2) & (cy == MM10) &
                (ex < ey + 3) & (fy + (p-2) < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, ey-1, fy), SELTZORange(sy, 0, 0, fx-1, fx-(p+1), fx-1))
            end
            checker("SELTZO-TwoSum-POW2-MM10-D5-Y",
                diff_sign & (cy == POW2) & (cx == MM10) &
                (ey < ex + 3) & (fx + (p-2) < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, ex-1, fx), SELTZORange(sx, 0, 0, fy-1, fy-(p+1), fy-1))
            end

            checker("SELTZO-TwoSum-R1R0-G00-S6-X",
                same_sign & (cx == R1R0) & (cy == G00) &
                (ex < ey + (p-1)) & (fx == ey) & (fy + p < ex) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx-1, fx), SELTZORange(sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx-1, fx), SELTZORange(sy, 0, 0, fy, gy, gy))
            end
            checker("SELTZO-TwoSum-R1R0-G00-S6-Y",
                same_sign & (cy == R1R0) & (cx == G00) &
                (ey < ex + (p-1)) & (fy == ex) & (fx + p < ey) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy-1, fy), SELTZORange(sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy-1, fy), SELTZORange(sx, 0, 0, fx, gx, gx))
            end

            checker("SELTZO-TwoSum-POW2-G00-D9-X",
                diff_sign & (cx == POW2) & (cy == G00) &
                (fy + (p+1) == ex) & (fy == gy + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ey), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ey), SELTZORange(~sy, 1, 0, gy+1, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ey), SELTZORange(~sy, 1, 0, fy-1, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ey), SELTZORange(~sy, 0, 0, fy-1, gy, gy))
            end
            checker("SELTZO-TwoSum-POW2-G00-D9-Y",
                diff_sign & (cy == POW2) & (cx == G00) &
                (fx + (p+1) == ey) & (fx == gx + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ex), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ex), SELTZORange(~sx, 1, 0, gx+1, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ex), SELTZORange(~sx, 1, 0, fx-1, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ex), SELTZORange(~sx, 0, 0, fx-1, gx, gx))
            end

            checker("SELTZO-TwoSum-R1R0-R0R1-S5-X",
                same_sign & (cx == R1R0) & (cy == R0R1) &
                (ex == ey + (p-1)) & (ex > fx + (p-2)) & (ey < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx-1, ex), SELTZORange(sy, 1, 0, fy, fx-p, fx-(p-1)))
            end
            checker("SELTZO-TwoSum-R1R0-R0R1-S5-Y",
                same_sign & (cy == R1R0) & (cx == R0R1) &
                (ey == ex + (p-1)) & (ey > fy + (p-2)) & (ex < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy-1, ey), SELTZORange(sx, 1, 0, fx, fy-p, fy-(p-1)))
            end

            checker("SELTZO-TwoSum-G00-R0R1-D2-X",
                diff_sign & (cx == G00) & (cy == R0R1) &
                (fx == ey) & (fx == gx + 2) & (ey < fy + (p-1)) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, gx, gx), SELTZORange(sy, 1, 0, fy, gx-(p-2), gx-(p-3)))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx-1, gx), SELTZORange(sy, 1, 0, fy, gx-(p-2), gx-(p-3)))
            end
            checker("SELTZO-TwoSum-G00-R0R1-D2-Y",
                diff_sign & (cy == G00) & (cx == R0R1) &
                (fy == ex) & (fy == gy + 2) & (ex < fx + (p-1)) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, gy, gy), SELTZORange(sx, 1, 0, fx, gy-(p-2), gy-(p-3)))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy-1, gy), SELTZORange(sx, 1, 0, fx, gy-(p-2), gy-(p-3)))
            end

            checker("SELTZO-TwoSum-ONE0-MM10-D1-X",
                diff_sign & (cx == ONE0) & (cy == MM10) &
                (ex > ey + (p-2)) & (fx < ey + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx+1), SELTZORange(sy, 0, 0, fy, gy-1, ey-(p-1)))
            end
            checker("SELTZO-TwoSum-ONE0-MM10-D1-Y",
                diff_sign & (cy == ONE0) & (cx == MM10) &
                (ey > ex + (p-2)) & (fy < ex + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy+1), SELTZORange(sx, 0, 0, fx, gx-1, ex-(p-1)))
            end

            checker("SELTZO-TwoSum-POW2-G10-D5-X",
                diff_sign & (cx == POW2) & (cy == G10) &
                (ex < ey + (p+2)) & (ey == fy + 2) & (fy + (p+2) < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ex-1), SELTZORange(~sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ex-1), SELTZORange(~sy, 1, 0, fy, gy+1:fy-2, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ex-1), SELTZORange(~sy, 0, 0, fy, gy:fy-2, gy))
            end
            checker("SELTZO-TwoSum-POW2-G10-D5-Y",
                diff_sign & (cy == POW2) & (cx == G10) &
                (ey < ex + (p+2)) & (ex == fx + 2) & (fx + (p+2) < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ey-1), SELTZORange(~sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ey-1), SELTZORange(~sx, 1, 0, fx, gx+1:fx-2, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ey-1), SELTZORange(~sx, 0, 0, fx, gx:fx-2, gx))
            end

            checker("SELTZO-TwoSum-R1R0-R1R0-S4-X",
                same_sign & (cx == R1R0) & (cy == R1R0) &
                (ex < ey + (p-2)) & (ex > fx + (p-2)) & (fy + p == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, gx+1), SELTZORange(sy, 0, 0, fx, fy-(p-1), fx))
            end
            checker("SELTZO-TwoSum-R1R0-R1R0-S4-Y",
                same_sign & (cy == R1R0) & (cx == R1R0) &
                (ey < ex + (p-2)) & (ey > fy + (p-2)) & (fx + p == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, gy+1), SELTZORange(sx, 0, 0, fy, fx-(p-1), fy))
            end

            checker("SELTZO-TwoSum-POW2-ONE0-D4-X",
                diff_sign & (cx == POW2) & (cy == ONE0) &
                (ex < ey + (p+1)) & (ey < fy + (p-2)) & (fy + (p+1) < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, ey+1), SELTZORange(~sy, 0, 0, fy, ey-(p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-ONE0-D4-Y",
                diff_sign & (cy == POW2) & (cx == ONE0) &
                (ey < ex + (p+1)) & (ex < fx + (p-2)) & (fx + (p+1) < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, ex+1), SELTZORange(~sx, 0, 0, fx, ex-(p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-POW2-MM10-D6-X",
                diff_sign & (cx == POW2) & (cy == MM10) &
                (ex > ey + 2) & (fy + (p-1) > ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, gy), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-MM10-D6-Y",
                diff_sign & (cy == POW2) & (cx == MM10) &
                (ey > ex + 2) & (fx + (p-1) > ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, gx), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-G10-POW2-S2-X",
                same_sign & (cx == G10) & (cy == POW2) &
                (ex + 1 > ey) & (fx + 1 < ey) & (ex < gx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey-1, gx), pos_zero)
            end
            checker("SELTZO-TwoSum-G10-POW2-S2-Y",
                same_sign & (cy == G10) & (cx == POW2) &
                (ey + 1 > ex) & (fy + 1 < ex) & (ey < gy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex-1, gy), pos_zero)
            end

            checker("SELTZO-TwoSum-G10-R1R0-D2-X",
                diff_sign & (cx == G10) & (cy == R1R0) &
                (ex > fx + 2) & (fx + 1 > ey) & (fx < ey + 2) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx+1, gx), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-G10-R1R0-D2-Y",
                diff_sign & (cy == G10) & (cx == R1R0) &
                (ey > fy + 2) & (fy + 1 > ex) & (fy < ex + 2) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy+1, gy), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-ONE1-G00-D2-X",
                diff_sign & (cx == ONE1) & (cy == G00) &
                (fx == ey) & (fy + (p+1) < ex) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex-p, ex), SELTZORange(sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex-p, ex), SELTZORange(sy, 0, 0, fy, gy, gy))
            end
            checker("SELTZO-TwoSum-ONE1-G00-D2-Y",
                diff_sign & (cy == ONE1) & (cx == G00) &
                (fy == ex) & (fx + (p+1) < ey) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey-p, ey), SELTZORange(sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey-p, ey), SELTZORange(sx, 0, 0, fx, gx, gx))
            end

            checker("SELTZO-TwoSum-TWO1-ONE1-S1-X",
                same_sign & (cx == TWO1) & (cy == ONE1) &
                (ex < ey + (p-1)) & (fx > ey + 1) & (fy + (p-1) < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-TWO1-ONE1-S1-Y",
                same_sign & (cy == TWO1) & (cx == ONE1) &
                (ey < ex + (p-1)) & (fy > ex + 1) & (fx + (p-1) < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-MM01-TWO1-D1-X",
                diff_sign & (cx == MM01) & (cy == TWO1) &
                (ex < ey + (p-1)) & (fx > ey + 1) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey), SELTZORange(sy, 1, 0, fy, gy-1, gy))
            end
            checker("SELTZO-TwoSum-MM01-TWO1-D1-Y",
                diff_sign & (cy == MM01) & (cx == TWO1) &
                (ey < ex + (p-1)) & (fy > ex + 1) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex), SELTZORange(sx, 1, 0, fx, gx-1, gx))
            end

            checker("SELTZO-TwoSum-G00-ONE1-D3-X",
                diff_sign & (cx == G00) & (cy == ONE1) &
                (fx == ey) & (fx == gx + 2) & (fy + (p-1) < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, gx, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx-1, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-G00-ONE1-D3-Y",
                diff_sign & (cy == G00) & (cx == ONE1) &
                (fy == ex) & (fy == gy + 2) & (fx + (p-1) < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, gy, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy-1, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ONE1-ONE1-D7-X",
                diff_sign & (cx == ONE1) & (cy == ONE1) &
                (ex == ey + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx-1, fx), SELTZORange(~sy, 1, 0, ey-1, fy-1, fy))
            end
            checker("SELTZO-TwoSum-ONE1-ONE1-D7-Y",
                diff_sign & (cy == ONE1) & (cx == ONE1) &
                (ey == ex + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy-1, fy), SELTZORange(~sx, 1, 0, ex-1, fx-1, fx))
            end

            checker("SELTZO-TwoSum-POW2-G10-S3-X",
                same_sign & (cx == POW2) & (cy == G10) &
                (ex == ey + p) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx+1, fx+2), SELTZORange(~sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx+1, fx+2), SELTZORange(~sy, 0, 0, fy, gy, gy))
            end
            checker("SELTZO-TwoSum-POW2-G10-S3-Y",
                same_sign & (cy == POW2) & (cx == G10) &
                (ey == ex + p) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy+1, fy+2), SELTZORange(~sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy+1, fy+2), SELTZORange(~sx, 0, 0, fx, gx, gx))
            end

            checker("SELTZO-TwoSum-ONE1-G10-D3-X",
                diff_sign & (cx == ONE1) & (cy == G10) &
                (ex < fx + (p-2)) & (fx < ey) & (fy == gy + 3) & (ex == gy + (p+2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, fy+1), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, fy), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, fy+1), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, fy+1), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-ONE1-G10-D3-Y",
                diff_sign & (cy == ONE1) & (cx == G10) &
                (ey < fy + (p-2)) & (fy < ex) & (fx == gx + 3) & (ey == gx + (p+2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, fx+1), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, fx), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, fx+1), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, fx+1), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-POW2-G00-D10-X",
                diff_sign & (cx == POW2) & (cy == G00) &
                (fy + p == ex) & (fy == gy + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ey), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ey), SELTZORange(sy, 1, 0, gy+1, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, fx+1), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, fx+1), SELTZORange(~sy, 1, 0, gy+1, gy-1, gy))
            end
            checker("SELTZO-TwoSum-POW2-G00-D10-Y",
                diff_sign & (cy == POW2) & (cx == G00) &
                (fx + p == ey) & (fx == gx + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ex), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ex), SELTZORange(sx, 1, 0, gx+1, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, fy+1), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, fy+1), SELTZORange(~sx, 1, 0, gx+1, gx-1, gx))
            end

            checker("SELTZO-TwoSum-ONE0-R1R0-S1-X",
                same_sign & (cx == ONE0) & (cy == R1R0) &
                (ex > ey) & (ex < fx + (p-2)) & (fx < fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, fx), SELTZORange(~sy, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end
            checker("SELTZO-TwoSum-ONE0-R1R0-S1-Y",
                same_sign & (cy == ONE0) & (cx == R1R0) &
                (ey > ex) & (ey < fy + (p-2)) & (fy < fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, fy), SELTZORange(~sx, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end

            checker("SELTZO-TwoSum-G10-ONE1-D2-X",
                diff_sign & (cx == G10) & (cy == ONE1) &
                (ex == ey + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-G10-ONE1-D2-Y",
                diff_sign & (cy == G10) & (cx == ONE1) &
                (ey == ex + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ONE1-ONE1-D8-X",
                diff_sign & (cx == ONE1) & (cy == ONE1) &
                (fx + 1 == ey) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fx-1, fx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-ONE1-ONE1-D8-Y",
                diff_sign & (cy == ONE1) & (cx == ONE1) &
                (fy + 1 == ex) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fy-1, fy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-POW2-MM10-D7-X",
                diff_sign & (cx == POW2) & (cy == MM10) &
                (ey < fy + (p-3)) & (fy + p == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ey), SELTZORange(sy, 1, 0, gy-1, ey-p, ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-MM10-D7-Y",
                diff_sign & (cy == POW2) & (cx == MM10) &
                (ex < fx + (p-3)) & (fx + p == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ex), SELTZORange(sx, 1, 0, gx-1, ex-p, ex-(p-1)))
            end

            checker("SELTZO-TwoSum-ONE1-TWO1-D7-X",
                diff_sign & (cx == ONE1) & (cy == TWO1) &
                (fx < ey) & (fy + p == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey-1, fy+1), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-ONE1-TWO1-D7-Y",
                diff_sign & (cy == ONE1) & (cx == TWO1) &
                (fy < ex) & (fx + p == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex-1, fx+1), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-G10-ONE1-S2-X",
                same_sign & (cx == G10) & (cy == ONE1) &
                (ex < ey + (p-1)) & (ey < gx) & (fy + (p-1) < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-G10-ONE1-S2-Y",
                same_sign & (cy == G10) & (cx == ONE1) &
                (ey < ex + (p-1)) & (ex < gy) & (fx + (p-1) < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-POW2-ONE0-D5-X",
                diff_sign & (cx == POW2) & (cy == ONE0) &
                (ex == ey + (p+1)) & (ey > fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ex-1), SELTZORange(~sy, 1, 0, fy, fy-2, fy-1))
            end
            checker("SELTZO-TwoSum-POW2-ONE0-D5-Y",
                diff_sign & (cy == POW2) & (cx == ONE0) &
                (ey == ex + (p+1)) & (ex > fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ey-1), SELTZORange(~sx, 1, 0, fx, fx-2, fx-1))
            end

            checker("SELTZO-TwoSum-TWO1-ALL1-D2-X",
                diff_sign & (cx == TWO1) & (cy == ALL1) &
                (ex == ey + 2) & (fx < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, fx, gx), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-TWO1-ALL1-D2-Y",
                diff_sign & (cy == TWO1) & (cx == ALL1) &
                (ey == ex + 2) & (fy < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, fy, gy), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-TWO0-POW2-S3-X",
                same_sign & (cx == TWO0) & (cy == POW2) &
                (ex + 1 > ey) & (ex < fx + (p-3)) & (fx + 1 < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey-1, gx), SELTZORange(~sy, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end
            checker("SELTZO-TwoSum-TWO0-POW2-S3-Y",
                same_sign & (cy == TWO0) & (cx == POW2) &
                (ey + 1 > ex) & (ey < fy + (p-3)) & (fy + 1 < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex-1, gy), SELTZORange(~sx, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end

            checker("SELTZO-TwoSum-G10-R1R0-D3-X",
                diff_sign & (cx == G10) & (cy == R1R0) &
                (ex == ey + (p-1)) & (ex > gx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, gx+1:fx-1), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx+1), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-G10-R1R0-D3-Y",
                diff_sign & (cy == G10) & (cx == R1R0) &
                (ey == ex + (p-1)) & (ey > gy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, gy+1:fy-1), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy+1), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-POW2-G00-D11-X",
                diff_sign & (cx == POW2) & (cy == G00) &
                (ex == ey + (p+1)) & (ey == fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ex-1), SELTZORange(~sy, 0, 0, ey-1, gy:fy-1, gy))
            end
            checker("SELTZO-TwoSum-POW2-G00-D11-Y",
                diff_sign & (cy == POW2) & (cx == G00) &
                (ey == ex + (p+1)) & (ex == fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ey-1), SELTZORange(~sx, 0, 0, ex-1, gx:fx-1, gx))
            end

            checker("SELTZO-TwoSum-ONE1-R0R1-D5-X",
                diff_sign & (cx == ONE1) & (cy == R0R1) &
                (ex == ey + p) & (ey > fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx-1, fx), SELTZORange(~sy, 1, 0, ey-1, fy-1, fy))
            end
            checker("SELTZO-TwoSum-ONE1-R0R1-D5-Y",
                diff_sign & (cy == ONE1) & (cx == R0R1) &
                (ey == ex + p) & (ex > fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy-1, fy), SELTZORange(~sx, 1, 0, ex-1, fx-1, fx))
            end

            checker("SELTZO-TwoSum-R1R0-G00-S7-X",
                same_sign & (cx == R1R0) & (cy == G00) &
                (fy == gy + 3) & (ex == gy + (p-1)) & (fx + 1 == fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, ey), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, fx), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, fx), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, gx), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-R1R0-G00-S7-Y",
                same_sign & (cy == R1R0) & (cx == G00) &
                (fx == gx + 3) & (ey == gx + (p-1)) & (fy + 1 == fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, ex), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, fy), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, fy), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, gy), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-G01-POW2-D2-X",
                diff_sign & (cx == G01) & (cy == POW2) &
                (ex == ey + p) & (ex < gx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey+2), SELTZORange(~sy, 0, 0, ey, fy, ey))
            end
            checker("SELTZO-TwoSum-G01-POW2-D2-Y",
                diff_sign & (cy == G01) & (cx == POW2) &
                (ey == ex + p) & (ey < gy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex+2), SELTZORange(~sx, 0, 0, ex, fx, ex))
            end

            checker("SELTZO-TwoSum-TWO1-R1R0-D5-X",
                diff_sign & (cx == TWO1) & (cy == R1R0) &
                (fx > ey + 1) & (fy + p > ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-TWO1-R1R0-D5-Y",
                diff_sign & (cy == TWO1) & (cx == R1R0) &
                (fy > ex + 1) & (fx + p > ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, gx), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-G10-D6-X",
                diff_sign & (cx == POW2) & (cy == G10) &
                (ex == ey + 1) & (fy == gy + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, fy, gy-1, gy), pos_zero)
                add_case!(lemma, SELTZORange(sx, 0, 0, fy, gy, gy), pos_zero)
                add_case!(lemma, SELTZORange(sx, 0, 0, fy, gy+1, gy), pos_zero)
                add_case!(lemma, SELTZORange(sx, 1, 0, fy, gy+1, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-G10-D6-Y",
                diff_sign & (cy == POW2) & (cx == G10) &
                (ey == ex + 1) & (fx == gx + 3)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, fx, gx-1, gx), pos_zero)
                add_case!(lemma, SELTZORange(sy, 0, 0, fx, gx, gx), pos_zero)
                add_case!(lemma, SELTZORange(sy, 0, 0, fx, gx+1, gx), pos_zero)
                add_case!(lemma, SELTZORange(sy, 1, 0, fx, gx+1, gx), pos_zero)
            end

            checker("SELTZO-TwoSum-ONE1-G10-D4-X",
                diff_sign & (cx == ONE1) & (cy == G10) &
                (fx == ey) & (fy + (p+1) < ex) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fx-1, fx), SELTZORange(~sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fx-1, fx), SELTZORange(~sy, 0, 0, fy, gy, gy))
            end
            checker("SELTZO-TwoSum-ONE1-G10-D4-Y",
                diff_sign & (cy == ONE1) & (cx == G10) &
                (fy == ex) & (fx + (p+1) < ey) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fy-1, fy), SELTZORange(~sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fy-1, fy), SELTZORange(~sx, 0, 0, fx, gx, gx))
            end

            checker("SELTZO-TwoSum-R1R0-ONE1-D6-X",
                diff_sign & (cx == R1R0) & (cy == ONE1) &
                (ex < ey + (p-1)) & (ex == fx + 2) & (fy + (p-1) < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-R1R0-ONE1-D6-Y",
                diff_sign & (cy == R1R0) & (cx == ONE1) &
                (ey < ex + (p-1)) & (ey == fy + 2) & (fx + (p-1) < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-R1R0-POW2-S2-X",
                same_sign & (cx == R1R0) & (cy == POW2) &
                (ex + 1 > ey) & (ex < ey + (p-2)) & (ex > fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex+1, ey-1, ey), pos_zero)
            end
            checker("SELTZO-TwoSum-R1R0-POW2-S2-Y",
                same_sign & (cy == R1R0) & (cx == POW2) &
                (ey + 1 > ex) & (ey < ex + (p-2)) & (ey > fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey+1, ex-1, ex), pos_zero)
            end

            checker("SELTZO-TwoSum-G00-TWO1-D1-X",
                diff_sign & (cx == G00) & (cy == TWO1) &
                (ey < gx) & (fy + (p-1) == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy+1), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-G00-TWO1-D1-Y",
                diff_sign & (cy == G00) & (cx == TWO1) &
                (ex < gy) & (fx + (p-1) == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx+1), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-G11-ONE1-D1-X",
                diff_sign & (cx == G11) & (cy == ONE1) &
                (ex == fx + 2) & (ey > gx) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-G11-ONE1-D1-Y",
                diff_sign & (cy == G11) & (cx == ONE1) &
                (ey == fy + 2) & (ex > gy) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ONE0-ALL1-D2-X",
                diff_sign & (cx == ONE0) & (cy == ALL1) &
                (ex == ey + p) & (ex == fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx-1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-ONE0-ALL1-D2-Y",
                diff_sign & (cy == ONE0) & (cx == ALL1) &
                (ey == ex + p) & (ey == fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy-1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-POW2-MM10-D8-X",
                diff_sign & (cx == POW2) & (cy == MM10) &
                (ex == ey + 2) & (fy + (p-1) > ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, ey-1, gy), SELTZORange(~sy, 0, 0, fx-1, fx-(p+1), fx-1))
            end
            checker("SELTZO-TwoSum-POW2-MM10-D8-Y",
                diff_sign & (cy == POW2) & (cx == MM10) &
                (ey == ex + 2) & (fx + (p-1) > ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, ex-1, gx), SELTZORange(~sx, 0, 0, fy-1, fy-(p+1), fy-1))
            end

            checker("SELTZO-TwoSum-POW2-MM10-S4-X",
                same_sign & (cx == POW2) & (cy == MM10) &
                (ex == ey + 1) & (ey < fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey-1, gy), SELTZORange(~sy, 0, 0, fx, fx-p, fx))
            end
            checker("SELTZO-TwoSum-POW2-MM10-S4-Y",
                same_sign & (cy == POW2) & (cx == MM10) &
                (ey == ex + 1) & (ex < fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex-1, gx), SELTZORange(~sx, 0, 0, fy, fy-p, fy))
            end

            checker("SELTZO-TwoSum-TWO0-ONE1-D1-X",
                diff_sign & (cx == TWO0) & (cy == ONE1) &
                (ex == ey + (p-1)) & (ex < fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey+1), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-TWO0-ONE1-D1-Y",
                diff_sign & (cy == TWO0) & (cx == ONE1) &
                (ey == ex + (p-1)) & (ey < fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex+1), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ONE1-MM10-D1-X",
                diff_sign & (cx == ONE1) & (cy == MM10) &
                (ex > ey + 1) & (fx < ey) & (fy + (p-1) > ex) & (fx > fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey-1, gy), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-ONE1-MM10-D1-Y",
                diff_sign & (cy == ONE1) & (cx == MM10) &
                (ey > ex + 1) & (fy < ex) & (fx + (p-1) > ey) & (fy > fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex-1, gx), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-ONE1-ONE0-D1-X",
                diff_sign & (cx == ONE1) & (cy == ONE0) &
                (ex == ey + p) & (ey < fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx-1, fx), SELTZORange(~sy, 0, 0, fy, ey-(p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-ONE1-ONE0-D1-Y",
                diff_sign & (cy == ONE1) & (cx == ONE0) &
                (ey == ex + p) & (ex < fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy-1, fy), SELTZORange(~sx, 0, 0, fx, ex-(p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-G11-ONE1-D2-X",
                diff_sign & (cx == G11) & (cy == ONE1) &
                (ex > ey + (p-2)) & (fx == gx + 3) & (ey + 2 > gx)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx+1), SELTZORange(sy, 0, 0, fy, fy-p, fy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx-1), SELTZORange(sy, 0, 0, fy, fy-p, fy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, gx+1), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-G11-ONE1-D2-Y",
                diff_sign & (cy == G11) & (cx == ONE1) &
                (ey > ex + (p-2)) & (fy == gy + 3) & (ex + 2 > gy)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy+1), SELTZORange(sx, 0, 0, fx, fx-p, fx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy-1), SELTZORange(sx, 0, 0, fx, fx-p, fx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, gy+1), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-TWO1-R1R0-D6-X",
                diff_sign & (cx == TWO1) & (cy == R1R0) &
                (fx < ey) & (fy + (p+1) < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, gx), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-TWO1-R1R0-D6-Y",
                diff_sign & (cy == TWO1) & (cx == R1R0) &
                (fy < ex) & (fx + (p+1) < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, gy), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-POW2-G00-D12-X",
                diff_sign & (cx == POW2) & (cy == G00) &
                (fy + (p+1) == ex) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ey), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ey), SELTZORange(~sy, 1, 0, fy-1, gy-1, gy))
            end
            checker("SELTZO-TwoSum-POW2-G00-D12-Y",
                diff_sign & (cy == POW2) & (cx == G00) &
                (fx + (p+1) == ey) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ex), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ex), SELTZORange(~sx, 1, 0, fx-1, gx-1, gx))
            end

            checker("SELTZO-TwoSum-ONE0-POW2-D3-X",
                diff_sign & (cx == ONE0) & (cy == POW2) &
                (ex == ey + (p-1)) & (ex < fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey+1), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE0-POW2-D3-Y",
                diff_sign & (cy == ONE0) & (cx == POW2) &
                (ey == ex + (p-1)) & (ey < fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex+1), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-R1R0-D4-X",
                diff_sign & (cx == POW2) & (cy == R1R0) &
                (ex == ey + 2) & (ey < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, gy, gy), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-R1R0-D4-Y",
                diff_sign & (cy == POW2) & (cx == R1R0) &
                (ey == ex + 2) & (ex < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, gx, gx), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-TWO0-D3-X",
                diff_sign & (cx == POW2) & (cy == TWO0) &
                (ex == ey + 2) & (fy + (p-1) > ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, fy, gy), SELTZORange(~sy, 0, 0, fx-1, fx-(p+1), fx-1))
            end
            checker("SELTZO-TwoSum-POW2-TWO0-D3-Y",
                diff_sign & (cy == POW2) & (cx == TWO0) &
                (ey == ex + 2) & (fx + (p-1) > ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, fx, gx), SELTZORange(~sx, 0, 0, fy-1, fy-(p+1), fy-1))
            end

            checker("SELTZO-TwoSum-R1R0-MM10-D2-X",
                diff_sign & (cx == R1R0) & (cy == MM10) &
                (ex == ey + p) & (ex > fx + 2) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, gx, gx), SELTZORange(~sy, 1, 0, ey-1, fy, ey-(p-1)))
            end
            checker("SELTZO-TwoSum-R1R0-MM10-D2-Y",
                diff_sign & (cy == R1R0) & (cx == MM10) &
                (ey == ex + p) & (ey > fy + 2) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, gy, gy), SELTZORange(~sx, 1, 0, ex-1, fx, ex-(p-1)))
            end

            checker("SELTZO-TwoSum-ONE1-ALL1-S1-X",
                same_sign & (cx == ONE1) & (cy == ALL1) &
                (ex < ey + p) & (fx > ey + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-ONE1-ALL1-S1-Y",
                same_sign & (cy == ONE1) & (cx == ALL1) &
                (ey < ex + p) & (fy > ex + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-R1R0-R1R0-S5-X",
                same_sign & (cx == R1R0) & (cy == R1R0) &
                (ex < ey + p) & (fx == ey + 1) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fx), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-R1R0-R1R0-S5-Y",
                same_sign & (cy == R1R0) & (cx == R1R0) &
                (ey < ex + p) & (fy == ex + 1) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fy), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-ONE0-POW2-D4-X",
                diff_sign & (cx == ONE0) & (cy == POW2) &
                (ex == ey) & (ex > fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fx, fy+1), pos_zero)
            end
            checker("SELTZO-TwoSum-ONE0-POW2-D4-Y",
                diff_sign & (cy == ONE0) & (cx == POW2) &
                (ey == ex) & (ey > fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fy, fx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-G00-D13-X",
                diff_sign & (cx == POW2) & (cy == G00) &
                (fy + p == ex) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, ey), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey, fx+1), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-POW2-G00-D13-Y",
                diff_sign & (cy == POW2) & (cx == G00) &
                (fx + p == ey) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, ex), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex, fy+1), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-POW2-G01-S6-X",
                same_sign & (cx == POW2) & (cy == G01) &
                (ex > ey + 1) & (fy == gy + 3) & (ex == gy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, gy+1), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy-1), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy+1), SELTZORange(~sy, 0, 0, ey-(p-1), ey-(p+p-1), ey-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-G01-S6-Y",
                same_sign & (cy == POW2) & (cx == G01) &
                (ey > ex + 1) & (fx == gx + 3) & (ey == gx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, gx+1), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx-1), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx+1), SELTZORange(~sx, 0, 0, ex-(p-1), ex-(p+p-1), ex-(p-1)))
            end

            checker("SELTZO-TwoSum-ONE1-MM01-D3-X",
                diff_sign & (cx == ONE1) & (cy == MM01) &
                (fx > ey + 1) & (fy + (p-1) == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx-1, fy+1), SELTZORange(sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-ONE1-MM01-D3-Y",
                diff_sign & (cy == ONE1) & (cx == MM01) &
                (fy > ex + 1) & (fx + (p-1) == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy-1, fx+1), SELTZORange(sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-POW2-G00-D14-X",
                diff_sign & (cx == POW2) & (cy == G00) &
                (ex < ey + p) & (fy + (p+1) < ex) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey-1, ey), SELTZORange(sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, ey-1, ey), SELTZORange(sy, 0, 0, fy, gy, gy))
            end
            checker("SELTZO-TwoSum-POW2-G00-D14-Y",
                diff_sign & (cy == POW2) & (cx == G00) &
                (ey < ex + p) & (fx + (p+1) < ey) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex-1, ex), SELTZORange(sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, ex-1, ex), SELTZORange(sx, 0, 0, fx, gx, gx))
            end

            checker("SELTZO-TwoSum-MM01-R0R1-S1-X",
                same_sign & (cx == MM01) & (cy == R0R1) &
                (ex + 1 > ey) & (ex < fx + (p-3)) & (fx + 1 < ey) & (ey > fy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey-1, gx), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-MM01-R0R1-S1-Y",
                same_sign & (cy == MM01) & (cx == R0R1) &
                (ey + 1 > ex) & (ey < fy + (p-3)) & (fy + 1 < ex) & (ex > fx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex-1, gy), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-POW2-R0R1-D11-X",
                diff_sign & (cx == POW2) & (cy == R0R1) &
                (ex == ey + p) & (ey < fy + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fx-1, ex-1), SELTZORange(sy, 1, 0, fy, fx-p, fx-(p-1)))
            end
            checker("SELTZO-TwoSum-POW2-R0R1-D11-Y",
                diff_sign & (cy == POW2) & (cx == R0R1) &
                (ey == ex + p) & (ex < fx + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fy-1, ey-1), SELTZORange(sx, 1, 0, fx, fy-p, fy-(p-1)))
            end

            checker("SELTZO-TwoSum-R1R0-G00-S8-X",
                same_sign & (cx == R1R0) & (cy == G00) &
                (ex < fx + (p-1)) & (fx + 3 == ey) & (fy + (p-1) < ex) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, gx+1, gx), SELTZORange(sy, 1, 0, fy, gy-1, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, gx+1, gx), SELTZORange(sy, 0, 0, fy, gy, gy))
            end
            checker("SELTZO-TwoSum-R1R0-G00-S8-Y",
                same_sign & (cy == R1R0) & (cx == G00) &
                (ey < fy + (p-1)) & (fy + 3 == ex) & (fx + (p-1) < ey) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, gy+1, gy), SELTZORange(sx, 1, 0, fx, gx-1, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, gy+1, gy), SELTZORange(sx, 0, 0, fx, gx, gx))
            end

            checker("SELTZO-TwoSum-G00-ALL1-D1-X",
                diff_sign & (cx == G00) & (cy == ALL1) &
                (fx == ey) & (fx == gx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, gx-1, gx), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
                add_case!(lemma, SELTZORange(sx, 1, 0, ex-1, fx-1, gx), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-G00-ALL1-D1-Y",
                diff_sign & (cy == G00) & (cx == ALL1) &
                (fy == ex) & (fy == gy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, gy-1, gy), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
                add_case!(lemma, SELTZORange(sy, 1, 0, ey-1, fy-1, gy), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-R1R0-G00-S9-X",
                same_sign & (cx == R1R0) & (cy == G00) &
                (ex == fx + (p-2)) & (fy == gy + 2) & (fx + 1 == fy)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, ey), SELTZORange(sy, 0, 0, gy, gy-p, gy))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, ey, gx), SELTZORange(~sy, 0, 0, gy, gy-p, gy))
            end
            checker("SELTZO-TwoSum-R1R0-G00-S9-Y",
                same_sign & (cy == R1R0) & (cx == G00) &
                (ey == fy + (p-2)) & (fx == gx + 2) & (fy + 1 == fx)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, ex), SELTZORange(sx, 0, 0, gx, gx-p, gx))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, ex, gy), SELTZORange(~sx, 0, 0, gx, gx-p, gx))
            end

            checker("SELTZO-TwoSum-G11-ONE1-D3-X",
                diff_sign & (cx == G11) & (cy == ONE1) &
                (ex == ey + (p-1)) & (ex < gx + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey+1), SELTZORange(sy, 0, 0, fy, fy-p, fy))
            end
            checker("SELTZO-TwoSum-G11-ONE1-D3-Y",
                diff_sign & (cy == G11) & (cx == ONE1) &
                (ey == ex + (p-1)) & (ey < gy + (p-2))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex+1), SELTZORange(sx, 0, 0, fx, fx-p, fx))
            end

            checker("SELTZO-TwoSum-ONE1-R0R1-D6-X",
                diff_sign & (cx == ONE1) & (cy == R0R1) &
                (ex > ey + 2) & (fx == ey) & (fy + (p+1) == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, fy, ex-1), SELTZORange(~sy, 0, 0, fx-(p-1), fx-(p+p-1), fx-(p-1)))
            end
            checker("SELTZO-TwoSum-ONE1-R0R1-D6-Y",
                diff_sign & (cy == ONE1) & (cx == R0R1) &
                (ey > ex + 2) & (fy == ex) & (fx + (p+1) == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, fx, ey-1), SELTZORange(~sx, 0, 0, fy-(p-1), fy-(p+p-1), fy-(p-1)))
            end

            checker("SELTZO-TwoSum-TWO1-R1R0-D7-X",
                diff_sign & (cx == TWO1) & (cy == R1R0) &
                (ex < ey + p) & (fx > ey + 2) & (fy + p < ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey+1), SELTZORange(~sy, 0, 0, gy, fy-(p-1), gy))
            end
            checker("SELTZO-TwoSum-TWO1-R1R0-D7-Y",
                diff_sign & (cy == TWO1) & (cx == R1R0) &
                (ey < ex + p) & (fy > ex + 2) & (fx + p < ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex+1), SELTZORange(~sx, 0, 0, gx, fx-(p-1), gx))
            end

            checker("SELTZO-TwoSum-ONE1-TWO1-D8-X",
                diff_sign & (cx == ONE1) & (cy == TWO1) &
                (ex == ey + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx-1, fx), SELTZORange(sy, 1, 0, fy, gy-1, gy))
            end
            checker("SELTZO-TwoSum-ONE1-TWO1-D8-Y",
                diff_sign & (cy == ONE1) & (cx == TWO1) &
                (ey == ex + (p-1))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy-1, fy), SELTZORange(sx, 1, 0, fx, gx-1, gx))
            end

            checker("SELTZO-TwoSum-TWO0-ALL1-D1-X",
                diff_sign & (cx == TWO0) & (cy == ALL1) &
                (ex == ey + p) & (ex < fx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey+2), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-TWO0-ALL1-D1-Y",
                diff_sign & (cy == TWO0) & (cx == ALL1) &
                (ey == ex + p) & (ey < fy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex+2), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-POW2-TWO1-D10-X",
                diff_sign & (cx == POW2) & (cy == TWO1) &
                (ex > ey + 2) & (fy + (p-1) == ex)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, fy), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-TWO1-D10-Y",
                diff_sign & (cy == POW2) & (cx == TWO1) &
                (ey > ex + 2) & (fx + (p-1) == ey)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, fx), pos_zero)
            end

            checker("SELTZO-TwoSum-ALL1-TWO1-D2-X",
                diff_sign & (cx == ALL1) & (cy == TWO1) &
                (ex == ey) & (ey == fy + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex-1, gy-1, fx+1), pos_zero)
            end
            checker("SELTZO-TwoSum-ALL1-TWO1-D2-Y",
                diff_sign & (cy == ALL1) & (cx == TWO1) &
                (ey == ex) & (ex == fx + 2)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey-1, gx-1, fy+1), pos_zero)
            end

            checker("SELTZO-TwoSum-R1R0-ALL1-S2-X",
                same_sign & (cx == R1R0) & (cy == ALL1) &
                (ex < ey + p) & (fx > ey + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey+1), SELTZORange(~sy, 0, 0, fy+1, fy-(p-1), fy+1))
            end
            checker("SELTZO-TwoSum-R1R0-ALL1-S2-Y",
                same_sign & (cy == R1R0) & (cx == ALL1) &
                (ey < ex + p) & (fy > ex + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex+1), SELTZORange(~sx, 0, 0, fx+1, fx-(p-1), fx+1))
            end

            checker("SELTZO-TwoSum-POW2-G00-D15-X",
                diff_sign & (cx == POW2) & (cy == G00) &
                (ex > ey + 2) & (fy == gy + 2) & (ex == gy + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, fx+1), pos_zero)
                add_case!(lemma, SELTZORange(sx, 1, 1, ex-1, ey, fy), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-G00-D15-Y",
                diff_sign & (cy == POW2) & (cx == G00) &
                (ey > ex + 2) & (fx == gx + 2) & (ey == gx + p)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, fy+1), pos_zero)
                add_case!(lemma, SELTZORange(sy, 1, 1, ey-1, ex, fx), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-G01-S7-X",
                same_sign & (cx == POW2) & (cy == G01) &
                (ex == ey + (p-1)) & (ey > gy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey+1), SELTZORange(sy, 0, 0, fy, gy-1, gy-1))
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey+1), SELTZORange(sy, 0, 0, fy, gy+1:fy-2, gy-1))
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey+1), SELTZORange(sy, 1, 0, fy, gy:fy-2, gy-1))
            end
            checker("SELTZO-TwoSum-POW2-G01-S7-Y",
                same_sign & (cy == POW2) & (cx == G01) &
                (ey == ex + (p-1)) & (ex > gx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex+1), SELTZORange(sx, 0, 0, fx, gx-1, gx-1))
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex+1), SELTZORange(sx, 0, 0, fx, gx+1:fx-2, gx-1))
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex+1), SELTZORange(sx, 1, 0, fx, gx:fx-2, gx-1))
            end

            checker("SELTZO-TwoSum-R1R0-G11-S1-X",
                same_sign & (cx == R1R0) & (cy == G11) &
                (fx < ey + 1) & (ey == fy + 2) & (fy + p < ex) & (ey > gy + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fx, ex+1), SELTZORange(~sy, 0, 0, fy, gy:fy-2, gy-1))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fx, ex+1), SELTZORange(~sy, 1, 0, fy, gy-2, gy-1))
                add_case!(lemma, SELTZORange(sx, 0, 0, ex+1, fx, ex+1), SELTZORange(~sy, 1, 0, fy, gy+1:fy-2, gy-1))
            end
            checker("SELTZO-TwoSum-R1R0-G11-S1-Y",
                same_sign & (cy == R1R0) & (cx == G11) &
                (fy < ex + 1) & (ex == fx + 2) & (fx + p < ey) & (ex > gx + (p-3))
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fy, ey+1), SELTZORange(~sx, 0, 0, fx, gx:fx-2, gx-1))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fy, ey+1), SELTZORange(~sx, 1, 0, fx, gx-2, gx-1))
                add_case!(lemma, SELTZORange(sy, 0, 0, ey+1, fy, ey+1), SELTZORange(~sx, 1, 0, fx, gx+1:fx-2, gx-1))
            end

            checker("SELTZO-TwoSum-POW2-ONE1-S4-X",
                same_sign & (cx == POW2) & (cy == ONE1) &
                (ex > ey + 1) & (gy == fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, gy+1), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-ONE1-S4-Y",
                same_sign & (cy == POW2) & (cx == ONE1) &
                (ey > ex + 1) & (gx == fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, gx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-MM01-S4-X",
                same_sign & (cx == POW2) & (cy == MM01) &
                (ex > ey + 1) & (gy == fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, gy+1), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-MM01-S4-Y",
                same_sign & (cy == POW2) & (cx == MM01) &
                (ey > ex + 1) & (gx == fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, gx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-TWO1-S5-X",
                same_sign & (cx == POW2) & (cy == TWO1) &
                (ex > ey + 1) & (gy == fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, gy+2), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-TWO1-S5-Y",
                same_sign & (cy == POW2) & (cx == TWO1) &
                (ey > ex + 1) & (gx == fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, gx+2), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-R1R0-S4-X",
                same_sign & (cx == POW2) & (cy == R1R0) &
                (ex > ey + 1) & (gy == fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey+1), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-R1R0-S4-Y",
                same_sign & (cy == POW2) & (cx == R1R0) &
                (ey > ex + 1) & (gx == fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex+1), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-G00-S8-X",
                same_sign & (cx == POW2) & (cy == G00) &
                (ex > ey + 1) & (gy == fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, gy+1:fy-1), pos_zero)
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy+1), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-G00-S8-Y",
                same_sign & (cy == POW2) & (cx == G00) &
                (ey > ex + 1) & (gx == fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, gx+1:fx-1), pos_zero)
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-G10-S4-X",
                same_sign & (cx == POW2) & (cy == G10) &
                (ex > ey + 1) & (gy == fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, gy+1:fy), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-G10-S4-Y",
                same_sign & (cy == POW2) & (cx == G10) &
                (ey > ex + 1) & (gx == fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, gx+1:fx), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-R1R0-S5-X",
                same_sign & (cx == POW2) & (cy == R1R0) &
                (ex == ey + 1) & (gy == fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex-p, ex), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-R1R0-S5-Y",
                same_sign & (cy == POW2) & (cx == R1R0) &
                (ey == ex + 1) & (gx == fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey-p, ey), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-ONE1-S5-X",
                same_sign & (cx == POW2) & (cy == ONE1) &
                (ex == ey + 1) & (gy == fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey-1, gy+1), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-ONE1-S5-Y",
                same_sign & (cy == POW2) & (cx == ONE1) &
                (ey == ex + 1) & (gx == fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex-1, gx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-TWO1-S6-X",
                same_sign & (cx == POW2) & (cy == TWO1) &
                (ex == ey + 1) & (gy == fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey-1, gy+2), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-TWO1-S6-Y",
                same_sign & (cy == POW2) & (cx == TWO1) &
                (ey == ex + 1) & (gx == fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex-1, gx+2), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-MM01-S5-X",
                same_sign & (cx == POW2) & (cy == MM01) &
                (ex == ey + 1) & (gy == fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy, gy+1), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-MM01-S5-Y",
                same_sign & (cy == POW2) & (cx == MM01) &
                (ey == ex + 1) & (gx == fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx, gx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-G00-S9-X",
                same_sign & (cx == POW2) & (cy == G00) &
                (ex == ey + 1) & (gy == fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey-1, gy+1:fy-1), pos_zero)
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey-1, fy+1), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-G00-S9-Y",
                same_sign & (cy == POW2) & (cx == G00) &
                (ey == ex + 1) & (gx == fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex-1, gx+1:fx-1), pos_zero)
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex-1, fx+1), pos_zero)
            end

            checker("SELTZO-TwoSum-POW2-G10-S5-X",
                same_sign & (cx == POW2) & (cy == G10) &
                (ex == ey + 1) & (gy == fx + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy, gy+1:fy), pos_zero)
            end
            checker("SELTZO-TwoSum-POW2-G10-S5-Y",
                same_sign & (cy == POW2) & (cx == G10) &
                (ey == ex + 1) & (gx == fy + 1)
            ) do lemma
                add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx, gx+1:fx), pos_zero)
            end

        end
        #! format: on

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
