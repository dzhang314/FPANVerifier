function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
    ::Val{ALL1},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ALL1-ALL1-DE",
        (ex == ey)
    ) do lemma
        add_case!(lemma, pos_zero, pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-ALL1-DA1-X",
        (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, fx - 1, gx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-ALL1-DA1-Y",
        (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, fy - 1, gy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-ALL1-DA2-X",
        (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ALL1-ALL1-DA2-Y",
        (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ALL1-ALL1-DG-X",
        (ex > ey + 2) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ALL1-ALL1-DG-Y",
        (ey > ex + 2) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ALL1-ALL1-DB-X",
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ALL1-ALL1-DB-Y",
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
