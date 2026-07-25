function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM10},
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

    checker("SELTZO-TwoSum-MM10-ALL1-DA1-X",
        (CLASS_X == MM10) & (CLASS_Y == ALL1) &
        (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fx - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ALL1-DA1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ALL1) &
        (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fy - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ALL1-DA2-X",
        (CLASS_X == MM10) & (CLASS_Y == ALL1) &
        (ex == ey + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, fx, ey - (p - 3)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ALL1-DA2-Y",
        (CLASS_Y == MM10) & (CLASS_X == ALL1) &
        (ey == ex + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, fy, ex - (p - 3)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ALL1-D1A1-X",
        (CLASS_X == MM10) & (CLASS_Y == ALL1) &
        (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 2, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ALL1-D1A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ALL1) &
        (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 2, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ALL1-D1A2-X",
        (CLASS_X == MM10) & (CLASS_Y == ALL1) &
        (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ALL1-D1A2-Y",
        (CLASS_Y == MM10) & (CLASS_X == ALL1) &
        (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ALL1-D2A-X",
        (CLASS_X == MM10) & (CLASS_Y == ALL1) &
        (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ALL1-D2A-Y",
        (CLASS_Y == MM10) & (CLASS_X == ALL1) &
        (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ALL1-DB-X",
        (CLASS_X == MM10) & (CLASS_Y == ALL1) &
        (ex == ey + p) & (fx == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ALL1-DB-Y",
        (CLASS_Y == MM10) & (CLASS_X == ALL1) &
        (ey == ex + p) & (fy == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

end
