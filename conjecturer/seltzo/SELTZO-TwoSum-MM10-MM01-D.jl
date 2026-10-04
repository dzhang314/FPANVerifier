function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM10},
    ::Val{MM01},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-MM10-MM01-DA100-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx > fy + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-DA100-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy > fx + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-DA101-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx > fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fx - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-DA101-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy > fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fy - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-DA110-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fx - 3, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-DA110-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fy - 3, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-DA111-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fx - 3, fx - 2), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-DA111-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fy - 3, fy - 2), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-DA120-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, fx - 3, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-DA120-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, fy - 3, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-DA121-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-DA121-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-DA13-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-DA13-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-DA14-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 2, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-DA14-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 2, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-DA15-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx + 2, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-DA15-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy + 2, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-DA16-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 2 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-DA16-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 2 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-DA20-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey + 1, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-DA20-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex + 1, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-DA21-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx + 2 > fy) & (fx < fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey + 1, fy + 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-DA21-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy + 2 > fx) & (fy < fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex + 1, fx + 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D1-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx > ey + 2) & (ex > fy + p) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-D1-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy > ex + 2) & (ey > fx + p) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-D1A1-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 2, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-D1A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 2, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-D1A2-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey + 2) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-D1A2-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex + 2) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-D1C0-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx > ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-D1C0-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy > ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-D1AC2-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-D1AC2-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-D1D0-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx > ey + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-MM01-D1D0-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy > ex + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-MM01-D1AD2-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-MM01-D1AD2-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-MM01-D1E-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D1E-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx < ey) & (fx > fy) & (ex < fy + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy < ex) & (fy > fx) & (ey < fx + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2G0-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx < ey) & (ex == fy + (p - 2)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2G0-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy < ex) & (ey == fx + (p - 2)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2G1-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (ex == fy + (p - 2)) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2G1-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey > ex + 2) & (ey == fx + (p - 2)) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2A00-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx > fy + 1) & (fx < ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey + 1, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2A00-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy > fx + 1) & (fy < ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex + 1, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2A01-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx > fy + 1) & (fx < ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey + 1, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2A01-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy > fx + 1) & (fy < ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex + 1, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2A10-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx == fy + 1) & (fx + 1 < ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey + 1, fx + 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2A10-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy == fx + 1) & (fy + 1 < ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex + 1, fy + 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2A11-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx == fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey + 1, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2A11-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy == fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex + 1, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2AB-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx < ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey + 1, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2AB-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy < ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex + 1, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2B-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx < ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2B-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy < ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2BC-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2BC-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2C0-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey) & (ex < fy + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2C0-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex) & (ey < fx + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2C1-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2C1-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2D0-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == fy + 1) & (ex > fy + 3) & (ex < fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2D0-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == fx + 1) & (ey > fx + 3) & (ey < fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2D1-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == fy + 1) & (ex == fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2D1-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == fx + 1) & (ey == fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2CD0-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey) & (ex > fy + 3) & (ex < fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2CD0-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex) & (ey > fx + 3) & (ey < fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2CD1-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2CD1-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2E-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx < ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2E-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy < ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2CE-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 2, ey - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2CE-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 2, ex - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-D2F-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx + 2 > fy) & (fx < fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D2F-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy + 2 > fx) & (fy < fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D3-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx < ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-D3-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy < ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-D3A-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-D3A-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-D3B-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx < ey) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-D3B-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy < ex) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-D3AB-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, ey - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-D3AB-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, ex - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-D4A-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D4A-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D4AB-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-D4AB-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-D4AC-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-MM01-D4AC-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-MM01-D4AD-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-D4AD-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-DB0-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-DB0-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-DB1-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-DB1-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
