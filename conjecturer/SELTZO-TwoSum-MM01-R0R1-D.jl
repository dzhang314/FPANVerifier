function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM01},
    ::Val{R0R1},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-MM01-R0R1-DE1-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx > fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DE1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex) & (fy > fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DE2-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ex - (p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DE2-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DE30-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy + 1) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx + 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DE30-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx + 1) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy + 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DE31-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy + 1) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DE31-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx + 1) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DE32-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy + 1) & (ex == fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DE32-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx + 1) & (ey == fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DE40-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx < fy + 1) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy + 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DE40-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex) & (fy < fx + 1) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx + 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DE41-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey) & (ey == fy + 3) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DE41-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex) & (ex == fx + 3) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DE42-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DE42-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DE43-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey) & (ey == fy + 2) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DE43-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex) & (ex == fx + 2) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DE44-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey) & (ey == fy + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 2, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DE44-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex) & (ex == fx + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 2, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DE45-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy) & (ex == fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 3, ex - (p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DE45-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx) & (ey == fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 3, ey - (p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DA0-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx > fy + 2) & (ex > fx + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DA0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy > fx + 2) & (ey > fy + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DA0A-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx > fy + 2) & (ex == fx + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DA0A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy > fx + 2) & (ey == fy + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DA0B-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx > fy + 2) & (ex > fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DA0B-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy > fx + 2) & (ey > fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DA0AB-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx > fy + 2) & (ex == fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - 3, ex - 3),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DA0AB-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy > fx + 2) & (ey == fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - 3, ey - 3),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DA1-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy + 3),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DA1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx + 3),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DA1A-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DA1A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DA2-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy + 1) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DA2-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx + 1) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DA2A-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DA2A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DA2B-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, fx - 2, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DA2B-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, fy - 2, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DA3-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx < fy + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DA3-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy < fx + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DA3B0-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx < fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DA3B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy < fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DA3B1-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DA3B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D1-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx < ey) & (fx > fy + 2) & (ex < fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy < ex) & (fy > fx + 2) & (ey < fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D1A0-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx + 1 < ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D1A0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy + 1 < ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D1A1-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx + 1 == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D1A1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy + 1 == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D1B0-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx + 1 < ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D1B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy + 1 < ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D1B1-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex > ey + 2) & (fx + 1 == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D1B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey > ex + 2) & (fy + 1 == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D1B2-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (fx + 1 == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D1B2-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (fy + 1 == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D1C-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx < ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D1C-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy < ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D2-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx < ey) & (ex > fy + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D2-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy < ex) & (ey > fx + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D2A-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx < ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D2A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy < ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D3A-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex == ey + 2) & (ex < fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D3A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex) & (ey == ex + 2) & (ey < fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D3C-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex > ey + 2) & (ex < fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D3C-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex) & (ey > ex + 2) & (ey < fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D3AC-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex == ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D3AC-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex) & (ey == ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D3B0-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex < fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D3B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey < fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D3B1-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex < fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D3B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey < fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D4-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx > ey + 1) & (ex > fy + p) & (ex < ey + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D4-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy > ex + 1) & (ey > fx + p) & (ey < ex + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D4A-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D4A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D4AC0-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex == fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D4AC0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey == fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D4AC1-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex == fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D4AC1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey == fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D4AD0-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex == fy + p) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D4AD0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex) & (ey == fx + p) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D4AD1-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex == fy + p) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D4AD1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex) & (ey == fx + p) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D4B-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D4B-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D4C0-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D4C0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D4C1-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D4C1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D4D0-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex > fy + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D4D0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex) & (ey > fx + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D4D1-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex > ey + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D4D1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex) & (ey > ex + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-D4D2-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex == ey + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-D4D2-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex) & (ey == ex + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DB10-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DB10-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DB11-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DB11-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DB20-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DB20-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DB21-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 3), fy - (p - 3)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DB21-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 3), fx - (p - 3)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-DB22-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-DB22-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
