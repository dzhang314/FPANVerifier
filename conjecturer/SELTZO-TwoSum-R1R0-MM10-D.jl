function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R1R0},
    ::Val{MM10},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R1R0-MM10-DE00-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey) & (fx == fy) & (ex == fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 3, ex - (p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DE00-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex) & (fy == fx) & (ey == fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 3, ey - (p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DE1-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey) & (fx == fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fy - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DE1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex) & (fy == fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fx - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DE2-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey) & (fx > fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DE2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex) & (fy > fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DE30-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey) & (fx + 1 == fy) & (ex == fx + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DE30-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex) & (fy + 1 == fx) & (ey == fy + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DE4-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey) & (fx == fy) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DE4-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex) & (fy == fx) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DE5-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey) & (fx > fy) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DE5-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex) & (fy > fx) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DE6-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey) & (fx + 1 > fy) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx + 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DE6-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex) & (fy + 1 > fx) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy + 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DE7-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey) & (fx + 1 == fy) & (ex == gx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DE7-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex) & (fy + 1 == fx) & (ey == gy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DE8-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey) & (fx + 1 == fy) & (ex > gx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy + 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DE8-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex) & (fy + 1 == fx) & (ey > gy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx + 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DE9-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey) & (fx + 2 == fy) & (ex == gx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ex - (p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DE9-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex) & (fy + 2 == fx) & (ey == gy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DE10-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey) & (fx + 1 < fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DE10-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex) & (fy + 1 < fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DE11-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey) & (fx + 2 < fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DE11-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex) & (fy + 2 < fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DA0-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 2 > fy) & (ex < fy + (p - 2)) & (ex > fx + 3) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DA0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 2 > fx) & (ey < fx + (p - 2)) & (ey > fy + 3) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DA1-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 > fy) & (ex > fx + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DA1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 > fx) & (ey > fy + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DA20-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DA20-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DA21-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fy, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DA21-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fx, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DA3-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy) & (ex == fx + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DA3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx) & (ey == fy + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DA5-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx > fy) & (ex == fx + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DA5-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy > fx) & (ey == fy + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DA6-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx > fy) & (ex == fx + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DA6-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy > fx) & (ey == fy + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DA7-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 == fy) & (ex == gx + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy, fx),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DA7-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 == fx) & (ey == gy + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx, fy),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DA10-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 == fy) & (ex > gx + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DA10-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 == fx) & (ey > gy + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DA11-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DA11-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DA12-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 2 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx + 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DA12-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 2 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy + 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D1B-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (fx > ey) & (ex == fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D1B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (fy > ex) & (ey == fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D1AB-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (fx > ey) & (ex == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D1AB-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (fy > ex) & (ey == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D1C-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (fx + 1 > ey) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, ey),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D1C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (fy + 1 > ex) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, ex),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D1AC-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (fx > ey) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D1AC-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (fy > ex) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D1D0-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (fx + 1 > ey) & (ex == fy + p) & (ex > fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, ey),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D1D0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (fy + 1 > ex) & (ey == fx + p) & (ey > fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, ex),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D1D1-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (fx + 1 > ey) & (ex == fy + p) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, ey),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D1D1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (fy + 1 > ex) & (ey == fx + p) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, ex),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D1AD0-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex == fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D1AD0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey == fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D1AD1-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D1AD1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D2A-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (fx == ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D2A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + 2) & (fy == ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D2B0-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex > ey + 2) & (fx + 1 == ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D2B0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey > ex + 2) & (fy + 1 == ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D2B1-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (fx + 1 == ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D2B1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + 2) & (fy + 1 == ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D2C-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex > ey + 2) & (fx + 2 > ey) & (fx < ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D2C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey > ex + 2) & (fy + 2 > ex) & (fy < ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D2AC-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (fx == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 1, fy),
            SELTZORange(~sy, 0, 0, fy - 3, fy - (p + 3), fy - 3))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D2AC-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + 2) & (fy == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 1, fx),
            SELTZORange(~sx, 0, 0, fx - 3, fx - (p + 3), fx - 3))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D2BC-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (fx + 1 == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy),
            SELTZORange(~sy, 0, 0, fy - 3, fy - (p + 3), fy - 3))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D2BC-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + 2) & (fy + 1 == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx),
            SELTZORange(~sx, 0, 0, fx - 3, fx - (p + 3), fx - 3))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D2D2-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex > ey + 2) & (fx + 1 == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D2D2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey > ex + 2) & (fy + 1 == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D2AD-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 1, ey),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D2AD-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + 2) & (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 1, ex),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D2BD-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (fx + 1 == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D2BD-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + 2) & (fy + 1 == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D2E0-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D2E0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D2E1-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D2E1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D3-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx + 1 < ey) & (fx + 2 > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy + 1 < ex) & (fy + 2 > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D3A-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D3A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D3B0-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx + 1 < ey) & (fx + 1 > fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D3B0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy + 1 < ex) & (fy + 1 > fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D3B1-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx + 1 == fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D3B1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy + 1 == fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D3C0-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D3C0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D3C1-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (ex == fy + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D3C1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (ey == fx + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D3D0-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D3D0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D3D1-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx + 1),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D3D1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy + 1),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D4-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (fx + 1 > ey) & (ex < ey + (p - 1)) & (ex > fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D4-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (fy + 1 > ex) & (ey < ex + (p - 1)) & (ey > fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D4A-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex < ey + (p - 1)) & (ex > fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D4A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey < ex + (p - 1)) & (ey > fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D5-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D5-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-D5A-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-D5A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DB10-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DB10-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DB11-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DB11-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DB20-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ey > fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DB20-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + p) & (ex > fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DB21-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ey > fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DB21-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + p) & (ex > fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DB22-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ey == fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DB22-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + p) & (ex == fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM10-DB23-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ey == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM10-DB23-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM10) &
        (ey == ex + p) & (ex == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - 1, ex - (p - 1)))
    end

end
