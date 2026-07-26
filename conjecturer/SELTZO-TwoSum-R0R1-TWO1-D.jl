function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
    ::Val{TWO1},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R0R1-TWO1-DE0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DE0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DE1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DE1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DE20-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy - 2, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DE20-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx - 2, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DE21-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DE21-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DE30-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy - 1, ex - (p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DE30-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx - 1, ey - (p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DE31-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fy - 1, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DE31-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fx - 1, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DE4-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy, ex - (p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DE4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx, ey - (p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DE5-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DE5-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DA0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 < ey) & (fx > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DA0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 < ex) & (fy > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DA1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 < ey) & (fx > fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DA1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 < ex) & (fy > fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DA4-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx == fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DA4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy == fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DA5-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx == fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, ey - p, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DA5-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy == fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, ex - p, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DA6-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 == fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DA6-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 == fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DA7-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 == fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DA7-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 == fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DA8-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 < fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DA8-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 < fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DA9-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 < fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fy - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DA9-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 < fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fx - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D2G-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ex - (p - 3)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D2G-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy > ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ey - (p - 3)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D2A-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, ex - (p - 3)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D2A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, ey - (p - 3)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D3G-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D3G-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy > ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D3A-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D3A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D4G0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex < ey + (p - 2)) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ex - (p - 2)),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D4G0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy > ex) & (ey < ex + (p - 2)) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ey - (p - 2)),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D4A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex < ey + (p - 2)) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, ex - (p - 2)),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D4A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey < ex + (p - 2)) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, ey - (p - 2)),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D4G1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex == ey + (p - 2)) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ex - (p - 3)),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D4G1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy > ex) & (ey == ex + (p - 2)) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ey - (p - 3)),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D4A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == ey + (p - 2)) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D4A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == ex + (p - 2)) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D5G-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex < ey + (p - 1)) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D5G-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy > ex) & (ey < ex + (p - 1)) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D5A-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex < ey + (p - 1)) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 1, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D5A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey < ex + (p - 1)) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 1, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D6G-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx + 1 > fy) & (fx + 1 < ey) & (ex > ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D6G-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy + 1 > fx) & (fy + 1 < ex) & (ey > ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D6A-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex > ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D6A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey > ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D6B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx > fy) & (fx + 1 < ey) & (ex > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D6B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy > fx) & (fy + 1 < ex) & (ey > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D6B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx == fy) & (fx < ey) & (ex > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D6B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy == fx) & (fy < ex) & (ey > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D6AB-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex > ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D6AB-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey > ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D6C0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx > fy) & (fx + 1 < ey) & (ex > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D6C0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy > fx) & (fy + 1 < ex) & (ey > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D6C1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx == fy) & (fx < ey) & (ex > ey + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D6C1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy == fx) & (fy < ex) & (ey > ex + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D6C2-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx == fy) & (fx < ey) & (ex == ey + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex - 1, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D6C2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy == fx) & (fy < ex) & (ey == ex + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey - 1, ex - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D6AC-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, fy + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D6AC-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, fx + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D7G-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx < fy) & (ex > ey + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D7G-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy < fx) & (ey > ex + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D7A-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx < fy) & (fx < ey) & (ex == ey + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ey - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D7A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy < fx) & (fy < ex) & (ey == ex + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ex - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D7B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx + 1 == fy) & (fx < ey) & (ex > ey + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D7B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy + 1 == fx) & (fy < ex) & (ey > ex + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D7B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx + 1 == fy) & (fx < ey) & (ex == ey + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D7B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy + 1 == fx) & (fy < ex) & (ey == ex + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D8G0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx > fy + 1) & (fx + 1 < ey) & (ex > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D8G0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy > fx + 1) & (fy + 1 < ex) & (ey > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D8G1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (fx + 1 < ey) & (ex > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D8G1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (fy + 1 < ex) & (ey > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D8A-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fy + 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D8A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fx + 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D9G-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (ex > ey + 1) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D9G-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (ey > ex + 1) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D9A-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex > ey + 1) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fy + 2, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D9A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey > ex + 1) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fx + 2, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D10G-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (ex < ey + (p + 1)) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D10G-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (ey < ex + (p + 1)) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-D10A-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex < ey + (p + 1)) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ex - p, ex - (p - 1)),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-D10A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey < ex + (p + 1)) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ey - p, ey - (p - 1)),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DB1G-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ex - (p - 2)),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DB1G-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy > ex) & (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ey - (p - 2)),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DB1A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == ey + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DB1A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == ex + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DB1A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == ey + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ex - (p + 1), ex - 1),
            SELTZORange(~sy, 0, 0, ex - (p + 2), ex - (p + p + 2), ex - (p + 2)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DB1A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == ex + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ey - (p + 1), ey - 1),
            SELTZORange(~sx, 0, 0, ey - (p + 2), ey - (p + p + 2), ey - (p + 2)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DB2G0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ex - (p - 2)),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DB2G0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ey - (p - 2)),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DB2A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DB2A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DB2G1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ex - (p - 2)),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DB2G1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ey - (p - 2)),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-DB2A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-DB2A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

end
