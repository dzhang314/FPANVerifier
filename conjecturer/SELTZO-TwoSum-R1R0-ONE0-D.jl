function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R1R0},
    ::Val{ONE0},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R1R0-ONE0-DE0-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 2 < fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy - 1, fx, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DE0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 2 < fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx - 1, fy, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DE1-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 2 == fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DE1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 2 == fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DE2-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 1 < fy) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy - 1, ey - p, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DE2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 1 < fx) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx - 1, ex - p, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DE3-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DE3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DE4-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx == fy) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fy - 1, ey - p, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DE4-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex) & (fy == fx) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fx - 1, ex - p, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DE5-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx == fy) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DE5-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex) & (fy == fx) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DE6-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fx, fy - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DE6-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fy, fx - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DE7-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fx, fy, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DE7-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fy, fx, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DA0-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy - 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DA0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx - 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DA1-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DA1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DA2-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx > fy) & (fx + 1 < ey) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DA2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy > fx) & (fy + 1 < ex) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DA3-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx + 1 == ey) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fy, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DA3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy + 1 == ex) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fx, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DA4-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx > fy) & (fx + 1 < ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DA4-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy > fx) & (fy + 1 < ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DA5-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx + 1 == ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DA5-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy + 1 == ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DA6-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx == fy) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx - 1, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DA6-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy == fx) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy - 1, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DA7-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx == fy) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, ey - p, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DA7-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy == fx) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, ex - p, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D1-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx + 1 > fy) & (fx < ey) & (ex < fy + (p - 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy + 1 > fx) & (fy < ex) & (ey < fx + (p - 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D1C-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx + 1 > fy) & (fx < ey) & (ex < fy + (p - 1)) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D1C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy + 1 > fx) & (fy < ex) & (ey < fx + (p - 1)) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D1CD-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex < fy + (p - 1)) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D1CD-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy == ex) & (ey < fx + (p - 1)) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D1A-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx + 1 == fy) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D1A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy + 1 == fx) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D1B0-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx > fy) & (fx < ey + 1) & (ex == fy + (p - 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D1B0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy > fx) & (fy < ex + 1) & (ey == fx + (p - 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D1B0C-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx > fy) & (fx < ey) & (ex == fy + (p - 1)) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D1B0C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy > fx) & (fy < ex) & (ey == fx + (p - 1)) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D1B0CD-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fy, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D1B0CD-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fx, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D1B1-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx == fy) & (ex == fy + (p - 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D1B1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy == fx) & (ey == fx + (p - 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D1B1C-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx == fy) & (ex == fy + (p - 1)) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D1B1C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy == fx) & (ey == fx + (p - 1)) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D2-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy < ex) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D2A0-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx > fy + 1) & (fx < ey + 1) & (ex == fy + p) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D2A0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy > fx + 1) & (fy < ex + 1) & (ey == fx + p) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D2A0C-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx > fy + 1) & (fx < ey) & (ex == fy + p) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 2),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D2A0C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy > fx + 1) & (fy < ex) & (ey == fx + p) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 2),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D2A0CD-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == fy + p) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fy + 1, fy + 2),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D2A0CD-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == fx + p) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fx + 1, fx + 2),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D2A1-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx == fy + 1) & (ex == fy + p) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D2A1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy == fx + 1) & (ey == fx + p) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D2A1C-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx == fy + 1) & (ex == fy + p) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D2A1C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy == fx + 1) & (ey == fx + p) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D2B-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex > fy + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D2B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy < ex) & (ey > fx + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D2D-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx + 2),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D2D-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy == ex) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy + 2),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D2BD-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex > fy + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D2BD-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy == ex) & (ey > fx + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D3-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx > ey) & (ex > fy + p) & (ex < ey + p) & (ex > fx + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy > ex) & (ey > fx + p) & (ey < ex + p) & (ey > fy + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D3A-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx > ey) & (ex > fy + p) & (ex < ey + p) & (ex == fx + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D3A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy > ex) & (ey > fx + p) & (ey < ex + p) & (ey == fy + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D3B-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx > ey) & (ex > fy + p) & (ex < ey + p) & (ex > fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D3B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy > ex) & (ey > fx + p) & (ey < ex + p) & (ey > fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D3AB-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx > ey) & (ex > fy + p) & (ex < ey + p) & (ex == fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D3AB-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy > ex) & (ey > fx + p) & (ey < ex + p) & (ey == fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D3C-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx > ey) & (ex == fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D3C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy > ex) & (ey == fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D3AC-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx > ey) & (ex == fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D3AC-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy > ex) & (ey == fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D3D-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx > ey) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D3D-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy > ex) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-D3AD-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx > ey) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-D3AD-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy > ex) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DB0-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ex > fx + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DB0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ey > fy + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DB1-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ex > fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DB1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ey > fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DB2-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ex == fx + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DB2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ey == fy + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-DB3-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ex == fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-DB3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ey == fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
