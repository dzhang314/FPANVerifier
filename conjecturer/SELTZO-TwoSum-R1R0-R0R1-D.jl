function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R1R0},
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

    checker("SELTZO-TwoSum-R1R0-R0R1-D1-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx + 1 < ey) & (ex > fy + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-D1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy + 1 < ex) & (ey > fx + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-D4-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex < ey + (p - 1)) & (ex > fy + p) & (fx + 1 > ey) & (ex > fx + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-D4-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey < ex + (p - 1)) & (ey > fx + p) & (fy + 1 > ex) & (ey > fy + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-D5-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx + 1 < ey) & (ex < fy + p) & (fx > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-D5-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy + 1 < ex) & (ey < fx + p) & (fy > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DE1-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx + 1 > fy) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx + 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DE1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy + 1 > fx) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy + 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DE2-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx < fy) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy + 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DE2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy < fx) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx + 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DE3-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey) & (ey == fy + 3) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ex - 3, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DE3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex) & (ex == fx + 3) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ey - 3, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DE4-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx + 1 < fy) & (ex < fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fx, fy - (p - 3)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DE4-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy + 1 < fx) & (ey < fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fy, fx - (p - 3)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DE5-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx + 2 == ey) & (fx < fy + (p - 3)) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy, fx - (p - 3)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DE5-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy + 2 == ex) & (fy < fx + (p - 3)) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx, fy - (p - 3)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DE6-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey) & (ex == fx + 3) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ex - 3, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DE6-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex) & (ey == fy + 3) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ey - 3, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DE7-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey) & (ex == fx + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 2, ex - (p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DE7-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex) & (ey == fy + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 2, ey - (p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DE8-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx - (p - 3), fx - (p + p - 3), fx - (p - 3)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DE8-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy - (p - 3), fy - (p + p - 3), fy - (p - 3)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DE9-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey) & (ex == fx + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 2, ex - (p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DE9-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex) & (ey == fy + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 2, ey - (p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DE10-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ex - (p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DE10-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DE11-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx + (p - 1) == ey) & (ex == fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DE11-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy + (p - 1) == ex) & (ey == fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DE12-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx + 2 == ey) & (ex == fy + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DE12-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy + 2 == ex) & (ey == fx + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DA11-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx + 2 < ey) & (fx > fy) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DA11-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy + 2 < ex) & (fy > fx) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DA12-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx < fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DA12-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy < fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DA13-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx + 1 == ey) & (fx < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, fx + 1, fy, fx - (p - 3)), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DA13-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy + 1 == ex) & (fy < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, fy + 1, fx, fy - (p - 3)), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DA14-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx + 2 == ey) & (ex > fy + 3) & (fx < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - 3, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DA14-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy + 2 == ex) & (ey > fx + 3) & (fy < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - 3, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DA15-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx < fy + (p - 2)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DA15-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy < fx + (p - 2)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DA16-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fy + 3) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy, fx + 1),
            SELTZORange(~sy, 0, 0, fy - (p - 3), fy - (p + p - 3), fy - (p - 3)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DA16-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fx + 3) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx, fy + 1),
            SELTZORange(~sx, 0, 0, fx - (p - 3), fx - (p + p - 3), fx - (p - 3)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DA17-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DA17-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DA18-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - (p - 1), ex),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DA18-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - (p - 1), ey),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DA201-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (ex < fy + p) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DA201-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (ey < fx + p) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DA202-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (ex < fy + p) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DA202-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (ey < fx + p) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DA211-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (ey == fy + (p - 2)) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 1, ey),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DA211-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (ex == fx + (p - 2)) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 1, ex),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DA212-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (ey == fy + (p - 2)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DA212-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (ex == fx + (p - 2)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-D1A-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx < fy + (p - 2)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-D1A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy < fx + (p - 2)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-D1B0-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx + 1 < ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-D1B0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy + 1 < ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-D1C0-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex > fy + p) & (fx < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx + 2),
            SELTZORange(sy, 1, 0, fy, fx - (p - 1), fx - (p - 2)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-D1C0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey > fx + p) & (fy < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy + 2),
            SELTZORange(sx, 1, 0, fx, fy - (p - 1), fy - (p - 2)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-D1C1-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (fx == fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx + 2),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-D1C1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (fy == fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy + 2),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-D1AC-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex == fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, fx + 1, fy - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-D1AC-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey == fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, fy + 1, fx - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-D1BC-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex > ey + 2) & (fx + 1 == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 2, fx + 2),
            SELTZORange(~sy, 0, 0, fx - (p - 2), fx - (p + p - 2), fx - (p - 2)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-D1BC-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey > ex + 2) & (fy + 1 == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 2, fy + 2),
            SELTZORange(~sx, 0, 0, fy - (p - 2), fy - (p + p - 2), fy - (p - 2)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-D2A0-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx == fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-D2A0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy == fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-D2A1-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx + 2 == ey) & (fx == fy) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fx - (p - 3), fx - (p + p - 3), fx - (p - 3)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-D2A1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy + 2 == ex) & (fy == fx) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fy - (p - 3), fy - (p + p - 3), fy - (p - 3)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-D3B0-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex < fy + p) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-D3B0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey < fx + p) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-D3C0-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx + 1 > ey) & (fx < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-D3C0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy + 1 > ex) & (fy < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-D3AC-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx > ey) & (fx == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-D3AC-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy > ex) & (fy == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-D4A0-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx < ey + (p - 3)) & (fx > fy + (p - 2)) & (ex == fx + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-D4A0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy < ex + (p - 3)) & (fy > fx + (p - 2)) & (ey == fy + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-D4B0-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex < ey + (p - 1)) & (fx > fy + (p - 2)) & (ey == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-D4B0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey < ex + (p - 1)) & (fy > fx + (p - 2)) & (ex == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-D4AB-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx < ey + (p - 3)) & (ex > fy + p) & (ex == fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-D4AB-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy < ex + (p - 3)) & (ey > fx + p) & (ey == fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DB10-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ex > fx + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DB10-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ey > fy + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DB11-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (fx == ey + (p - 3)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DB11-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (fy == ex + (p - 3)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DB12-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ex == fy + (p + p - 2)) & (fx + 2 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DB12-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ey == fx + (p + p - 2)) & (fy + 2 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DB13-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ex == fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ex - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DB13-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ey == fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ey - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DB20-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ex > fx + 2) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DB20-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ey > fy + 2) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DB21-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (fx < fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 3), fy - (p - 3)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DB21-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + p) & (fy < fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 3), fx - (p - 3)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DB22-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ex > fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DB22-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ey > fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DB23-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (fx == ey + (p - 2)) & (fx == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 3), fy - (p - 3)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DB23-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + p) & (fy == ex + (p - 2)) & (fy == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 3), fx - (p - 3)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DB24-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (fx == ey + (p - 2)) & (ex == fy + (p + p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DB24-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + p) & (fy == ex + (p - 2)) & (ey == fx + (p + p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-DB25-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx == ey + (p - 2)) & (ex > fy + (p + 2)) & (ex == fx + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-DB25-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy == ex + (p - 2)) & (ey > fx + (p + 2)) & (ey == fy + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

end
