function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO0},
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

    checker("SELTZO-TwoSum-TWO0-TWO1-DE0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 > fy) & (fx < fy + 2) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx + 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DE0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 > fx) & (fy < fx + 2) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy + 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DE10-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy + 1) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DE10-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx + 1) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DE11-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DE11-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DE2-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DE2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DE3-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DE3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DE4-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy) & (ex > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy + 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DE4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx) & (ey > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx + 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DE5-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy) & (ex == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DE5-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx) & (ey == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DE6-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy) & (ex == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DE6-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx) & (ey == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DE7-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx > fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DE7-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy > fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DE8-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DE8-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DE9-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 < fy) & (ex > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DE9-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 < fx) & (ey > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DE90-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 < fy) & (ex == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DE90-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 < fx) & (ey == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DE91-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 == fy) & (ex == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DE91-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 == fx) & (ey == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DA0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx > fy) & (ex == ey + 1) & (ex > fx + 2) & (ey > fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ex - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DA0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy > fx) & (ey == ex + 1) & (ey > fy + 2) & (ex > fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ey - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DA0A-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx > fy + 2) & (ex == ey + 1) & (ex == fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DA0A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy > fx + 2) & (ey == ex + 1) & (ey == fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DA1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx > fy + 2) & (ex == ey + 1) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DA1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy > fx + 2) & (ey == ex + 1) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DA20-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == fy + 2) & (ex == ey + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex - 2, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DA20-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == fx + 2) & (ey == ex + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey - 2, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DA21-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex == ey + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DA21-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey == ex + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DA30-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex == ey + 1) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DA30-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey == ex + 1) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DA31-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == fy + 2) & (ex == ey + 1) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DA31-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == fx + 2) & (ey == ex + 1) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DA50-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 == fy) & (ex == ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ex - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DA50-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 == fx) & (ey == ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ey - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DA51-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == fy) & (ex == ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ex - 2, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DA51-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == fx) & (ey == ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ey - 2, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DA60-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 == fy) & (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DA60-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 == fx) & (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DA61-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == fy) & (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DA61-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == fx) & (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DA7-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fy - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DA7-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fx - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DA9-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DA9-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D1A-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D1A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D1AE0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx > ey + 2) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D1AE0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy > ex + 2) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D1AE1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey + 2) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 3),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D1AE1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex + 2) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 3),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D1B-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D1B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D1C-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D1C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D1AD1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex == fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D1AD1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey == fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D2-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx < ey) & (fx > fy) & (ex < fy + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy < ex) & (fy > fx) & (ey < fx + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D2B0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx < ey) & (fx > fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D2B0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy < ex) & (fy > fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D2B10-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx + 1 < ey) & (fx == fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D2B10-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy + 1 < ex) & (fy == fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D2B11-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (fx == fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D2B11-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (fy == fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D2B2-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx + 1 < ey) & (fx == fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D2B2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy + 1 < ex) & (fy == fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D2C0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D2C0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D2C1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D2C1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D2D-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex > ey + 2) & (ex < fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D2D-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey > ex + 2) & (ey < fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D2AD-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex == ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D2AD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey == ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D2BD-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex == fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, ey - 2), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D2BD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey == fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, ex - 2), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D3A0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex < fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D3A0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey < fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D3A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D3A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D3AB0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 > ey) & (fx < ey + 2) & (fx > fy + 2) & (ex == fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D3AB0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 > ex) & (fy < ex + 2) & (fy > fx + 2) & (ey == fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D3AB1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D3AB1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D3ABC-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D3ABC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D4-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ey > fx) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ex > fy) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D4C0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D4C0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D4C1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D4C1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D4A-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ey > fx) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D4A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ex > fy) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D4AD0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ey > fx + 1) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D4AD0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ex > fy + 1) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D4AD1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ey == fx + 1) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D4AD1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ex == fy + 1) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D4AC0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + p) & (fx > fy + 3) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D4AC0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + p) & (fy > fx + 3) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D4AC1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 > ey) & (fx == fy + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, ey),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D4AC1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 > ex) & (fy == fx + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, ex),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D4B-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ey > fx) & (fy + 2 < fx) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D4B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ex > fy) & (fx + 2 < fy) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D4BC-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 > ey) & (fx < ey + 2) & (fx > fy + 2) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D4BC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 > ex) & (fy < ex + 2) & (fy > fx + 2) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D4BCE-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx < ey + 2) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D4BCE-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy < ex + 2) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D4BD0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ey > fx + 1) & (fy + 2 == fx) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D4BD0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ex > fy + 1) & (fx + 2 == fy) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D4BD1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (fx == fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D4BD1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (fy == fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-D4BCD-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey) & (fx == fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-D4BCD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex) & (fy == fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DB10-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ex - (p - 2)),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DB10-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ey - (p - 2)),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DB11-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DB11-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DB20-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (ey > fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ex - (p - 2)),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DB20-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex + p) & (ex > fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ey - (p - 2)),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DB21-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (ey == fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ex - (p - 2)),
            SELTZORange(~sy, 0, 0, fy + 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DB21-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex + p) & (ex == fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ey - (p - 2)),
            SELTZORange(~sx, 0, 0, fx + 1, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DB22-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DB22-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex + p) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-DB23-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-DB23-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex + p) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - 1, fx - 1))
    end

end
