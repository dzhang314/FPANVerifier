function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO0},
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

    checker("SELTZO-TwoSum-TWO0-MM10-DE0A-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy) & (ex == ey) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DE0A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx) & (ey == ex) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DE0B-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (ex == ey) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DE0B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx + 1) & (ey == ex) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DE1A-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy) & (ex == ey) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ex - 3, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DE1A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx) & (ey == ex) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ey - 3, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DE1B-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (ex == ey) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ex - 3, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DE1B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx + 1) & (ey == ex) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ey - 3, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DE2-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey) & (ex == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fx - p, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DE2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex) & (ey == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fy - p, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DE3-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey) & (ex == fx + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fx - 3, fx - 2), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DE3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex) & (ey == fy + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fy - 3, fy - 2), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DE4-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx + 1 == fy) & (ex == ey) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DE4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy + 1 == fx) & (ey == ex) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DE5-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey) & (fx + 1 == fy) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ex - 3, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DE5-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex) & (fy + 1 == fx) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ey - 3, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DE6-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey) & (ex == fx + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DE6-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex) & (ey == fy + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DE7-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx > fy + 2) & (ex == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DE7-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy > fx + 2) & (ey == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DE8-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy + 2) & (ex == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, fx - 3, fx - 3), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DE8-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx + 2) & (ey == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, fy - 3, fy - 3), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DE9-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx + 1 < fy) & (ex == ey) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DE9-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy + 1 < fx) & (ey == ex) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DE10-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx + 2 < fy) & (ex == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DE10-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy + 2 < fx) & (ey == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DE11-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx + 2 == fy) & (ex == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DE11-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy + 2 == fx) & (ey == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DA10-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx > fy) & (fx + 1 < ey) & (ex == ey + 1) & (ey > fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DA10-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy > fx) & (fy + 1 < ex) & (ey == ex + 1) & (ex > fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DA11-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + 2) & (ey > fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, fy - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DA11-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + 2) & (ex > fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, fx - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DA120-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + 3) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - 3, fx - 2),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DA120-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + 3) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - 3, fy - 2),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DA121-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 == fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - 3, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DA121-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 == fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - 3, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DA13-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy - 1, fy - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DA13-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx - 1, fx - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DA14-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fy - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DA14-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fx - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DA15-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy) & (ex == ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DA15-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx) & (ey == ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DA16-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy) & (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DA16-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx) & (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DA17-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx < fy) & (ey > fx + 3) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DA17-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy < fx) & (ex > fy + 3) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DA18-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx > fy + 2) & (fx + 1 < ey) & (ex == ey + 1) & (ey > fy + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DA18-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy > fx + 2) & (fy + 1 < ex) & (ey == ex + 1) & (ex > fx + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DA19-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + 2) & (ey > fy + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DA19-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + 2) & (ex > fx + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DA110-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy + 2) & (ex == ey + 1) & (ey > fy + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DA110-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx + 2) & (ey == ex + 1) & (ex > fx + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DA112-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (ex == ey + 1) & (ey > fy + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DA112-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx + 1) & (ey == ex + 1) & (ex > fx + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DA23-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex == ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DA23-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey == ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DA29-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (ex == fx + 2) & (ey > fy + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DA29-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex + 2) & (ey == fy + 2) & (ex > fx + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DA210-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (ey == fy + (p - 3)) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DA210-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex + 2) & (ex == fx + (p - 3)) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DA211-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (ex > fx + 3) & (ex == fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DA211-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex + 2) & (ey > fy + 3) & (ey == fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx > fy) & (fx < ey) & (ex < fy + (p - 2)) & (ex > ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy > fx) & (fy < ex) & (ey < fx + (p - 2)) & (ey > ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1A-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (fx == fy + 1) & (ex < fy + (p - 2)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (fy == fx + 1) & (ey < fx + (p - 2)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1B0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy) & (ex < fy + (p - 2)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1B0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx) & (ey < fx + (p - 2)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1B1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx + 1 == fy) & (ex < fy + (p - 2)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy - 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1B1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy + 1 == fx) & (ey < fx + (p - 2)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx - 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1C0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx > fy + 2) & (fx < ey) & (ex == fy + (p - 2)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1C0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy > fx + 2) & (fy < ex) & (ey == fx + (p - 2)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1C10-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy + 2) & (fx + 1 < ey) & (ex == fy + (p - 2)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 3),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1C10-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx + 2) & (fy + 1 < ex) & (ey == fx + (p - 2)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 3),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1C11-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (fx + 1 < ey) & (ex == fy + (p - 2)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1C11-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx + 1) & (fy + 1 < ex) & (ey == fx + (p - 2)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1C20-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy + 2) & (fx + 1 == ey) & (ex == fy + (p - 2)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy + 3, fx + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1C20-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx + 2) & (fy + 1 == ex) & (ey == fx + (p - 2)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx + 3, fy + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1C21-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy + 2) & (fx == ey) & (ex == fy + (p - 2)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy + 3, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1C21-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx + 2) & (fy == ex) & (ey == fx + (p - 2)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx + 3, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1C22-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (fx + 1 == ey) & (ex == fy + (p - 2)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy + 3, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1C22-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx + 1) & (fy + 1 == ex) & (ey == fx + (p - 2)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx + 3, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1D0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx > fy + 2) & (fx < ey) & (ex == fy + (p - 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1D0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy > fx + 2) & (fy < ex) & (ey == fx + (p - 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy + 2) & (fx + 1 < ey) & (ex == fy + (p - 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx + 2) & (fy + 1 < ex) & (ey == fx + (p - 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1D20-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy + 2) & (fx + 1 == ey) & (ex == fy + (p - 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, ey + 1),
            SELTZORange(sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1D20-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx + 2) & (fy + 1 == ex) & (ey == fx + (p - 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, ex + 1),
            SELTZORange(sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1D21-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy + 2) & (fx == ey) & (ex == fy + (p - 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, ey),
            SELTZORange(sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1D21-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx + 2) & (fy == ex) & (ey == fx + (p - 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, ex),
            SELTZORange(sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1E0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx > fy + 3) & (fx < ey) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ex - (p - 2)),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1E0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy > fx + 3) & (fy < ex) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ey - (p - 2)),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1E1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy + 3) & (fx + 1 < ey) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1E1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx + 3) & (fy + 1 < ex) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1E2-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy + 3) & (fx + 1 == ey) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1E2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx + 3) & (fy + 1 == ex) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1E3-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx > fy + 3) & (fx < ey) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ex - (p - 2)),
            SELTZORange(~sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1E3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy > fx + 3) & (fy < ex) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ey - (p - 2)),
            SELTZORange(~sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D1E4-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy + 3) & (fx + 1 < ey) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D1E4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx + 3) & (fy + 1 < ex) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex > fy + p) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey > fx + p) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2A0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2A0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2C0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ex - (p - 2)),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2C0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ey - (p - 2)),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2C1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx > ey + 2) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2C1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy > ex + 2) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2C2-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == ey + 2) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2C2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == ex + 2) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2AC0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx > fy + 3) & (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, ex - (p - 2)),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2AC0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy > fx + 3) & (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, ey - (p - 2)),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2AC1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == fy + 3) & (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, ey),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2AC1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == fx + 3) & (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, ex),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2AC2-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx > fy + 3) & (fx == ey) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, ex - (p - 2)),
            SELTZORange(~sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2AC2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy > fx + 3) & (fy == ex) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, ey - (p - 2)),
            SELTZORange(~sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2AC3-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ex - (p - 2)),
            SELTZORange(~sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2AC3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ey - (p - 2)),
            SELTZORange(~sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2D-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2D-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2AD0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx > fy + 2) & (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fy + 1),
            SELTZORange(sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2AD0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy > fx + 2) & (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fx + 1),
            SELTZORange(sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2AD1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2AD1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2E-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2AE0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx > fy + 2) & (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2AE0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy > fx + 2) & (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2AE1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2AE1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2F0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex < fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2F0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey < fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D2F1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D2F1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-D3-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (fx < ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-D3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (fy < ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DB10-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DB10-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DB11-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DB11-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DB20-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ex < fx + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ex - (p - 2)),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DB20-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex + p) & (ey < fy + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ey - (p - 2)),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DB21-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ex == fx + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DB21-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex + p) & (ey == fy + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DB22-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ex < fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ex - (p - 2)),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DB22-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex + p) & (ey < fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ey - (p - 2)),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM10-DB23-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ex == fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM10-DB23-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM10) &
        (ey == ex + p) & (ey == fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

end
