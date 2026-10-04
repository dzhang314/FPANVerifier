function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM01},
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

    checker("SELTZO-TwoSum-MM01-MM10-DE0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey) & (fx + 1 > fy) & (fx < fy + 2) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fx + 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM10-DE0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex) & (fy + 1 > fx) & (fy < fx + 2) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fy + 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM10-DE1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey) & (fx + 1 > fy) & (fx < fy + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM10-DE1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex) & (fy + 1 > fx) & (fy < fx + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM10-DE2-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey) & (fx == fy) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, ey - (p - 1), ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM10-DE2-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex) & (fy == fx) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, ex - (p - 1), ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM10-DE3-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey) & (fx == fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM10-DE3-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex) & (fy == fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM10-DE4-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey) & (fx + 1 == fy) & (ex > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy + 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM10-DE4-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex) & (fy + 1 == fx) & (ey > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx + 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM10-DE50-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey) & (fx + 1 == fy) & (ex == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM10-DE50-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex) & (fy + 1 == fx) & (ey == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM10-DE51-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey) & (fx + 2 == fy) & (ex == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fy - 3, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM10-DE51-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex) & (fy + 2 == fx) & (ey == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fx - 3, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM10-DE6-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey) & (fx + 1 == fy) & (ex == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fx - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM10-DE6-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex) & (fy + 1 == fx) & (ey == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fy - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM10-DE7-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx > fy + 2) & (ex == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fx - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM10-DE7-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy > fx + 2) & (ey == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fy - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM10-DE8-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey) & (fx == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM10-DE8-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex) & (fy == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM10-DE9-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey) & (fx + 1 < fy) & (ex > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM10-DE9-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex) & (fy + 1 < fx) & (ey > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM10-DE10-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey) & (fx + 2 < fy) & (ex == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fy - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM10-DE10-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex) & (fy + 2 < fx) & (ey == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fx - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM10-DA00-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx > fy) & (ex == ey + 1) & (ex > fx + 2) & (ey > fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM01-MM10-DA00-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy > fx) & (ey == ex + 1) & (ey > fy + 2) & (ex > fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM01-MM10-DA01-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx > fy + 2) & (ex == ey + 1) & (ex == fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, fy - 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM01-MM10-DA01-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy > fx + 2) & (ey == ex + 1) & (ey == fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, fx - 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM01-MM10-DA1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx > fy + 1) & (ex == ey + 1) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-DA1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy > fx + 1) & (ey == ex + 1) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-DA2-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (ex == ey + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-DA2-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == fx + 1) & (ey == ex + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-DA30-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (ex == ey + 1) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM01-MM10-DA30-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == fx + 1) & (ey == ex + 1) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM01-MM10-DA31-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == fy + 2) & (ex == ey + 1) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 3, fy - 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM01-MM10-DA31-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == fx + 2) & (ey == ex + 1) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 3, fx - 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM01-MM10-DA4-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 < fy) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM01-MM10-DA4-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 < fx) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM01-MM10-DA50-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 == fy) & (ex == ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM01-MM10-DA50-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 == fx) & (ey == ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM01-MM10-DA51-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == fy) & (ex == ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM01-MM10-DA51-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == fx) & (ey == ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM01-MM10-DA60-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 == fy) & (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy, fx - 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM01-MM10-DA60-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 == fx) & (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx, fy - 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM01-MM10-DA61-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == fy) & (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy, fx),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM01-MM10-DA61-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == fx) & (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx, fy),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM01-MM10-DA7-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM10-DA7-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == fx + 1) & (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM10-DA9-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, fy),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-DA9-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, fx),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D1A-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D1A-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D1B-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D1B-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D1C-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D1C-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D1AD1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ex - 1),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D1AD1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ey - 1),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D2-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx < ey) & (fx > fy) & (ex < fy + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D2-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy < ex) & (fy > fx) & (ey < fx + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D2B0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx < ey) & (fx > fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D2B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy < ex) & (fy > fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D2B1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx == fy + 1) & (ex == fy + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D2B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy == fx + 1) & (ey == fx + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D2C0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == fy) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D2C0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == fx) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D2C1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 == fy) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D2C1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 == fx) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D2D-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex > ey + 2) & (ex < fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D2D-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey > ex + 2) & (ey < fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D2AD-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex == ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D2AD-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey == ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D2BD-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex == fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D2BD-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey == fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D3A0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex < fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fy - 1),
            SELTZORange(~sy, 0, 0, fx - p, fx - (p + p), fx - p))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D3A0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey < fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fx - 1),
            SELTZORange(~sx, 0, 0, fy - p, fy - (p + p), fy - p))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D3A1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D3A1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D3AB0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D3AB0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D3AB1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D3AB1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D4-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx < ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D4-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy < ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D4C0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D4C0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D4C1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D4C1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D4A0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx < ey) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D4A0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy < ex) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D4A1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx < ey) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx - 1),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D4A1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy < ex) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy - 1),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D4AC00-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D4AC00-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D4AC01-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D4AC01-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D4AC1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey - 1),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D4AC1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex - 1),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D4B0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx < ey) & (ex == fy + (p - 1)) & (ey > fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx - 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D4B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy < ex) & (ey == fx + (p - 1)) & (ex > fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy - 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D4B1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx < ey) & (ex == fy + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D4B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy < ex) & (ey == fx + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D4BC0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey) & (fx > fy + 2) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx - 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D4BC0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex) & (fy > fx + 2) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy - 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D4BC1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (fx > fy + 2) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D4BC1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex + 1) & (fy > fx + 2) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D4BCE0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ex - 1),
            SELTZORange(sy, 1, 0, fy - 2, gy - 3, fy - 3))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D4BCE0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ey - 1),
            SELTZORange(sx, 1, 0, fx - 2, gx - 3, fx - 3))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D4BCE1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey - 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D4BCE1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex - 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-D4BD1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 2 > ey) & (fx == fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-D4BD1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 2 > ex) & (fy == fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-DB1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-DB1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-DB20-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-DB20-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-DB21-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-DB21-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

end
