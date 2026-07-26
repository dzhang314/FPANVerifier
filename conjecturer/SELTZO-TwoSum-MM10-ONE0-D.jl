function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM10},
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

    checker("SELTZO-TwoSum-MM10-ONE0-DE0-X",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > fx + 1) & (ey == ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DE0-Y",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > fy + 1) & (ex == ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DE1-X",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > fx + 1) & (ey == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy - 2, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DE1-Y",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > fy + 1) & (ex == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx - 2, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DE20-X",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx) & (ey == ex) & (ey > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DE20-Y",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy) & (ex == ey) & (ex > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DE21-X",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx + 1) & (ey == ex) & (ey > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DE21-Y",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy + 1) & (ex == ey) & (ex > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DE3-X",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx + 1) & (ey == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ex - (p + 1), ex - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DE3-Y",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy + 1) & (ex == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ey - (p + 1), ey - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DE4-X",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx) & (ey == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fy - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DE4-Y",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy) & (ex == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fx - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DE5-X",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx) & (ey == ex) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DE5-Y",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy) & (ex == ey) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DE6-X",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy + 1 == fx) & (ey == ex) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DE6-Y",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx + 1 == fy) & (ex == ey) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DE7-X",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy + 1 < fx) & (ey == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DE7-Y",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx + 1 < fy) & (ex == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DA10-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx + 1 < fy) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fx, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DA10-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy + 1 < fx) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fy, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DA11-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx + 1 == fy) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fx - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DA11-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy + 1 == fx) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fy - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DA12-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy + 1, fy - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DA12-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx + 1, fx - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DA13-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy + 1) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, ey - p, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DA13-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx + 1) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, ex - p, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DA14-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > fy + 1) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fx - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DA14-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > fx + 1) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fy - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DA20-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < fy) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, fy, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DA20-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < fx) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, fx, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DA21-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, fx + 1, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DA21-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, fy + 1, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DA22-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey) & (fx > fy) & (ex == ey + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, fx, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DA22-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex) & (fy > fx) & (ey == ex + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, fy, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DA23-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex == ey + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DA23-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex) & (ey == ex + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DA24-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex == ey + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, fx, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DA24-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex) & (ey == ex + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, fy, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DA25-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == ey + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey + 1, ey - 2, ey - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DA25-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == ex + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex + 1, ex - 2, ex - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D1A-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D1A-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D1B1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D1B1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D1B2-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D1B2-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D1C1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D1C1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D1C2-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D1C2-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D1D01-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 2, fx - 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D1D01-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 2, fy - 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D1D02-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D1D02-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D1D11-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 2, fx - 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D1D11-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 2, fy - 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D1D12-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D1D12-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D2A-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 2, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D2A-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 2, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D2B-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 2, ey - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D2B-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 2, ex - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D2C-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, ey - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D2C-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, ex - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D2D0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == fy + (p + 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, ey - 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D2D0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == fx + (p + 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, ex - 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D2D1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == fy + (p + 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, ey - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D2D1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == fx + (p + 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, ex - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D2E0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex > fy + (p + 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D2E0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex) & (ey > fx + (p + 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D2E1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex > fy + (p + 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D2E1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex) & (ey > fx + (p + 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D3A-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey) & (fx + 1 > fy) & (ex < fy + (p - 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D3A-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex) & (fy + 1 > fx) & (ey < fx + (p - 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D3B-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex == fy + (p - 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D3B-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex) & (ey == fx + (p - 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D3C-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex == fy + p) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D3C-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex) & (ey == fx + p) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D3D0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex == fy + (p + 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fx - 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D3D0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex) & (ey == fx + (p + 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fy - 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D3D1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex == fy + (p + 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D3D1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex) & (ey == fx + (p + 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D3E0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex > fy + (p + 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D3E0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex) & (ey > fx + (p + 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D3E1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex > fy + (p + 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D3E1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex) & (ey > fx + (p + 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D4A-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > ey + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D4A-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > ex + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D4B-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D4B-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D40-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > ey + 2) & (ex > fy + p) & (ex < ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D40-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > ex + 2) & (ey > fx + p) & (ey < ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-D41-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > ey + 2) & (ex < ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-D41-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > ex + 2) & (ey < ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DB10-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 3) & (ex == ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DB10-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 3) & (ey == ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DB11-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 3) & (ex == ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DB11-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 3) & (ey == ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DB20-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > ey + 3) & (ex == ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DB20-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > ex + 3) & (ey == ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-DB21-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > ey + 3) & (ex == ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-DB21-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > ex + 3) & (ey == ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

end
