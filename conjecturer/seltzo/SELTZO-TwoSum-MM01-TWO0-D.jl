function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM01},
    ::Val{TWO0},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-MM01-TWO0-DA0-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx + 1 < fy) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-DA0-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy + 1 < fx) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-DA1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx + 1 == fy) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-DA1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy + 1 == fx) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-DA2-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx == fy) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-DA2-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy == fx) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-DA3-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx == fy + 1) & (ex == ey + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO0-DA3-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy == fx + 1) & (ey == ex + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO0-DA4-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx == fy + 1) & (ex == ey + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fy, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO0-DA4-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy == fx + 1) & (ey == ex + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fx, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO0-DA5-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx > fy + 1) & (ex == ey + 1) & (ex == fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO0-DA5-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy > fx + 1) & (ey == ex + 1) & (ey == fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO0-DA6-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO0-DA6-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO0-DA7-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx > fy + 1) & (ex == ey + 1) & (ex > fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO0-DA7-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy > fx + 1) & (ey == ex + 1) & (ey > fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO0-DA8-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx == fy + 2) & (ex == ey + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO0-DA8-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy == fx + 2) & (ey == ex + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO0-DA9-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx > fy + 2) & (ex == ey + 1) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO0-DA9-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy > fx + 2) & (ey == ex + 1) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx + 1 == fy) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy + 1 == fx) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D1C-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx == fy) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D1C-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy == fx) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D2-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx < ey) & (fx > fy) & (ex < fy + (p - 2)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D2-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy < ex) & (fy > fx) & (ey < fx + (p - 2)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D2A-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx < ey) & (fx > fy) & (ex < fy + (p - 2)) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D2A-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy < ex) & (fy > fx) & (ey < fx + (p - 2)) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D2AC0-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx < ey) & (fx > fy + 2) & (ex == fy + (p - 2)) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D2AC0-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy < ex) & (fy > fx + 2) & (ey == fx + (p - 2)) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D2AC1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx == fy + 2) & (ex == fy + (p - 2)) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D2AC1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy == fx + 2) & (ey == fx + (p - 2)) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D2AC2-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx == fy + 1) & (ex == fy + (p - 2)) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D2AC2-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy == fx + 1) & (ey == fx + (p - 2)) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D2ACD-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + (p - 2)) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D2ACD-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + (p - 2)) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D2AD-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex < fy + (p - 2)) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D2AD-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy == ex) & (ey < fx + (p - 2)) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D2B-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex < fy + (p - 2)) & (ex > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D2B-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey < fx + (p - 2)) & (ey > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D2BA-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex < fy + (p - 2)) & (ex == ey + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D2BA-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey < fx + (p - 2)) & (ey == ex + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D2BC0-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fy + (p - 2)) & (ex > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D2BC0-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fx + (p - 2)) & (ey > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D2BC1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fy + (p - 2)) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D2BC1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fx + (p - 2)) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D2C0-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx < ey + 1) & (fx > fy + 2) & (ex == fy + (p - 2)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D2C0-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy < ex + 1) & (fy > fx + 2) & (ey == fx + (p - 2)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D2C1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx == fy + 2) & (ex == fy + (p - 2)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D2C1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy == fx + 2) & (ey == fx + (p - 2)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D2C2-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx == fy + 1) & (ex == fy + (p - 2)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D2C2-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy == fx + 1) & (ey == fx + (p - 2)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D3A-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D3A-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D4-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == fy + (p - 1)) & (ex > ey + 2) & (fx > fy + 2) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D4-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == fx + (p - 1)) & (ey > ex + 2) & (fy > fx + 2) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D4A-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == fy + (p - 1)) & (ex == ey + 2) & (fx > fy + 2) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, ey - (p + p - 1), fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D4A-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == fx + (p - 1)) & (ey == ex + 2) & (fy > fx + 2) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, ex - (p + p - 1), fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D4AB-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == fy + (p - 1)) & (ex == ey + 2) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx),
            SELTZORange(sy, 0, 0, fy - 2, ey - (p + p - 1), fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D4AB-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == fx + (p - 1)) & (ey == ex + 2) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy),
            SELTZORange(sx, 0, 0, fx - 2, ex - (p + p - 1), fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D4AC-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == fy + (p - 1)) & (ex == ey + 2) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, ey - (p + p - 1), fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D4AC-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == fx + (p - 1)) & (ey == ex + 2) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, ex - (p + p - 1), fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D4B-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == fy + (p - 1)) & (ex > ey + 2) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D4B-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == fx + (p - 1)) & (ey > ex + 2) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D4D-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == fy + (p - 1)) & (fx == ey + 1) & (ex > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D4D-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == fx + (p - 1)) & (fy == ex + 1) & (ey > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D4DA-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == fy + (p - 1)) & (fx == ey + 1) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D4DA-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == fx + (p - 1)) & (fy == ex + 1) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D4E-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == fy + (p - 1)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D4E-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == fx + (p - 1)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D5-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (ex > ey + 3) & (fx > fy + 3) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fy + 2),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D5-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == fx + p) & (ey > ex + 3) & (fy > fx + 3) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fx + 2),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D5A-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (ex == ey + 3) & (fx > fy + 3) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fy + 2),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D5A-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == fx + p) & (ey == ex + 3) & (fy > fx + 3) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fx + 2),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D5B-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (ex > ey + 3) & (fx == fy + 3) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D5B-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == fx + p) & (ey > ex + 3) & (fy == fx + 3) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D5BA-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (ex == ey + 3) & (fx == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D5BA-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == fx + p) & (ey == ex + 3) & (fy == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D5D-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (fx == ey + 1) & (ex > ey + 3) & (fx > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fy + 2),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D5D-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == fx + p) & (fy == ex + 1) & (ey > ex + 3) & (fy > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fx + 2),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D5DA-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (fx == ey + 1) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 2),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D5DA-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == fx + p) & (fy == ex + 1) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 2),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D5DB-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (fx == ey + 1) & (fx == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D5DB-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == fx + p) & (fy == ex + 1) & (fy == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D5E-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 2),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D5E-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == fx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 2),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D60-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex > fy + p) & (fx < ey + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D60-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey > fx + p) & (fy < ex + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D61-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex > fy + p) & (fx < ey + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D61-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey > fx + p) & (fy < ex + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D6D0-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex > fy + p) & (fx == ey + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D6D0-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey > fx + p) & (fy == ex + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D6D1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex > fy + p) & (fx == ey + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D6D1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey > fx + p) & (fy == ex + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D6E0-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex > fy + p) & (fx == ey + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D6E0-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey > fx + p) & (fy == ex + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D6E1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx == ey + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D6E1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy == ex + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D6F0-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex > fy + p) & (fx > ey + 2) & (ex < ey + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D6F0-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey > fx + p) & (fy > ex + 2) & (ey < ex + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-D6F1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (fx > ey + 2) & (ex < ey + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-D6F1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (fy > ex + 2) & (ey < ex + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-DB0-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-DB0-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-TWO0-DB1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-TWO0-DB1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

end
