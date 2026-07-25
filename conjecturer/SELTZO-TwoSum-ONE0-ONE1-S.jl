function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
    ::Val{ONE1},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ONE0-ONE1-SE0-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx < fy) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-SE0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex) & (fy < fx) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-SE1-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 1 < fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx + 1),
            SELTZORange(sy, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-SE1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 1 < fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy + 1),
            SELTZORange(sx, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-SE2-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, ex),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-SE2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, ey),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-SE4-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 1 == fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, ex),
            SELTZORange(sy, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-SE4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 1 == fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, ey),
            SELTZORange(sx, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S1-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex > fy + p) & (fx > ey) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey > fx + p) & (fy > ex) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S1A-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (fx > ey + 1) & (ex < ey + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, ey),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S1A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == fx + p) & (fy > ex + 1) & (ey < ex + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, ex),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S1C-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, ey),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S1C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, ex),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S2-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex + 1 > ey) & (fx < ey) & (fx > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey + 1 > ex) & (fy < ex) & (fy > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S2A-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx < ey) & (fx > fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S2A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy < ex) & (fy > fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S2B-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx < ey) & (fx == fy) & (ex > ey) & (ex < ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S2B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy < ex) & (fy == fx) & (ey > ex) & (ey < ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S2C-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx < fy) & (ex > ey) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S2C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy < fx) & (ey > ex) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S2D-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx + 1 < fy) & (ex > ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S2D-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy + 1 < fx) & (ey > ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S2E-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx + 1 == fy) & (ex > ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S2E-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy + 1 == fx) & (ey > ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S3-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S4-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fy, ex + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fx, ey + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S4A-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S4A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy == ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S4B-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S4B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S4C-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S4C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S4D-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S4D-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S5-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S5-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S7-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S7-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S7A-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S7A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S9-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx < ey) & (ex > ey) & (ex == fy + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S9-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy < ex) & (ey > ex) & (ey == fx + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S10-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == fx + (p - 2)) & (ex == fy + (p - 1)) & (ex > ey) & (ex < ey + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S10-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == fy + (p - 2)) & (ey == fx + (p - 1)) & (ey > ex) & (ey < ex + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S11-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx < ey) & (ex > fy + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 1, 0, ex - p, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S11-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy < ex) & (ey > fx + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 1, 0, ey - p, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S11A-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx < ey) & (ex > fy + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 1, 0, ex - p, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S11A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy < ex) & (ey > fx + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 1, 0, ey - p, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S11B-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx < ey) & (ex == fy + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S11B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy < ex) & (ey == fx + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-S11AB-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (fx < ey) & (ex == fy + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-S11AB-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (fy < ex) & (ey == fx + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-SB1-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-SB1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-SB2-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-SB2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
