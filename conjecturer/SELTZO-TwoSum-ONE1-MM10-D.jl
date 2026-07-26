function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
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

    checker("SELTZO-TwoSum-ONE1-MM10-DA00-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx > fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx - 1, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM10-DA00-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy > fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy - 1, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM10-DA01-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx > fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM10-DA01-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy > fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM10-DA10-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fy - 1, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM10-DA10-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fx - 1, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM10-DA11-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM10-DA11-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM10-DA20-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fy - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM10-DA20-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fx - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM10-DA21-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fy - 3, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM10-DA21-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fx - 3, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM10-DA3-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fy - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM10-DA3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fx - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM10-DA40-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 < fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fy, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM10-DA40-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 < fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fx, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM10-DA41-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 < fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 2, fy - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM10-DA41-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 < fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 2, fx - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx < ey) & (fx > fy) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy < ex) & (fy > fx) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D1A-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex > ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D1A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey > ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D1B-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex > ey + 2) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D1B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey > ex + 2) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D1C0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, ey - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D1C0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, ex - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D1C1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, ey - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D1C1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 2) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, ex - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D1C2-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D1C2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 2) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D1D-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (fx == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fy, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D1D-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (fy == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fx, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D2-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx < ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy < ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D2A-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx == ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fy, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D2A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy == ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fx, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D2B-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx < ey) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D2B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy < ex) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D2AB-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx == ey) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fy - 1, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D2AB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy == ex) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fx - 1, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D3-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx < ey) & (ex > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fx),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy < ex) & (ey > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fy),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D3A-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx == ey) & (ex > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ex - (p + 1), ex - 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D3A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy == ex) & (ey > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ey - (p + 1), ey - 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D3B-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx < ey) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D3B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy < ex) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D3AB-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx == ey) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ex - (p + 1), ex - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D3AB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy == ex) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ey - (p + 1), ey - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D4-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p + 1)) & (fx < ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p + 1)) & (fy < ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D4A-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p + 1)) & (fx == ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ex - (p + 1), ex - 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D4A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p + 1)) & (fy == ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ey - (p + 1), ey - 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D4B-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p + 1)) & (fx < ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fx),
            SELTZORange(~sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D4B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p + 1)) & (fy < ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fy),
            SELTZORange(~sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D4AB-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p + 1)) & (fx == ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ex - (p + 1), ex - 1),
            SELTZORange(~sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D4AB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p + 1)) & (fy == ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ey - (p + 1), ey - 1),
            SELTZORange(~sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D5-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D5-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D5A-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D5A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D5B-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (fx == ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D5B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (fy == ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D6A-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D6A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D6B0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D6B0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D6B1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 2, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D6B1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 2, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D6C0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, ey),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D6C0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, ex),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D6C1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 2, ey),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D6C1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 2, ex),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D6D0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, ey),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D6D0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, ex),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D6D1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + p) & (ex > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 2, ey),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D6D1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + p) & (ey > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 2, ex),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D6D2-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + p) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 2, ey),
            SELTZORange(~sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D6D2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + p) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 2, ex),
            SELTZORange(~sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-D6E-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (fx > ey) & (ex < ey + (p - 1)) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-D6E-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (fy > ex) & (ey < ex + (p - 1)) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-DB1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-DB1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-DB20-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-DB20-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-DB21-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-DB21-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

end
