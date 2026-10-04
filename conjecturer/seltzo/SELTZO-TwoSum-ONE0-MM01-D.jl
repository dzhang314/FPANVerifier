function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
    ::Val{MM01},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ONE0-MM01-DA0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx > fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-DA0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy > fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-DA1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx > fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-DA1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy > fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-DA2-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-DA2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-DA3-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-DA3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-DA4-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-DA4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-DA5-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-DA5-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-DA6-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-DA6-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D1A-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex > ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D1A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey > ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D2-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx < ey) & (fx > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy < ex) & (fy > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D2A0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex > ey + 1) & (fx == fy) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D2A0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey > ex + 1) & (fy == fx) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D2A1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex > ey + 1) & (fx == fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D2A1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey > ex + 1) & (fy == fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D2B-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D2B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D2D0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx > fy) & (fx < ey + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D2D0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy > fx) & (fy < ex + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D2BD-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx > fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D2BD-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy > fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D2D1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D2D1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D2E-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx < ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D2E-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy < ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D2BE-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D2BE-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey == ex + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D2F-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx < ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx),
            SELTZORange(sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D2F-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy < ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy),
            SELTZORange(sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D3-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx < ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy < ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D3A-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D3A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D4C0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D4C0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D4C1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D4C1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D5-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex > fy + p) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D5-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey > fx + p) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D5B0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D5B0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D5B1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D5B1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D5C0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex == ey + p) & (fx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D5C0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey == ex + p) & (fy > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-D5C1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex == ey + p) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-D5C1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey == ex + p) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
