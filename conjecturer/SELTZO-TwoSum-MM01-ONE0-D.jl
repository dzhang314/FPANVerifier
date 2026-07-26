function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM01},
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

    checker("SELTZO-TwoSum-MM01-ONE0-DE0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 2 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy - 1, fx, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DE0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 2 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx - 1, fy, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DE1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy - 1, fy - 3, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DE1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx - 1, fx - 3, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DE20-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 1 == fy) & (ey + 1 < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy - 2, ey - (p - 1), ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DE20-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 1 == fx) & (ex + 1 < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx - 2, ex - (p - 1), ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DE21-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 1 == fy) & (ey + 1 == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy - 2, ey - p, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DE21-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 1 == fx) & (ex + 1 == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx - 2, ex - p, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DE30-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fy - 2, ey - p, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DE30-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fx - 2, ex - p, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DE31-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy - 2, fy - (p + 2), fy - 2), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DE31-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx - 2, fx - (p + 2), fx - 2), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DE4-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fy, ey - p, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DE4-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fx, ex - p, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DE50-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fx, fx - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DE50-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fy, fy - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DE51-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fx, fx - 3, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DE51-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fy, fy - 3, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DA0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx > fy + 1) & (ex > fx + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DA0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy > fx + 1) & (ey > fy + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DA0D0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx > fy + 2) & (ex > fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DA0D0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy > fx + 2) & (ey > fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DA0D1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx == fy + 2) & (ex > fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DA0D1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy == fx + 2) & (ey > fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DA1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx > fy + 1) & (ex == fx + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx - 1, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DA1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy > fx + 1) & (ey == fy + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy - 1, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DA1D0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx > fy + 2) & (ex == fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DA1D0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy > fx + 2) & (ey == fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DA2-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx - 1, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DA2-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy - 1, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DA3-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx - 2, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DA3-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy - 2, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DA4-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DA4-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DA5-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DA5-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx < ey) & (fx > fy + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy < ex) & (fy > fx + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D1A-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx < ey) & (fx > fy + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D1A-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy < ex) & (fy > fx + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D1B-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D1B-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D1AB-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D1AB-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D1C-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D1C-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D1AC-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D1AC-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D1AD-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D1AD-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D1E0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx < ey + 1) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D1E0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy < ex + 1) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D1E1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx == fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D1E1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy == fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D1AE0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx < ey) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D1AE0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy < ex) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D1AE1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx < ey) & (fx == fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D1AE1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy < ex) & (fy == fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D1ADE0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx == ey) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D1ADE0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy == ex) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D2A-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex > ey + 3) & (fx == ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D2A-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey > ex + 3) & (fy == ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D2AC-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 3) & (fx == ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D2AC-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 3) & (fy == ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D2E-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D2E-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D2AE-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex > ey + 3) & (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D2AE-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey > ex + 3) & (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D2ACE-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 3) & (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D2ACE-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 3) & (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D3-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx < ey + 1) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D3-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy < ex + 1) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D3D-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx < ey + 1) & (ex > fy + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D3D-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy < ex + 1) & (ey > fx + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D3C0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx < ey + 1) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D3C0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy < ex + 1) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D3C1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx < ey + 1) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fy + 3),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D3C1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy < ex + 1) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fx + 3),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D3ACD0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx < ey) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D3ACD0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy < ex) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D3ACD1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx < ey) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 3),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D3ACD1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy < ex) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 3),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D3ABCD-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D3ABCD-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D4-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx > ey + 2) & (ex > fy + p) & (ex < ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D4-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy > ex + 2) & (ey > fx + p) & (ey < ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D4E-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx > ey + 2) & (ex < ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D4E-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy > ex + 2) & (ey < ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D4A-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D4A-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D4AE-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D4AE-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D4B-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D4B-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D4BE-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > ey + 3) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D4BE-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > ex + 3) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D4BCE-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex == ey + 3) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D4BCE-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey == ex + 3) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D4D-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D4D-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D4BD0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > ey + 3) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D4BD0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > ex + 3) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D4BD1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > ey + 3) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D4BD1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > ex + 3) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-D4BCD-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex == ey + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-D4BCD-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey == ex + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DB0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DB0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-DB1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-DB1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
