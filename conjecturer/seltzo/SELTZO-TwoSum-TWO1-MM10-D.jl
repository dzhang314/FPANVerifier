function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO1},
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

    checker("SELTZO-TwoSum-TWO1-MM10-DE-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM10-DE-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM10-DA0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, ey - (p - 1), ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM10-DA0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, ex - (p - 1), ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM10-DA10-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fy, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM10-DA10-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fx, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM10-DA11-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM10-DA11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM10-DA2-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (fx < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, ex - 3, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-DA2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 2) & (fy < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, ey - 3, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-DA3-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM10-DA3-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM10-DA40-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 < fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM10-DA40-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 < fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM10-DA41-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 < fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM10-DA41-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 < fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM10-DA50-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx > fy + 1) & (ex > fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM10-DA50-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy > fx + 1) & (ey > fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM10-DA51-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx > fy + 1) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM10-DA51-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy > fx + 1) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM10-DA60-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ey > fy + 2) & (ey < fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ex - 3, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM10-DA60-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ex > fx + 2) & (ex < fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ey - 3, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM10-DA61-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ey == fy + (p - 3)) & (ex == fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ex - 3, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM10-DA61-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ex == fx + (p - 3)) & (ey == fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ey - 3, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex < ey + (p - 1)) & (fx > ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey < ex + (p - 1)) & (fy > ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D1A-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D1A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D1B-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex > fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D1B-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey > fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D1AB0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + p) & (ex > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D1AB0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + p) & (ey > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D1AB1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + p) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(~sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D1AB1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + p) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(~sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D1BC-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D1BC-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D20-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (ex < fy + (p - 1)) & (fx > fy + 1) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D20-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (ey < fx + (p - 1)) & (fy > fx + 1) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D2A-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx + 1 == ey) & (fx > fy + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D2A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy + 1 == ex) & (fy > fx + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D21-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D21-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D2B0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx + 1 < ey) & (fx > fy + 1) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D2B0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy + 1 < ex) & (fy > fx + 1) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D2B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx + 1 < ey) & (fx > fy + 1) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D2B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy + 1 < ex) & (fy > fx + 1) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D2AB0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx + 1 == ey) & (fx > fy + 1) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D2AB0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy + 1 == ex) & (fy > fx + 1) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D2AB1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx + 1 == ey) & (fx > fy + 1) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D2AB1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy + 1 == ex) & (fy > fx + 1) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D3D1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx == ey) & (fx > fy + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D3D1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy == ex) & (fy > fx + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D3D2-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (fx > fy + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D3D2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy == ex + 1) & (fy > fx + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D3AD1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx == ey) & (ex < fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 3, fx - 3),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D3AD1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy == ex) & (ey < fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 3, fy - 3),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D3BD1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx == ey) & (fx > fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 2, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D3BD1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy == ex) & (fy > fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 2, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D3BD2-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (fx > fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D3BD2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy == ex + 1) & (fy > fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D3ABD1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 3, fx - 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D3ABD1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 3, fy - 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D3C0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 2, ey - 1),
            SELTZORange(sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D3C0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 2, ex - 1),
            SELTZORange(sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D3C1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 2, ey - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D3C1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 2, ex - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D4A-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D4A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D4B-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D4B-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D5-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D5-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D5A-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 == fy) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D5A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 == fx) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D6-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D6-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D6A0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (ex == fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p + 2), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D6A0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (ey == fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p + 2), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D6A1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (ex == fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fx - 1),
            SELTZORange(~sy, 1, 0, ex - (p + 2), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D6A1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (ey == fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fy - 1),
            SELTZORange(~sx, 1, 0, ey - (p + 2), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D6B0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (ex == fy + p) & (ex > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fx - 1),
            SELTZORange(sy, 1, 0, ex - (p + 2), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D6B0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (ey == fx + p) & (ey > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fy - 1),
            SELTZORange(sx, 1, 0, ey - (p + 2), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D6B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (ex == fy + p) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D6B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (ey == fx + p) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D6C-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D6C-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D6AC0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex == fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p + 2), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D6AC0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey == fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p + 2), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D6AC1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex == fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 1, fx - 1),
            SELTZORange(~sy, 1, 0, ex - (p + 2), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D6AC1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey == fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 1, fy - 1),
            SELTZORange(~sx, 1, 0, ey - (p + 2), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D6BC0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex == fy + p) & (ex > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 1, fx - 1),
            SELTZORange(sy, 1, 0, ex - (p + 2), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D6BC0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey == fx + p) & (ey > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 1, fy - 1),
            SELTZORange(sx, 1, 0, ey - (p + 2), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D6BC1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex == fy + p) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 1, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D6BC1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey == fx + p) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 1, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D6D-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, ey - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D6D-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, ex - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D6BD0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + p) & (ex > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 2, ey - 1),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D6BD0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + p) & (ey > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 2, ex - 1),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-D6BD1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + p) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 2, ey - 1),
            SELTZORange(~sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-D6BD1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + p) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 2, ex - 1),
            SELTZORange(~sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-DB1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-DB1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-DB20-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-DB20-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-DB21-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-DB21-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

end
