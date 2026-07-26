function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO1},
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

    checker("SELTZO-TwoSum-TWO1-TWO0-DA10-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fx - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-DA10-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fy - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-DA11-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, gx - 3, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-DA11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, gy - 3, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-DA11F-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy - 3, gx - 3), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-DA11F-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx - 3, gy - 3), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-DA12A-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, fx + 1, gy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-DA12A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, fy + 1, gx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-DA12-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, gy, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-DA12-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, gx, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-DA13-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx + 1, gx, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-DA13-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy + 1, gy, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-DA14-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 2, gx, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-DA14-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 2, gy, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-DA15-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fx - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-DA15-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fy - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-DA16-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 2 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fy - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-DA16-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 2 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fx - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-DA20-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fy, gx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-DA20-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fx, gy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-DA211-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fy + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-DA211-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fx + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-DA212-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fy + 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-DA212-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fx + 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx > ey + 2) & (ex > fy + p) & (ex < ey + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy > ex + 2) & (ey > fx + p) & (ey < ex + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D1F-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx > ey + 2) & (ex > fy + p) & (ex < ey + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D1F-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy > ex + 2) & (ey > fx + p) & (ey < ex + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D1A1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D1A1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D1A2-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey + 2) & (ex > fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D1A2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex + 2) & (ey > fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D1AF1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex > fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D1AF1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey > fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D1AF2-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey + 2) & (ex > fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D1AF2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex + 2) & (ey > fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D1C-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 2),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D1C-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 2),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D1D-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D1D-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D1E-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D1E-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx < ey) & (fx > fy) & (ex < fy + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy < ex) & (fy > fx) & (ey < fx + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2A0-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx > fy + 1) & (fx < ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2A0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy > fx + 1) & (fy < ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2A1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx == fy + 1) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx + 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2A1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy == fx + 1) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy + 1, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2B0-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx < ey) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2B0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy < ex) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx < ey) & (fx == fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy < ex) & (fy == fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2AB0-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx < ey) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2AB0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy < ex) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2AB1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx < ey) & (fx == fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2AB1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy < ex) & (fy == fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2C-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex < fy + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2C-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey < fx + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2D1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == fy + 1) & (ex > fy + 3) & (ex < fy + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2D1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == fx + 1) & (ey > fx + 3) & (ey < fx + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2D2-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == fy + 2) & (ex > fy + 3) & (ex < fy + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fy - 2, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2D2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == fx + 2) & (ey > fx + 3) & (ey < fx + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fx - 2, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2BC-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + (p - 1)) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2BC-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + (p - 1)) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2BCF-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + (p - 1)) & (ey > fy + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2BCF-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + (p - 1)) & (ex > fx + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2BCD-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ex - (p + 1), ex - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2BCD-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ey - (p + 1), ey - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2E-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2E-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2EF-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2EF-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2CE0-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + p) & (ey > fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2CE0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + p) & (ex > fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2CE0F-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + p) & (ey > fy + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2CE0F-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + p) & (ex > fx + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2CE1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + p) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fy, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2CE1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + p) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fx, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2F1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2F1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D2F2-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D2F2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D3-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex > fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, gx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D3-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey > fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, gy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D3F-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex > fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, gx),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D3F-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey > fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, gy),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D3A-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex > fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, gx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D3A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey > fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, gy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D3AF-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex > fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, gx),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D3AF-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey > fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, gy),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D3B-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex == fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fy + 2),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D3B-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey == fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fx + 2),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D3BF-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex == fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fy + 2),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D3BF-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey == fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fx + 2),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D3AB-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 2, fy + 2),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D3AB-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 2, fx + 2),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D3ABF-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 2, fy + 2),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D3ABF-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 2, fx + 2),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D4A-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D4A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D4AB-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D4AB-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D4AC-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D4AC-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D4AD0-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (fx > fy + 3) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 2),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D4AD0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (fy > fx + 3) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 2),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D4AD0F-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (fx > fy + 3) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 2),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D4AD0F-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (fy > fx + 3) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 2),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-D4AD1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (fx == fy + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-D4AD1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (fy == fx + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-DB20-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, gx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-DB20-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, gy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-DB21-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, gx),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-DB21-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, gy),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

end
