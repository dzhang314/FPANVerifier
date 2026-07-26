function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM10},
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

    checker("SELTZO-TwoSum-MM10-TWO0-DA10-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fx - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DA10-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fy - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DA11-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DA11-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DA12-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex - 1, fx - 3, fx - 2), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DA12-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey - 1, fy - 3, fy - 2), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DA13-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, fy - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DA13-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, fx - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DA14-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, fx - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DA14-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, fy - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DA15-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy + 1, fx - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DA15-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx + 1, fy - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DA16-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fx - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DA16-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fy - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DA17-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 2 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fy - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DA17-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 2 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fx - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DA20-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx > fy + 1) & (ex == ey + 2) & (ex > fx + 2) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx, ey - (p - 3)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DA20-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy > fx + 1) & (ey == ex + 2) & (ey > fy + 2) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy, ex - (p - 3)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DA21-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx + 1 < fy) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fy, ey - (p - 3)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DA21-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy + 1 < fx) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fx, ex - (p - 3)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DA22-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx + 2 > fy) & (fx < fy + 1) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fy + 1, ey - (p - 3)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DA22-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy + 2 > fx) & (fy < fx + 1) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fx + 1, ex - (p - 3)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DA23-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == fy + 1) & (ex == ey + 2) & (ex > fx + 3) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx + 1, ey - (p - 3)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DA23-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == fx + 1) & (ey == ex + 2) & (ey > fy + 3) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy + 1, ex - (p - 3)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DA27-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx > fy + 1) & (ex == ey + 2) & (ey == gy + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DA27-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy > fx + 1) & (ey == ex + 2) & (ex == gx + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DA28-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == fy + 1) & (ex == ey + 2) & (ey == gy + (p - 3)) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DA28-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == fx + 1) & (ey == ex + 2) & (ex == gx + (p - 3)) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DA212-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (ey == fy + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DA212-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (ex == fx + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DA213-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx > fy + 2) & (ex == ey + 2) & (ey == fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DA213-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy > fx + 2) & (ey == ex + 2) & (ex == fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx + 2 > fy) & (fx + 1 < ey) & (ex < fy + (p - 2)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy + 2 > fx) & (fy + 1 < ex) & (ey < fx + (p - 2)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1A0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex < fy + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1A0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex) & (ey < fx + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1A1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == fy + 2) & (ex < fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fy - 1, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == fx + 2) & (ey < fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fx - 1, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1B0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex == fy + (p - 2)) & (ex > ey + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1B0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy < ex) & (ey == fx + (p - 2)) & (ey > ex + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1B10-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (ex == fy + (p - 2)) & (ex > ey + 2) & (ex == fx + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1B10-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (ey == fx + (p - 2)) & (ey > ex + 2) & (ey == fy + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1B11-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (ex == fy + (p - 2)) & (ex > ey + 2) & (ex == fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1B11-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (ey == fx + (p - 2)) & (ey > ex + 2) & (ey == fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1AB0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1AB0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1AB1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == fy + 2) & (ex == fy + (p - 2)) & (ex > ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fy - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1AB1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == fx + 2) & (ey == fx + (p - 2)) & (ey > ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fx - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1C-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex == fy + (p - 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1C-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy < ex) & (ey == fx + (p - 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1AC-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 2, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1AC-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 2, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1D0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx - 1),
            SELTZORange(sy, 1, 0, ex - (p + 2), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1D0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy < ex) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy - 1),
            SELTZORange(sx, 1, 0, ey - (p + 2), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1D1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1D1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy < ex) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1AD0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, fx - 1),
            SELTZORange(sy, 1, 0, ex - (p + 2), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1AD0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, fy - 1),
            SELTZORange(sx, 1, 0, ey - (p + 2), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1AD1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1AD1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1E0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex == fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fx - 1),
            SELTZORange(sy, 1, 0, ex - (p + 3), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1E0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy < ex) & (ey == fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fy - 1),
            SELTZORange(sx, 1, 0, ey - (p + 3), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1E1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex == fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1E1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy < ex) & (ey == fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1AE0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 1, fx - 1),
            SELTZORange(sy, 1, 0, ex - (p + 3), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1AE0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 1, fy - 1),
            SELTZORange(sx, 1, 0, ey - (p + 3), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1AE1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 1, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1AE1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 1, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1F0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx + 1 == ey) & (ex < fy + (p - 2)) & (ex > ey + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1F0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy + 1 == ex) & (ey < fx + (p - 2)) & (ey > ex + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D1F1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx + 1 == ey) & (ex < fy + (p - 2)) & (ex > ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D1F1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy + 1 == ex) & (ey < fx + (p - 2)) & (ey > ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D2-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx > ey + 2) & (ex > fy + p) & (ex < ey + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D2-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy > ex + 2) & (ey > fx + p) & (ey < ex + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D2A0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey + 2) & (ex > fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D2A0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex + 2) & (ey > fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D2A1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 1, ey),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D2A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 1, ex),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D2B-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx > ey + 2) & (ex > fy + p) & (ex < ey + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D2B-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy > ex + 2) & (ey > fx + p) & (ey < ex + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D2AB0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey + 2) & (ex > fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D2AB0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex + 2) & (ey > fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 3, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D2AB1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex > fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 1, ey),
            SELTZORange(~sy, 1, 0, fy, fy - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D2AB1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey > fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 1, ex),
            SELTZORange(~sx, 1, 0, fx, fx - 3, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D2C0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx > ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, ex - (p + 2), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D2C0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy > ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, ey - (p + 2), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D2C1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey + 2) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(sy, 1, 0, ex - (p + 2), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D2C1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex + 2) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(sx, 1, 0, ey - (p + 2), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D2C20-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, ey),
            SELTZORange(sy, 1, 0, ex - (p + 2), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D2C20-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, ex),
            SELTZORange(sx, 1, 0, ey - (p + 2), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D2C21-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, ey),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D2C21-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, ex),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D2D0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D2D0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D2D1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fy + 1),
            SELTZORange(sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D2D1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fx + 1),
            SELTZORange(sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D2E0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D2E0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D2E1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D2E1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D2F-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D2F-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D3-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex > fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D3-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy < ex) & (ey > fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D3A-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex > fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, ex - (p - 1)),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D3A-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex) & (ey > fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, ey - (p - 1)),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D3B-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex > fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 1, 0, fy, fy - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D3B-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy < ex) & (ey > fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 1, 0, fx, fx - 3, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-D3AB-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex > fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, ex - (p - 1)),
            SELTZORange(~sy, 1, 0, fy, fy - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-D3AB-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (fy == ex) & (ey > fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, ey - (p - 1)),
            SELTZORange(~sx, 1, 0, fx, fx - 3, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DB0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ex < fx + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DB0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ey < fy + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DB1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ex < fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DB1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ey < fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 3, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DB2-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ex == fx + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DB2-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ey == fy + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO0-DB3-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ex == fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO0-DB3-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ey == fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 3, ex - (p - 1)))
    end

end
