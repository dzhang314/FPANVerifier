function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
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

    checker("SELTZO-TwoSum-R0R1-TWO0-DA10-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx > fy) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, fy, ex - p), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-DA10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy > fx) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, fx, ey - p), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-DA11-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx > fy) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, fx + 1, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-DA11-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy > fx) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, fy + 1, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-DA12-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 2 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fy - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-DA12-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 2 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fx - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-DA13-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, ey - p, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-DA13-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, ex - p, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-DA14-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 2, fx - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-DA14-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 2, fy - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-DA15-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx + 1, fy - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-DA15-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy + 1, fx - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-DA20-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx + 1 < ey) & (fx + 1 > fy) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx + 1, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-DA20-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy + 1 < ex) & (fy + 1 > fx) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy + 1, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-DA21-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx + 1 == fy) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx + 2, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-DA21-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy + 1 == fx) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy + 2, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-DA22-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fy, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-DA22-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fx, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-DA23-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx + 1 < ey) & (fx + 1 > fy) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx + 1, ex - (p - 2)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-DA23-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy + 1 < ex) & (fy + 1 > fx) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy + 1, ey - (p - 2)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-DA24-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx + 1 == fy) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx + 2, fx + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-DA24-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy + 1 == fx) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy + 2, fy + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-DA25-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx + 1 < ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx + 1, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-DA25-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy + 1 < ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy + 1, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-DA26-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx + 1 == ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-DA26-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy + 1 == ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-DA27-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx == ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fy, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-DA27-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy == ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fx, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D1A-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex + 1 == fy) & (fx + p > ey) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 1, ey, fy + 1, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D1A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey + 1 == fx) & (fy + p > ex) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 1, ex, fx + 1, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D1B-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex + 1 < fy) & (fx + p == ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey, fy, fx + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D1B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey + 1 < fx) & (fy + p == ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex, fx, fy + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D1AB-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx + p == ey) & (fx + 3 < fy) & (ex < fy + 1) & (ex + 2 > fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey, fy + 1, fx + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D1AB-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy + p == ex) & (fy + 3 < fx) & (ey < fx + 1) & (ey + 2 > fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex, fx + 1, fy + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D1AC1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex + 1 == fy) & (fx + (p + 1) == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sy, 1, 0, fx, fx - 2, fx - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D1AC1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey + 1 == fx) & (fy + (p + 1) == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sx, 1, 0, fy, fy - 2, fy - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D1AC2-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex + 1 == fy) & (fx + (p + 2) == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sy, 0, 0, fx, fx - p, fx))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D1AC2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey + 1 == fx) & (fy + (p + 2) == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sx, 0, 0, fy, fy - p, fy))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D1BD0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx + p == ey) & (ex == fx + 2) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey, fy, ex + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D1BD0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy + p == ex) & (ey == fy + 2) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex, fx, ey + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D1BD1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx + p == ey) & (ex == fx + 2) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey, fy, fy + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D1BD1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy + p == ex) & (ey == fy + 2) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex, fx, fx + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D2B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == fy) & (fx + (p + 1) == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 1, ey, fy, fy - 1),
            SELTZORange(~sy, 0, 0, fx, fx - p, fx))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D2B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == fx) & (fy + (p + 1) == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 1, ex, fx, fx - 1),
            SELTZORange(~sx, 0, 0, fy, fy - p, fy))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D3A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (fx > ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D3A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == fx + p) & (fy > ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D3A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (fx == ey + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D3A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == fx + p) & (fy == ex + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D3B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (fx == ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D3B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == fx + p) & (fy == ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D3B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (fx == ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D3B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == fx + p) & (fy == ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D3C0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (fx + 1 == ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx, fx + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D3C0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == fx + p) & (fy + 1 == ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy, fy + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D3C1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (fx + 1 == ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D3C1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == fx + p) & (fy + 1 == ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D3D0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (fx + 1 < ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D3D0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == fx + p) & (fy + 1 < ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D3D1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (fx + 1 < ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D3D1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == fx + p) & (fy + 1 < ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D4E-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx + p < ey) & (ex + (p - 1) > ey) & (ex > fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 1, ey, ex, fy - 1),
            SELTZORange(~sy, 1, 0, fx, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D4E-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy + p < ex) & (ey + (p - 1) > ex) & (ey > fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 1, ex, ey, fx - 1),
            SELTZORange(~sx, 1, 0, fy, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D10A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx + 1 == ey) & (ex > ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D10A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy + 1 == ex) & (ey > ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D10A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx + 1 == ey) & (ex > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx, ex - (p - 2)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D10A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy + 1 == ex) & (ey > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy, ey - (p - 2)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D10A2-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx + 1 == ey) & (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D10A2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy + 1 == ex) & (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D10B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx + 1 < ey) & (fx + 2 > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D10B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy + 1 < ex) & (fy + 2 > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D10B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx + 1 < ey) & (ex == fy + (p - 2)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 2)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D10B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy + 1 < ex) & (ey == fx + (p - 2)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 2)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D10B2-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (ex == fy + (p - 2)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 3)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D10B2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (ey == fx + (p - 2)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 3)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D10B3-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx + 1 < ey) & (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D10B3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy + 1 < ex) & (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D13A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == fy + (p - 2)) & (fx > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D13A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == fx + (p - 2)) & (fy > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D13A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == fy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D13A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == fx + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D13B-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fy, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D13B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fx, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D13AB0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D13AB0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D13AB1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fy, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D13AB1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fx, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D14A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex > fy + p) & (ex < fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D14A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey > fx + p) & (ey < fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D14A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex > fy + p) & (ex < fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D14A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey > fx + p) & (ey < fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D14AB0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D14AB0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D14AB1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D14AB1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D15-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex > fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D15-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey > fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D15A-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex > fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D15A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey > fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D15B-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex == fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D15B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey == fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D15C-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex > fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ex - p, ex - (p - 1)),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D15C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey > fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ey - p, ey - (p - 1)),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D15AB-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex == fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D15AB-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey == fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D15AC-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex > fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ex - p, ex - (p - 1)),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D15AC-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey > fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ey - p, ey - (p - 1)),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D15BC-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ex - (p + 1), ex - 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D15BC-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ey - (p + 1), ey - 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D15ABC-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ex - (p + 1), ex - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D15ABC-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ey - (p + 1), ey - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D16A-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex < fy + 1) & (ex + 2 > fy) & (fx + 2 < fy) & (fx + p > ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 1, ey, ey - 2, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D16A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey < fx + 1) & (ey + 2 > fx) & (fy + 2 < fx) & (fy + p > ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 1, ex, ex - 2, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D16AB-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex < fy + 1) & (ex + 2 > fy) & (fx + p == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ey, ey - 2, fx + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D16AB-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey < fx + 1) & (ey + 2 > fx) & (fy + p == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 0, ex, ex - 2, fy + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D16BC0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx + p == ey) & (ex + 1 < ey) & (ex > gx + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey, ex, gx + 3),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D16BC0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy + p == ex) & (ey + 1 < ex) & (ey > gy + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex, ey, gy + 3),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D16BC1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx + p == ey) & (ex == fy + 1) & (ey == fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey, fy + 1, ex + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D16BC1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy + p == ex) & (ey == fx + 1) & (ex == fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex, fx + 1, ey + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-D16BC2-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx + p == ey) & (ex < fy + 1) & (ey == fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey, fy + 1, ex),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-D16BC2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy + p == ex) & (ey < fx + 1) & (ex == fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex, fx + 1, ey),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-DB10-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + (p - 1)) & (fx > ey + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-DB10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + (p - 1)) & (fy > ex + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-DB20-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (fx > ey + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-DB20-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (fy > ex + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-DB21-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (fx > ey + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-DB21-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (fy > ex + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

end
