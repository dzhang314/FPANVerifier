function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO0},
    ::Val{R1R0},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-TWO0-R1R0-SE0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx < fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fy + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-SE0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy < fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fx + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-SE1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx > fy + 2) & (ey < fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-SE1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy > fx + 2) & (ex < fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-SE2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx == fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx + 1, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-SE2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy == fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy + 1, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-SE3-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-SE3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-SE4-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx > fy + 3) & (ey == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx, ex - (p - 3)),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-SE4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy > fx + 3) & (ex == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy, ey - (p - 3)),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-SE5-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx == fy + 3) & (ey == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-SE5-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy == fx + 3) & (ex == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-SE6-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fy + 1, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-SE6-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fx + 1, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-SE7-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx + 1, fx + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-SE7-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy + 1, fy + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-SE8-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx == fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx + 1, fx),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-SE8-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy == fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy + 1, fy),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx + 1 < ey) & (fx < fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex) & (fy + 1 < ex) & (fy < fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S1A-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx + 1 == ey) & (fx == fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S1A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex) & (fy + 1 == ex) & (fy == fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S1B0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx + 1 < ey) & (fx < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S1B0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex) & (fy + 1 < ex) & (fy < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S1B1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx + 1 < ey) & (fx == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S1B1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex) & (fy + 1 < ex) & (fy == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S1B2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx + 1 < ey) & (fx == fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S1B2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex) & (fy + 1 < ex) & (fy == fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S1AB-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx + 1 == ey) & (fx == fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fx),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S1AB-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex) & (fy + 1 == ex) & (fy == fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fy),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx < ey) & (fx > fy + 2) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex) & (fy < ex) & (fy > fx + 2) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S2A-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx < ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S2A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex) & (fy < ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S2C-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx > fy + 2) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S2C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex) & (fy > fx + 2) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S2AC-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S2AC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S2B0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx < ey) & (fx > fy + 3) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ex - (p - 3)),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S2B0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex) & (fy < ex) & (fy > fx + 3) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ey - (p - 3)),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S2B1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx < ey) & (fx == fy + 3) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S2B1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex) & (fy < ex) & (fy == fx + 3) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S2BC0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx > fy + 3) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 2, ex - (p - 3)),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S2BC0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex) & (fy > fx + 3) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 2, ey - (p - 3)),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S2BC1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx == fy + 3) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S2BC1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex) & (fy == fx + 3) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S3-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx < ey) & (ex > fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 1, 0, ex - p, fy, fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy < ex) & (ey > fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 1, 0, ey - p, fx, fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S3A-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex > fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, ey - 1),
            SELTZORange(sy, 1, 0, ex - p, fy, fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S3A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex) & (ey > fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, ex - 1),
            SELTZORange(sx, 1, 0, ey - p, fx, fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S3B-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx < ey) & (fx > gy + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, ex - p, fy, fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S3B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex) & (fy < ex) & (fy > gx + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, ey - p, fx, fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S3AB-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx > gy + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 1, 0, ex - p, fy, fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S3AB-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex) & (fy > gx + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 1, 0, ey - p, fx, fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S3C-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx < ey) & (ex == fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S3C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy < ex) & (ey == fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S3AC-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex == fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, ey - 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S3AC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex) & (ey == fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, ex - 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S3BC-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx < ey) & (fx == gy + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S3BC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex) & (fy < ex) & (fy == gx + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S3ABC-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx == gy + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S3ABC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex) & (fy == gx + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S3D-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx < ey) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S3D-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy < ex) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S3AD-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 2, ey - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S3AD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 2, ex - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S3BD-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx < ey) & (fx == fy + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S3BD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy < ex) & (fy == fx + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S3ABD-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx == fy + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S3ABD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex) & (fy == fx + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S4-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx > ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy > ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S4A-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S4A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S4B-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S4B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S4AB0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S4AB0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S4AB1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S4AB1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S5-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx > ey + 2) & (ex > fy + (p + 1)) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S5-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy > ex + 2) & (ey > fx + (p + 1)) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S5A-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey + 2) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S5A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex + 2) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S5B-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx > ey + 1) & (ex == fy + (p + 1)) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 3),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S5B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy > ex + 1) & (ey == fx + (p + 1)) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 3),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S5BD-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx > ey + 1) & (ex == fy + (p + 1)) & (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S5BD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy > ex + 1) & (ey == fx + (p + 1)) & (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S5C-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, ey),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S5C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, ex),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S5BC0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex == fy + (p + 1)) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 3),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S5BC0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey == fx + (p + 1)) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 3),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-S5BC1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex == fy + (p + 1)) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-S5BC1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey == fx + (p + 1)) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
