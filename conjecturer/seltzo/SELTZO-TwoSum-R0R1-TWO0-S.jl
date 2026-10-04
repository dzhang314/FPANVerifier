function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
    ::Val{TWO0},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R0R1-TWO0-SE0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx + 1 > fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, ex - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SE0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex) & (fy + 1 > fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, ey - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SE1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx > fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, ex - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SE1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex) & (fy > fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, ey - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SE2-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx + 1 == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ex - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SE2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex) & (fy + 1 == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ey - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SE3-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ex - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SE3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ey - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SE4-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx + 2 < fy) & (ex < fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ex - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SE4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex) & (fy + 2 < fx) & (ey < fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ey - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SE5-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey) & (ex == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ex - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SE5-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex) & (ey == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ey - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SE6-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx + 1 == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ex - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SE6-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex) & (fy + 1 == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ey - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SE7-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, ex - 1, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SE7-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex) & (fy == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, ey - 1, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SA10-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + (p - 2) > ey) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy, ey - (p - 3)),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SA10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + (p - 2) > ex) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx, ex - (p - 3)),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SA11-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 1 == fy) & (ex > fx + 3) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SA11-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 1 == fx) & (ey > fy + 3) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SA12-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 1 == fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SA12-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 1 == fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SA13-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 1 == fy) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SA13-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 1 == fx) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SA20-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex + 1 == ey) & (fx + 1 > fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 2, ex, fy - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SA20-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey + 1 == ex) & (fy + 1 > fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 2, ey, fx - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SA21-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex + 1 == ey) & (fx > fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 2, ex, fy + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SA21-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey + 1 == ex) & (fy > fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 2, ey, fx + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SA22-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex + 1 == ey) & (fx == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 2, ex, ex),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SA22-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey + 1 == ex) & (fy == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 2, ey, ey),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SA230-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex + 1 == ey) & (fx + 1 == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 2, ex - 1, fy - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SA230-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey + 1 == ex) & (fy + 1 == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 2, ey - 1, fx - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SA231-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex + 1 == ey) & (fx + 1 == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 2, ex - 1, fy),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SA231-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey + 1 == ex) & (fy + 1 == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 2, ey - 1, fx),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SA250-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex + 1 == ey) & (fx + 2 == fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 2, ex - 1, fy),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SA250-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey + 1 == ex) & (fy + 2 == fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 2, ey - 1, fx),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SA251-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex + 1 == ey) & (fx + 2 == fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 2, ex - 2, fy),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SA251-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey + 1 == ex) & (fy + 2 == fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 2, ey - 2, fx),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SA270-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex + 1 == ey) & (fx + 2 < fy) & (ex < fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 2, ex - 1, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SA270-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey + 1 == ex) & (fy + 2 < fx) & (ey < fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 2, ey - 1, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SA271-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex + 1 == ey) & (fx + 2 < fy) & (ex < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 2, ex - 2, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SA271-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey + 1 == ex) & (fy + 2 < fx) & (ey < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 2, ey - 2, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx < ey + 1) & (ex < fy + (p - 2)) & (fx + 1 > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy < ex + 1) & (ey < fx + (p - 2)) & (fy + 1 > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S1A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx < ey + 1) & (ex == fy + (p - 2)) & (fx > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S1A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy < ex + 1) & (ey == fx + (p - 2)) & (fy > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S1A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (ex == fy + (p - 2)) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S1A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (ey == fx + (p - 2)) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S1A2-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (ex == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S1A2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (ey == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S1A3-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx > ey) & (ex == fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S1A3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy > ex) & (ey == fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S1A4-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex > ey + 1) & (ex == fy + (p - 2)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S1A4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey > ex + 1) & (ey == fx + (p - 2)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S1B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx < ey + 1) & (ex == fy + (p - 1)) & (fx > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S1B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy < ex + 1) & (ey == fx + (p - 1)) & (fy > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S1B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (ex == fy + (p - 1)) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S1B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (ey == fx + (p - 1)) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S1B2-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx > ey) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S1B2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy > ex) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S1C0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex > ey + 3) & (fx < ey + 1) & (ex == fy + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy + 2),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S1C0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey > ex + 3) & (fy < ex + 1) & (ey == fx + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx + 2),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S1C1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex > ey + 3) & (ex == fy + p) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S1C1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey > ex + 3) & (ey == fx + p) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S1C2-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 3) & (ex == fy + p) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy + 2),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S1C2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 3) & (ey == fx + p) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx + 2),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S1C3-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + 3) & (ex == fy + p) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S1C3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + 3) & (ey == fx + p) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S2-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex + 1 < fy) & (fx + p > ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ey, fy, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey + 1 < fx) & (fy + p > ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ex, fx, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S3-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex < ey + (p - 1)) & (ex > fy + p) & (fx < ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey < ex + (p - 1)) & (ey > fx + p) & (fy < ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S3A-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex < ey + (p - 1)) & (ex > fy + p) & (fx < ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S3A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey < ex + (p - 1)) & (ey > fx + p) & (fy < ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S3B-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex < ey + p) & (ex > fy + p) & (fx == ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fx + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S3B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey < ex + p) & (ey > fx + p) & (fy == ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fy + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S3AB-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex > fy + p) & (fx == ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fx + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S3AB-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey > fx + p) & (fy == ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fy + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 3, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S4-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx > ey) & (ex < fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy > ex) & (ey < fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S4A-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (ex < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S4A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (ey < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S5A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx + 1 == fy) & (ex > ey + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S5A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy + 1 == fx) & (ey > ex + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S5A2-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx + 2 == fy) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S5A2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy + 2 == fx) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-S6-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (fx + p > ey) & (ex + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ey, ex, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-S6-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (fy + p > ex) & (ey + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ex, ey, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SB10-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + (p - 1)) & (fx > ey) & (ex > fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SB10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + (p - 1)) & (fy > ex) & (ey > fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SB110-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + (p - 1)) & (fx > ey) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SB110-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + (p - 1)) & (fy > ex) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SB111-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + (p - 2)) & (fx == ey + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SB111-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + (p - 2)) & (fy == ex + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SB20-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ex > fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SB20-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ey > fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SB21-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SB21-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SB22-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ex == fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SB22-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ey == fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO0-SB23-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-R0R1-TWO0-SB23-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

end
