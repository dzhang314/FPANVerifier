function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
    ::Val{TWO1},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R0R1-TWO1-SE0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 > fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SE0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 > fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SE1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 > fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx + 1, fy),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SE1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 > fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy + 1, fx),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SE4-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SE4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SE5-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy + 1, fy + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SE5-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx + 1, fx + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SE6-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SE6-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SE7-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 < fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SE7-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 < fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SE8-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 < fy) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, fy - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SE8-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 < fx) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, fx - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SA10-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SA10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SA11-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 == fy) & (ey == fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SA11-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 == fx) & (ex == fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SA12B-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 == fy) & (ey > fy + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ex - 2, fx + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SA12B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 == fx) & (ex > fx + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ey - 2, fy + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SA14-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx == fy) & (ey == fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SA14-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy == fx) & (ex == fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SA17-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx > fy) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SA17-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy > fx) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SA18-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx > fy) & (ex == fx + 2) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, fy),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SA18-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy > fx) & (ey == fy + 2) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, fx),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SA19-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx > fy) & (ex == fx + 2) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SA19-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy > fx) & (ey == fy + 2) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SA20-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx > fy) & (ex == fx + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ex - 3, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SA20-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy > fx) & (ey == fy + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ey - 3, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SA21-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx > fy) & (ex == fx + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - 3, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SA21-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy > fx) & (ey == fy + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - 3, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SA22-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 > fy) & (ex > fx + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ex - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SA22-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 > fx) & (ey > fy + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ey - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SA23-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 2 > fy) & (ey > fy + 2) & (ex > fx + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SA23-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 2 > fx) & (ex > fx + 2) & (ey > fy + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (fx + 1 < ey) & (fx + 2 > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (fy + 1 < ex) & (fy + 2 > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S1A-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S1A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S1B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (fx + 1 < ey) & (fx + 1 > fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S1B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (fy + 1 < ex) & (fy + 1 > fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S1B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (fx + 1 == fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S1B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (fy + 1 == fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S1C0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (fx + 1 == ey) & (ex > ey + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S1C0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (fy + 1 == ex) & (ey > ex + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S1C1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (fx + 1 == ey) & (ex == ey + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S1C1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (fy + 1 == ex) & (ey == ex + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S1BC0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (fx + 1 == ey) & (ex > ey + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S1BC0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (fy + 1 == ex) & (ey > ex + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S1BC1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (fx + 1 == ey) & (ex == ey + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S1BC1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (fy + 1 == ex) & (ey == ex + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S1D-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex == fy + (p - 1)) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S1D-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey == fx + (p - 1)) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S1CD0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex == fy + (p - 1)) & (fx + 1 == ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S1CD0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey == fx + (p - 1)) & (fy + 1 == ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S1CD1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex == fy + (p - 1)) & (fx + 1 == ey) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S1CD1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey == fx + (p - 1)) & (fy + 1 == ex) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S2-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (fx + 1 > ey) & (ex > fx + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (fy + 1 > ex) & (ey > fy + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S2A-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (fx + 1 > ey) & (ex > fx + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S2A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (fy + 1 > ex) & (ey > fy + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S2B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (fx > ey) & (ex == fx + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S2B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (fy > ex) & (ey == fy + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S2B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (fx == ey) & (ex == fx + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S2B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (fy == ex) & (ey == fy + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S2AB0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (fx > ey) & (ex == fx + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S2AB0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (fy > ex) & (ey == fy + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S2AB1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (fx == ey) & (ex == fx + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S2AB1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (fy == ex) & (ey == fy + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S2C-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex == fy + (p - 1)) & (fx + 1 > ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, ey),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S2C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey == fx + (p - 1)) & (fy + 1 > ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, ex),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S2BC0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex == fy + (p - 1)) & (fx > ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S2BC0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey == fx + (p - 1)) & (fy > ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S2BC1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex == fy + (p - 1)) & (fx == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, ey),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S2BC1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey == fx + (p - 1)) & (fy == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, ex),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S3-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex > fy + p) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey > fx + p) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S3A-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex > fy + p) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S3A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey > fx + p) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S3B-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex == fy + p) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S3B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey == fx + p) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S3AB-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex == fy + p) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S3AB-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey == fx + p) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S4-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex > fy + p) & (fx + 1 > ey) & (ex > fx + 2) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey > fx + p) & (fy + 1 > ex) & (ey > fy + 2) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S4A-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex > fy + p) & (ex == fx + 2) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S4A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey > fx + p) & (ey == fy + 2) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S4B-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex == ey + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S4B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey == ex + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S4AB-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex == ey + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S4AB-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey == ex + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S4C-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex == fy + p) & (fx + 1 > ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, ey),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S4C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey == fx + p) & (fy + 1 > ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, ex),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-S4AC-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex == fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-S4AC-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey == fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SB0-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex == ey + p) & (ex > fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SB0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey == ex + p) & (ey > fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SB1-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex == ey + p) & (ex > fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SB1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey == ex + p) & (ey > fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SB2-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex == ey + p) & (ex == fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SB2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey == ex + p) & (ey == fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-TWO1-SB3-X",
        (CLASS_X == R0R1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < ey + (p + 1)) & (fx + 3 > fy) & (ex == ey + p) & (ex == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-TWO1-SB3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < ex + (p + 1)) & (fy + 3 > fx) & (ey == ex + p) & (ey == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

end
