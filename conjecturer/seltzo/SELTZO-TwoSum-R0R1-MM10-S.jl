function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
    ::Val{MM10},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R0R1-MM10-SA00-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex > gx + 3) & (ex < fx + (p - 1)) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, ey - (p - 3)),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SA00-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey > gy + 3) & (ey < fy + (p - 1)) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, ex - (p - 3)),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SA01-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == gx + 3) & (ey > fy + 2) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, ey - (p - 3)),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SA01-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == gy + 3) & (ex > fx + 2) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, ex - (p - 3)),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SA1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + 3) & (ey > fy + 2) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey - (p - 3)),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SA1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + 3) & (ex > fx + 2) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex - (p - 3)),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SA2-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == gx + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy, ey - (p - 3)),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SA2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == gy + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx, ex - (p - 3)),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SA3-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy - 1, ey - (p - 3)),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SA3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx - 1, ex - (p - 3)),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SA4-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fy - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SA4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fx - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SA5-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + 2) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fy, fy - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SA5-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + 2) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fx, fx - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SA6-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SA6-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SA7-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fy, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SA7-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fx, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SA8-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + 3) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SA8-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + 3) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SA9-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex > fx + 3) & (ex < fx + (p - 2)) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SA9-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey > fy + 3) & (ey < fy + (p - 2)) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SA10-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + (p - 2)) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SA10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + (p - 2)) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SA11-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SA11-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SA12-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex > fx + 3) & (ex < fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SA12-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey > fy + 3) & (ey < fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SA13-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SA13-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (ex < fy + (p - 2)) & (fx + 2 > fy) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (ey < fx + (p - 2)) & (fy + 2 > fx) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S1A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S1A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S1B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex < fy + (p - 2)) & (fx + 1 == ey) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S1B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey < fx + (p - 2)) & (fy + 1 == ex) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S1B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex < fy + (p - 2)) & (fx + 1 == ey) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S1B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey < fx + (p - 2)) & (fy + 1 == ex) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S2-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex < fy + (p - 2)) & (fx + 1 > ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey < fx + (p - 2)) & (fy + 1 > ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S2A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex < fy + (p - 2)) & (fx > ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S2A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey < fx + (p - 2)) & (fy > ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S2A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex < fy + (p - 2)) & (fx == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S2A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey < fx + (p - 2)) & (fy == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S3-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (ex == fy + (p - 2)) & (fx + 1 < ey) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (ey == fx + (p - 2)) & (fy + 1 < ex) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S3A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (ex == fy + (p - 2)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S3A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (ey == fx + (p - 2)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S3B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (fx + 1 == ey) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S3B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (fy + 1 == ex) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S3B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (fx + 1 == ey) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S3B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (fy + 1 == ex) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S4-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (fx + 1 > ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (fy + 1 > ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S4A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (fx > ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S4A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (fy > ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S4A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (fx == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S4A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (fy == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S5-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx + 1 < ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S5-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy + 1 < ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S5A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx + 1 < ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S5A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy + 1 < ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S5B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx + 1 == ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S5B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy + 1 == ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S5B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx + 1 == ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S5B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy + 1 == ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S6-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx + 1 > ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, ey),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S6-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy + 1 > ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, ex),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S6A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx > ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S6A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy > ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S6A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, ey),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S6A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, ex),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S7-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx + 1 < ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S7-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy + 1 < ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S7A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx + 1 < ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S7A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy + 1 < ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S7B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx + 1 == ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S7B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy + 1 == ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S7B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx + 1 == ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S7B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy + 1 == ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S8-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx + 1 > ey) & (ex > fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, ey),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S8-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy + 1 > ex) & (ey > fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, ex),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S8A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx == ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, ey),
            SELTZORange(~sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S8A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy == ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, ex),
            SELTZORange(~sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S8B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex == fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S8B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey == fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S8B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(~sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S8B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(~sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S9-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > fy + p) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S9-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > fx + p) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S9A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > fy + p) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S9A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > fx + p) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S10-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > fy + p) & (ex < ey + (p - 1)) & (fx + 1 > ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > fx + p) & (ey < ex + (p - 1)) & (fy + 1 > ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-S10A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > fy + p) & (ex < ey + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-S10A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > fx + p) & (ey < ex + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SB10-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SB10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SB11-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SB11-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SB20-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ex > fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SB20-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + p) & (ey > fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SB21-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ex > fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - 1, ey - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SB21-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + p) & (ey > fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - 1, ex - 3, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SB22-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ex == fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SB22-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + p) & (ey == fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-SB23-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ex == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - 1, ey - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-SB23-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + p) & (ey == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - 1, ex - 3, ex - (p - 1)))
    end

end
