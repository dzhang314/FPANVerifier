function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM10},
    ::Val{R0R1},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-MM10-R0R1-SE0-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SE0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex) & (fy > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SE1-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx > fy + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SE1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex) & (fy > fx + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SE2-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SE2-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SE3-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SE3-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SE4-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SE4-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SE5-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx < fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fy + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SE5-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex) & (fy < fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fx + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SE6-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx < fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fy + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SE6-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex) & (fy < fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fx + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SA00-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex > fx + 3) & (ey > fy + 2) & (ex < fx + (p - 3)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SA00-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey > fy + 3) & (ex > fx + 2) & (ey < fy + (p - 3)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SA01-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fx + 3) & (ey > fy + 3) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SA01-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fy + 3) & (ex > fx + 3) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SA1-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ey == fy + 2) & (ex > fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 3, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SA1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ex == fx + 2) & (ey > fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 3, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SA2-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fx + 3) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 3, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SA2-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fy + 3) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 3, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SA3-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey > fy + 3) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SA3-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex > fx + 3) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SA4-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fx + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SA4-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fy + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SA5-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 2, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SA5-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 2, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SA6-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - (p - 1), ex - (p - 2)),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SA6-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - (p - 1), ey - (p - 2)),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SA7-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 3, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SA7-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 3, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SA8-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ey > fy + 2) & (ey < fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SA8-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ex > fx + 2) & (ex < fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SA9-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SA9-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SA10-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex > fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SA10-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey > fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SA11-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SA11-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SA12-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex > fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SA12-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey > fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SA13-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SA13-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S1-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (ex < fy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (ey < fx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S1A-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex < fy + p) & (fx == ey + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S1A-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey < fx + p) & (fy == ex + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S1B-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex < fy + p) & (fx > fy + 2) & (fx + 1 > ey) & (fx < ey + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S1B-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey < fx + p) & (fy > fx + 2) & (fy + 1 > ex) & (fy < ex + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S2-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (ex < fy + p) & (fx > fy + 2) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S2-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (ey < fx + p) & (fy > fx + 2) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S31-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex > ey + 2) & (ex < fy + p) & (fx == fy + 1) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fy + 3, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S31-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey > ex + 2) & (ey < fx + p) & (fy == fx + 1) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fx + 3, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S32-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex > ey + 2) & (ex < fy + p) & (fx == fy + 2) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fy + 3, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S32-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey > ex + 2) & (ey < fx + p) & (fy == fx + 2) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fx + 3, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S33-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (ex < fy + p) & (fx == fy + 2) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fy + 3, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S33-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (ey < fx + p) & (fy == fx + 2) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fx + 3, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S3A1-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (fx == fy + 1) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S3A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (fy == fx + 1) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S3A2-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (fx == fy + 2) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S3A2-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (fy == fx + 2) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S41-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (ex < fy + p) & (fx == fy + 1) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S41-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (ey < fx + p) & (fy == fx + 1) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S42-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (ex < fy + p) & (fx == fy + 2) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S42-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (ey < fx + p) & (fy == fx + 2) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S5-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx > ey + 1) & (ex > ey + 1) & (ex < ey + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S5-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy > ex + 1) & (ey > ex + 1) & (ey < ex + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S5A-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx > ey + 1) & (ex > ey + 1) & (ex < ey + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S5A-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy > ex + 1) & (ey > ex + 1) & (ey < ex + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S5B-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx > ey + 1) & (ex == ey + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S5B-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy > ex + 1) & (ey == ex + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S5AB-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx > ey + 1) & (ex == ey + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S5AB-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy > ex + 1) & (ey == ex + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S5C-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx > ey + 1) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S5C-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy > ex + 1) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S61-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx == ey) & (ex > ey + 2) & (ex < ey + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S61-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy == ex) & (ey > ex + 2) & (ey < ex + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S62-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx == ey + 1) & (ex > ey + 2) & (ex < ey + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S62-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy == ex + 1) & (ey > ex + 2) & (ey < ex + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S6A1-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx == ey) & (ex > ey + 2) & (ex < ey + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S6A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy == ex) & (ey > ex + 2) & (ey < ex + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S6A2-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx == ey + 1) & (ex > ey + 2) & (ex < ey + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S6A2-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy == ex + 1) & (ey > ex + 2) & (ey < ex + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S6AB-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (fx == ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S6AB-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (fy == ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S6B01-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx == ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S6B01-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy == ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S6B02-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx == ey + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S6B02-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy == ex + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S6B11-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S6B11-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S6B12-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S6B12-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S7-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx < ey) & (ex > ey + 1) & (ex < ey + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S7-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy < ex) & (ey > ex + 1) & (ey < ex + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S7A-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx < ey) & (ex > ey + 1) & (ex < ey + p) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S7A-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy < ex) & (ey > ex + 1) & (ey < ex + p) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-S7B-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx < ey) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-S7B-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy < ex) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SB0-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SB0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SB1-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SB1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-SB2-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-SB2-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
