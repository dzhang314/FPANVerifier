function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
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

    checker("SELTZO-TwoSum-ALL1-R1R0-SE0-X",
        (CLASS_X == ALL1) & (CLASS_Y == R1R0) &
        (ex == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fy, fy + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R1R0-SE0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R1R0) &
        (ey == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fx, fx + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R1R0-SE1-X",
        (CLASS_X == ALL1) & (CLASS_Y == R1R0) &
        (ex == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fy + 1, fy + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R1R0-SE1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R1R0) &
        (ey == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fx + 1, fx + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R1R0-S1-X",
        (CLASS_X == ALL1) & (CLASS_Y == R1R0) &
        (ex > fy + (p + 1)) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(sy, 1, 0, ex - p, fy, fy + 1))
    end
    checker("SELTZO-TwoSum-ALL1-R1R0-S1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R1R0) &
        (ey > fx + (p + 1)) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(sx, 1, 0, ey - p, fx, fx + 1))
    end

    checker("SELTZO-TwoSum-ALL1-R1R0-S1A-X",
        (CLASS_X == ALL1) & (CLASS_Y == R1R0) &
        (ex == fy + (p + 1)) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(sy, 0, 0, ex - p, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ALL1-R1R0-S1A-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R1R0) &
        (ey == fx + (p + 1)) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(sx, 0, 0, ey - p, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ALL1-R1R0-S1B-X",
        (CLASS_X == ALL1) & (CLASS_Y == R1R0) &
        (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-R1R0-S1B-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R1R0) &
        (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-R1R0-S2-X",
        (CLASS_X == ALL1) & (CLASS_Y == R1R0) &
        (ex < fy + (p - 1)) & (ex > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R1R0-S2-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R1R0) &
        (ey < fx + (p - 1)) & (ey > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R1R0-S2A-X",
        (CLASS_X == ALL1) & (CLASS_Y == R1R0) &
        (ex == fy + (p - 1)) & (ex > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R1R0-S2A-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R1R0) &
        (ey == fx + (p - 1)) & (ey > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R1R0-SB10-X",
        (CLASS_X == ALL1) & (CLASS_Y == R1R0) &
        (ex == ey + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ex + 1),
            SELTZORange(sy, 1, 0, ex - p, fy, fy + 1))
    end
    checker("SELTZO-TwoSum-ALL1-R1R0-SB10-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R1R0) &
        (ey == ex + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ey + 1),
            SELTZORange(sx, 1, 0, ey - p, fx, fx + 1))
    end

    checker("SELTZO-TwoSum-ALL1-R1R0-SB11-X",
        (CLASS_X == ALL1) & (CLASS_Y == R1R0) &
        (ex == ey + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ex + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ALL1-R1R0-SB11-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R1R0) &
        (ey == ex + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ey + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ALL1-R1R0-SB2-X",
        (CLASS_X == ALL1) & (CLASS_Y == R1R0) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey + 1, ex + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ALL1-R1R0-SB2-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R1R0) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex + 1, ey + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
