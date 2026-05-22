function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
    ::Val{R1R0},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ALL1-R1R0-DE0-X",
        (CLASS_X == ALL1) & (CLASS_Y == R1R0) &
        (ex == ey) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-R1R0-DE0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R1R0) &
        (ey == ex) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-R1R0-DE1-X",
        (CLASS_X == ALL1) & (CLASS_Y == R1R0) &
        (ex == ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fy - p, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-R1R0-DE1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R1R0) &
        (ey == ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fx - p, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-R1R0-D1-X",
        (CLASS_X == ALL1) & (CLASS_Y == R1R0) &
        (ex > fy + (p + 1)) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ALL1-R1R0-D1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R1R0) &
        (ey > fx + (p + 1)) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ALL1-R1R0-D1A-X",
        (CLASS_X == ALL1) & (CLASS_Y == R1R0) &
        (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ALL1-R1R0-D1A-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R1R0) &
        (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ALL1-R1R0-D1B0-X",
        (CLASS_X == ALL1) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-R1R0-D1B0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R1R0) &
        (ey == fx + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-R1R0-D1B1-X",
        (CLASS_X == ALL1) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-R1R0-D1B1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R1R0) &
        (ey == fx + p) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-R1R0-DB-X",
        (CLASS_X == ALL1) & (CLASS_Y == R1R0) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ALL1-R1R0-DB-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R1R0) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
