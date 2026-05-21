function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
    ::Val{ALL1},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R0R1-ALL1-S1-X",
        (CLASS_X == R0R1) & (CLASS_Y == ALL1) &
        (fx > ey) & (ex < ey + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ALL1-S1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ALL1) &
        (fy > ex) & (ey < ex + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ALL1-S1A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ALL1) &
        (fx > ey) & (ex < ey + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ALL1-S1A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ALL1) &
        (fy > ex) & (ey < ex + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ALL1-S1B-X",
        (CLASS_X == R0R1) & (CLASS_Y == ALL1) &
        (ex == ey + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ALL1-S1B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ALL1) &
        (ey == ex + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ALL1-S1AB-X",
        (CLASS_X == R0R1) & (CLASS_Y == ALL1) &
        (ex == ey + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ALL1-S1AB-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ALL1) &
        (ey == ex + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ALL1-S2-X",
        (CLASS_X == R0R1) & (CLASS_Y == ALL1) &
        (fx < ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ALL1-S2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ALL1) &
        (fy < ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ALL1-S2A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ALL1) &
        (fx == ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ALL1-S2A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ALL1) &
        (fy == ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

end
