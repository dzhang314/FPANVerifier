function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
    ::Val{ALL1},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R0R1-ALL1-D1-X",
        (CLASS_X == R0R1) & (CLASS_Y == ALL1) &
        (fx > ey + 1) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ALL1-D1-Y",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (fy > ex + 1) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 1, ey, fy, ex + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ALL1-D1A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ALL1) &
        (fx == ey + 1) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ALL1-D1A-Y",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (fy == ex + 1) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 1, ey, fy - 1, ex + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ALL1-D1B-X",
        (CLASS_X == R0R1) & (CLASS_Y == ALL1) &
        (fx > ey + 1) & (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ALL1-D1B-Y",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (fy > ex + 1) & (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ey, fy, ex + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ALL1-D1AB-X",
        (CLASS_X == R0R1) & (CLASS_Y == ALL1) &
        (fx == ey + 1) & (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ALL1-D1AB-Y",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (fy == ex + 1) & (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ey, ey - p, ey),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ALL1-D2-X",
        (CLASS_X == R0R1) & (CLASS_Y == ALL1) &
        (fx < ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ALL1-D2-Y",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (fy < ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ALL1-D2A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ALL1) &
        (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ex - p, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ALL1-D2A-Y",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey - 1, ey - p, ey - (p - 1)),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

end
