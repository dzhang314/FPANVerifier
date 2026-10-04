function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
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

    checker("SELTZO-TwoSum-ONE0-ALL1-S1-X",
        (CLASS_X == ONE0) & (CLASS_Y == ALL1) &
        (fx < ey) & (ex > ey + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ALL1-S1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ALL1) &
        (fy < ex) & (ey > ex + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ALL1-S1A-X",
        (CLASS_X == ONE0) & (CLASS_Y == ALL1) &
        (fx < ey) & (ex > ey + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ALL1-S1A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ALL1) &
        (fy < ex) & (ey > ex + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ALL1-S1B-X",
        (CLASS_X == ONE0) & (CLASS_Y == ALL1) &
        (fx == ey) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ALL1-S1B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ALL1) &
        (fy == ex) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ALL1-S1AB-X",
        (CLASS_X == ONE0) & (CLASS_Y == ALL1) &
        (fx == ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, ex + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ALL1-S1AB-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ALL1) &
        (fy == ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, ey + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ALL1-S1C-X",
        (CLASS_X == ONE0) & (CLASS_Y == ALL1) &
        (ex == ey + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-ALL1-S1C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ALL1) &
        (ey == ex + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-ALL1-S1AC-X",
        (CLASS_X == ONE0) & (CLASS_Y == ALL1) &
        (ex == ey + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-ALL1-S1AC-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ALL1) &
        (ey == ex + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-ALL1-S2-X",
        (CLASS_X == ONE0) & (CLASS_Y == ALL1) &
        (fx > ey + 1) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ALL1-S2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ALL1) &
        (fy > ex + 1) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ALL1-S2A-X",
        (CLASS_X == ONE0) & (CLASS_Y == ALL1) &
        (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, fx - p, fx - (p + p), fx - p))
    end
    checker("SELTZO-TwoSum-ONE0-ALL1-S2A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ALL1) &
        (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, fy - p, fy - (p + p), fy - p))
    end

    checker("SELTZO-TwoSum-ONE0-ALL1-S2B-X",
        (CLASS_X == ONE0) & (CLASS_Y == ALL1) &
        (ex == ey + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ALL1-S2B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ALL1) &
        (ey == ex + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

end
