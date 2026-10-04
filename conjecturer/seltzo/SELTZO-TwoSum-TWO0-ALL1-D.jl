function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO0},
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

    checker("SELTZO-TwoSum-TWO0-ALL1-DA10-X",
        (CLASS_X == TWO0) & (CLASS_Y == ALL1) &
        (ex == ey + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ALL1-DA10-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ALL1) &
        (ey == ex + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ALL1-DA11-X",
        (CLASS_X == TWO0) & (CLASS_Y == ALL1) &
        (ex == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ALL1-DA11-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ALL1) &
        (ey == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ALL1-DA20-X",
        (CLASS_X == TWO0) & (CLASS_Y == ALL1) &
        (ex == ey + 2) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ALL1-DA20-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ALL1) &
        (ey == ex + 2) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ALL1-DA21-X",
        (CLASS_X == TWO0) & (CLASS_Y == ALL1) &
        (ex == ey + 2) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 2, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ALL1-DA21-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ALL1) &
        (ey == ex + 2) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 2, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ALL1-D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ALL1) &
        (fx < ey + 1) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ALL1-D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ALL1) &
        (fy < ex + 1) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ALL1-D21-X",
        (CLASS_X == TWO0) & (CLASS_Y == ALL1) &
        (fx == ey + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ALL1-D21-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ALL1) &
        (fy == ex + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ALL1-D22-X",
        (CLASS_X == TWO0) & (CLASS_Y == ALL1) &
        (fx == ey + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ALL1-D22-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ALL1) &
        (fy == ex + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ALL1-D2A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ALL1) &
        (fx == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ALL1-D2A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ALL1) &
        (fy == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ALL1-D2A2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ALL1) &
        (fx == ey + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ALL1-D2A2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ALL1) &
        (fy == ex + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ALL1-DB-X",
        (CLASS_X == TWO0) & (CLASS_Y == ALL1) &
        (ex == ey + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ALL1-DB-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ALL1) &
        (ey == ex + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

end
