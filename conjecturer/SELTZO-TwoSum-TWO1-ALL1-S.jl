function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO1},
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

    checker("SELTZO-TwoSum-TWO1-ALL1-SA10-X",
        (CLASS_X == TWO1) & (CLASS_Y == ALL1) &
        (ex == ey + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ALL1-SA10-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ALL1) &
        (ey == ex + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ALL1-SA11-X",
        (CLASS_X == TWO1) & (CLASS_Y == ALL1) &
        (ex == ey + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ALL1-SA11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ALL1) &
        (ey == ex + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ALL1-SA20-X",
        (CLASS_X == TWO1) & (CLASS_Y == ALL1) &
        (ex == ey + 2) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ALL1-SA20-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ALL1) &
        (ey == ex + 2) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ALL1-SA21-X",
        (CLASS_X == TWO1) & (CLASS_Y == ALL1) &
        (ex == ey + 2) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ALL1-SA21-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ALL1) &
        (ey == ex + 2) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ALL1-S1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ALL1) &
        (ex > ey + 2) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ALL1-S1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ALL1) &
        (ey > ex + 2) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ALL1-S21-X",
        (CLASS_X == TWO1) & (CLASS_Y == ALL1) &
        (fx == ey + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ALL1-S21-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ALL1) &
        (fy == ex + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ALL1-S22-X",
        (CLASS_X == TWO1) & (CLASS_Y == ALL1) &
        (fx == ey + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ALL1-S22-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ALL1) &
        (fy == ex + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ALL1-S2A1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ALL1) &
        (fx == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ALL1-S2A1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ALL1) &
        (fy == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ALL1-S2A2-X",
        (CLASS_X == TWO1) & (CLASS_Y == ALL1) &
        (fx == ey + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ALL1-S2A2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ALL1) &
        (fy == ex + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ALL1-SB-X",
        (CLASS_X == TWO1) & (CLASS_Y == ALL1) &
        (ex == ey + p) & (fx == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ALL1-SB-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ALL1) &
        (ey == ex + p) & (fy == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

end
