function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
    ::Val{TWO0},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ALL1-TWO0-SE0-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-SE0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-SE1-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-SE1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-SA10-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy - 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-SA10-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx - 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-SA11-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-SA11-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-SA2-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ex - 1),
            SELTZORange(~sy, 1, 0, ex - p, ex - (p + 2), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-SA2-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ey - 1),
            SELTZORange(~sx, 1, 0, ey - p, ey - (p + 2), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-S1-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex < fy + (p - 3)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy - 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-S1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey < fx + (p - 3)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx - 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-S1A-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == fy + (p - 3)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-S1A-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == fx + (p - 3)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-S1B-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-S1B-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-S2-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex > fy + (p + 1)) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-S2-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey > fx + (p + 1)) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-S2A-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == fy + (p + 1)) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(sy, 0, 0, ex - p, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-S2A-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == fx + (p + 1)) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(sx, 0, 0, ey - p, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-S2B0-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-S2B0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-S2B1-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-S2B1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-S2C-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ex - p, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-S2C-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ey - p, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-SB10-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == ey + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-SB10-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == ex + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-SB11-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == ey + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, ex - p, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-SB11-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == ex + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, ey - p, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-SB20-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-SB20-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-SB21-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-SB21-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

end
