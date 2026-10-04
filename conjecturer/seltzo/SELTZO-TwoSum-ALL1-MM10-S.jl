function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
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

    checker("SELTZO-TwoSum-ALL1-MM10-SE0-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex == ey) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, ex - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-MM10-SE0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey == ex) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, ey - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-MM10-SE1-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex == ey) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, ex - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-MM10-SE1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey == ex) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, ey - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-MM10-SA10-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy - 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ALL1-MM10-SA10-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx - 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ALL1-MM10-SA11-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ALL1-MM10-SA11-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ALL1-MM10-SA2-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-MM10-SA2-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-MM10-S1-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex < fy + (p - 3)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy - 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-MM10-S1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey < fx + (p - 3)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx - 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-MM10-S1A-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 3)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-MM10-S1A-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey == fx + (p - 3)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-MM10-S1B-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (ex > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-MM10-S1B-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (ey > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-MM10-S2-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex > fy + (p + 1)) & (ex < ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-MM10-S2-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey > fx + (p + 1)) & (ey < ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-MM10-S2A-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex == ey + (p - 2)) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(~sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-MM10-S2A-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey == ex + (p - 2)) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(~sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-MM10-S2B-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex == fy + (p + 1)) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 0, 0, ex - p, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-MM10-S2B-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey == fx + (p + 1)) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 0, 0, ey - p, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-MM10-S2AB-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex == fy + (p + 1)) & (ex == ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ex - p, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-MM10-S2AB-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey == fx + (p + 1)) & (ey == ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ey - p, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-MM10-S2C0-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-MM10-S2C0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey == fx + p) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-MM10-S2C1-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ey > fy + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-MM10-S2C1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey == fx + p) & (ex > fx + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-MM10-S2AC-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex == ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-MM10-S2AC-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey == ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-MM10-S2D-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-MM10-S2D-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-MM10-SB1-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ex + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-MM10-SB1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ey + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-MM10-SB20-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sy, 1, 0, ex - (p + 1), fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-MM10-SB20-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sx, 1, 0, ey - (p + 1), fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-MM10-SB21-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sy, 0, 0, ex - (p + 1), fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-MM10-SB21-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM10) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sx, 0, 0, ey - (p + 1), fx - 1, ex - (p - 1)))
    end

end
