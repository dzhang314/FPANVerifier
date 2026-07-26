function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO1},
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

    checker("SELTZO-TwoSum-TWO1-MM10-SA1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 < ey) & (fx > fy) & (ey > fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SA1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 < ex) & (fy > fx) & (ex > fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SA2-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SA2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SA31-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 == fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SA31-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 == fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SA32-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SA32-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SA41-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 == fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SA41-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 == fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SA42-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SA42-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SA5-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx > fy + 2) & (ex < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SA5-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy > fx + 2) & (ey < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SA6-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy + 2) & (ex < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy - 2, fx - 3),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SA6-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx + 2) & (ey < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx - 2, fy - 3),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SA7-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SA7-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SA8-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SA8-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SA9-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx > fy + 2) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SA9-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy > fx + 2) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SA10-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex > fx + 2) & (ex < fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SA10-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey > fy + 2) & (ey < fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SA11-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ey > fy + 3) & (ex == fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SA11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ex > fx + 3) & (ey == fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S1A0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex < fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 2, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S1A0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey < fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 2, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S1A1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S1A1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S1B0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S1B0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S1B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 > ey) & (fx < ey + 2) & (fx > fy + 2) & (ex == fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S1B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 > ex) & (fy < ex + 2) & (fy > fx + 2) & (ey == fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S1B2-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 > ey) & (fx < ey + 2) & (fx > fy + 2) & (ex == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S1B2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 > ex) & (fy < ex + 2) & (fy > fx + 2) & (ey == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S1C-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S1C-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S1CA0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx < ey + 2) & (fx + 1 > ey) & (ex > fx + 2) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S1CA0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy < ex + 2) & (fy + 1 > ex) & (ey > fy + 2) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S1CA1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S1CA1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S1CA2-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx == ey) & (ex == fx + 2) & (ey == fy + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S1CA2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy == ex) & (ey == fy + 2) & (ex == fx + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S1CA3-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx == ey) & (ey == fy + 2) & (ex == fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, ey),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S1CA3-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy == ex) & (ex == fx + 2) & (ey == fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, ex),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S2-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (ex < fy + (p - 2)) & (fx < ey) & (fx > fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (ey < fx + (p - 2)) & (fy < ex) & (fy > fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S2A1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (ex < fy + (p - 2)) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S2A1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (ey < fx + (p - 2)) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S2A2-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (ex < fy + (p - 2)) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S2A2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (ey < fx + (p - 2)) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S2B0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ey == fy + 2) & (ex < fy + (p - 2)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S2B0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ex == fx + 2) & (ey < fx + (p - 2)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S2B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex == ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S2B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey == ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S2C0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx < ey) & (fx > fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S2C0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy < ex) & (fy > fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S2C11-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx == fy + 1) & (fx + 1 < ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S2C11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy == fx + 1) & (fy + 1 < ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S2C12-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx == fy + 2) & (fx + 1 < ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S2C12-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy == fx + 2) & (fy + 1 < ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S2C21-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx == ey) & (ex > fx + 2) & (ex == fy + (p - 2)) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S2C21-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy == ex) & (ey > fy + 2) & (ey == fx + (p - 2)) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S2C22-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex > fx + 2) & (ex == fy + (p - 2)) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S2C22-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey > fy + 2) & (ey == fx + (p - 2)) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S2C3-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex > ey + 2) & (ex == fy + (p - 2)) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S2C3-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey > ex + 2) & (ey == fx + (p - 2)) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S2D0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx < ey) & (ex < fx + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S2D0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy < ex) & (ey < fy + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S2D1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx < ey) & (ex < fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S2D1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy < ex) & (ey < fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S2DA0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx < ey) & (ex == fx + (p - 3)) & (ey > fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S2DA0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy < ex) & (ey == fy + (p - 3)) & (ex > fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S2DA1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx < ey) & (ex == fx + (p - 3)) & (ey == fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S2DA1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy < ex) & (ey == fy + (p - 3)) & (ex == fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S2DA2-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx < ey) & (ex == fx + (p - 3)) & (ey == fy + (p - 3)) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S2DA2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy < ex) & (ey == fy + (p - 3)) & (ex == fx + (p - 3)) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S3-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex < ey + (p - 1)) & (fx > ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S3-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey < ex + (p - 1)) & (fy > ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S3A-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex > fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S3A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey > fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S3B0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx > ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S3B0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy > ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S3B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx > ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S3B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy > ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S3B2-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx == ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S3B2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy == ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S3AB00-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx == ey + 1) & (ex > fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S3AB00-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy == ex + 1) & (ey > fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S3AB01-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx == ey) & (ex > fx + 2) & (ey > fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S3AB01-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy == ex) & (ey > fy + 2) & (ex > fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S3AB1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 2),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S3AB1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 2),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S3AB2-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx == ey) & (ey == fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fx),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S3AB2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy == ex) & (ex == fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fy),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S3AB3-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx == ey) & (ey == fy + (p - 3)) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fy + 2),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S3AB3-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy == ex) & (ex == fx + (p - 3)) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fx + 2),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S4-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex > fy + p) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S4-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey > fx + p) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S4A-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex > fy + p) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S4A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey > fx + p) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S4B0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx < ey) & (ex < fx + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S4B0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy < ex) & (ey < fy + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S4B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx < ey) & (ex < fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 2),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S4B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy < ex) & (ey < fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 2),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S4BC0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx < ey) & (ex == fx + (p - 3)) & (fx + 1 < ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S4BC0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy < ex) & (ey == fy + (p - 3)) & (fy + 1 < ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S4BC1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx < ey) & (ex == fx + (p - 3)) & (fx + 1 == ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S4BC1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy < ex) & (ey == fy + (p - 3)) & (fy + 1 == ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-S4BC2-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx < ey) & (ex == fx + (p - 3)) & (ey == fy + (p - 3)) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx + 1),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-S4BC2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy < ex) & (ey == fy + (p - 3)) & (ex == fx + (p - 3)) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy + 1),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SB10-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SB10-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SB11-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SB11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SB20-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (fx > ey + 3) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SB20-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + p) & (fy > ex + 3) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SB21-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (fx > ey + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SB21-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + p) & (fy > ex + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SB22-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (fx == ey + 3) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SB22-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + p) & (fy == ex + 3) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-MM10-SB23-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (fx == ey + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-MM10-SB23-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM10) &
        (ey == ex + p) & (fy == ex + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

end
