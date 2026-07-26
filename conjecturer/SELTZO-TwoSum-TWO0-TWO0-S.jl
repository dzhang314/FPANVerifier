function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO0},
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

    checker("SELTZO-TwoSum-TWO0-TWO0-SE0",
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, fx + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-SE1-X",
        (ex == ey) & (fx == fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, fx + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-SE1-Y",
        (ey == ex) & (fy == fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, fy + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-SE2-X",
        (ex == ey) & (fx > fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-SE2-Y",
        (ey == ex) & (fy > fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-SE30-X",
        (ex == ey) & (fx == fy + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, fy + 2, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-SE30-Y",
        (ey == ex) & (fy == fx + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, fx + 2, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-SE31-X",
        (ex == ey) & (fx == fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, fy + 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-SE31-Y",
        (ey == ex) & (fy == fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, fx + 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-SE4-X",
        (ex == ey) & (fx > fy + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-SE4-Y",
        (ey == ex) & (fy > fx + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-SA0-X",
        (ex == ey + 1) & (fx > fy) & (ey > fy + 2) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy - 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-SA0-Y",
        (ey == ex + 1) & (fy > fx) & (ex > fx + 2) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx - 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-SA10-X",
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-SA10-Y",
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-SA11-X",
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fy - 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-SA11-Y",
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fx - 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-SA2-X",
        (ex == ey + 1) & (fx < fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-SA2-Y",
        (ey == ex + 1) & (fy < fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-SA3-X",
        (ex == ey + 1) & (fx > fy + 2) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-SA3-Y",
        (ey == ex + 1) & (fy > fx + 2) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-SA40-X",
        (ex == ey + 1) & (fx == fy + 2) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-SA40-Y",
        (ey == ex + 1) & (fy == fx + 2) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-SA41-X",
        (ex == ey + 1) & (fx == fy + 1) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx - 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-SA41-Y",
        (ey == ex + 1) & (fy == fx + 1) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy - 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-SA5-X",
        (ex == ey + 1) & (ex == fx + (p - 3)) & (fx + 2 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-SA5-Y",
        (ey == ex + 1) & (ey == fy + (p - 3)) & (fy + 2 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-SA60-X",
        (ex == ey + 1) & (fx + 2 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-SA60-Y",
        (ey == ex + 1) & (fy + 2 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-SA61-X",
        (ex == ey + 1) & (fx + 1 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy - 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-SA61-Y",
        (ey == ex + 1) & (fy + 1 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx - 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S1-X",
        (ex < ey + p) & (fx > ey + 2) & (ex > fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S1-Y",
        (ey < ex + p) & (fy > ex + 2) & (ey > fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S1A-X",
        (ex < ey + p) & (fx > ey + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S1A-Y",
        (ey < ex + p) & (fy > ex + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S1B0-X",
        (fx == ey + 2) & (ex > fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S1B0-Y",
        (fy == ex + 2) & (ey > fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S1B1-X",
        (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S1B1-Y",
        (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S1AB0-X",
        (fx == ey + 2) & (ex > fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S1AB0-Y",
        (fy == ex + 2) & (ey > fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S1AB1-X",
        (fx == ey + 1) & (ex > fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S1AB1-Y",
        (fy == ex + 1) & (ey > fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S2-X",
        (fx > ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S2-Y",
        (fy > ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S2A-X",
        (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S2A-Y",
        (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S2B0-X",
        (ex == fy + (p - 2)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S2B0-Y",
        (ey == fx + (p - 2)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S2B1-X",
        (ex == fy + (p - 2)) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S2B1-Y",
        (ey == fx + (p - 2)) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S2B2-X",
        (ex == fy + (p - 2)) & (fx == ey) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S2B2-Y",
        (ey == fx + (p - 2)) & (fy == ex) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S2B3-X",
        (ex == fy + (p - 2)) & (fx == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S2B3-Y",
        (ey == fx + (p - 2)) & (fy == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S2B4-X",
        (ex == fy + (p - 2)) & (fx < ey) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S2B4-Y",
        (ey == fx + (p - 2)) & (fy < ex) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S2B5-X",
        (ex == fy + (p - 2)) & (fx < ey) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S2B5-Y",
        (ey == fx + (p - 2)) & (fy < ex) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S2B6-X",
        (ex == fy + (p - 2)) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S2B6-Y",
        (ey == fx + (p - 2)) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S2B7-X",
        (ex == fy + (p - 2)) & (ex == fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fy + 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S2B7-Y",
        (ey == fx + (p - 2)) & (ey == fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fx + 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S2C-X",
        (ex == fy + (p - 1)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S2C-Y",
        (ey == fx + (p - 1)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S2AC-X",
        (ex == fy + (p - 1)) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S2AC-Y",
        (ey == fx + (p - 1)) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S2D-X",
        (ex == fy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 2),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S2D-Y",
        (ey == fx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 2),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S2AD0-X",
        (ex == fy + p) & (fx == ey + 1) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fy + 2),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S2AD0-Y",
        (ey == fx + p) & (fy == ex + 1) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fx + 2),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S2AD1-X",
        (ex == fy + p) & (fx == ey + 1) & (ey == fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S2AD1-Y",
        (ey == fx + p) & (fy == ex + 1) & (ex == fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S2AD2-X",
        (ex == fy + p) & (fx == ey + 1) & (ey > fy + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fy + 2),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S2AD2-Y",
        (ey == fx + p) & (fy == ex + 1) & (ex > fx + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fx + 2),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3-X",
        (ex > ey + 1) & (fx < fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3-Y",
        (ey > ex + 1) & (fy < fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3A0-X",
        (ex > ey + 1) & (fx + 2 < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3A0-Y",
        (ey > ex + 1) & (fy + 2 < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3A1-X",
        (ex > ey + 1) & (fx + 2 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 3),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3A1-Y",
        (ey > ex + 1) & (fy + 2 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 3),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3A2-X",
        (ex > ey + 1) & (fx + 1 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3A2-Y",
        (ey > ex + 1) & (fy + 1 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3H-X",
        (ex > ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3H-Y",
        (ey > ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3C0-X",
        (ex == fy + (p - 1)) & (fx < ey) & (ex < fx + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ex - p, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3C0-Y",
        (ey == fx + (p - 1)) & (fy < ex) & (ey < fy + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ey - p, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3C1-X",
        (ex == fy + (p - 1)) & (fx < ey) & (ex < fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(~sy, 1, 0, ex - p, ey - p, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3C1-Y",
        (ey == fx + (p - 1)) & (fy < ex) & (ey < fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(~sx, 1, 0, ey - p, ex - p, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3C2-X",
        (ex == fy + (p - 1)) & (fx < ey) & (ex == fx + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ex - p, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3C2-Y",
        (ey == fx + (p - 1)) & (fy < ex) & (ey == fy + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ey - p, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3C3-X",
        (ex == fy + (p - 1)) & (fx < ey) & (ex == fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 1, 0, ex - p, ey - p, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3C3-Y",
        (ey == fx + (p - 1)) & (fy < ex) & (ey == fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 1, 0, ey - p, ex - p, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3CA0-X",
        (ex == fy + (p - 1)) & (fx == ey) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, ey - 1),
            SELTZORange(~sy, 0, 0, ex - p, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3CA0-Y",
        (ey == fx + (p - 1)) & (fy == ex) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, ex - 1),
            SELTZORange(~sx, 0, 0, ey - p, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3CA1-X",
        (ex == fy + (p - 1)) & (fx == ey) & (ex == fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, ey - 1),
            SELTZORange(~sy, 1, 0, ex - p, ey - p, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3CA1-Y",
        (ey == fx + (p - 1)) & (fy == ex) & (ey == fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, ex - 1),
            SELTZORange(~sx, 1, 0, ey - p, ex - p, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3CA2-X",
        (ex == fy + (p - 1)) & (fx == ey) & (ex > fx + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3CA2-Y",
        (ey == fx + (p - 1)) & (fy == ex) & (ey > fy + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3D0-X",
        (ex == fy + p) & (fx < ey) & (ex < fx + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3D0-Y",
        (ey == fx + p) & (fy < ex) & (ey < fy + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3D1-X",
        (ex == fy + p) & (fx < ey) & (ex < fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3D1-Y",
        (ey == fx + p) & (fy < ex) & (ey < fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3D2-X",
        (ex == fy + p) & (fx < ey) & (ex == fx + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3D2-Y",
        (ey == fx + p) & (fy < ex) & (ey == fy + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3D3-X",
        (ex == fy + p) & (fx < ey) & (ex == fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3D3-Y",
        (ey == fx + p) & (fy < ex) & (ey == fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3DA0-X",
        (ex == fy + p) & (fx == ey) & (ex < fx + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, ey - 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3DA0-Y",
        (ey == fx + p) & (fy == ex) & (ey < fy + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, ex - 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3DA1-X",
        (ex == fy + p) & (fx == ey) & (ex < fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, ey - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3DA1-Y",
        (ey == fx + p) & (fy == ex) & (ey < fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, ex - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3DA2-X",
        (ex == fy + p) & (fx == ey) & (ex == fx + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3DA2-Y",
        (ey == fx + p) & (fy == ex) & (ey == fy + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3E-X",
        (ex == fy + (p + 1)) & (fx < ey) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 0, 0, ex - p, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3E-Y",
        (ey == fx + (p + 1)) & (fy < ex) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 0, 0, ey - p, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3EA-X",
        (ex == fy + (p + 1)) & (fx < ey) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ex - p, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3EA-Y",
        (ey == fx + (p + 1)) & (fy < ex) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ey - p, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3EB-X",
        (ex == fy + (p + 1)) & (fx == ey) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, ey - 1),
            SELTZORange(sy, 0, 0, ex - p, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3EB-Y",
        (ey == fx + (p + 1)) & (fy == ex) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, ex - 1),
            SELTZORange(sx, 0, 0, ey - p, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S3EAB-X",
        (ex == fy + (p + 1)) & (fx == ey) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, ex - p, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S3EAB-Y",
        (ey == fx + (p + 1)) & (fy == ex) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, ey - p, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S4-X",
        (fx < ey) & (fx > fy) & (ex > ey + 1) & (ex < fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy - 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S4-Y",
        (fy < ex) & (fy > fx) & (ey > ex + 1) & (ey < fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx - 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S4A-X",
        (fx == ey) & (ex < fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, fy - 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S4A-Y",
        (fy == ex) & (ey < fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, fx - 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S4B-X",
        (fx + 1 == ey) & (ex > ey + 1) & (ex < fy + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fy + 1, ey - 3),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S4B-Y",
        (fy + 1 == ex) & (ey > ex + 1) & (ey < fx + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fx + 1, ex - 3),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S4AB-X",
        (fx == ey) & (ex > ey + 1) & (ex < fy + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fy - 2, ey - 3),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S4AB-Y",
        (fy == ex) & (ey > ex + 1) & (ey < fx + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fx - 2, ex - 3),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S4D-X",
        (fx < ey) & (fx > fy + 2) & (ex > ey + 1) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S4D-Y",
        (fy < ex) & (fy > fx + 2) & (ey > ex + 1) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S4DA-X",
        (fx == ey) & (ex == fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 2, fy + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S4DA-Y",
        (fy == ex) & (ey == fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 2, fx + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S4DB-X",
        (fx < ey) & (fx == fy + 2) & (ex > ey + 1) & (ex == fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 3),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S4DB-Y",
        (fy < ex) & (fy == fx + 2) & (ey > ex + 1) & (ey == fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 3),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S4DC-X",
        (fx < ey) & (fx == fy + 1) & (ex > ey + 1) & (ex == fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S4DC-Y",
        (fy < ex) & (fy == fx + 1) & (ey > ex + 1) & (ey == fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S4DBA-X",
        (fx == ey) & (ex == fy + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S4DBA-Y",
        (fy == ex) & (ey == fx + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S4DCA-X",
        (fx + 1 == ey) & (fx == fy + 1) & (ex > ey + 1) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, ey - 2),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S4DCA-Y",
        (fy + 1 == ex) & (fy == fx + 1) & (ey > ex + 1) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, ex - 2),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S5-X",
        (ex > fy + (p + 1)) & (fx < ey) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S5-Y",
        (ey > fx + (p + 1)) & (fy < ex) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S5A-X",
        (ex > fy + (p + 1)) & (fx < ey) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S5A-Y",
        (ey > fx + (p + 1)) & (fy < ex) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S5B-X",
        (ex > fy + (p + 1)) & (fx == ey) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, ey - 1),
            SELTZORange(sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S5B-Y",
        (ey > fx + (p + 1)) & (fy == ex) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, ex - 1),
            SELTZORange(sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-S5AB-X",
        (ex > fy + (p + 1)) & (fx == ey) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-S5AB-Y",
        (ey > fx + (p + 1)) & (fy == ex) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-SB0-X",
        (ex == ey + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-SB0-Y",
        (ey == ex + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO0-SB1-X",
        (ex == ey + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO0-SB1-Y",
        (ey == ex + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

end
