function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM10},
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

    checker("SELTZO-TwoSum-MM10-MM10-SE0-X",
        (ex == ey) & (fx > fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM10-SE0-Y",
        (ey == ex) & (fy > fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM10-SE1-X",
        (ex == ey) & (fx == fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM10-SE1-Y",
        (ey == ex) & (fy == fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM10-SE2-X",
        (ex == ey) & (fx == fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM10-SE2-Y",
        (ey == ex) & (fy == fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM10-SE3",
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM10-SE4-X",
        (ex == ey) & (fx > fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM10-SE4-Y",
        (ey == ex) & (fy > fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA100-X",
        (ex == ey + 1) & (fx < fy + 2) & (fx + 2 > fy) & (ex > fy + 3) & (ex < fy + (p - 3)) & (ex > fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA100-Y",
        (ey == ex + 1) & (fy < fx + 2) & (fy + 2 > fx) & (ey > fx + 3) & (ey < fx + (p - 3)) & (ey > fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA101-X",
        (ex == ey + 1) & (fx > fy + 1) & (ex < fy + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA101-Y",
        (ey == ex + 1) & (fy > fx + 1) & (ey < fx + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA102-X",
        (ex == ey + 1) & (fx + 1 < fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA102-Y",
        (ey == ex + 1) & (fy + 1 < fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA103-X",
        (ex == ey + 1) & (fx == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA103-Y",
        (ey == ex + 1) & (fy == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA110-X",
        (ex == ey + 1) & (fx < fy + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 3, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA110-Y",
        (ey == ex + 1) & (fy < fx + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 3, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA111-X",
        (ex == ey + 1) & (fx + 1 == fy) & (ex == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 3, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA111-Y",
        (ey == ex + 1) & (fy + 1 == fx) & (ey == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 3, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA120-X",
        (ex == ey + 1) & (fx > fy + 2) & (ex < fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA120-Y",
        (ey == ex + 1) & (fy > fx + 2) & (ey < fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA121-X",
        (ex == ey + 1) & (fx == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy - 1, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA121-Y",
        (ey == ex + 1) & (fy == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx - 1, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA122-X",
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fy - 2, fy - 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA122-Y",
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fx - 2, fx - 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA130-X",
        (ex == ey + 1) & (fx + 1 < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, fx),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA130-Y",
        (ey == ex + 1) & (fy + 1 < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, fy),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA131-X",
        (ex == ey + 1) & (fx + 1 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, fy + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA131-Y",
        (ey == ex + 1) & (fy + 1 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, fx + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA140-X",
        (ex == ey + 1) & (fx > fy + 1) & (ex == fy + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, fy),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA140-Y",
        (ey == ex + 1) & (fy > fx + 1) & (ey == fx + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, fx),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA141-X",
        (ex == ey + 1) & (ex == fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fy),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA141-Y",
        (ey == ex + 1) & (ey == fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fx),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA142-X",
        (ex == ey + 1) & (fx == fy + 1) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, fx + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA142-Y",
        (ey == ex + 1) & (fy == fx + 1) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, fy + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA150-X",
        (ex == ey + 1) & (fx > fy + 1) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, fy),
            SELTZORange(~sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA150-Y",
        (ey == ex + 1) & (fy > fx + 1) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, fx),
            SELTZORange(~sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA151-X",
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fy),
            SELTZORange(~sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA151-Y",
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fx),
            SELTZORange(~sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA152-X",
        (ex == ey + 1) & (fx == fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA152-Y",
        (ey == ex + 1) & (fy == fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA20-X",
        (ex == ey + 2) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - 2, fx - 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA20-Y",
        (ey == ex + 2) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - 2, fy - 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA21-X",
        (ex == ey + 2) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA21-Y",
        (ey == ex + 2) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SA22-X",
        (fx + 1 == ey) & (ex == ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - 2, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SA22-Y",
        (fy + 1 == ex) & (ey == ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - 2, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S1-X",
        (ex < fy + (p - 2)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S1-Y",
        (ey < fx + (p - 2)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S1A0-X",
        (ex < fy + (p - 2)) & (fx == ey + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S1A0-Y",
        (ey < fx + (p - 2)) & (fy == ex + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S1A1-X",
        (fx + 1 > ey) & (fx < ey + 2) & (ex < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S1A1-Y",
        (fy + 1 > ex) & (fy < ex + 2) & (ey < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S1B0-X",
        (ex == fy + (p - 2)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S1B0-Y",
        (ey == fx + (p - 2)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S1B1-X",
        (ex == fy + (p - 2)) & (fx + 1 > ey) & (fx < ey + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S1B1-Y",
        (ey == fx + (p - 2)) & (fy + 1 > ex) & (fy < ex + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S1B2-X",
        (ex == fy + (p - 2)) & (fx + 1 > ey) & (fx < ey + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S1B2-Y",
        (ey == fx + (p - 2)) & (fy + 1 > ex) & (fy < ex + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S1C0-X",
        (ex == fy + (p - 1)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S1C0-Y",
        (ey == fx + (p - 1)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S1C10-X",
        (ex == fy + (p - 1)) & (fx == ey + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S1C10-Y",
        (ey == fx + (p - 1)) & (fy == ex + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S1C11-X",
        (ex == fy + (p - 1)) & (fx == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S1C11-Y",
        (ey == fx + (p - 1)) & (fy == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S1C2-X",
        (ex == fy + (p - 1)) & (fx == ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S1C2-Y",
        (ey == fx + (p - 1)) & (fy == ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S2-X",
        (ex > ey + 1) & (ex < fy + (p - 2)) & (fx < ey) & (fx > fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S2-Y",
        (ey > ex + 1) & (ey < fx + (p - 2)) & (fy < ex) & (fy > fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S2AB-X",
        (ex > ey + 2) & (ex < fy + (p - 2)) & (fx + 1 == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S2AB-Y",
        (ey > ex + 2) & (ey < fx + (p - 2)) & (fy + 1 == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S2C0-X",
        (ex > ey + 1) & (ex < fy + (p - 2)) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S2C0-Y",
        (ey > ex + 1) & (ey < fx + (p - 2)) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S2C1-X",
        (ex > ey + 1) & (ex < fy + (p - 2)) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S2C1-Y",
        (ey > ex + 1) & (ey < fx + (p - 2)) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S2E-X",
        (ex == fy + (p - 2)) & (ex > ey + 1) & (fx < ey) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S2E-Y",
        (ey == fx + (p - 2)) & (ey > ex + 1) & (fy < ex) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S2BE-X",
        (ex == fy + (p - 2)) & (ex > ey + 1) & (fx == fy + 1) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S2BE-Y",
        (ey == fx + (p - 2)) & (ey > ex + 1) & (fy == fx + 1) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S2ABE0-X",
        (ex == fy + (p - 2)) & (fx == fy + 1) & (fx + 1 == ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S2ABE0-Y",
        (ey == fx + (p - 2)) & (fy == fx + 1) & (fy + 1 == ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S2F-X",
        (ex == fy + (p - 1)) & (fx < ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S2F-Y",
        (ey == fx + (p - 1)) & (fy < ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S3-X",
        (ex > fy + p) & (fx > ey + 1) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S3-Y",
        (ey > fx + p) & (fy > ex + 1) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S3A0-X",
        (ex > fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S3A0-Y",
        (ey > fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S3A1-X",
        (ex > fy + p) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S3A1-Y",
        (ey > fx + p) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S3B-X",
        (ex == fy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S3B-Y",
        (ey == fx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S3AB00-X",
        (ex == fy + p) & (fx == ey + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S3AB00-Y",
        (ey == fx + p) & (fy == ex + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S3AB01-X",
        (ex == fy + p) & (fx == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S3AB01-Y",
        (ey == fx + p) & (fy == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S3AB10-X",
        (ex == fy + p) & (fx == ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S3AB10-Y",
        (ey == fx + p) & (fy == ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S3AB11-X",
        (ex == fy + p) & (fx == ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S3AB11-Y",
        (ey == fx + p) & (fy == ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S4-X",
        (ex > fy + p) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S4-Y",
        (ey > fx + p) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S4A0-X",
        (ex == fy + p) & (fx < ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S4A0-Y",
        (ey == fx + p) & (fy < ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-S4A1-X",
        (ex == fy + p) & (fx < ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM10-S4A1-Y",
        (ey == fx + p) & (fy < ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SB1-X",
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SB1-Y",
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SB20-X",
        (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SB20-Y",
        (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-SB21-X",
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-SB21-Y",
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

end
