function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO1},
    ::Val{TWO1},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-TWO1-TWO1-SE0",
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SE1-X",
        (ex == ey) & (fx > fy + 1) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SE1-Y",
        (ey == ex) & (fy > fx + 1) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SE2-X",
        (ex == ey) & (fx == fy + 1) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SE2-Y",
        (ey == ex) & (fy == fx + 1) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SE3-X",
        (ex == ey) & (fx > fy + 2) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SE3-Y",
        (ey == ex) & (fy > fx + 2) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SE4-X",
        (ex == ey) & (fx == fy + 2) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SE4-Y",
        (ey == ex) & (fy == fx + 2) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SE5-X",
        (ex == ey) & (fx == fy + 1) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SE5-Y",
        (ey == ex) & (fy == fx + 1) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SA10-X",
        (ex == ey + 1) & (fx > fy) & (ex < fy + (p - 2)) & (ey > fy + 3) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SA10-Y",
        (ey == ex + 1) & (fy > fx) & (ey < fx + (p - 2)) & (ex > fx + 3) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SA12-X",
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fy - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SA12-Y",
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fx - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SA13-X",
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SA13-Y",
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SA14-X",
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SA14-Y",
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SA15-X",
        (ex == ey + 1) & (fx > fy + 2) & (ex < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SA15-Y",
        (ey == ex + 1) & (fy > fx + 2) & (ey < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SA16-X",
        (ex == ey + 1) & (fx == fy + 2) & (ex < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy - 2, fx - 3), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SA16-Y",
        (ey == ex + 1) & (fy == fx + 2) & (ey < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx - 2, fy - 3), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SA17-X",
        (ex == ey + 1) & (fx > fy + 2) & (ex == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SA17-Y",
        (ey == ex + 1) & (fy > fx + 2) & (ey == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SA181-X",
        (fx + 1 == fy) & (ex == ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SA181-Y",
        (fy + 1 == fx) & (ey == ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SA182-X",
        (fx == fy) & (ex == ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SA182-Y",
        (fy == fx) & (ey == ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SA191-X",
        (fx + 1 == fy) & (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SA191-Y",
        (fy + 1 == fx) & (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SA192-X",
        (fx == fy) & (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SA192-Y",
        (fy == fx) & (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SA112-X",
        (ex == ey + 1) & (ex == fy + (p - 2)) & (fx + 1 < ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SA112-Y",
        (ey == ex + 1) & (ey == fx + (p - 2)) & (fy + 1 < ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SA113-X",
        (ex == ey + 1) & (ex == fy + (p - 2)) & (fx + 1 < ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - 2, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SA113-Y",
        (ey == ex + 1) & (ey == fx + (p - 2)) & (fy + 1 < ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - 2, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S1-X",
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S1-Y",
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S2A-X",
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S2A-Y",
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S2B-X",
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S2B-Y",
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S2C-X",
        (fx > ey + 1) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S2C-Y",
        (fy > ex + 1) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S3-X",
        (fx < ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S3-Y",
        (fy < ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S3B1-X",
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S3B1-Y",
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S3B2-X",
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S3B2-Y",
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S4-X",
        (ex > ey + 1) & (fx < ey) & (fx > fy) & (ex < fy + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S4-Y",
        (ey > ex + 1) & (fy < ex) & (fy > fx) & (ey < fx + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S4A1-X",
        (ex > ey + 1) & (fx + 1 == fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S4A1-Y",
        (ey > ex + 1) & (fy + 1 == fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S4A2-X",
        (ex > ey + 1) & (fx == fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S4A2-Y",
        (ey > ex + 1) & (fy == fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S4C-X",
        (ex > ey + 1) & (ex == fy + (p - 2)) & (fx < ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S4C-Y",
        (ey > ex + 1) & (ey == fx + (p - 2)) & (fy < ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S4CB01-X",
        (ex == fy + (p - 2)) & (fx == fy + 1) & (fx + 1 < ey) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S4CB01-Y",
        (ey == fx + (p - 2)) & (fy == fx + 1) & (fy + 1 < ex) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S4CB02-X",
        (ex == fy + (p - 2)) & (fx == fy + 2) & (fx + 1 < ey) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S4CB02-Y",
        (ey == fx + (p - 2)) & (fy == fx + 2) & (fy + 1 < ex) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S4CB11-X",
        (ex == fy + (p - 2)) & (fx == fy + 2) & (ey == fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx + 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S4CB11-Y",
        (ey == fx + (p - 2)) & (fy == fx + 2) & (ex == fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy + 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S4CB12-X",
        (ex == fy + (p - 2)) & (fx == fy + 2) & (ey == fx + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx + 1, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S4CB12-Y",
        (ey == fx + (p - 2)) & (fy == fx + 2) & (ex == fy + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy + 1, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S4CC1-X",
        (ex == fy + (p - 2)) & (fx + 1 == ey) & (fx == fy + 1) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S4CC1-Y",
        (ey == fx + (p - 2)) & (fy + 1 == ex) & (fy == fx + 1) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S4D-X",
        (ex == fy + (p - 1)) & (fx < ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S4D-Y",
        (ey == fx + (p - 1)) & (fy < ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S4DB0-X",
        (ex == fy + (p - 1)) & (fx + 1 < ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S4DB0-Y",
        (ey == fx + (p - 1)) & (fy + 1 < ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S4DB11-X",
        (ex == fy + (p - 1)) & (fx == fy + 2) & (ey == fx) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S4DB11-Y",
        (ey == fx + (p - 1)) & (fy == fx + 2) & (ex == fy) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S4DB12-X",
        (ex == fy + (p - 1)) & (fx == fy + 2) & (ey == fx + 1) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S4DB12-Y",
        (ey == fx + (p - 1)) & (fy == fx + 2) & (ex == fy + 1) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S4E-X",
        (ex == fy + p) & (fx < ey) & (fx > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S4E-Y",
        (ey == fx + p) & (fy < ex) & (fy > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S4EB0-X",
        (ex == fy + p) & (fx + 1 < ey) & (fx == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S4EB0-Y",
        (ey == fx + p) & (fy + 1 < ex) & (fy == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S4EB11-X",
        (fx + 1 > ey) & (fx == fy + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, ey),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S4EB11-Y",
        (fy + 1 > ex) & (fy == fx + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, ex),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S4EB12-X",
        (ex == fy + p) & (fx == fy + 3) & (ey == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S4EB12-Y",
        (ey == fx + p) & (fy == fx + 3) & (ex == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S5-X",
        (fx == ey + 1) & (ex < fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S5-Y",
        (fy == ex + 1) & (ey < fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S5A0-X",
        (ex < fy + (p - 2)) & (ex == fx + 2) & (fx + 1 > ey) & (fx < ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ex - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S5A0-Y",
        (ey < fx + (p - 2)) & (ey == fy + 2) & (fy + 1 > ex) & (fy < ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ey - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S5A1-X",
        (ex == ey + 2) & (fx + 1 == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ex - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S5A1-Y",
        (ey == ex + 2) & (fy + 1 == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ey - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S5B-X",
        (ex == fy + (p - 2)) & (fx + 1 > ey) & (fx < ey + 2) & (fx > fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S5B-Y",
        (ey == fx + (p - 2)) & (fy + 1 > ex) & (fy < ex + 2) & (fy > fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S5C-X",
        (ex == fy + (p - 2)) & (fx + 1 > ey) & (fx < ey + 2) & (fx > fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S5C-Y",
        (ey == fx + (p - 2)) & (fy + 1 > ex) & (fy < ex + 2) & (fy > fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S5D-X",
        (ex == fy + (p - 1)) & (fx + 1 > ey) & (fx < ey + 2) & (fx > fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S5D-Y",
        (ey == fx + (p - 1)) & (fy + 1 > ex) & (fy < ex + 2) & (fy > fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S5E-X",
        (ex == fy + (p - 1)) & (fx + 1 > ey) & (fx < ey + 2) & (fx > fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S5E-Y",
        (ey == fx + (p - 1)) & (fy + 1 > ex) & (fy < ex + 2) & (fy > fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S5F-X",
        (fx == ey + 1) & (ex == fy + p) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S5F-Y",
        (fy == ex + 1) & (ey == fx + p) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S5G0-X",
        (ex == fy + p) & (fx + 1 > ey) & (fx < ey + 2) & (fx > fy + 3) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S5G0-Y",
        (ey == fx + p) & (fy + 1 > ex) & (fy < ex + 2) & (fy > fx + 3) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-S6A-X",
        (fx + 1 == ey) & (ex < fy + (p - 2)) & (ex > ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-S6A-Y",
        (fy + 1 == ex) & (ey < fx + (p - 2)) & (ey > ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SB10-X",
        (ex == ey + (p - 2)) & (gx > fy + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 3),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SB10-Y",
        (ey == ex + (p - 2)) & (gy > fx + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 3),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SB11-X",
        (ex == ey + (p - 2)) & (gx == fy + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SB11-Y",
        (ey == ex + (p - 2)) & (gy == fx + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SB20-X",
        (ex == ey + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SB20-Y",
        (ey == ex + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SB21-X",
        (ex == ey + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SB21-Y",
        (ey == ex + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SB30-X",
        (ex == ey + p) & (ey > fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SB30-Y",
        (ey == ex + p) & (ex > fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SB31-X",
        (ex == ey + p) & (ey == fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, fy + 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SB31-Y",
        (ey == ex + p) & (ex == fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, fx + 1, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SB32-X",
        (ex == ey + p) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SB32-Y",
        (ey == ex + p) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-SB33-X",
        (ex == ey + p) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-SB33-Y",
        (ey == ex + p) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - 1, fx - 1))
    end

end
