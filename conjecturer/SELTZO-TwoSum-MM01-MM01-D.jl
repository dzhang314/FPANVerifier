function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM01},
    ::Val{MM01},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-MM01-MM01-DE0",
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, pos_zero, pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-DE1-X",
        (ex == ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-DE1-Y",
        (ey == ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-DE2-X",
        (ex == ey) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-DE2-Y",
        (ey == ex) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-DE3-X",
        (ex == ey) & (fx + 2 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fy - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-DE3-Y",
        (ey == ex) & (fy + 2 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fx - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-DA0-X",
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-DA0-Y",
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-DA1-X",
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-DA1-Y",
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-DA3-X",
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-DA3-Y",
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-DA4-X",
        (ex == ey + 1) & (fx > fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-DA4-Y",
        (ey == ex + 1) & (fy > fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D1-X",
        (ex > ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-D1-Y",
        (ey > ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D1C-X",
        (ex > ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-D1C-Y",
        (ey > ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D2-X",
        (ex > ey + 2) & (fx < ey) & (fx > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-D2-Y",
        (ey > ex + 2) & (fy < ex) & (fy > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D2A-X",
        (ex == ey + 2) & (fx < ey) & (fx > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-D2A-Y",
        (ey == ex + 2) & (fy < ex) & (fy > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D2AC0-X",
        (ex == ey + 2) & (fx < ey) & (fx > fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-D2AC0-Y",
        (ey == ex + 2) & (fy < ex) & (fy > fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D2AC1-X",
        (ex == ey + 2) & (fx < ey) & (fx == fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-D2AC1-Y",
        (ey == ex + 2) & (fy < ex) & (fy == fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D2AC2-X",
        (ex == ey + 2) & (fx < ey) & (fx == fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-D2AC2-Y",
        (ey == ex + 2) & (fy < ex) & (fy == fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D2ACD0-X",
        (ex == ey + 2) & (fx == ey) & (fx > fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-D2ACD0-Y",
        (ey == ex + 2) & (fy == ex) & (fy > fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D2AD-X",
        (ex == ey + 2) & (fx == ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-D2AD-Y",
        (ey == ex + 2) & (fy == ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D2B-X",
        (ex > ey + 3) & (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-D2B-Y",
        (ey > ex + 3) & (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D2BC0-X",
        (ex > ey + 3) & (fx == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-D2BC0-Y",
        (ey > ex + 3) & (fy == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D2BC1-X",
        (ex == ey + 3) & (fx == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-D2BC1-Y",
        (ey == ex + 3) & (fy == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D2C0-X",
        (ex > ey + 2) & (fx < ey + 1) & (fx > fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-D2C0-Y",
        (ey > ex + 2) & (fy < ex + 1) & (fy > fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D2C1-X",
        (ex > ey + 2) & (fx < ey + 1) & (fx == fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-D2C1-Y",
        (ey > ex + 2) & (fy < ex + 1) & (fy == fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D2C2-X",
        (ex > ey + 2) & (fx < ey + 1) & (fx == fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-D2C2-Y",
        (ey > ex + 2) & (fy < ex + 1) & (fy == fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D3-X",
        (fx > ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-D3-Y",
        (fy > ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D3A-X",
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-D3A-Y",
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-D4-X",
        (ex == fy + (p - 1)) & (ex > ey + 2) & (fx > fy + 2) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D4-Y",
        (ey == fx + (p - 1)) & (ey > ex + 2) & (fy > fx + 2) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-D4A-X",
        (ex == fy + (p - 1)) & (ex == ey + 2) & (fx > fy + 2) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D4A-Y",
        (ey == fx + (p - 1)) & (ey == ex + 2) & (fy > fx + 2) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-D4AB-X",
        (ex == fy + (p - 1)) & (ex == ey + 2) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D4AB-Y",
        (ey == fx + (p - 1)) & (ey == ex + 2) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-D4AC-X",
        (ex == fy + (p - 1)) & (ex == ey + 2) & (fx > fy + 2) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D4AC-Y",
        (ey == fx + (p - 1)) & (ey == ex + 2) & (fy > fx + 2) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-D4B-X",
        (ex == fy + (p - 1)) & (ex > ey + 2) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D4B-Y",
        (ey == fx + (p - 1)) & (ey > ex + 2) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-D4D-X",
        (ex == fy + (p - 1)) & (fx == ey + 1) & (ex > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D4D-Y",
        (ey == fx + (p - 1)) & (fy == ex + 1) & (ey > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-D4DA-X",
        (ex == fy + (p - 1)) & (fx == ey + 1) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D4DA-Y",
        (ey == fx + (p - 1)) & (fy == ex + 1) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-D4E-X",
        (ex == fy + (p - 1)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D4E-Y",
        (ey == fx + (p - 1)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-D5-X",
        (ex == fy + p) & (fx > fy + 3) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D5-Y",
        (ey == fx + p) & (fy > fx + 3) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-D5B-X",
        (ex == fy + p) & (fx == fy + 3) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D5B-Y",
        (ey == fx + p) & (fy == fx + 3) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-D5D-X",
        (ex == fy + p) & (fx == ey + 1) & (ex > ey + 3) & (fx > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D5D-Y",
        (ey == fx + p) & (fy == ex + 1) & (ey > ex + 3) & (fy > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-D5DA-X",
        (ex == fy + p) & (fx == ey + 1) & (ex == ey + 3) & (fx > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D5DA-Y",
        (ey == fx + p) & (fy == ex + 1) & (ey == ex + 3) & (fy > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-D5DB-X",
        (ex == fy + p) & (fx == ey + 1) & (ex > ey + 3) & (fx == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D5DB-Y",
        (ey == fx + p) & (fy == ex + 1) & (ey > ex + 3) & (fy == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-D5E-X",
        (ex == fy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D5E-Y",
        (ey == fx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-D6-X",
        (ex > fy + p) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D6-Y",
        (ey > fx + p) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-D6D-X",
        (ex > fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D6D-Y",
        (ey > fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-D6E-X",
        (ex > fy + p) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D6E-Y",
        (ey > fx + p) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-D6F-X",
        (ex > fy + p) & (fx > ey + 2) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-D6F-Y",
        (ey > fx + p) & (fy > ex + 2) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-DB-X",
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-DB-Y",
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
