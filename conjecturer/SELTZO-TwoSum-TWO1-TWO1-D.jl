function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO1},
    ::Val{TWO1},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-TWO1-TWO1-DE0",
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, pos_zero, pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-DE1-X",
        (ex == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fy - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-DE1-Y",
        (ey == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fx - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-DE2-X",
        (ex == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fy - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-DE2-Y",
        (ey == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fx - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-DE3-X",
        (ex == ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fx - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-DE3-Y",
        (ey == ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fy - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-DA10-X",
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, ey - p, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-DA10-Y",
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, ex - p, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-DA11-X",
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-DA11-Y",
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-DA13-X",
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-DA13-Y",
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-DA140-X",
        (ex == ey + 1) & (fx + 1 < fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-DA140-Y",
        (ey == ex + 1) & (fy + 1 < fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-DA141-X",
        (ex == ey + 1) & (fx + 1 < fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fy - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-DA141-Y",
        (ey == ex + 1) & (fy + 1 < fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fx - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-DA2-X",
        (ex == ey + 2) & (fx < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ex - 3, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-DA2-Y",
        (ey == ex + 2) & (fy < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ey - 3, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D1-X",
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D1-Y",
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D1A1-X",
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D1A1-Y",
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D1A2-X",
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D1A2-Y",
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D2-X",
        (fx > ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D2-Y",
        (fy > ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D2A-X",
        (fx > ey + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D2A-Y",
        (fy > ex + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D2B-X",
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D2B-Y",
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D2C1-X",
        (ex == fy + (p - 1)) & (fx == ey) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D2C1-Y",
        (ey == fx + (p - 1)) & (fy == ex) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D2C2-X",
        (ex == fy + (p - 1)) & (fx == ey + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D2C2-Y",
        (ey == fx + (p - 1)) & (fy == ex + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D2E-X",
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D2E-Y",
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D2F1-X",
        (ex == fy + p) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 2, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D2F1-Y",
        (ey == fx + p) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 2, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D2F2-X",
        (ex == fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D2F2-Y",
        (ey == fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D2G-X",
        (fx + 1 < ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D2G-Y",
        (fy + 1 < ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D3-X",
        (ex > ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D3-Y",
        (ey > ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D40-X",
        (ex > ey + 1) & (ex < fy + (p - 1)) & (fx > fy + 1) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D40-Y",
        (ey > ex + 1) & (ey < fx + (p - 1)) & (fy > fx + 1) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D41-X",
        (ex > ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D41-Y",
        (ey > ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D5-X",
        (fx + 1 == ey) & (fx > fy + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D5-Y",
        (fy + 1 == ex) & (fy > fx + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D5A-X",
        (fx + 1 == ey) & (fx > fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D5A-Y",
        (fy + 1 == ex) & (fy > fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D5B-X",
        (fx + 1 == ey) & (fx > fy + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D5B-Y",
        (fy + 1 == ex) & (fy > fx + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D5C-X",
        (fx + 1 == ey) & (fx > fy + 1) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D5C-Y",
        (fy + 1 == ex) & (fy > fx + 1) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D5D-X",
        (fx + 1 == ey) & (fx > fy + 1) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, fx - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D5D-Y",
        (fy + 1 == ex) & (fy > fx + 1) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, fy - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D61-X",
        (fx == ey) & (fx > fy + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D61-Y",
        (fy == ex) & (fy > fx + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D62-X",
        (fx == ey + 1) & (fx > fy + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D62-Y",
        (fy == ex + 1) & (fy > fx + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D6A-X",
        (fx == ey) & (ex < fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 3, fx - 3), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D6A-Y",
        (fy == ex) & (ey < fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 3, fy - 3), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D6B1-X",
        (fx == ey) & (fx > fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D6B1-Y",
        (fy == ex) & (fy > fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D6B2-X",
        (fx == ey + 1) & (fx > fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D6B2-Y",
        (fy == ex + 1) & (fy > fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D6C-X",
        (fx == ey) & (ex == fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 3, fx - 2), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D6C-Y",
        (fy == ex) & (ey == fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 3, fy - 2), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D6D-X",
        (fx == ey) & (ex == fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D6D-Y",
        (fy == ex) & (ey == fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D7-X",
        (fx + 1 < ey) & (fx < fy) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D7-Y",
        (fy + 1 < ex) & (fy < fx) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D8A-X",
        (fx + 1 < ey) & (fx > fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D8A-Y",
        (fy + 1 < ex) & (fy > fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D8B-X",
        (fx + 1 < ey) & (fx > fy + 1) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D8B-Y",
        (fy + 1 < ex) & (fy > fx + 1) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-D8C-X",
        (fx + 1 < ey) & (fx > fy + 1) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-D8C-Y",
        (fy + 1 < ex) & (fy > fx + 1) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-DB1-X",
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-DB1-Y",
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-DB20-X",
        (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-DB20-Y",
        (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-TWO1-DB21-X",
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-TWO1-DB21-Y",
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - 1, fx - 1))
    end

end
