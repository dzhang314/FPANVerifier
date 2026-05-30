function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R1R0},
    ::Val{R1R0},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R1R0-R1R0-DE0-X",
        (ex == ey) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-DE0-Y",
        (ey == ex) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-DE1-X",
        (ex == ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fy - p, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-DE1-Y",
        (ey == ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fx - p, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-DE2",
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, pos_zero, pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-DA0-X",
        (ex == ey + 1) & (fx > fy + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-DA0-Y",
        (ey == ex + 1) & (fy > fx + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-DA1-X",
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-DA1-Y",
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-DA2-X",
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-DA2-Y",
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-DA3-X",
        (ex == ey + 1) & (fx > fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-DA3-Y",
        (ey == ex + 1) & (fy > fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D1-X",
        (ex < fy + p) & (fx < ey) & (ex > ey + 2) & (fx > fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D1-Y",
        (ey < fx + p) & (fy < ex) & (ey > ex + 2) & (fy > fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D1A-X",
        (ex == fy + p) & (fx < ey) & (ex > ey + 2) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D1A-Y",
        (ey == fx + p) & (fy < ex) & (ey > ex + 2) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D1B-X",
        (ex < fy + p) & (fx < ey) & (ex == ey + 2) & (fx > fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D1B-Y",
        (ey < fx + p) & (fy < ex) & (ey == ex + 2) & (fy > fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D1C-X",
        (ex > ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D1C-Y",
        (ey > ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D1AB-X",
        (ex == fy + p) & (fx < ey) & (ex == ey + 2) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D1AB-Y",
        (ey == fx + p) & (fy < ex) & (ey == ex + 2) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D1AC-X",
        (ex == fy + p) & (ex > ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D1AC-Y",
        (ey == fx + p) & (ey > ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D1ABC-X",
        (ex == fy + p) & (ex == ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D1ABC-Y",
        (ey == fx + p) & (ey == ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D2-X",
        (ex < fy + p) & (fx + 1 > ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D2-Y",
        (ey < fx + p) & (fy + 1 > ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D2A-X",
        (ex == fy + p) & (fx + 1 > ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx + 1, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D2A-Y",
        (ey == fx + p) & (fy + 1 > ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy + 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D2C-X",
        (ex < fy + p) & (fx > ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D2C-Y",
        (ey < fx + p) & (fy > ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D2AC-X",
        (ex == fy + p) & (fx > ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D2AC-Y",
        (ey == fx + p) & (fy > ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D2BC-X",
        (ex < fy + p) & (fx == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fy + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D2BC-Y",
        (ey < fx + p) & (fy == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fx + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D2ABC-X",
        (ex == fy + p) & (fx == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy + 1, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D2ABC-Y",
        (ey == fx + p) & (fy == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx + 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D3-X",
        (ex > fy + p) & (fx < ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D3-Y",
        (ey > fx + p) & (fy < ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D3B-X",
        (ex > fy + p) & (fx == ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx + 2),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D3B-Y",
        (ey > fx + p) & (fy == ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy + 2),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D3AC-X",
        (ex == fy + (p + 1)) & (fx < ey) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D3AC-Y",
        (ey == fx + (p + 1)) & (fy < ex) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D3ABC-X",
        (ex == fy + (p + 1)) & (fx == ey) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D3ABC-Y",
        (ey == fx + (p + 1)) & (fy == ex) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D4-X",
        (ex > fy + p) & (fx > ey) & (ex < ey + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D4-Y",
        (ey > fx + p) & (fy > ex) & (ey < ex + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D4A-X",
        (ex > fy + p) & (fx > ey) & (ex < ey + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D4A-Y",
        (ey > fx + p) & (fy > ex) & (ey < ex + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-DB0-X",
        (ex == ey + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-DB0-Y",
        (ey == ex + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-DB1-X",
        (ex == ey + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-DB1-Y",
        (ey == ex + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
