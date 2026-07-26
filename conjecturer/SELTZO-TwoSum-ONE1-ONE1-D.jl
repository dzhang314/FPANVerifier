function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
    ::Val{ONE1},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ONE1-ONE1-DE0",
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, pos_zero, pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-DE1-X",
        (ex == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fy - p, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-DE1-Y",
        (ey == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fx - p, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-DE2-X",
        (ex == ey) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx - 1, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-DE2-Y",
        (ey == ex) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy - 1, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-DA0-X",
        (ex == ey + 1) & (fx > fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-DA0-Y",
        (ey == ex + 1) & (fy > fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-DA1-X",
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, ey - p, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-DA1-Y",
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, ex - p, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-DA2-X",
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-DA2-Y",
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-DA3-X",
        (ex == ey + 1) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-DA3-Y",
        (ey == ex + 1) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-D1-X",
        (fx > ey) & (ex < ey + (p - 1)) & (ex > fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-D1-Y",
        (fy > ex) & (ey < ex + (p - 1)) & (ey > fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-D1A0-X",
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-D1A0-Y",
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-D1A1-X",
        (fx == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, fy - 1, ex - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-D1A1-Y",
        (fy == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, fx - 1, ey - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-D2-X",
        (fx > ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-D2-Y",
        (fy > ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-D2A-X",
        (fx == ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-D2A-Y",
        (fy == ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-D2B-X",
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-D2B-Y",
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-D2AB-X",
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-D2AB-Y",
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-D3-X",
        (fx + 1 < ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-D3-Y",
        (fy + 1 < ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-D3A-X",
        (fx + 1 == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-D3A-Y",
        (fy + 1 == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-D3B-X",
        (fx < ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-D3B-Y",
        (fy < ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-D4-X",
        (fx < ey) & (fx > fy) & (ex > ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-D4-Y",
        (fy < ex) & (fy > fx) & (ey > ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-D4A-X",
        (fx == ey) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-D4A-Y",
        (fy == ex) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-D5-X",
        (ex > ey + 2) & (fx < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-D5-Y",
        (ey > ex + 2) & (fy < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-D5A-X",
        (ex == ey + 2) & (fx < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-D5A-Y",
        (ey == ex + 2) & (fy < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-D5B-X",
        (fx == fy) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-D5B-Y",
        (fy == fx) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-DB1-X",
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-DB1-Y",
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-DB2-X",
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-DB2-Y",
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
