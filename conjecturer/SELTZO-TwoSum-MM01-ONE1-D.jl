function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM01},
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

    checker("SELTZO-TwoSum-MM01-ONE1-DE1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx > fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DE1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex) & (fy > fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DE20-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DE20-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DE21-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ex - (p + 1), ex - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DE21-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ey - (p + 1), ey - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DE30-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DE30-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DE31-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DE31-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DE32-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DE32-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DE40-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx < fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DE40-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex) & (fy < fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DE41-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey) & (ey == fy + 2) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DE41-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex) & (ex == fx + 2) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DE42-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey) & (ey == fy + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DE42-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex) & (ex == fx + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DA0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx > fy + 1) & (ex > fx + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DA0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy > fx + 1) & (ey > fy + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DA0A-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey > fy + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 3, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DA0A-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex > fx + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 3, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DA0B-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (ex > fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DA0B-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (ey > fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DA0AB-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 3, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DA0AB-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 3, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DA1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DA1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DA1A-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DA1A-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DA2-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DA2-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DA2A-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DA2A-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx < ey) & (fx > fy + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy < ex) & (fy > fx + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D1A-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx == fy) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D1A-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy == fx) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D1B0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx == fy + 1) & (ex < fy + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D1B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy == fx + 1) & (ey < fx + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D1B1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx == fy + 1) & (ex < fy + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy + 3), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D1B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy == fx + 1) & (ey < fx + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx + 3), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D1C-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx < ey) & (fx + 1 > fy) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D1C-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy < ex) & (fy + 1 > fx) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D2-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D2-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D2A0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex < fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D2A0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey < fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D2A0B-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D2A0B-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D2A1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex < fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D2A1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey < fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D2A1B-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D2A1B-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D2B-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D2B-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D3-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx < ey) & (fx + 1 > fy) & (ex > fy + (p - 1)) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D3-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy < ex) & (fy + 1 > fx) & (ey > fx + (p - 1)) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D3A0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex > fy + (p - 1)) & (ex < ey + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D3A0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy == ex) & (ey > fx + (p - 1)) & (ey < ex + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D3A1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex > fy + (p - 1)) & (ex < ey + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D3A1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy == ex) & (ey > fx + (p - 1)) & (ey < ex + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D3AB0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D3AB0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D3AB1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D3AB1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D4-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex > fy + (p - 1)) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D4-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey > fx + (p - 1)) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-ONE1-D4A-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex > fy + (p - 1)) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-D4A-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey > fx + (p - 1)) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DB1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DB1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-ONE1-DB2-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-DB2-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
