function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
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

    checker("SELTZO-TwoSum-ONE1-MM01-DA10-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-DA10-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-DA11-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-DA11-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-DA12-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy + 1, fy - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-DA12-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx + 1, fx - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-DA13-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy + 1, fy - (p - 1), fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-DA13-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx + 1, fx - (p - 1), fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-DA1B0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 2 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fy - 2, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-DA1B0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 2 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fx - 2, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-DA1B1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fy - 3, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-DA1B1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fx - 3, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-DA20-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx > fy + 1) & (fx < ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey + 1, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-DA20-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy > fx + 1) & (fy < ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex + 1, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-DA22-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx + 1 > fy) & (fx < fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey + 1, fy + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-DA22-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy + 1 > fx) & (fy < fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex + 1, fx + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-DA2A0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey + 1, fy, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-DA2A0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex + 1, fx, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-DA2A1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey + 1, fy + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-DA2A1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex + 1, fx + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-DA2B0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx > fy + 1) & (fx < ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey + 1, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-DA2B0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy > fx + 1) & (fy < ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex + 1, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-DA2B2-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx == fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey + 1, fy + 1, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-DA2B2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy == fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex + 1, fx + 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx < ey) & (fx + 1 > fy) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy < ex) & (fy + 1 > fx) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D1A-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (fx == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D1A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (fy == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D1B-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D1B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D1C0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx > fy + 1) & (fx < ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D1C0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy > fx + 1) & (fy < ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D1C1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D1C1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D1C2-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx == fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D1C2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy == fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D2-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex > fy + (p + 1)) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey > fx + (p + 1)) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D2A-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex > fy + (p + 1)) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D2A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey > fx + (p + 1)) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D2B0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == fy + p) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D2B0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == fx + p) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D2B1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == fy + p) & (fx == ey) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D2B1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == fx + p) & (fy == ex) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D2B2-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == fy + p) & (fx == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 2, ey - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D2B2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == fx + p) & (fy == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 2, ex - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D2C0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == fy + (p + 1)) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D2C0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == fx + (p + 1)) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D2C1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == fy + (p + 1)) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D2C1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == fx + (p + 1)) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D3-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D3A-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D3A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D3B0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D3B0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D3B1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D3B1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D4-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex > fy + p) & (ex < ey + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey > fx + p) & (ey < ex + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D4A-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex > fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D4A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey > fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D4B0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D4B0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D4B1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy + 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D4B1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx + 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D4C0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D4C0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-D4C1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fy + 1, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-D4C1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fx + 1, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-DB-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-DB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
