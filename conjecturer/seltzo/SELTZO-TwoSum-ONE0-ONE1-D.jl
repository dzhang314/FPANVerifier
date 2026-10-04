function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
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

    checker("SELTZO-TwoSum-ONE0-ONE1-DE1-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey) & (ex > fy + 2) & (fx < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DE1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex) & (ey > fx + 2) & (fy < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DE2-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 2 == ey) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DE2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 2 == ex) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DE3-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey) & (ey == fy + 2) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DE3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex) & (ex == fx + 2) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DE4-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey) & (ex == fx + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DE4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex) & (ey == fy + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DE5-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey) & (ex == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DE5-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex) & (ey == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DE6-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey) & (ex == fx + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DE6-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex) & (ey == fy + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DE7-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DE7-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DE8-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx + 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DE8-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy + 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DA0-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx + 1 < ey) & (fx > fy) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DA0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy + 1 < ex) & (fy > fx) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DA0A-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx + 1 < ey) & (fx > fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DA0A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy + 1 < ex) & (fy > fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DA1-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx + 1 == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DA1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy + 1 == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DA2-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx + 1 == ey) & (ey > fy + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DA2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy + 1 == ex) & (ex > fx + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DA3-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx + 1 == ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DA3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy + 1 == ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DA4A-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (ey == fy + (p - 2)) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DA4A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (ex == fx + (p - 2)) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DA5-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DA5-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DA6-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy) & (ey > fy + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DA6-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx) & (ex > fx + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D1-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex > fy + p) & (fx > ey) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey > fx + p) & (fy > ex) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D1A-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (fx > ey) & (ex < ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D1A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == fx + p) & (fy > ex) & (ey < ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D1B-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (fx == ey) & (ex < ey + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D1B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == fx + p) & (fy == ex) & (ey < ex + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D1C-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (fx == ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D1C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == fx + p) & (fy == ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D1D-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == fy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D1D-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == fx + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D2-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx < ey) & (fx > fy) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy < ex) & (fy > fx) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D2A-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx < ey) & (fx > fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D2A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy < ex) & (fy > fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D2A1-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx + 1 < ey) & (fx == fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D2A1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy + 1 < ex) & (fy == fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D2A2-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 3)) & (fx + 1 == ey) & (fx == fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D2A2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + (p - 3)) & (fy + 1 == ex) & (fy == fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D2B-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx < ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D2B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy < ex) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D2C1-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex > ey + 2) & (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D2C1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey > ex + 2) & (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D2C2-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + 2) & (fx == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D2C2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + 2) & (fy == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D2C3-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + 2) & (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D2C3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + 2) & (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D3-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex > fy + p) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey > fx + p) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D3B-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (fx < ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D3B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == fx + p) & (fy < ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D3C1-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (fx + 1 == ey) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D3C1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == fx + p) & (fy + 1 == ex) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D3D-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (fx + 1 < ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D3D-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == fx + p) & (fy + 1 < ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-D4-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex > fy + p) & (fx == ey) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-D4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey > fx + p) & (fy == ex) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DB0-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 2)) & (ex == fy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DB0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + (p - 2)) & (ey == fx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DB0B-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 2)) & (ex == fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DB0B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + (p - 2)) & (ey == fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DB1-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DB1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DB1A-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DB1A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DB2-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DB2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-ONE0-ONE1-DB2A-X",
        (CLASS_X == ONE0) & (CLASS_Y == ONE1) &
        (ex == ey + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 3),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-ONE0-ONE1-DB2A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ONE1) &
        (ey == ex + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 3),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
