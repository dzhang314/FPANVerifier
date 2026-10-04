function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM10},
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

    checker("SELTZO-TwoSum-MM10-ONE1-DE0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 2 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fy - 1, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DE0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 2 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fx - 1, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DE1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy - 1, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DE1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx - 1, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DE20-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 1 == fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DE20-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 1 == fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DE21-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 1 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fx - 1, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DE21-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 1 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fy - 1, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DE30-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DE30-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DE31-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DE31-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DE4-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DE4-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DE5-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fx - 3, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DE5-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fy - 3, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DE6-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DE6-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DA0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fy - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DA0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fx - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DA1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DA1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DA2-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DA2-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DA3-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DA3-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DA50-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx > fy + 1) & (ex < fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DA50-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy > fx + 1) & (ey < fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DA51-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (ex == fy + (p - 1)) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DA51-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (ey == fx + (p - 1)) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DA60-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx > fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DA60-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy > fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex > ey + 2) & (fx < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey > ex + 2) & (fy < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D1A-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + 2) & (fx < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ey - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D1A-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + 2) & (fy < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ex - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D1B-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx + 1 == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D1B-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy + 1 == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D2-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx + 1 < ey) & (fx + 1 > fy) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D2-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy + 1 < ex) & (fy + 1 > fx) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D2A0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx + 1 < ey) & (ex == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D2A0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy + 1 < ex) & (ey == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D2A1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx + 1 < ey) & (ex == fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D2A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy + 1 < ex) & (ey == fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D2B-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx + 1 < ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D2B-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy + 1 < ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D2C-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (fx > fy + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D2C-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (fy > fx + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D2AC0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx - 1, ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D2AC0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy - 1, ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D2AC1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex == fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D2AC1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey == fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D2BC-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D2BC-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D2D0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex < fy + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D2D0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex) & (ey < fx + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D2D1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex < fy + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 3, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D2D1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex) & (ey < fx + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 3, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D2AD0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 2, ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D2AD0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 2, ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D2AD1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D2AD1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D2BD0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, ex - (p - 2)),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D2BD0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, ey - (p - 2)),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D2BD1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D2BD1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D2E-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D2E-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D2AE-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D2AE-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D2BE-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, ex - (p - 2)),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D2BE-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, ey - (p - 2)),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D3-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx + 1 < ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D3-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy + 1 < ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D3A-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, ex - (p - 1)),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D3A-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, ey - (p - 1)),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D3B-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 2, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D3B-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 2, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D3C-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D3C-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D4-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D4-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D4A-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D4A-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D4B-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex == fy + p) & (ex < ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ex - (p - 2)),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D4B-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey == fx + p) & (ey < ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ey - (p - 2)),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D4C0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx > ey + 2) & (ex == fy + p) & (ex == ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ex - (p - 3)),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D4C0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy > ex + 2) & (ey == fx + p) & (ey == ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ey - (p - 3)),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-D4C1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey + 2) & (ex == fy + p) & (ex == ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-D4C1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex + 2) & (ey == fx + p) & (ey == ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DB10-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DB10-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DB11-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DB11-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DB20-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DB20-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-DB21-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-DB21-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
