function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM01},
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

    checker("SELTZO-TwoSum-MM01-TWO1-DE00-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex == ey) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DE00-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey == ex) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DE01-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == fy) & (ex == ey) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DE01-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == fx) & (ey == ex) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DE10-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex == ey) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DE10-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey == ex) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DE11-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == fy) & (ex == ey) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DE11-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == fx) & (ey == ex) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DE20-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DE20-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DE21-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fx - p, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DE21-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fy - p, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DE30-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy) & (ex > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DE30-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx) & (ey > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DE31-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy) & (ex == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DE31-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx) & (ey == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DE32-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy) & (ex == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DE32-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx) & (ey == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DE40-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx > fy + 2) & (ex == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DE40-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy > fx + 2) & (ey == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DE41-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DE41-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DE50-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 < fy) & (ex > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DE50-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 < fx) & (ey > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DE51-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 < fy) & (ex == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DE51-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 < fx) & (ey == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DE52-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 == fy) & (ex == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DE52-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 == fx) & (ey == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DA0-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx > fy) & (ex == ey + 1) & (ex > fx + 2) & (ey > fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DA0-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy > fx) & (ey == ex + 1) & (ey > fy + 2) & (ex > fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DA1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx > fy + 1) & (ex == ey + 1) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DA1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy > fx + 1) & (ey == ex + 1) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DA2-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex == ey + 1) & (ey == fy + (p - 3)) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DA2-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey == ex + 1) & (ex == fx + (p - 3)) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DA30-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex == ey + 1) & (ey == fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DA30-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey == ex + 1) & (ex == fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DA31-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == fy + 2) & (ex == ey + 1) & (ey == fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 3, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DA31-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == fx + 2) & (ey == ex + 1) & (ex == fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 3, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DA50-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx + 1 == fy) & (ex == ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DA50-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy + 1 == fx) & (ey == ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DA51-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == fy) & (ex == ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DA51-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == fx) & (ey == ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DA60-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx + 1 == fy) & (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fy, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DA60-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy + 1 == fx) & (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fx, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DA61-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == fy) & (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fy, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DA61-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == fx) & (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fx, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DA7-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DA7-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DA8-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx > fy + 2) & (ex == ey + 1) & (ex < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DA8-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy > fx + 2) & (ey == ex + 1) & (ey < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DA9-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 3)) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DA9-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 3)) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D1A-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D1A-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D1B-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D1B-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D1C-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx > ey + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D1C-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy > ex + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D1AD1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex == fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D1AD1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey == fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D2-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx < ey) & (fx > fy) & (ex < fy + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D2-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy < ex) & (fy > fx) & (ey < fx + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D2B0-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx < ey) & (fx > fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D2B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy < ex) & (fy > fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D2B1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx == fy + 1) & (ex == fy + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D2B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy == fx + 1) & (ey == fx + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D2C0-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == fy) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D2C0-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == fx) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D2C1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx + 1 == fy) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D2C1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy + 1 == fx) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D2D-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex > ey + 2) & (ex < fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D2D-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey > ex + 2) & (ey < fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D2AD-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex == ey + 2) & (ex < fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D2AD-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey == ex + 2) & (ey < fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D2BD-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex > ey + 2) & (ex == fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D2BD-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey > ex + 2) & (ey == fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D3-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D3-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D3A0-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex < fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D3A0-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey < fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D3A1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D3A1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D3AB0-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D3AB0-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D3AB1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D3AB1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D4-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ey > fx) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D4-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ex > fy) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D4C0-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D4C0-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D4C1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D4C1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D4A-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ey > fx) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D4A-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ex > fy) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D4AC0-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D4AC0-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D4AC1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex == fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D4AC1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey == fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D4B-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ey > fx) & (fy + 2 < fx) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D4B-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ex > fy) & (fx + 2 < fy) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D4BC-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx + 1 > ey) & (fx < ey + 2) & (fx > fy + 2) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D4BC-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy + 1 > ex) & (fy < ex + 2) & (fy > fx + 2) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D4BCE-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx < ey + 2) & (fx > fy + 2) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D4BCE-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy < ex + 2) & (fy > fx + 2) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D4BD0-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ey > fx + 1) & (fy + 2 == fx) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D4BD0-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ex > fy + 1) & (fx + 2 == fy) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D4BD1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (fx == fy + 2) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D4BD1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (fy == fx + 2) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-D4BCD-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (fx == ey) & (fx == fy + 2) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-D4BCD-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (fy == ex) & (fy == fx + 2) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DB1-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DB1-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DB20-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DB20-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-TWO1-DB21-X",
        (CLASS_X == MM01) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-TWO1-DB21-Y",
        (CLASS_Y == MM01) & (CLASS_X == TWO1) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - 1, fx - 1))
    end

end
