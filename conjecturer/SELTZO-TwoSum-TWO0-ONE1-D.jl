function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO0},
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

    checker("SELTZO-TwoSum-TWO0-ONE1-DE0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx < fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DE0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex) & (fy < fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DE1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 1 > fy) & (fx < fy + 2) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fx + 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DE1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 1 > fx) & (fy < fx + 2) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fy + 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DE2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx > fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fx - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DE2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex) & (fy > fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fy - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DE3-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey) & (ex > fx + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, ey - 3, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DE3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex) & (ey > fy + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, ex - 3, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DE4-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 1 > fy) & (fx < fy + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, ey - 3, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DE4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 1 > fx) & (fy < fx + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, ex - 3, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DE5-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DE5-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DE6-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey) & (ex == fx + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fy - 3, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DE6-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex) & (ey == fy + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fx - 3, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DE7-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey) & (ex == fx + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 2, ey - p, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DE7-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex) & (ey == fy + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 2, ex - p, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DE8-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey) & (ex == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 2, fy - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DE8-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex) & (ey == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 2, fx - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DA0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx > fy + 1) & (ex > fx + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DA0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy > fx + 1) & (ey > fy + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DA1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx > fy + 2) & (ex == fx + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DA1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy > fx + 2) & (ey == fy + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DA2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy + 2) & (ex == fx + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 3, fx - 2), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DA2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx + 2) & (ey == fy + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 3, fy - 2), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DA31-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy) & (fx + 2 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DA31-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx) & (fy + 2 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DA32-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy + 1) & (fx + 2 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DA32-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx + 1) & (fy + 2 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DA41-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy) & (fx + 2 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DA41-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx) & (fy + 2 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DA42-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy + 1) & (fx + 2 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DA42-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx + 1) & (fy + 2 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DA5-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy + 1) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DA5-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx + 1) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DA6-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx > fy + 2) & (ex > fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DA6-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy > fx + 2) & (ey > fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DA7-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy + 2) & (ex > fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DA7-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx + 2) & (ey > fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DA8-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx > fy + 2) & (ex == fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DA8-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy > fx + 2) & (ey == fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D1D0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D1D0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D1D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx > ey + 2) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D1D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy > ex + 2) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D1D2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == ey + 2) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D1D2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == ex + 2) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D1A01-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex > fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D1A01-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == ex) & (ey > fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D1A02-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex > fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D1A02-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey > fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D1A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex > fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D1A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey > fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D1AD0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 > ey) & (fx < ey + 2) & (fx > fy + 3) & (ex == fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D1AD0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 > ex) & (fy < ex + 2) & (fy > fx + 3) & (ey == fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D1AD1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 > ey) & (fx == fy + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, ey),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D1AD1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 > ex) & (fy == fx + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, ex),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D1AD2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx < ey + 2) & (ex == fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D1AD2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy < ex + 2) & (ey == fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D1B-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D1B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D1AB0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + (p - 1)) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D1AB0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + (p - 1)) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D1AB1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + (p - 1)) & (ex == fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D1AB1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + (p - 1)) & (ey == fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D1AB2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex > fx + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D1AB2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey > fy + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D1C0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex < fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D1C0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey < fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D1C1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex < fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D1C1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey < fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx < ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy < ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D2D0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx < ey) & (ex == fy + p) & (fx > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D2D0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy < ex) & (ey == fx + p) & (fy > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D2D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex == fy + p) & (fx == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D2D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey == fx + p) & (fy == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D2D2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 < ey) & (ex == fy + p) & (fx == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D2D2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 < ex) & (ey == fx + p) & (fy == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D3-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx < ey) & (fx > fy + 1) & (ex > ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy < ex) & (fy > fx + 1) & (ey > ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D3A0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx < ey) & (fx > fy + 2) & (ex > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D3A0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy < ex) & (fy > fx + 2) & (ey > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D3A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == fy + 2) & (fx + 1 < ey) & (ex > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D3A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == fx + 2) & (fy + 1 < ex) & (ey > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D3A2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == fy + 2) & (fx + 1 == ey) & (ex > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D3A2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == fx + 2) & (fy + 1 == ex) & (ey > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D3B01-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == fy) & (fx + 1 < ey) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D3B01-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == fx) & (fy + 1 < ex) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D3B02-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == fy + 1) & (fx + 1 < ey) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D3B02-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == fx + 1) & (fy + 1 < ex) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D3B1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == fy + 1) & (fx + 1 == ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D3B1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == fx + 1) & (fy + 1 == ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-D3B2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == fy + 1) & (fx + 1 == ey) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-D3B2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == fx + 1) & (fy + 1 == ex) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DB10-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1)) & (fx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DB10-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1)) & (fy > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DB11-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1)) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DB11-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1)) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DB20-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey + p) & (fx > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DB20-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex + p) & (fy > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-DB21-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey + p) & (fx == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-DB21-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex + p) & (fy == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
