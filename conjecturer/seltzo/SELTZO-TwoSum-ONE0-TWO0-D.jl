function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
    ::Val{TWO0},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ONE0-TWO0-DE0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fy - 2, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-DE0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fx - 2, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-DE1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fy - p, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-DE1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fx - p, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-DE2-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy - 1, fy - (p + 1), fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-DE2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx - 1, fx - (p + 1), fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-DE3-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy - 1, fy - (p + 1), fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-DE3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx - 1, fx - (p + 1), fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-DE4-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy + 1, fy - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-DE4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx + 1, fx - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-DE5-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fx - 1, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-DE5-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fy - 1, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-DA0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-DA0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-DA1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-DA1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-DA20-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (fx == fy) & (ex == ey + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy - 1, fy - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-DA20-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (fy == fx) & (ey == ex + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx - 1, fx - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-DA21-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-DA21-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-DA3-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx - 2, fx - 2), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-DA3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy - 2, fy - 2), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-DA4-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-DA4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D1A-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex > ey + 1) & (fx + 1 == fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D1A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey > ex + 1) & (fy + 1 == fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D2-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx < ey) & (fx > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy < ex) & (fy > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D2A0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex > ey + 1) & (fx == fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D2A0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey > ex + 1) & (fy == fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D2A1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex > ey + 1) & (fx == fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D2A1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey > ex + 1) & (fy == fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D2B-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D2B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D2D0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx > fy) & (fx < ey + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D2D0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy > fx) & (fy < ex + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D2BD-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx > fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D2BD-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy > fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D2D1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D2D1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D2E0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx < ey + 1) & (fx > fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D2E0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy < ex + 1) & (fy > fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D2E1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx == fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D2E1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy == fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D2BE0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx > fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D2BE0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy > fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D2BE1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx == fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D2BE1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy == fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D2F0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (fx < ey + 1) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D2F0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (fy < ex + 1) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D2F1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (fx < ey + 1) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D2F1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (fy < ex + 1) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D3-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (fx < ey + 1) & (ex > fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (fy < ex + 1) & (ey > fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D3B-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (fx < ey + 1) & (ex > fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D3B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (fy < ex + 1) & (ey > fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 3, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D3A-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D3A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D3AB-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex > fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D3AB-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey > fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D4C-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (fx > ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D4C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (fy > ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D5-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex > fy + p) & (ex < ey + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D5-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey > fx + p) & (ey < ex + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D5E-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex < ey + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D5E-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey < ex + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D5B-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D5B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D5BD-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D5BD-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D5BDE-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D5BDE-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D5C-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (fx > ey + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D5C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex + p) & (fy > ex + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D5CE-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (fx > ey + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D5CE-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex + p) & (fy > ex + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 3, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D5CD-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (fx == ey + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D5CD-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex + p) & (fy == ex + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO0-D5CDE-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (fx == ey + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO0-D5CDE-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO0) &
        (ey == ex + p) & (fy == ex + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, ex - (p - 1)))
    end

end
