function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R1R0},
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

    checker("SELTZO-TwoSum-R1R0-MM01-DA0-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 1 < ey) & (fx > fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-DA0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 1 < ex) & (fy > fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-DA1-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-DA1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-DA2-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-DA2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-DA3-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 1 == fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-DA3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 1 == fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-DA4-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 1 == fy) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-DA4-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 1 == fx) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-DA5-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fy, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-DA5-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fx, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D1A-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > ey + 1) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D1A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > ex + 1) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D2-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx < ey) & (fx + 1 > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy < ex) & (fy + 1 > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D2A0-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > ey + 1) & (fx + 1 == fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D2A0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > ex + 1) & (fy + 1 == fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D2A1-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > ey + 1) & (fx + 1 == fy) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D2A1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > ex + 1) & (fy + 1 == fx) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D2B-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx < ey) & (fx + 1 > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D2B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy < ex) & (fy + 1 > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D2BC-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D2BC-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy == ex) & (ey < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D2D0-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx < ey) & (fx > fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D2D0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy < ex) & (fy > fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D2D1-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx == fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D2D1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy == fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D2BD0-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx < ey) & (fx > fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D2BD0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy < ex) & (fy > fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D2BD1-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx == fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D2BD1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy == fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D2BCD-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D2BCD-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D2E0-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx < ey) & (fx > fy) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D2E0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy < ex) & (fy > fx) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D2E1-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx == fy) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D2E1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy == fx) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D2BE-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx < ey) & (fx > fy) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D2BE-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy < ex) & (fy > fx) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D2BCE-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - (p - 2), ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D2BCE-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - (p - 2), ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D2F0-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx < ey) & (fx > fy + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D2F0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy < ex) & (fy > fx + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D2F1-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx == fy + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D2F1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy == fx + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D3-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx < ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy < ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D3A-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D3A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D4-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx + 1 > ey) & (ex < fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D4-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy + 1 > ex) & (ey < fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D4A-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D4A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D4B-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx + 1 > ey) & (ex == fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D4B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy + 1 > ex) & (ey == fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D4AB-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx > ey) & (ex == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D4AB-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy > ex) & (ey == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D4C-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx + 1 > ey) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D4C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy + 1 > ex) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D4AC-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx > ey) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D4AC-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy > ex) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D5-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx > ey) & (ex > fy + p) & (ex < ey + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D5-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy > ex) & (ey > fx + p) & (ey < ex + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D5A-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > fy + p) & (ex < ey + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D5A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > fx + p) & (ey < ex + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D5B-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx + 1 > ey) & (ex == fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D5B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy + 1 > ex) & (ey == fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D5AB-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex == fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D5AB-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey == fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D5C-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex == ey + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D5C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey == ex + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-D5AC-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex == ey + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-D5AC-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey == ex + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
