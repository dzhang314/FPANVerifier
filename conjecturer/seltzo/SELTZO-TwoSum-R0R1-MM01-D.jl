function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
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

    checker("SELTZO-TwoSum-R0R1-MM01-DA1A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx > fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-DA1A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy > fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-DA1A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx > fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, fy, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-DA1A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy > fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, fx, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-DA1B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx + 1, fy - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-DA1B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy + 1, fx - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-DA1B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx + 1, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-DA1B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy + 1, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-DA1C0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 1 == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy + 1, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-DA1C0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 1 == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx + 1, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-DA1C1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 1 == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy + 1, fy - (p - 1), fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-DA1C1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 1 == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx + 1, fx - (p - 1), fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-DA1D-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-DA1D-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-DA1E-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 2 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-DA1E-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 2 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-DA2C0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx + 1 > fy) & (fx + 1 < ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx + 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-DA2C0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy + 1 > fx) & (fy + 1 < ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy + 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-DA2C1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx + 1 > fy) & (fx + 1 < ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-DA2C1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy + 1 > fx) & (fy + 1 < ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-DA2C2-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx + 1 < ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex - 1, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-DA2C2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy + 1 < ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey - 1, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-DA2D0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx + 1 == fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy + 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-DA2D0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy + 1 == fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx + 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-DA2D1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx + 1 == fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-DA2D1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy + 1 == fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-DA2E-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-DA2E-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx + 1 < ey) & (fx + 2 > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy + 1 < ex) & (fy + 2 > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D1A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > ey + 1) & (fx + 1 == ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D1A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > ex + 1) & (fy + 1 == ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D1B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx + 1 > fy) & (fx + 1 < ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D1B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy + 1 > fx) & (fy + 1 < ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D1B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx + 1 == fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D1B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy + 1 == fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D1AB-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > ey + 1) & (fx + 1 == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D1AB-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > ex + 1) & (fy + 1 == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D1C-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx + 1 < ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D1C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy + 1 < ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D1AC-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (fx + 1 == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D1AC-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (fy + 1 == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D2-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > fy + (p + 1)) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > fx + (p + 1)) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D2B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == fy + p) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D2B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == fx + p) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D2B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == fy + p) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D2B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == fx + p) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D2C-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == fy + (p + 1)) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D2C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == fx + (p + 1)) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D3B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (fx > ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D3B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (fy > ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D3B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fy, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D3B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fx, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D4-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > fy + p) & (ex < ey + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > fx + p) & (ey < ex + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D4A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > fy + p) & (ex < ey + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D4A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > fx + p) & (ey < ex + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D4B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == fy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D4B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == fx + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D4B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == fy + (p - 1)) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D4B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == fx + (p - 1)) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D4C0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == fy + p) & (fx > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D4C0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == fx + p) & (fy > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D4C1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == fy + p) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D4C1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == fx + p) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D4D0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > fy + (p + 1)) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ex - p, ex - (p - 1)),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D4D0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > fx + (p + 1)) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ey - p, ey - (p - 1)),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-D4D1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == fy + (p + 1)) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ex - (p + 1), ex - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-D4D1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == fx + (p + 1)) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ey - (p + 1), ey - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-DB0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-DB0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-DB1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-DB1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
