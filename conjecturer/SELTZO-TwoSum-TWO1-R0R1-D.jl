function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO1},
    ::Val{R0R1},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-TWO1-R0R1-DA0-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        ((ex == ey + 1) & (ex == fy + p)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-DA0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        ((ey == ex + 1) & (ey == fx + p)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-DA1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx < fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-DA1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy < fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-DA2-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx < fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-DA2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy < fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-DA3-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fx - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-DA3-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fy - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-DA4-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx - 1, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-DA4-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy - 1, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-DA5-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx > fy + 1) & (fx + 1 < ey) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-DA5-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy > fx + 1) & (fy + 1 < ex) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-DA6-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx + 1 == ey) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx - 1, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-DA6-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy + 1 == ex) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy - 1, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-DA7-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx + 1 == ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-DA7-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy + 1 == ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ex > fy + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ey > fx + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D1A1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex > fy + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D1A1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex) & (ey > fx + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D1A2-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D1A2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D1B-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D1B-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D1AB1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D1AB1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D1AB2-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D1AB2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D1C-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D1C-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D1AC1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 2, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D1AC1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 2, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D1AC2-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D1AC2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D2A01-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey) & (fx > fy + 2) & (ex < fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D2A01-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex) & (fy > fx + 2) & (ey < fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D2A02-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (fx > fy + 2) & (ex < fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D2A02-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (fy > fx + 2) & (ey < fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D2A1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D2A1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D3-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx + 1 < ey) & (ex > fy + (p + 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D3-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy + 1 < ex) & (ey > fx + (p + 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D3A-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex > fy + (p + 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D3A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey > fx + (p + 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D3B-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx + 1 < ey) & (ex > ey + 1) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D3B-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy + 1 < ex) & (ey > ex + 1) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D3AB-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex > ey + 1) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D3AB-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey > ex + 1) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D3C-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx + 1 < ey) & (ex == fy + (p + 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D3C-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy + 1 < ex) & (ey == fx + (p + 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D3AC-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex == fy + (p + 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D3AC-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey == fx + (p + 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D4-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx > fy + 2) & (fx + 1 < ey) & (ex > ey + 1) & (ex < fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D4-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy > fx + 2) & (fy + 1 < ex) & (ey > ex + 1) & (ey < fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D4A-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == fy + 2) & (fx + 1 < ey) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D4A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == fx + 2) & (fy + 1 < ex) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D4B-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == fy + 1) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D4B-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == fx + 1) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D4C-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx < fy + 1) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D4C-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy < fx + 1) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D4D-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx > fy + 2) & (fx + 1 == ey) & (ex > ey + 1) & (ex < fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D4D-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy > fx + 2) & (fy + 1 == ex) & (ey > ex + 1) & (ey < fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-D4AD-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == fy + 2) & (fx + 1 == ey) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-D4AD-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == fx + 2) & (fy + 1 == ex) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-DB10-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-DB10-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-DB11-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-DB11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-DB20-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-DB20-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-DB21-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-DB21-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-DB22-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-DB22-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
