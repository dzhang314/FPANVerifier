function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
    ::Val{MM10},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R0R1-MM10-DA0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM10-DA0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM10-DA1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex > fx + 2) & (fx > fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM10-DA1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey > fy + 2) & (fy > fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM10-DA2-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fy - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM10-DA2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fx - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM10-DA3-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM10-DA3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM10-DA4A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 < fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM10-DA4A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 < fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM10-DA4B-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 < fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM10-DA4B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 < fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D1A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (ex < fy + (p - 2)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fy, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D1A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (ey < fx + (p - 2)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fx, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D1B-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (ex < fy + (p - 2)) & (fx + 1 < ey) & (fx + 1 > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D1B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (ey < fx + (p - 2)) & (fy + 1 < ex) & (fy + 1 > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D1C-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > ey + 2) & (ex < fy + (p - 2)) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D1C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > ex + 2) & (ey < fx + (p - 2)) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D1D-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (ex < fy + (p - 2)) & (fx < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D1D-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 2) & (ey < fx + (p - 2)) & (fy < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D2A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (ex == fy + (p - 2)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fy, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D2A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (ey == fx + (p - 2)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fx, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D2B-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (ex == fy + (p - 2)) & (fx + 1 < ey) & (fx > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D2B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (ey == fx + (p - 2)) & (fy + 1 < ex) & (fy > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D2C-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (ex == fy + (p - 2)) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D2C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (ey == fx + (p - 2)) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D2D-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > ey + 2) & (ex == fy + (p - 2)) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D2D-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > ex + 2) & (ey == fx + (p - 2)) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D2E-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (ex == fy + (p - 2)) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, ey - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D2E-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 2) & (ey == fx + (p - 2)) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, ex - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D3A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > ey + 2) & (ex == fy + (p - 1)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fy + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D3A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > ex + 2) & (ey == fx + (p - 1)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fx + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D3B-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > ey + 2) & (ex == fy + (p - 1)) & (fx + 1 < ey) & (fx > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D3B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > ex + 2) & (ey == fx + (p - 1)) & (fy + 1 < ex) & (fy > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D3C-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > ey + 2) & (ex == fy + (p - 1)) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D3C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > ex + 2) & (ey == fx + (p - 1)) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D3D1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (ex == fy + (p - 1)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fy, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D3D1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 2) & (ey == fx + (p - 1)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fx, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D3D0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (ex == fy + (p - 1)) & (fx + 1 < ey) & (fx > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D3D0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 2) & (ey == fx + (p - 1)) & (fy + 1 < ex) & (fy > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D3D2-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (ex == fy + (p - 1)) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D3D2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 2) & (ey == fx + (p - 1)) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D4A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx + 1 == ey) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fy + 1, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D4A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy + 1 == ex) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fx + 1, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D4A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx + 1 == ey) & (ex > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fy + 1, fy + 1),
            SELTZORange(sy, 1, 0, ex - (p + 2), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D4A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy + 1 == ex) & (ey > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fx + 1, fx + 1),
            SELTZORange(sx, 1, 0, ey - (p + 2), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D4G1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx + 1 < ey) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D4G1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy + 1 < ex) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D4G0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx + 1 < ey) & (ex > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 1),
            SELTZORange(sy, 1, 0, ex - (p + 2), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D4G0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy + 1 < ex) & (ey > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 1),
            SELTZORange(sx, 1, 0, ey - (p + 2), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D5A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p + 1)) & (fx + 1 == ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fy + 2, fy + 2),
            SELTZORange(~sy, 1, 0, ex - (p + 2), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D5A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p + 1)) & (fy + 1 == ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fx + 2, fx + 2),
            SELTZORange(~sx, 1, 0, ey - (p + 2), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D5A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p + 1)) & (fx + 1 == ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fy + 2, fy + 2),
            SELTZORange(~sy, 0, 0, ex - (p + 2), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D5A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p + 1)) & (fy + 1 == ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fx + 2, fx + 2),
            SELTZORange(~sx, 0, 0, ey - (p + 2), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D5G1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p + 1)) & (fx + 1 < ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 2),
            SELTZORange(~sy, 1, 0, ex - (p + 2), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D5G1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p + 1)) & (fy + 1 < ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 2),
            SELTZORange(~sx, 1, 0, ey - (p + 2), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D5G0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p + 1)) & (fx + 1 < ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 2),
            SELTZORange(~sy, 0, 0, ex - (p + 2), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D5G0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p + 1)) & (fy + 1 < ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 2),
            SELTZORange(~sx, 0, 0, ey - (p + 2), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D6A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > fy + (p + 1)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ex - p, ex - (p - 1)),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D6A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > fx + (p + 1)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ey - p, ey - (p - 1)),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D6G-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > fy + (p + 1)) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D6G-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > fx + (p + 1)) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D7G-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (fx > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ex - (p - 3)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D7G-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (fy > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ey - (p - 3)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D7A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, ex - (p - 3)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D7A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, ey - (p - 3)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D8B-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (ex == fy + (p - 1)) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D8B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + 2) & (ey == fx + (p - 1)) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D8G-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ex - (p - 2)),
            SELTZORange(sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D8G-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ey - (p - 2)),
            SELTZORange(sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D8A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > ey + 2) & (ex == fy + (p - 1)) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, ex - (p - 2)),
            SELTZORange(sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D8A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > ex + 2) & (ey == fx + (p - 1)) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, ey - (p - 2)),
            SELTZORange(sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D9G1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx > ey) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ex - (p - 2)),
            SELTZORange(~sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D9G1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy > ex) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ey - (p - 2)),
            SELTZORange(~sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D9A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx == ey) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, ex - (p - 2)),
            SELTZORange(~sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D9A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy == ex) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, ey - (p - 2)),
            SELTZORange(~sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D9G0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx > ey) & (ex > ey + 3) & (ex < ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ex - (p - 2)),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D9G0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy > ex) & (ey > ex + 3) & (ey < ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ey - (p - 2)),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D9A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx == ey) & (ex > ey + 3) & (ex < ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, ex - (p - 2)),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D9A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy == ex) & (ey > ex + 3) & (ey < ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, ey - (p - 2)),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D9G2-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx > ey) & (ex == ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ex - (p - 3)),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D9G2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy > ex) & (ey == ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ey - (p - 3)),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D9A2-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx == ey) & (ex == ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D9A2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy == ex) & (ey == ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D10G-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > fy + p) & (ex < ey + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D10G-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > fx + p) & (ey < ex + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-D10A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex > fy + p) & (ex < ey + (p - 1)) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 1, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-D10A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey > fx + p) & (ey < ex + (p - 1)) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 1, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-DB1G-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-DB1G-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-DB1A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1)) & (fx == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fy, ex - 1),
            SELTZORange(~sy, 0, 0, ey - 3, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-DB1A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + (p - 1)) & (fy == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fx, ey - 1),
            SELTZORange(~sx, 0, 0, ex - 3, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-DB1A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1)) & (fx == ey) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-DB1A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + (p - 1)) & (fy == ex) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-DB2G1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (fx > ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-DB2G1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + p) & (fy > ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-DB2G0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (fx > ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-DB2G0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + p) & (fy > ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-DB2A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (fx == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, ex),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-DB2A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + p) & (fy == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, ey),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM10-DB2A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (fx == ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, ex),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM10-DB2A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM10) &
        (ey == ex + p) & (fy == ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, ey),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

end
