function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM10},
    ::Val{R1R0},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-MM10-R1R0-DA10-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy + 1, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-DA10-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx + 1, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-DA11-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy + 1, fy - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-DA11-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx + 1, fx - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-DA12-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, fy - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-DA12-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, fx - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-DA13-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-DA13-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-DA14-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-DA14-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-DA15-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-DA15-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-DA20-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey + 1, fy + 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-DA20-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex + 1, fx + 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-DA21-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx + 1 < ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey + 1, fx + 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-DA21-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy + 1 < ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex + 1, fy + 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-DA22-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < ey) & (fx > fy + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey + 1, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-DA22-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < ex) & (fy > fx + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex + 1, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-DA23-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey + 1, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-DA23-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex + 1, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-DA24-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey + 1, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-DA24-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex + 1, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-D1A-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-D1A-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-D1AB-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-D1AB-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-D1AC0-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 1, ey),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-D1AC0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 1, ex),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-D1AC1-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, ey),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-D1AC1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, ex),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-D1B-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (fx == ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-D1B-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (fy == ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-D1C0-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (fx == ey + 2) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-D1C0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (fy == ex + 2) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-D1C1-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (fx == ey + 2) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-D1C1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (fy == ex + 2) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-D2A-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-D2A-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (fy == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-D2B0-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx > fy + 2) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-D2B0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (fy == ex) & (fy > fx + 2) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-D2B1-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 2, ey - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-D2B1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (fy == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 2, ex - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-D2C-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey - 1, ey - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-D2C-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (fy == ex) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex - 1, ex - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-D2D-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-D2D-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (fy == ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-D30-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey) & (fx > fy) & (ex < fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-D30-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex) & (fy > fx) & (ey < fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-D31-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-D31-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-D3A-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 1) & (fx + 1 == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-D3A-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 1) & (fy + 1 == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-D3C-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-D3C-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-D3D-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (fx < ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-D3D-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (fy < ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-DB-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + p) & (fx == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-DB-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + p) & (fy == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
