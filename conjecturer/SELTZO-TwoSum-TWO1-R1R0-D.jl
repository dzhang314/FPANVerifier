function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO1},
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

    checker("SELTZO-TwoSum-TWO1-R1R0-DA10-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy + 1, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-DA10-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx + 1, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-DA11-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx + 1, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-DA11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy + 1, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-DA12-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-DA12-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-DA13-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-DA13-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-DA14-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fx - 3, fx - 2), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-DA14-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fy - 3, fy - 2), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-DA15-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fx - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-DA15-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fy - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-DA20-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-DA20-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-DA21-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx + 1 < ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-DA21-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy + 1 < ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-DA22-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx + 1 < ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-DA22-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy + 1 < ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-DA23-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < ey) & (fx > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-DA23-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < ex) & (fy > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-DA24-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex - 1, fx, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-DA24-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey - 1, fy, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx > ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy > ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D1A-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D1A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D1AB0-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D1AB0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D1AB1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D1AB1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D1AC-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D1AC-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D1B-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D1B-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D1C-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey + 2) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D1C-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex + 2) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D1D-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx > ey + 2) & (ex < ey + p) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D1D-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy > ex + 2) & (ey < ex + p) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D2-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx > fy + 3) & (ex < fy + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex) & (fy > fx + 3) & (ey < fx + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D2A-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D2A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D2B-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx - 3, fx - 2), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D2B-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex) & (fy == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy - 3, fy - 2), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D2C-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, fx - 2, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D2C-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, fy - 2, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D2D-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D2D-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D3-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey) & (fx > fy + 2) & (ex < fy + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D3-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex) & (fy > fx + 2) & (ey < fx + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D3A0-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx + 1 < ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D3A0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy + 1 < ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D3A1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex > ey + 1) & (fx + 1 == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D3A1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey > ex + 1) & (fy + 1 == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D3B0-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx + 1 < ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D3B0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy + 1 < ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D3B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex > ey + 1) & (fx + 1 == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D3B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey > ex + 1) & (fy + 1 == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D3C-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D3C-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-D3D-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx < ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-D3D-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy < ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-DB-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-DB-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
