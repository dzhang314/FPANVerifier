function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO1},
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

    checker("SELTZO-TwoSum-TWO1-MM01-DA10-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fx - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-DA10-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fy - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-DA11-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-DA11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-DA12-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, fx - 2, fx - 2), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-DA12-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, fy - 2, fy - 2), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-DA13-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx + 1, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-DA13-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy + 1, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-DA14-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy + 1, fy - 2, fy - 2), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-DA14-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx + 1, fx - 2, fx - 2), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-DA15-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-DA15-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-DA16-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 2 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fy - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-DA16-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 2 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fx - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-DA20-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-DA20-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-DA21-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-DA21-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-DA22-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-DA22-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx > ey + 2) & (ex > fy + p) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy > ex + 2) & (ey > fx + p) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D1A1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D1A1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D1A2-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx == ey + 2) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D1A2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy == ex + 2) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D1C-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D1C-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D1D-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D1D-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D1E-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D1E-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D2-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx < ey) & (fx > fy) & (ex < fy + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy < ex) & (fy > fx) & (ey < fx + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D2A0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx > fy + 1) & (fx < ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D2A0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy > fx + 1) & (fy < ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D2A1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx == fy + 1) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D2A1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy == fx + 1) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D2B0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx < ey) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D2B0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy < ex) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D2B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx < ey) & (fx == fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D2B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy < ex) & (fy == fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D2AB0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx < ey) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex - 1, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D2AB0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy < ex) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey - 1, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D2AB1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx < ey) & (fx == fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex - 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D2AB1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy < ex) & (fy == fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey - 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D2C-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx == ey) & (ex < fy + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D2C-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy == ex) & (ey < fx + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D2D-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx == fy + 1) & (ex > fy + 3) & (ex < fy + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D2D-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy == fx + 1) & (ey > fx + 3) & (ey < fx + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D2CD-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx == ey) & (ex > fy + 3) & (ex < fy + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D2CD-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy == ex) & (ey > fx + 3) & (ey < fx + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D2BC-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, fx - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D2BC-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, fy - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D2BCD-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ex - (p + 1), ex - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D2BCD-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ey - (p + 1), ey - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D2E-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx < ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D2E-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy < ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D2CE0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + p) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D2CE0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + p) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D2CE1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + p) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fy, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D2CE1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + p) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fx, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D2F1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D2F1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D2F2-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D2F2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D3-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx < ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D3-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy < ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D3A-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx == ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D3A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy == ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D3B-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx < ey) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D3B-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy < ex) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D3AB-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 2, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D3AB-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 2, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D4-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D4-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D4A-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D4A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D4AB-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D4AB-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D4AC-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D4AC-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D4AD0-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (fx > fy + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D4AD0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy == ex + 1) & (fy > fx + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-MM01-D4AD1-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (fx == fy + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-MM01-D4AD1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (fy == ex + 1) & (fy == fx + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-MM01-DB-X",
        (CLASS_X == TWO1) & (CLASS_Y == MM01) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-MM01-DB-Y",
        (CLASS_Y == TWO1) & (CLASS_X == MM01) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
