function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM01},
    ::Val{R1R0},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-MM01-R1R0-SE0-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx < fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, fy + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-SE0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex) & (fy < fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, fx + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-SE1-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx > fy + 2) & (ey < fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-SE1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex) & (fy > fx + 2) & (ex < fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-SE2-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx == fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-SE2-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex) & (fy == fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-SE3-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-SE3-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-SE4-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx > fy + 2) & (ey == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-SE4-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex) & (fy > fx + 2) & (ex == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-SE5-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx < fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, fy + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-SE5-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex) & (fy < fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, fx + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-SE7-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx == fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-SE7-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex) & (fy == fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S1-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx + 1 < ey) & (fx < fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex) & (fy + 1 < ex) & (fy < fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S1A-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx + 1 == ey) & (fx == fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S1A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex) & (fy + 1 == ex) & (fy == fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S1B0-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx + 1 < ey) & (fx < fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S1B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex) & (fy + 1 < ex) & (fy < fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S1B1-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx + 1 < ey) & (fx == fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S1B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex) & (fy + 1 < ex) & (fy == fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S1AB-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx + 1 == ey) & (fx == fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S1AB-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex) & (fy + 1 == ex) & (fy == fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S2-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx < ey) & (fx > fy + 2) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S2-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex) & (fy < ex) & (fy > fx + 2) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S2A-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx < ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S2A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex) & (fy < ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S2B-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx < ey) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S2B-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex) & (fy < ex) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S2C-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx > fy + 2) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S2C-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy == ex) & (fy > fx + 2) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S2AC-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S2AC-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S2BC-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 2, ey - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S2BC-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy == ex) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 2, ex - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S3-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx < ey) & (fx > fy + 3) & (ex > fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S3-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex) & (fy < ex) & (fy > fx + 3) & (ey > fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S3A-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx > fy + 3) & (ex > fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, ey - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S3A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy == ex) & (fy > fx + 3) & (ey > fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, ex - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S3B0-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx < ey) & (fx > fy + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S3B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex) & (fy < ex) & (fy > fx + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S3B1-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx < ey) & (fx == fy + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S3B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex) & (fy < ex) & (fy == fx + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S3AB0-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx > fy + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S3AB0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy == ex) & (fy > fx + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S3AB1-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx == ey) & (fx == fy + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S3AB1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy == ex) & (fy == fx + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S4A-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S4A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S4B-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx == ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S4B-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy == ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S4AB-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S4AB-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S5A-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx == ey + 2) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S5A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy == ex + 2) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM01-R1R0-S5B-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, ey),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM01-R1R0-S5B-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, ex),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM01-R1R0-SB-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx == ey + 3) & (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM01-R1R0-SB-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy == ex + 3) & (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
