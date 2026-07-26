function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
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

    checker("SELTZO-TwoSum-R0R1-R1R0-S1-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (fx + 1 > ey) & (ex < fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-S1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (fy + 1 > ex) & (ey < fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-S2-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex > fy + (p + 1)) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-S2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey > fx + (p + 1)) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-S3-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex > fy + (p + 1)) & (ex < ey + p) & (fx > ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-S3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey > fx + (p + 1)) & (ey < ex + p) & (fy > ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-S4-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (ex < fy + p) & (fx < ey) & (fx > fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-S4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (ey < fx + p) & (fy < ex) & (fy > fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-SA10-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (ex < fy + (p - 1)) & (fx > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-SA10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (ey < fx + (p - 1)) & (fy > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-SA11-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (ey == fy + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-SA11-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (ex == fx + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-SA12-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx > fy + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fy + 2),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-SA12-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy > fx + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fx + 2),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-SA13-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - (p - 1), ex), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-SA13-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - (p - 1), ey), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-SA14-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx + (p - 2) == ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fy + 1, ex + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-SA14-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy + (p - 2) == ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fx + 1, ey + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-SA15-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (ex == fy + (p - 1)) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, ex + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-SA15-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (ey == fx + (p - 1)) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, ey + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-SA20-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < ey) & (fx > fy) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-SA20-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < ex) & (fy > fx) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-SA21-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < fy + (p - 2)) & (ey == fy + (p - 2)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-SA21-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < fx + (p - 2)) & (ex == fx + (p - 2)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-SA22-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == ey) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-SA22-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == ex) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-SA23-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (ex == fy + (p + 1)) & (fx > fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 3),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-SA23-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (ey == fx + (p + 1)) & (fy > fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 3),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-SA24-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == fy + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-SA24-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == fx + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-SA25-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy + 2, fy + 3),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-SA25-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx + 2, fx + 3),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-SA26-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx + (p - 3) == ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-SA26-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy + (p - 3) == ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-S1A-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < fy + (p - 2)) & (ex == fx + 2) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-S1A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < fx + (p - 2)) & (ey == fy + 2) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-S1B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (fx > ey) & (fx < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx + 1, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-S1B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == fx + p) & (fy > ex) & (fy < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy + 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-S1B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (fx > ey) & (fx == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-S1B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == fx + p) & (fy > ex) & (fy == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-S1B2-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (fx == ey) & (fx == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy + 1, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-S1B2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == fx + p) & (fy == ex) & (fy == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx + 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-S2A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey) & (ex == fy + (p + 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy + 3),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-S2A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex) & (ey == fx + (p + 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx + 3),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-S2A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == fy + (p + 1)) & (fx == fy + 2) & (fx + (p - 3) > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-S2A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == fx + (p + 1)) & (fy == fx + 2) & (fy + (p - 3) > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-S2B-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex > fy + (p + 1)) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx + 2),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-S2B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey > fx + (p + 1)) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy + 2),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-S3A-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (fx < ey + (p - 2)) & (fx > fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-S3A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (fy < ex + (p - 2)) & (fy > fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-S3B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == fy + (p + 1)) & (fx + 1 > ey) & (ey > fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fy + 3),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-S3B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == fx + (p + 1)) & (fy + 1 > ex) & (ex > fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fx + 3),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-S3AB-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex < ey + (p - 1)) & (ex == fy + (p + 1)) & (fx > ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 3),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-S3AB-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey < ex + (p - 1)) & (ey == fx + (p + 1)) & (fy > ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 3),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-S4A-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex > ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-S4A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey > ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-S4B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (ex == fy + p) & (fx < ey + 1) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-S4B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (ey == fx + p) & (fy < ex + 1) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-S4B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (fx + (p - 3) > ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-S4B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == fx + p) & (fy + (p - 3) > ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-SB10-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + (p - 1)) & (ex == fy + (p + 1)) & (fx > fy + 2) & (fx < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-SB10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + (p - 1)) & (ey == fx + (p + 1)) & (fy > fx + 2) & (fy < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-SB11-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + (p - 1)) & (fx == fy + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-SB11-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + (p - 1)) & (fy == fx + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-SB20-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + p) & (fx < ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-SB20-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + p) & (fy < ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-SB21-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-SB21-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
