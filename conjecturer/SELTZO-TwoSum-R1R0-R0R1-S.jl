function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R1R0},
    ::Val{R0R1},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R1R0-R0R1-S1-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex < ey + (p - 1)) & (ex > fy + p) & (fx > ey) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey < ex + (p - 1)) & (ey > fx + p) & (fy > ex) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S3-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex > ey) & (fx < fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey > ex) & (fy < fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S4-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex + 1 > ey) & (fx + 1 < ey) & (ex < fy + (p - 1)) & (fx > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S4-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey + 1 > ex) & (fy + 1 < ex) & (ey < fx + (p - 1)) & (fy > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S5-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex > fy + (p - 1)) & (fx + 1 < ey) & (ey < fy + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S5-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey > fx + (p - 1)) & (fy + 1 < ex) & (ex < fx + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-SE0-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx < fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-SE0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy < fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-SE1-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, ex),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-SE1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, ey),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-SE2-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey) & (ex == fx + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx + 2),
            SELTZORange(sy, 0, 0, fx, fx - p, fx))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-SE2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex) & (ey == fy + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy + 2),
            SELTZORange(sx, 0, 0, fy, fy - p, fy))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-SE3-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey) & (ex == fy + (p - 2)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, ex),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-SE3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex) & (ey == fx + (p - 2)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, ey),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S1A0-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex > fy + p) & (fx < fy + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(sy, 1, 0, fy, fx - p, fx - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S1A0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy == ex) & (ey > fx + p) & (fy < fx + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(sx, 1, 0, fx, fy - p, fy - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S1A1-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex < fx + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S1A1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy == ex) & (ey < fy + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S1B-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx > fy + (p - 1)) & (ex < ey + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S1B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy > fx + (p - 1)) & (ey < ex + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S2A0-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx > ey) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S2A0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy > ex) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S2B1-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex < ey + (p - 2)) & (fx == fy + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy, fy + 1),
            SELTZORange(~sy, 0, 0, fy - (p - 3), fy - (p + p - 3), fy - (p - 3)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S2B1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey < ex + (p - 2)) & (fy == fx + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx, fx + 1),
            SELTZORange(~sx, 0, 0, fx - (p - 3), fx - (p + p - 3), fx - (p - 3)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S2AB-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex < ey + (p - 2)) & (fx == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fy + 2),
            SELTZORange(~sy, 0, 0, fx - (p - 1), fx - (p + p - 1), fx - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S2AB-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey < ex + (p - 2)) & (fy == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fx + 2),
            SELTZORange(~sx, 0, 0, fy - (p - 1), fy - (p + p - 1), fy - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S3A-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex > ey) & (fx < fy) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S3A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey > ex) & (fy < fx) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S3B-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex > ey) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S3B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey > ex) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S4A-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S4A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S5A0-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == fy + (p - 1)) & (fx + 1 < ey) & (ex < fx + (p - 2)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S5A0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == fx + (p - 1)) & (fy + 1 < ex) & (ey < fy + (p - 2)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S5A1-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == fy + (p - 1)) & (fx == fy + 1) & (fx + 1 < ey) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S5A1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == fx + (p - 1)) & (fy == fx + 1) & (fy + 1 < ex) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S5B0-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex < ey + (p - 2)) & (ex > fy + (p - 1)) & (ex == fx + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S5B0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey < ex + (p - 2)) & (ey > fx + (p - 1)) & (ey == fy + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S5B1-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex < ey + (p - 2)) & (fx + (p - 1) > ey) & (ex == fx + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S5B1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey < ex + (p - 2)) & (fy + (p - 1) > ex) & (ey == fy + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S5C0-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex > fy + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 1, 0, fy, fx - (p - 1), fx - (p - 2)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S5C0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey > fx + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 1, 0, fx, fy - (p - 1), fy - (p - 2)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S5D0-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex > fy + (p - 2)) & (fx < fy + (p - 2)) & (ey == fy + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S5D0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey > fx + (p - 2)) & (fy < fx + (p - 2)) & (ex == fx + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S5D1-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx == fy + (p - 2)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S5D1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy == fx + (p - 2)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-S5AC-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fy + 1, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-S5AC-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fx + 1, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-SB10-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 2)) & (ex == fy + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy - (p - 3), fy - (p + p - 3), fy - (p - 3)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-SB10-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + (p - 2)) & (ey == fx + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx - (p - 3), fx - (p + p - 3), fx - (p - 3)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-SB11-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 2)) & (fx == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fy, ex),
            SELTZORange(~sy, 0, 0, fy - (p - 3), fy - (p + p - 3), fy - (p - 3)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-SB11-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + (p - 2)) & (fy == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fx, ey),
            SELTZORange(~sx, 0, 0, fx - (p - 3), fx - (p + p - 3), fx - (p - 3)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-SB20-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (fx > ey) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-SB20-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (fy > ex) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-SB21-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (fx > ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-SB21-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (fy > ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-SB22-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ex == fx + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, ex),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-SB22-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ey == fy + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, ey),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-SB23-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (fx == ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, ex),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-SB23-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (fy == ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, ey),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-SB31-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (fx == ey + 1) & (fx > fy + 3) & (fx < fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, ex),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-SB31-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + p) & (fy == ex + 1) & (fy > fx + 3) & (fy < fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, ey),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-SB34-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ex == fx + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, ex),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-SB34-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ey == fy + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, ey),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-R1R0-R0R1-SB36-X",
        (CLASS_X == R1R0) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex == fy + (p + 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, ex),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 3), fy - (p - 3)))
    end
    checker("SELTZO-TwoSum-R1R0-R0R1-SB36-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey == fx + (p + 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, ey),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 3), fx - (p - 3)))
    end

end
