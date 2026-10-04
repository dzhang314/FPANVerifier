function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
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

    checker("SELTZO-TwoSum-ONE0-R1R0-S1-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex > ey) & (ex < fy + (p - 1)) & (fx < fy + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey > ex) & (ey < fx + (p - 1)) & (fy < fx + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S1A0-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex > ey) & (ex < fy + (p - 2)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S1A0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey > ex) & (ey < fx + (p - 2)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S1A1-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex > ey) & (ex == fy + (p - 2)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S1A1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey > ex) & (ey == fx + (p - 2)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S1B-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S1B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey > ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S2-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex > ey) & (ex < fy + (p - 1)) & (fx > fy + 1) & (fx < ey) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey > ex) & (ey < fx + (p - 1)) & (fy > fx + 1) & (fy < ex) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S2A0-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex > ey) & (ex == fy + (p - 1)) & (fx < ey) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S2A0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey > ex) & (ey == fx + (p - 1)) & (fy < ex) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S2A0B-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex < ey + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S2A0B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey < ex + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S2A1-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex > ey) & (ex == fy + (p - 1)) & (fx < ey) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S2A1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey > ex) & (ey == fx + (p - 1)) & (fy < ex) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S2A1B-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex == ey + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S2A1B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey == ex + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S2B-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S2B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S3-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex > fy + (p + 1)) & (fx < ey) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(sy, 1, 0, ex - p, fy, fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey > fx + (p + 1)) & (fy < ex) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(sx, 1, 0, ey - p, fx, fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S3A0-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == fy + (p + 1)) & (fx < ey) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S3A0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == fx + (p + 1)) & (fy < ex) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S3A0B-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == fy + (p + 1)) & (fx < ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S3A0B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == fx + (p + 1)) & (fy < ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S3A0C-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex == fy + (p + 1)) & (ex < ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S3A0C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy == ex) & (ey == fx + (p + 1)) & (ey < ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S3A0BC-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex == fy + (p + 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S3A0BC-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy == ex) & (ey == fx + (p + 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S3A1-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (fx < ey) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S3A1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == fx + p) & (fy < ex) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S3A1B-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (fx < ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S3A1B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == fx + p) & (fy < ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S3A1C-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex == fy + p) & (ex < ey + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S3A1C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy == ex) & (ey == fx + p) & (ey < ex + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S3A1BC-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex == fy + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S3A1BC-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy == ex) & (ey == fx + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S3B-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex > fy + (p + 1)) & (fx < ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, ex - p, fy, fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S3B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey > fx + (p + 1)) & (fy < ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, ey - p, fx, fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S3C-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex > fy + (p + 1)) & (ex < ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(sy, 1, 0, ex - p, fy, fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S3C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy == ex) & (ey > fx + (p + 1)) & (ey < ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(sx, 1, 0, ey - p, fx, fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S3BC-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex > fy + (p + 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 1, 0, ex - p, fy, fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S3BC-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy == ex) & (ey > fx + (p + 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 1, 0, ey - p, fx, fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S4-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx > ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy > ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S4A-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S4A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S4B-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S4B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S4AB-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ex - (p - 1), ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S4AB-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ey - (p - 1), ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S5-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx > ey + 1) & (ex > fy + (p + 1)) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S5-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy > ex + 1) & (ey > fx + (p + 1)) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S5A0-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx > ey + 1) & (ex == fy + (p + 1)) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, ex - (p - 2)),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S5A0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy > ex + 1) & (ey == fx + (p + 1)) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, ey - (p - 2)),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S5A0B-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex == fy + (p + 1)) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - (p - 1), ex - (p - 2)),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S5A0B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey == fx + (p + 1)) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - (p - 1), ey - (p - 2)),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S5A1-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx > ey) & (ex == fy + (p + 1)) & (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S5A1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy > ex) & (ey == fx + (p + 1)) & (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-S5B-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-S5B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-SB-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-SB-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
