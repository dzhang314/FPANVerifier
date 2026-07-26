function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM01},
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

    checker("SELTZO-TwoSum-MM01-R0R1-SE0-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx < fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-SE0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex) & (fy < fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-SE1-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-SE1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex) & (fy < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-SE2-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, ex),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-SE2-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, ey),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-SE3-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - 1, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-SE3-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - 1, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S1-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex > ey) & (fx < fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey > ex) & (fy < fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S1A-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex > ey) & (fx < fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S1A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey > ex) & (fy < fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S1B-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex + 1 > ey) & (fx == fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S1B-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey + 1 > ex) & (fy == fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S1AB-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex > ey) & (fx == fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S1AB-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey > ex) & (fy == fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S1C-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex + 1 > ey) & (fx < ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S1C-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey + 1 > ex) & (fy < ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S2-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex + 1 > ey) & (fx + 1 < ey) & (fx > fy + 2) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S2-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey + 1 > ex) & (fy + 1 < ex) & (fy > fx + 2) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S2A-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (fx > fy + 2) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S2A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (fy > fx + 2) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S2B-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex > ey) & (fx + 1 < ey) & (fx > fy + 3) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S2B-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey > ex) & (fy + 1 < ex) & (fy > fx + 3) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S2AB-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (fx > fy + 3) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S2AB-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (fy > fx + 3) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S2BC-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex > ey) & (fx + 1 < ey) & (fx == fy + 3) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S2BC-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey > ex) & (fy + 1 < ex) & (fy == fx + 3) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S2ABC-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (fx == fy + 3) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S2ABC-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (fy == fx + 3) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S3-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx + 1 < ey) & (ex > fy + (p - 1)) & (ex < fx + (p - 3)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S3-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy + 1 < ex) & (ey > fx + (p - 1)) & (ey < fy + (p - 3)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S3A-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex > fy + (p - 1)) & (ex < fx + (p - 3)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S3A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey > fx + (p - 1)) & (ey < fy + (p - 3)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S3B-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx + 1 < ey) & (ex > fy + (p - 1)) & (ex == fx + (p - 3)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S3B-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy + 1 < ex) & (ey > fx + (p - 1)) & (ey == fy + (p - 3)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S3AB-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex > fy + (p - 1)) & (ex == fx + (p - 3)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S3AB-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey > fx + (p - 1)) & (ey == fy + (p - 3)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S3C-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex + 1 > ey) & (fx + 1 < ey) & (ex < fx + (p - 3)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S3C-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey + 1 > ex) & (fy + 1 < ex) & (ey < fy + (p - 3)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S3AC-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex < fx + (p - 3)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S3AC-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey < fy + (p - 3)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S3BC-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex > ey) & (fx + 1 < ey) & (ex == fx + (p - 3)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S3BC-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey > ex) & (fy + 1 < ex) & (ey == fy + (p - 3)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S3ABC-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex == fx + (p - 3)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S3ABC-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey == fy + (p - 3)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S4-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex < ey + (p - 1)) & (fx > ey + 1) & (ex > fy + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S4-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey < ex + (p - 1)) & (fy > ex + 1) & (ey > fx + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S4C-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex < ey + (p - 1)) & (fx > ey + 1) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S4C-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey < ex + (p - 1)) & (fy > ex + 1) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S4D0-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx > ey + 1) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S4D0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy > ex + 1) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S4D1-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey + 2) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S4D1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex + 2) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S4D2-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx > ey + 2) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S4D2-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy > ex + 2) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S4A0-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S4A0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S4A1-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S4A1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S4A2-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S4A2-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S4A3-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S4A3-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S4B0-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex < fy + p) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S4B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex) & (ey < fx + p) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S4B1-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex < fy + p) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 3, fx - 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S4B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex) & (ey < fx + p) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 3, fy - 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S4B2-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S4B2-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S4B3-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex == fy + p) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 2, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S4B3-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex) & (ey == fx + p) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 2, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S4B4-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex == fy + p) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S4B4-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex) & (ey == fx + p) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S4B5-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex > fy + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S4B5-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex) & (ey > fx + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-S4B6-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (fx == ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-S4B6-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (fy == ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-SB10-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ex < fx + (p - 3)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-SB10-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ey < fy + (p - 3)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-SB11-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ex == fx + (p - 3)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-SB11-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ey == fy + (p - 3)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-SB12-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ex < fx + (p - 3)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-SB12-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ey < fy + (p - 3)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-SB13-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ex == fx + (p - 3)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-SB13-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ey == fy + (p - 3)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-SB20-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ex == fx + (p - 3)) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-SB20-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ey == fy + (p - 3)) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-SB21-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ex == fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 3), fy - (p - 3)))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-SB21-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ey == fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 3), fx - (p - 3)))
    end

    checker("SELTZO-TwoSum-MM01-R0R1-SB22-X",
        (CLASS_X == MM01) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ex == fx + (p - 3)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-MM01-R0R1-SB22-Y",
        (CLASS_Y == MM01) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ey == fy + (p - 3)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
