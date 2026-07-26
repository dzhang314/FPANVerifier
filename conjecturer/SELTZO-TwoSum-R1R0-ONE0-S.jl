function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R1R0},
    ::Val{ONE0},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R1R0-ONE0-SE0-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 1 < fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fy, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-SE0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 1 < fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fx, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-SE1-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 2 < fy) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fy, fx + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-SE1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 2 < fx) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fx, fy + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-SE2-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 2 == fy) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fy, fy + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-SE2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 2 == fx) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fx, fx + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-SE3-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fy, fy + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-SE3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fx, fx + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-SE4-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 1 > fy) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx + 1, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-SE4-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 1 > fx) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy + 1, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-SE5-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx > fy) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx + 1, fy + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-SE5-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex) & (fy > fx) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy + 1, fx + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-SE6-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx == fy) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx + 1, fx + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-SE6-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex) & (fy == fx) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy + 1, fy + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-SA0-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx > fy) & (fx + 1 < ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-SA0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy > fx) & (fy + 1 < ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-SA1-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx + 1 == ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-SA1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy + 1 == ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-SA2-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx == fy) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 2),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-SA2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy == fx) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 2),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S1-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx + 1 < ey) & (ex < fy + (p - 2)) & (fx + 1 > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy + 1 < ex) & (ey < fx + (p - 2)) & (fy + 1 > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S1A-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx + 1 < ey) & (ex == fy + (p - 2)) & (fx + 1 > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S1A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy + 1 < ex) & (ey == fx + (p - 2)) & (fy + 1 > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S1B-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx + 1 == ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S1B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy + 1 == ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S1AB-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx + 1 == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S1AB-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy + 1 == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S1C-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S1C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S2-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx + 1 < fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy + 1 < fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S2A-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S2A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S2B-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx + 1 < fy) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S2B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy + 1 < fx) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S3-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex > fy + (p - 1)) & (ex < fx + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy < ex) & (ey > fx + (p - 1)) & (ey < fy + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S3A-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex > fy + (p - 1)) & (ex == fx + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S3A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy < ex) & (ey > fx + (p - 1)) & (ey == fy + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S3B-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex > fy + (p - 1)) & (ex < fx + (p - 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S3B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy < ex) & (ey > fx + (p - 1)) & (ey < fy + (p - 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S3AB-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex > fy + (p - 1)) & (ex == fx + (p - 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S3AB-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy < ex) & (ey > fx + (p - 1)) & (ey == fy + (p - 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S3C0-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex > ey + 1) & (ex == fy + (p - 1)) & (fx + 1 < ey) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S3C0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey > ex + 1) & (ey == fx + (p - 1)) & (fy + 1 < ex) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S3C1-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex > ey + 1) & (ex == fy + (p - 1)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S3C1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey > ex + 1) & (ey == fx + (p - 1)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S3AC0-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex > ey + 1) & (ex == fy + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S3AC0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey > ex + 1) & (ey == fx + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S4-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx > ey + 1) & (ex > fy + p) & (ex < ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S4-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy > ex + 1) & (ey > fx + p) & (ey < ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S4A-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > fy + p) & (ex < ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S4A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > fx + p) & (ey < ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S4B-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx > ey + 1) & (ex > fy + p) & (ex < ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S4B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy > ex + 1) & (ey > fx + p) & (ey < ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S4AB-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > fy + p) & (ex < ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S4AB-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > fx + p) & (ey < ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S4C-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex > fy + p) & (ex < ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S4C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy == ex) & (ey > fx + p) & (ey < ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S4BC-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex > fy + p) & (ex < ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S4BC-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy == ex) & (ey > fx + p) & (ey < ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S4D0-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx > ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S4D0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy > ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S4CD0-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S4CD0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S4BCD0-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == fy + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S4BCD0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == fx + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S4D1-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx > ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S4D1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy > ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-S4CD1-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-S4CD1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-SB0-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx > ey + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-SB0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy > ex + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-SB1-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx > ey + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-SB1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy > ex + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-SB2-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx == ey + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-SB2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy == ex + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R1R0-ONE0-SB3-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx == ey + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-ONE0-SB3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy == ex + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
