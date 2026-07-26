function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO0},
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

    checker("SELTZO-TwoSum-TWO0-ONE0-S1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx > ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy > ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx < fy + 1) & (ex > ey + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy < fx + 1) & (ey > ex + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S2E-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx < fy + 1) & (ex == ey + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey + 2, ey, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S2E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy < fx + 1) & (ey == ex + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex + 2, ex, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S2B0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (ex > ey + 1) & (fx + 1 < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S2B0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (ey > ex + 1) & (fy + 1 < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S2B0E-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (ex == ey + 1) & (fx + 1 < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 2, ey, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S2B0E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (ey == ex + 1) & (fy + 1 < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 2, ex, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S2B11-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == fy) & (ex > ey + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S2B11-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == fx) & (ey > ex + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S2B12-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx + 1 == fy) & (ex > ey + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S2B12-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy + 1 == fx) & (ey > ex + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S2B1E1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == fy) & (ex == ey + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 2, ey, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S2B1E1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == fx) & (ey == ex + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 2, ex, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S2B1E2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx + 1 == fy) & (ex == ey + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 2, ey, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S2B1E2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy + 1 == fx) & (ey == ex + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 2, ex, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S3-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx < ey) & (fx > fy + 1) & (ex < fy + (p - 2)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy < ex) & (fy > fx + 1) & (ey < fx + (p - 2)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S3E-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx > fy + 1) & (ex < fy + (p - 2)) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey + 2, ey, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S3E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy > fx + 1) & (ey < fx + (p - 2)) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex + 2, ex, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S3A0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == fy + 1) & (ex > ey + 1) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S3A0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == fx + 1) & (ey > ex + 1) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S3A0E-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == fy + 1) & (ex == ey + 1) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey + 2, ey, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S3A0E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == fx + 1) & (ey == ex + 1) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex + 2, ex, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S3A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey + 1) & (ex < ey + (p - 3)) & (fx + 1 == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S3A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex + 1) & (ey < ex + (p - 3)) & (fy + 1 == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S3A1E-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == fy + 1) & (ex == ey + 1) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey + 2, ey - 1, ey),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S3A1E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == fx + 1) & (ey == ex + 1) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex + 2, ex - 1, ex),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S3A2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (ex < gx + (p - 3)) & (fx == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fy - 1, fy),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S3A2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (ey < gy + (p - 3)) & (fy == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fx - 1, fx),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S3B0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx < ey) & (ex == fy + (p - 2)) & (ex > ey + 1) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S3B0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy < ex) & (ey == fx + (p - 2)) & (ey > ex + 1) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S3B0E-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (ex == fy + (p - 2)) & (ex == ey + 1) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 2, ey, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S3B0E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (ey == fx + (p - 2)) & (ey == ex + 1) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 2, ex, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S3B1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx == fy + 2) & (fx < ey) & (ex == gx + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S3B1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy == fx + 2) & (fy < ex) & (ey == gy + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S3B1E-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (ex == fy + (p - 2)) & (ex == ey + 1) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 2, ey, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S3B1E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (ey == fx + (p - 2)) & (ey == ex + 1) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 2, ex, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S3B2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx == fy + 3) & (fx < ey) & (ex == fx + (p - 3)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S3B2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy == fx + 3) & (fy < ex) & (ey == fy + (p - 3)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S3C0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey) & (ex < fy + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, fy),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S3C0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex) & (ey < fx + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, fx),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S3BC0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey) & (ex == fy + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 2, fy + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S3BC0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex) & (ey == fx + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 2, fx + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S3BC1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey) & (ex == fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 3, ex + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S3BC1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex) & (ey == fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 3, ey + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx < ey) & (ex > fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy < ex) & (ey > fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4E-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx < ey) & (ex == fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy < ex) & (ey == fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4F-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx < ey) & (ex == fy + p) & (ex < fx + (p - 3)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4F-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy < ex) & (ey == fx + p) & (ey < fy + (p - 3)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4FD-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx < ey) & (ex == fy + p) & (ex < fx + (p - 3)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey + 3, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, ey - (p + p - 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4FD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy < ex) & (ey == fx + p) & (ey < fy + (p - 3)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex + 3, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, ex - (p + p - 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4C-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx < ey) & (ex == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy < ex) & (ey == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4A-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey) & (ex > fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, ey - 1),
            SELTZORange(sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex) & (ey > fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, ex - 1),
            SELTZORange(sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4AE-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey) & (ex == fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, ey - 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4AE-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex) & (ey == fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, ex - 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4AF-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey) & (ex == fy + p) & (ex < fx + (p - 3)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, ey - 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4AF-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex) & (ey == fx + p) & (ey < fy + (p - 3)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, ex - 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4AFD-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey) & (ex == fy + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey + 3, ey - 2, ey - 1),
            SELTZORange(sy, 0, 0, fy - 1, ey - (p + p - 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4AFD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex) & (ey == fx + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex + 3, ex - 2, ex - 1),
            SELTZORange(sx, 0, 0, fx - 1, ex - (p + p - 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4AC-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey) & (ex == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, ey - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4AC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex) & (ey == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, ex - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4B0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx < ey) & (ex > fy + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4B0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy < ex) & (ey > fx + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4B0E-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx < ey) & (ex == fy + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4B0E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy < ex) & (ey == fx + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4B0FD-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (ex == fy + p) & (ex == fx + (p - 3)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 3, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy - 1, ey - (p + p - 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4B0FD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (ey == fx + p) & (ey == fy + (p - 3)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 3, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx - 1, ex - (p + p - 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4B1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx < ey) & (fx == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4B1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy < ex) & (fy == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4AB0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey) & (ex > fy + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 2, ex + 1),
            SELTZORange(sy, 1, 0, ey - 3, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4AB0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex) & (ey > fx + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 2, ey + 1),
            SELTZORange(sx, 1, 0, ex - 3, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4AB0E-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey) & (ex == fy + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 2, ex + 1),
            SELTZORange(sy, 0, 0, ey - 3, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4AB0E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex) & (ey == fx + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 2, ey + 1),
            SELTZORange(sx, 0, 0, ex - 3, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4AB0F-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 2, ex + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4AB0F-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 2, ey + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S4AB1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey) & (fx == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, ex + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S4AB1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex) & (fy == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, ey + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S5A-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S5A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S5B0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S5B0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S5AB-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S5AB-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S6-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx > ey + 2) & (ex > fy + p) & (ex < ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S6-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy > ex + 2) & (ey > fx + p) & (ey < ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S6A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S6A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S6A2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey + 2) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S6A2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex + 2) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S6C-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S6C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S6BC0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey + 1) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S6BC0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex + 1) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S6BC1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey + 1) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 1, 0, ey - 3, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S6BC1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex + 1) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 1, 0, ex - 3, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S6D-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx > ey + 2) & (ex < ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S6D-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy > ex + 2) & (ey < ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S6AD1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S6AD1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-S6AD2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == ey + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 1, 0, fy, ey - p, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-S6AD2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == ex + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 1, 0, fx, ex - p, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-SB0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (ex == ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-SB0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (ey == ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-SB1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey) & (ex == ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-SB1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex) & (ey == ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

end
