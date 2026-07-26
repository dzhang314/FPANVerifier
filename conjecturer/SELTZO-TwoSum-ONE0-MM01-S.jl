function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
    ::Val{MM01},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ONE0-MM01-S1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx + 1 < fy) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey > ex) & (fy + 1 < fx) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S1A0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx + 2 < fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S1A0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey > ex) & (fy + 2 < fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S1A1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx + 2 == fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 3),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S1A1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey > ex) & (fy + 2 == fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 3),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S1B-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S1B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey > ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S2-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx + 1 > fy) & (fx < ey) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey > ex) & (fy + 1 > fx) & (fy < ex) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S2A-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx > fy + 1) & (fx < ey) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S2A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey > ex) & (fy > fx + 1) & (fy < ex) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S2AE-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx == fy + 1) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S2AE-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey > ex) & (fy == fx + 1) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S2B-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx > fy + 1) & (fx < ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S2B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy > fx + 1) & (fy < ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S2C-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx > fy + 1) & (fx < ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S2C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy > fx + 1) & (fy < ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S2BE-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S2BE-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S2CE-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S2CE-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S2F-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S2F-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S2AD-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx == fy) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S2AD-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey > ex) & (fy == fx) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S2AF-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fy + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S2AF-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fx + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S2BD-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S2BD-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S2BF-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S2BF-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S2BG-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S2BG-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S2CF-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S2CF-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S2CG-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S2CG-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S2G-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S2G-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S3-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex > fy + (p + 1)) & (fx < ey) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(sy, 1, 0, ex - p, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey > fx + (p + 1)) & (fy < ex) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(sx, 1, 0, ey - p, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S3E-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex == fy + (p + 1)) & (fx < ey) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(sy, 0, 0, ex - p, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S3E-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey == fx + (p + 1)) & (fy < ex) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(sx, 0, 0, ey - p, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S3A-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex == fy + p) & (fx < ey) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S3A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey == fx + p) & (fy < ex) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S3B-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S3B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S3AB-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - (p - 1), ex - (p - 2)),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S3AB-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - (p - 1), ey - (p - 2)),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S3C-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex > fy + (p + 1)) & (fx < ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, ex - p, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S3C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey > fx + (p + 1)) & (fy < ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, ey - p, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S3CE-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex == fy + (p + 1)) & (fx < ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ex - p, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S3CE-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey == fx + (p + 1)) & (fy < ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ey - p, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S3AC-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (ex == fy + p) & (fx < ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S3AC-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (ey == fx + p) & (fy < ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S3D-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex > fy + (p + 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(sy, 1, 0, ex - p, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S3D-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex) & (ey > fx + (p + 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(sx, 1, 0, ey - p, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S3DE-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p + 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(sy, 0, 0, ex - p, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S3DE-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p + 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(sx, 0, 0, ey - p, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S3AD-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S3AD-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S3CD-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex > fy + (p + 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 1, 0, ex - p, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S3CD-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex) & (ey > fx + (p + 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 1, 0, ey - p, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S3CDE-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p + 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, ex - p, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S3CDE-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p + 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, ey - p, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S3ACD-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S3ACD-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S4-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex > fy + p) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey > fx + p) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S4B-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S4B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S4C-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S4C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S4D-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S4D-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S4E-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S4E-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-MM01-S5-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-MM01-S5-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 1, fx - 1), pos_zero)
    end

end
