function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM01},
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

    checker("SELTZO-TwoSum-MM01-ONE0-SE0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx < fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fy, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-SE0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy < fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fx, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-SE1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx > fy + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-SE1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy > fx + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-SE2-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx == fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-SE2-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy == fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-SE3-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-SE3-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-SE40-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx > fy + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-SE40-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy > fx + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-SE41-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx == fy + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-SE41-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy == fx + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-SE5-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 1 < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fy, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-SE5-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 1 < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fx, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-SE6-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 1 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fy, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-SE6-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 1 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fx, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-SE7-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx + 1, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-SE7-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex) & (fy == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy + 1, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx + 1 < ey) & (fx < fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey > ex) & (fy + 1 < ex) & (fy < fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S1B0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx + 1 < ey) & (fx < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S1B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey > ex) & (fy + 1 < ex) & (fy < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S1B1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx + 1 < ey) & (fx == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S1B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey > ex) & (fy + 1 < ex) & (fy == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S2-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx < ey) & (fx > fy + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S2-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey > ex) & (fy < ex) & (fy > fx + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S2A-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S2A-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey > ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S2B-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex > ey) & (fx < ey) & (fx > fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S2B-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey > ex) & (fy < ex) & (fy > fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S2C-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 2, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S2C-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 2, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S2BC-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, ey - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S2BC-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, ex - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S3-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx < ey) & (fx > fy + 2) & (ex > fy + (p - 1)) & (ex < fx + (p - 3)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S3-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy < ex) & (fy > fx + 2) & (ey > fx + (p - 1)) & (ey < fy + (p - 3)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S3C-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex == fy + (p - 1)) & (ex < fx + (p - 3)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S3C-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy < ex) & (ey == fx + (p - 1)) & (ey < fy + (p - 3)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S3D-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx < ey) & (fx > fy + 2) & (ex > fy + (p - 1)) & (ex < fx + (p - 3)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S3D-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy < ex) & (fy > fx + 2) & (ey > fx + (p - 1)) & (ey < fy + (p - 3)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S3CD-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == fy + (p - 1)) & (ex < fx + (p - 3)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S3CD-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == fx + (p - 1)) & (ey < fy + (p - 3)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S3A-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex > fy + (p - 1)) & (ex < fx + (p - 3)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, ey - 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S3A-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex) & (ey > fx + (p - 1)) & (ey < fy + (p - 3)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, ex - 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S3AC-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, ey - 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S3AC-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, ex - 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S3AD-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex > fy + (p - 1)) & (ex < fx + (p - 3)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, ey - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S3AD-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex) & (ey > fx + (p - 1)) & (ey < fy + (p - 3)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, ex - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S3B0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx < ey) & (fx > fy + 2) & (ex == fx + (p - 3)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S3B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy < ex) & (fy > fx + 2) & (ey == fy + (p - 3)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S3B0D-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx < ey) & (fx > fy + 2) & (ex == fx + (p - 3)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S3B0D-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy < ex) & (fy > fx + 2) & (ey == fy + (p - 3)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S3B1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx < ey) & (fx == fy + 2) & (ex == fx + (p - 3)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S3B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy < ex) & (fy == fx + 2) & (ey == fy + (p - 3)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S3B1D-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == fy + 2) & (ex == fx + (p - 3)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S3B1D-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == fx + 2) & (ey == fy + (p - 3)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S3AB0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey) & (fx > fy + 2) & (ex == fx + (p - 3)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S3AB0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex) & (fy > fx + 2) & (ey == fy + (p - 3)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S3AB0D-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == fx + (p - 3)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S3AB0D-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == fy + (p - 3)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S3AB1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey) & (fx == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S3AB1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex) & (fy == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S4A-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S4A-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S4B0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx > ey + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S4B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy > ex + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S4B1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S4B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S4AB-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S4AB-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S5-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx > ey + 2) & (ex > fy + p) & (ex < ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S5-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy > ex + 2) & (ey > fx + p) & (ey < ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S5C-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx > ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S5C-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy > ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S5D-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx > ey + 2) & (ex > fy + p) & (ex < ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S5D-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy > ex + 2) & (ey > fx + p) & (ey < ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S5A-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S5A-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S5AC-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S5AC-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S5AD-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ex > fy + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S5AD-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ey > fx + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S5B-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, ey),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S5B-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, ex),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S5BC-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, ey),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S5BC-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, ex),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-S5BD-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > fy + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, ey),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-S5BD-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > fx + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, ex),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-SB0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx > ey + 3) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-SB0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy > ex + 3) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-SB0D-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx > ey + 3) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-SB0D-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy > ex + 3) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-SB1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx == ey + 3) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-SB1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy == ex + 3) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-ONE0-SB1D-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx == ey + 3) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-ONE0-SB1D-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy == ex + 3) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
