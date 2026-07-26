function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
    ::Val{MM10},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ONE0-MM10-SA0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx > fy) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fy - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-SA0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy > fx) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fx - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-SA1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx > fy) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-SA1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy > fx) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-SA20-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-SA20-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-SA21-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-SA21-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-SA22-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-SA22-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-SA4-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 < fy) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-SA4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 < fx) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-SA5-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 2 < fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-SA5-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 2 < fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-SA6-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 2 == fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-SA6-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 2 == fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx < ey) & (fx > fy) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fy - 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy < ex) & (fy > fx) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fx - 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S1A-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fy, fy - 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S1A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fx, fx - 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S1B-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx < ey) & (fx > fy) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S1B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy < ex) & (fy > fx) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S1AB-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, fy),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S1AB-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, fx),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S1C0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S1C0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S1C1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx == fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy - 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S1C1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy == fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx - 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S1C2-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx == fy) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S1C2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy == fx) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S2-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx + 1 < fy) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy + 1 < fx) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S2A0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx + 2 < fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S2A0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy + 2 < fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S2A1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx + 2 == fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S2A1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy + 2 == fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex > fy + (p + 1)) & (fx < ey) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey > fx + (p + 1)) & (fy < ex) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3A-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == fy + (p + 1)) & (fx < ey) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == fx + (p + 1)) & (fy < ex) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3B0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex > ey + 3) & (fx < ey) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3B0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey > ex + 3) & (fy < ex) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3B1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex == ey + 3) & (fx < ey) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3B1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey == ex + 3) & (fy < ex) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3C-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3CB0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + p) & (ex > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy + 1, ex + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3CB0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + p) & (ey > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx + 1, ey + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3CB1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + p) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy + 1, ex + 1),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3CB1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + p) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx + 1, ey + 1),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3CE0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, ex + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3CE0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, ey + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3CE1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, ex + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3CE1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, ey + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3CF-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fy, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3CF-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fx, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3D-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex > fy + (p + 1)) & (fx < ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3D-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey > fx + (p + 1)) & (fy < ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3DA-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == fy + (p + 1)) & (fx < ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, ex - p, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3DA-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == fx + (p + 1)) & (fy < ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, ey - p, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3DB0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex > ey + 3) & (fx < ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3DB0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey > ex + 3) & (fy < ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3DB1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex == ey + 3) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3DB1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey == ex + 3) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3E00-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx < ey) & (fx > fy + 1) & (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3E00-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy < ex) & (fy > fx + 1) & (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3E01-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx < ey) & (fx > fy + 1) & (ex == fy + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3E01-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy < ex) & (fy > fx + 1) & (ey == fx + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3E10-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3E10-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == fx + 1) & (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3E11-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (ex == fy + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3E11-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == fx + 1) & (ey == fx + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3F0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx < ey) & (fx > fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3F0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy < ex) & (fy > fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3F1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3F1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S3F2-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S3F2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S4-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx > ey) & (ex > fy + p) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy > ex) & (ey > fx + p) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S4B0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, ey),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S4B0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, ex),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S4B10-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, ey),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S4B10-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, ex),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S4B11-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, ey),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S4B11-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, ex),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S4C0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, ey),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S4C0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, ex),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S4C1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, ey),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S4C1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, ex),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S4D0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S4D0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S4D1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S4D1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S5-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S5-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-S5A-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-S5A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-SB1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-SB1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-SB20-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-SB20-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-SB21-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-SB21-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

end
