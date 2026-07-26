function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM01},
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

    checker("SELTZO-TwoSum-MM01-MM10-SE0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, ex),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-SE0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, ey),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S1A0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S1A0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S1A10-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx > ey + 2) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - 3, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S1A10-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy > ex + 2) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - 3, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S1A11-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey + 2) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 0, 0, ey - 3, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S1A11-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex + 2) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 0, 0, ex - 3, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S1B-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S1B-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S1C-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S1C-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S1D0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S1D0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S1D1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S1D1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S1AD00-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S1AD00-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S1AD01-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fy + 2),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S1AD01-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fx + 2),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S1AD10-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + p) & (ey > fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 2, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S1AD10-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + p) & (ex > fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 2, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S1AD11-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 2, fy + 2),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S1AD11-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 2, fx + 2),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S1AD12-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey) & (fx == fy + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fy, ex),
            SELTZORange(~sy, 0, 0, gx - 3, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S1AD12-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex) & (fy == fx + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fx, ey),
            SELTZORange(~sx, 0, 0, gy - 3, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S1BD0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S1BD0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S1BD10-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey) & (fx > fy + 2) & (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 2, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S1BD10-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex) & (fy > fx + 2) & (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 2, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S1BD11-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey - 2, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S1BD11-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex - 2, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S1BD12-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey) & (fx == fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey - 3, ex),
            SELTZORange(sy, 1, 0, fy - 2, fy - (p - 2), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S1BD12-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex) & (fy == fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex - 3, ey),
            SELTZORange(sx, 1, 0, fx - 2, fx - (p - 2), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S2A-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == fy) & (ex > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S2A-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == fx) & (ey > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex + 1 > ey) & (fx + 1 < ey) & (fx > fy) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey + 1 > ex) & (fy + 1 < ex) & (fy > fx) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3A0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (fx > fy + 1) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 2, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3A0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (fy > fx + 1) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 2, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3A1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (fx == fy + 1) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, ey - 3),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3A1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (fy == fx + 1) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, ex - 3),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3AB0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (fx > fy + 2) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3AB0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (fy > fx + 2) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3AB1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (fx == fy + 2) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3AB1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (fy == fx + 2) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3B00-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (fx > fy + 2) & (ex == fy + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3B00-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (fy > fx + 2) & (ey == fx + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3B01-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx > fy + 1) & (ex == ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - 1, fy),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3B01-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy > fx + 1) & (ey == ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - 1, fx),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3B10-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (fx == fy + 2) & (ex == fy + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3B10-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (fy == fx + 2) & (ey == fx + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3B20-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (ex == fy + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3B20-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == fx + 1) & (ey == fx + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3B21-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex + 1 > ey) & (fx == fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3B21-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey + 1 > ex) & (fy == fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3C00-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx > fy + 2) & (fx + 1 < ey) & (ex == fy + (p - 2)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3C00-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy > fx + 2) & (fy + 1 < ex) & (ey == fx + (p - 2)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3C01-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx > fy + 2) & (fx + 1 < ey) & (ex == fy + (p - 2)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ex - 2, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3C01-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy > fx + 2) & (fy + 1 < ex) & (ey == fx + (p - 2)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ey - 2, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3AC0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx > fy + 2) & (fx + 1 == ey) & (ex == fy + (p - 2)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, fx - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3AC0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy > fx + 2) & (fy + 1 == ex) & (ey == fx + (p - 2)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, fy - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3AC1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex == fy + (p - 2)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ex - 3, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3AC1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey == fx + (p - 2)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ey - 3, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3C10-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == fy + 2) & (ex == fy + (p - 2)) & (ey < fy + (p - 3)) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(sy, 1, 0, gx - 3, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3C10-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == fx + 2) & (ey == fx + (p - 2)) & (ex < fx + (p - 3)) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(sx, 1, 0, gy - 3, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3C11-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == fy + 2) & (ex == fy + (p - 2)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, fx),
            SELTZORange(sy, 1, 0, gx - 3, fx - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3C11-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == fx + 2) & (ey == fx + (p - 2)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, fy),
            SELTZORange(sx, 1, 0, gy - 3, fy - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3C12-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == fy + 2) & (ex == fy + (p - 2)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ex - 2, fx),
            SELTZORange(sy, 0, 0, gx - 3, gx - (p + 3), gx - 3))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3C12-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == fx + 2) & (ey == fx + (p - 2)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ey - 2, fy),
            SELTZORange(sx, 0, 0, gy - 3, gy - (p + 3), gy - 3))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3C13-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == fy + 2) & (fx < ey) & (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, fx - 3, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3C13-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == fx + 2) & (fy < ex) & (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, fy - 3, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3C14-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == fy + 2) & (ex == fy + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - 3, fx),
            SELTZORange(~sy, 1, 0, fx - 3, fy - 3, gx - 3))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3C14-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == fx + 2) & (ey == fx + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - 3, fy),
            SELTZORange(~sx, 1, 0, fy - 3, fx - 3, gy - 3))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S3C2-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (ex == fy + (p - 2)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(sy, 1, 0, fx - 3, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S3C2-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == fx + 1) & (ey == fx + (p - 2)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(sx, 1, 0, fy - 3, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S4-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex > ey) & (fx < fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S4-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey > ex) & (fy < fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S4B0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex > ey) & (fx + 1 < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S4B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey > ex) & (fy + 1 < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S4B1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex > ey) & (fx + 1 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S4B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey > ex) & (fy + 1 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S50-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S50-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S51-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey) & (fx > fy + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S51-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex) & (fy > fx + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S5A1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey) & (fx == fy + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy - 2, ey - 3),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S5A1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex) & (fy == fx + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx - 2, ex - 3),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S5B0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S5B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S5B1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey) & (fx > fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S5B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex) & (fy > fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S5AB1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == ey) & (fx == fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fy - 2, ex),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S5AB1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == ex) & (fy == fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fx - 2, ey),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S6-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (ex > fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S6-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (ey > fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S6A-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex > fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 2, ey - 2),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S6A-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey > fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 2, ex - 2),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S6B-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (ex > fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S6B-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (ey > fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S6AB-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex > fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, fx),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S6AB-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey > fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, fy),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S6C0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (fx > fy + 3) & (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S6C0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (fy > fx + 3) & (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S6C1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (fx > fy + 3) & (ex == fy + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ex - 3, fy + 2),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S6C1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (fy > fx + 3) & (ey == fx + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ey - 3, fx + 2),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S6AC0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (fx > fy + 3) & (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S6AC0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (fy > fx + 3) & (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S6AC1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (ex == fy + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, fy + 2),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S6AC1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (ey == fx + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, fx + 2),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S6CD0-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (fx == fy + 3) & (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, gx - 3, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S6CD0-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (fy == fx + 3) & (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, gy - 3, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S6CD1-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx == fy + 3) & (ex == fy + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ex - 3, fx),
            SELTZORange(~sy, 1, 0, gx - 3, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S6CD1-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy == fx + 3) & (ey == fx + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ey - 3, fy),
            SELTZORange(~sx, 1, 0, gy - 3, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM01-MM10-S6ACD-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (fx + 1 == ey) & (fx == fy + 3) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, fx),
            SELTZORange(~sy, 0, 0, gx - 3, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-S6ACD-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (fy + 1 == ex) & (fy == fx + 3) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, fy),
            SELTZORange(~sx, 0, 0, gy - 3, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-SB10-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1)) & (fx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-SB10-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex + (p - 1)) & (fy > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-SB11-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1)) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-SB11-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex + (p - 1)) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-SB20-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey + p) & (fx > ey + 3) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-SB20-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex + p) & (fy > ex + 3) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-SB21-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey + p) & (fx > ey + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - 1, ey - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-SB21-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex + p) & (fy > ex + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, ex - 1, ex - 3, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-SB22-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey + p) & (fx == ey + 3) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-SB22-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex + p) & (fy == ex + 3) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM01-MM10-SB23-X",
        (CLASS_X == MM01) & (CLASS_Y == MM10) &
        (ex == ey + p) & (fx == ey + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 0, 0, ey - 1, ey - 3, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM01-MM10-SB23-Y",
        (CLASS_Y == MM01) & (CLASS_X == MM10) &
        (ey == ex + p) & (fy == ex + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 0, 0, ex - 1, ex - 3, ex - (p - 1)))
    end

end
