function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO0},
    ::Val{TWO1},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-TWO0-TWO1-SE0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, ex),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-SE0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, ey),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-SE2-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx < fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-SE2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy < fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-SE5-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fy - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-SE5-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fx - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-SE6-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fy),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-SE6-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fx),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-SE7-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-SE7-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S1A-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S1A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S1B-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S1B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S1C-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx > ey + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S1C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy > ex + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S1D0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S1D0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S1D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fx - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S1D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fy - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S1AD0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S1AD0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S1AD1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S1AD1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S1BD0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S1BD0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S1BD1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S1BD1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S2A-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == fy) & (ex > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S2A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == fx) & (ey > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S3-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex + 1 > ey) & (fx + 1 < ey) & (fx > fy) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey + 1 > ex) & (fy + 1 < ex) & (fy > fx) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S3A0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (fx > fy + 1) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S3A0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (fy > fx + 1) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S3A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (fx == fy + 1) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S3A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (fy == fx + 1) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S3AB-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (fx > fy + 1) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fy),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S3AB-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (fy > fx + 1) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fx),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S3B0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (fx > fy + 1) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S3B0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (fy > fx + 1) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S3B1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S3B1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S3C0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx > fy + 2) & (fx + 1 < ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S3C0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy > fx + 2) & (fy + 1 < ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S3AC0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx > fy + 2) & (fx + 1 == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S3AC0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy > fx + 2) & (fy + 1 == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S3C1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == fy + 2) & (fx + 1 < ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S3C1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == fx + 2) & (fy + 1 < ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S3AC1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == fy + 2) & (fx + 1 == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S3AC1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == fx + 2) & (fy + 1 == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S3D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == fy + 2) & (fx + 1 < ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S3D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == fx + 2) & (fy + 1 < ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S3AD1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == fy + 2) & (fx + 1 == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S3AD1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == fx + 2) & (fy + 1 == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S3C2-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S3C2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S4-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex > ey) & (fx < fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey > ex) & (fy < fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S4B0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex > ey) & (fx + 2 < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S4B0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey > ex) & (fy + 2 < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S4B1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex > ey) & (fx + 2 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy),
            SELTZORange(sy, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S4B1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey > ex) & (fy + 2 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx),
            SELTZORange(sx, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S4B2-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex > ey) & (fx + 1 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx),
            SELTZORange(sy, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S4B2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey > ex) & (fy + 1 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy),
            SELTZORange(sx, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S50-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (fx > fy + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S50-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (fy > fx + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S51-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey) & (fx > fy + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S51-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex) & (fy > fx + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S5A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey) & (fx == fy + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S5A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex) & (fy == fx + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S5B0-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (fx > fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S5B0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (fy > fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S5B1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey) & (fx > fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S5B1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex) & (fy > fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S5AB1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx == ey) & (fx == fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S5AB1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy == ex) & (fy == fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S6-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (ex > fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(~sy, 1, 0, ex - p, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S6-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (ey > fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(~sx, 1, 0, ey - p, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S6A-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex > fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(~sy, 1, 0, ex - p, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S6A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey > fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(~sx, 1, 0, ey - p, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S6B-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (ex > fy + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 1, 0, ex - p, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S6B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (ey > fx + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 1, 0, ey - p, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S6AB-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex > fy + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(~sy, 1, 0, ex - p, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S6AB-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey > fx + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(~sx, 1, 0, ey - p, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S6C-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S6C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S6AC-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S6AC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S6D-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S6D-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S6AD-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S6AD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S6BD-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S6BD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S6ABD-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S6ABD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S6E-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (ex == fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S6E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (ey == fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S6AE-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex == fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S6AE-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey == fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S6BE-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (ex == fy + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S6BE-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (ey == fx + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S6ABE-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex == fy + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S6ABE-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey == fx + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-S7-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-S7-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-SB1-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-SB1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-SB20-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-SB20-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-TWO1-SB21-X",
        (CLASS_X == TWO0) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-TWO1-SB21-Y",
        (CLASS_Y == TWO0) & (CLASS_X == TWO1) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

end
