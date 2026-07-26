function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
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

    checker("SELTZO-TwoSum-ONE1-MM01-SA0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx > fy + 1) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-SA0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy > fx + 1) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-SA1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx > fy + 1) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-SA1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy > fx + 1) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-SA2-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx > fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-SA2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy > fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-SA3-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy + 1) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fy - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-SA3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx + 1) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fx - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-SA4-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy + 1) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-SA4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx + 1) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-SA5-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-SA5-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-SA60-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-SA60-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-SA61-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-SA61-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-SA7-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-SA7-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx > fy) & (fx < ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy > fx) & (fy < ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S1A-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S1A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S1B-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex > ey + 1) & (fx == fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S1B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey > ex + 1) & (fy == fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S1C-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex > ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S1C-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey > ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S1D-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx > fy) & (fx < ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S1D-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy > fx) & (fy < ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S1E-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (fx > ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S1E-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (fy > ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S1AD-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx > fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S1AD-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy > fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S1BD-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex > ey + 1) & (fx == fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S1BD-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey > ex + 1) & (fy == fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S2A0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == fy + (p - 1)) & (ex > ey + 2) & (fx > fy + 1) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S2A0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == fx + (p - 1)) & (ey > ex + 2) & (fy > fx + 1) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S2A1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == fy + (p - 1)) & (ex == ey + 2) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S2A1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == fx + (p - 1)) & (ey == ex + 2) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S2A2-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == fy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S2A2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == fx + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S2A3-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == fy + (p - 1)) & (ex > ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S2A3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == fx + (p - 1)) & (ey > ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S2A4-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == fy + (p - 1)) & (ex == ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S2A4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == fx + (p - 1)) & (ey == ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S2B0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == fy + p) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S2B0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == fx + p) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S2B1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, ey + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S2B1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, ex + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S2B2-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == fy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S2B2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == fx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S3-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex > fy + p) & (ex < ey + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey > fx + p) & (ey < ex + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S3A-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex > fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 2, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S3A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey > fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 2, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-S4-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex > fy + p) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-S4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey > fx + p) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-SB0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + p) & (fx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-SB0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + p) & (fy > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-MM01-SB1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM01) &
        (ex == ey + p) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 2, ey + 3),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-MM01-SB1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM01) &
        (ey == ex + p) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 2, ex + 3),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
