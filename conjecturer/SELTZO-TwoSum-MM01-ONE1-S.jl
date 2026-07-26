function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM01},
    ::Val{ONE1},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-MM01-ONE1-SE0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey) & (fy > fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-SE0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex) & (fx > fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-SE1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey) & (fy > fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, ex - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-SE1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex) & (fx > fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, ey - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex > ey) & (fy > fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey > ex) & (fx > fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S1C-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex > ey) & (fy > fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S1C-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey > ex) & (fx > fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S1A-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex + 1 > ey) & (fy == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S1A-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey + 1 > ex) & (fx == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S1AC-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex + 1 > ey) & (fy == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S1AC-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey + 1 > ex) & (fx == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S1B-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex + 1 > ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S1B-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey + 1 > ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex + 1 > ey) & (ey > fx + 1) & (fx > fy + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey + 1 > ex) & (ex > fy + 1) & (fy > fx + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2A0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ey == fx + 1) & (fx > fy + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2A0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ex == fy + 1) & (fy > fx + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2B0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ey > fx + 1) & (ex == fy + (p - 2)) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ex > fy + 1) & (ey == fx + (p - 2)) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2A0B0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ey == fx + 1) & (ex == fy + (p - 2)) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2A0B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ex == fy + 1) & (ey == fx + (p - 2)) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2B1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ey > fx + 1) & (ex == fy + (p - 2)) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ex > fy + 1) & (ey == fx + (p - 2)) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2A0B1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ey == fx + 1) & (ex == fy + (p - 2)) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2A0B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ex == fy + 1) & (ey == fx + (p - 2)) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2C-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ey > fx + 1) & (ex > fy + (p - 2)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2C-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ex > fy + 1) & (ey > fx + (p - 2)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2A0C-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ey == fx + 1) & (ex > fy + (p - 2)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2A0C-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ex == fy + 1) & (ey > fx + (p - 2)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2D-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ey > fx + 1) & (ex > fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2D-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ex > fy + 1) & (ey > fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2A0D-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ey == fx + 1) & (ex > fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2A0D-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ex == fy + 1) & (ey > fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2E-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ey > fx) & (ex == fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2E-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ex > fy) & (ey == fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2A10-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ey == fx) & (fx > fy + 2) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2A10-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ex == fy) & (fy > fx + 2) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2A11-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ey == fx) & (fx == fy + 2) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2A11-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ex == fy) & (fy == fx + 2) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2A1B0-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ey == fx) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2A1B0-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ex == fy) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2A1B1-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ey == fx) & (fx == fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2A1B1-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ex == fy) & (fy == fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2A1C-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ey == fx) & (ex > fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2A1C-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ex == fy) & (ey > fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2A2-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2A2-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2A2B-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2A2B-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S2A2C-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex > fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S2A2C-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey > fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S3-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex > fy + (p - 1)) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S3-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey > fx + (p - 1)) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-ONE1-S3A-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-ONE1-S3A-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-ONE1-SB10-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1)) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-SB10-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1)) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-ONE1-SB11-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1)) & (fx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-SB11-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1)) & (fy > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM01-ONE1-SB20-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey + p) & (fx == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-SB20-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex + p) & (fy == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-MM01-ONE1-SB21-X",
        (CLASS_X == MM01) & (CLASS_Y == ONE1) &
        (ex == ey + p) & (fx > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-MM01-ONE1-SB21-Y",
        (CLASS_Y == MM01) & (CLASS_X == ONE1) &
        (ey == ex + p) & (fy > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
