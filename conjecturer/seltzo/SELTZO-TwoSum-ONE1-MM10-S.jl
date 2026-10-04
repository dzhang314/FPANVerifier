function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
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

    checker("SELTZO-TwoSum-ONE1-MM10-SA10-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 == ey) & (ey < fy + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy - 2, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-SA10-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 == ex) & (ex < fx + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx - 2, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-SA20-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 == ey) & (ey < fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 2, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-SA20-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 == ex) & (ex < fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 2, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-SA21-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 == ey) & (ey == fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 2, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-SA21-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 == ex) & (ex == fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 2, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-SA30-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy) & (ey < fy + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 2, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-SA30-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx) & (ex < fx + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 2, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-SA40-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 < ey) & (fx + 1 > fy) & (ey < fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-SA40-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 < ex) & (fy + 1 > fx) & (ex < fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-SA41-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 < ey) & (fx > fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-SA41-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 < ex) & (fy > fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-SA42-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx == fy) & (ey == fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-SA42-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy == fx) & (ex == fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-SA5-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 == fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-SA5-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 == fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-SA6-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 == fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-SA6-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 == fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-SA7-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-SA7-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 1) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx < ey) & (fx + 1 > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy < ex) & (fy + 1 > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S1A-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex > ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S1A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey > ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S1B-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + 2) & (fx == ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S1B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + 2) & (fy == ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S2A0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (ex > ey + 1) & (fx < ey) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S2A0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (ey > ex + 1) & (fy < ex) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S2A1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (ex > ey + 1) & (fx == fy + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S2A1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (ey > ex + 1) & (fy == fx + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S2A2-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (ex > ey + 1) & (fx == fy + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S2A2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (ey > ex + 1) & (fy == fx + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S2A3-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (ex > ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S2A3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (ey > ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S2B0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (fx == ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S2B0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (fy == ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S2B1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (fx == ey) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S2B1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (fy == ex) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S2C-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (fx > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S2C-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (fy > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S3A0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (ex > ey + 2) & (fx < ey) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S3A0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (ey > ex + 2) & (fy < ex) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S3A1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (ex > ey + 2) & (fx == fy + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 2),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S3A1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (ey > ex + 2) & (fy == fx + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 2),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S3A2-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (ex > ey + 2) & (fx == fy + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S3A2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (ey > ex + 2) & (fy == fx + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S3B0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (ex == ey + 2) & (fx < ey) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S3B0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (ey == ex + 2) & (fy < ex) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S3B1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (ex == ey + 2) & (fx == fy + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 2),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S3B1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (ey == ex + 2) & (fy == fx + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 2),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S3C0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx == ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S3C0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy == ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S3C1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx == ey) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S3C1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy == ex) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S3D-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S3D-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S4A0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex > ey + 3) & (fx < ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S4A0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey > ex + 3) & (fy < ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S4A1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex == ey + 3) & (fx < ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 2),
            SELTZORange(~sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S4A1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey == ex + 3) & (fy < ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 2),
            SELTZORange(~sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S4B0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex > ey + 3) & (fx == fy + 2) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 3),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S4B0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey > ex + 3) & (fy == fx + 2) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 3),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S4B1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex == ey + 3) & (fx == fy + 2) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 3),
            SELTZORange(~sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S4B1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey == ex + 3) & (fy == fx + 2) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 3),
            SELTZORange(~sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S4C0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex > ey + 3) & (fx == fy + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S4C0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey > ex + 3) & (fy == fx + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S4D0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex > ey + 3) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S4D0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey > ex + 3) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S4D1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex == ey + 3) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fy + 2),
            SELTZORange(~sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S4D1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey == ex + 3) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fx + 2),
            SELTZORange(~sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S4E0-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex > ey + 3) & (fx > ey) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S4E0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey > ex + 3) & (fy > ex) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S4E1-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex == ey + 3) & (fx == ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 2),
            SELTZORange(~sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S4E1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey == ex + 3) & (fy == ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 2),
            SELTZORange(~sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S4E2-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx > ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S4E2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy > ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S4E3-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ex > ey + 3) & (fx == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S4E3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == fx + p) & (ey > ex + 3) & (fy == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S5-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex > fy + p) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S5-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey > fx + p) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S5A-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex > fy + p) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S5A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey > fx + p) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-S6-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex > fy + p) & (fx > ey) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-S6-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey > fx + p) & (fy > ex) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-SB10-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-SB10-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + (p - 1)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-SB11-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1)) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-SB11-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + (p - 1)) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-SB20-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ex < fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-SB20-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + p) & (ey < fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-SB21-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ex == fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-SB21-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + p) & (ey == fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-SB22-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ex < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-SB22-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + p) & (ey < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-MM10-SB23-X",
        (CLASS_X == ONE1) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ex == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-MM10-SB23-Y",
        (CLASS_Y == ONE1) & (CLASS_X == MM10) &
        (ey == ex + p) & (ey == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

end
