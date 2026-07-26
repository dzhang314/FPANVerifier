function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM10},
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

    checker("SELTZO-TwoSum-MM10-ONE1-SE0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx < fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-SE0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex) & (fy < fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-SE1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, fx),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-SE1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex) & (fy < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, fy),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-SE2-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-SE2-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-SE3-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-SE3-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-SE4-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-SE4-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-SE5-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx > fy + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-SE5-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex) & (fy > fx + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-SE6-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx > fy + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fx - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-SE6-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex) & (fy > fx + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fy - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-SA10-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-SA10-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-SA11-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-SA11-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-SA20-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - 2, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-SA20-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - 2, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-SA21-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-SA21-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-SA30-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx > fy + 1) & (ex < fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-SA30-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy > fx + 1) & (ey < fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-SA31-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx > fy + 1) & (ex < fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-SA31-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy > fx + 1) & (ey < fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-SA32-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ex - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-SA32-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ey - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-SA33-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-SA33-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx < ey) & (fx > fy + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy < ex) & (fy > fx + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S1A0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx == fy + 1) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S1A0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy == fx + 1) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S1A1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx == fy + 1) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S1A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy == fx + 1) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S1B-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S1B-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S1C-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx < ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S1C-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy < ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S1D-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx < ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S1D-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy < ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S1E-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx < ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S1E-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy < ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S2A-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex < fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S2A-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey < fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S2B0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S2B0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S2B1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S2B1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S2C0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S2C0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S2C1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S2C1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S2D-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S2D-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S3-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex < fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S3-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey < fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S3A0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S3A0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S3A1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S3A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S3B0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex == fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S3B0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey == fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S3B1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex == fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S3B1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey == fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S3C-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S3C-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S4-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S4-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S4A-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S4A-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S4B-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S4B-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-S4C-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex > fy + p) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-S4C-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey > fx + p) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-SB1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-SB1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-ONE1-SB2-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE1) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-MM10-ONE1-SB2-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE1) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
