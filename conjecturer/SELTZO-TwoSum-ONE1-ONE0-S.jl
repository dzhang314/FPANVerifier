function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
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

    checker("SELTZO-TwoSum-ONE1-ONE0-SA10-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-SA10-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-SA11-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-SA11-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-SA12-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-SA12-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-SA14-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx > fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-SA14-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy > fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-SA15-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx == fy + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-SA15-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy == fx + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-SA16-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx > fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-SA16-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy > fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-SA17-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx > fy + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-SA17-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy > fx + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-SA21-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ex - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-SA21-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ey - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-SA22-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx > fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-SA22-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy > fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-SA23-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx > fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-SA23-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy > fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-SA24-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx > fy) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-SA24-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy > fx) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-S1-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex > fy + p) & (fx > ey + 1) & (ex < ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-S1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey > fx + p) & (fy > ex + 1) & (ey < ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-S1A-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex > fy + p) & (fx == ey + 1) & (ex < ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-S1A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey > fx + p) & (fy == ex + 1) & (ey < ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-S1G-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex > ey + 3) & (ex < ey + p) & (fx == ey + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-S1G-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey > ex + 3) & (ey < ex + p) & (fy == ex + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-S1L-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (ex < ey + p) & (fx < ey + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-S1L-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (ey < ex + p) & (fy < ex + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-S1M-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (ex < ey + p) & (fx > ey + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-S1M-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (ey < ex + p) & (fy > ex + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-S1R-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex > fy + p) & (fx < ey + 1) & (ex < ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-S1R-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey > fx + p) & (fy < ex + 1) & (ey < ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-S1T-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 3) & (fx == ey + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-S1T-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 3) & (fy == ex + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-S1J0-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == fy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-S1J0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == fx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-S1J1-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-S1J1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-S1K-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (ex == fy + p) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-S1K-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (ey == fx + p) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-S2A-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-S2A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-S3-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx > fy) & (fx < ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-S3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy > fx) & (fy < ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-S3A-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx > fy) & (fx < ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-S3A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy > fx) & (fy < ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-S3B-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == fy + (p - 1)) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-S3B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == fx + (p - 1)) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-S3D-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == fy + (p - 1)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-S3D-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == fx + (p - 1)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-SB20-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx == ey + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-SB20-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy == ex + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-SB21-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx == ey + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-SB21-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy == ex + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-SB41-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx > ey + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-SB41-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy > ex + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-SB-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ex < fx + (p - 2)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-SB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ey < fy + (p - 2)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

end
