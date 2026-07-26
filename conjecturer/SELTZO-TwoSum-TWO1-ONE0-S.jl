function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO1},
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

    checker("SELTZO-TwoSum-TWO1-ONE0-SE0-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx > fy + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-SE0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (ey == ex) & (fy > fx + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-SA-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx < ey) & (fx > fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-SA-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy < ex) & (fy > fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S2-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx < ey + 1) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy < ex + 1) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S2A-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S2A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S2B0-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ex > fy + p) & (ex > fx + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S2B0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ey > fx + p) & (ey > fy + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S2B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S2B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S2C-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx < ey + 1) & (ex > ey + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S2C-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy < ex + 1) & (ey > ex + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S2AC0-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ey == fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S2AC0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ex == fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S2AC1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ey == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S2AC1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ex == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S2BC0-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ey == fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S2BC0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ex == fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S2BC1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ey == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S2BC1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ex == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S3-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx < ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx - 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S3-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy < ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy - 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S4-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (ex < ey) & (fx == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, ex, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S4-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (ey < ex) & (fy == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, ey, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S5-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx + (p - 2) > ey) & (ex + 1 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fy - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S5-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy + (p - 2) > ex) & (ey + 1 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fx - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S5B-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx + (p - 2) > ey) & (ex + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fy - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S5B-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy + (p - 2) > ex) & (ey + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fx - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S6-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx + (p - 2) == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey + 1, ex, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S6-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy + (p - 2) == ex) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex + 1, ey, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S7-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx + 1 == fy) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(sy, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S7-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy + 1 == fx) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(sx, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S10-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx < ey + 1) & (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S10-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy < ex + 1) & (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S10A0-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex == fy + (p - 1)) & (ex > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S10A0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey == fx + (p - 1)) & (ey > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S10A1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex == fy + (p - 1)) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S10A1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey == fx + (p - 1)) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S11-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx > fy + 2) & (ey == fy + (p - 2)) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy > fx + 2) & (ex == fx + (p - 2)) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S11A-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (fx == fy + 2) & (ex < ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, ex, fx),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S11A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (fy == fx + 2) & (ey < ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, ey, fy),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S12-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (ex < ey) & (fx > fy + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, ex, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S12-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (ey < ex) & (fy > fx + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, ey, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-S13A-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-S13A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-SB100-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (ex == ey + (p - 1)) & (fx > ey + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-SB100-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (ey == ex + (p - 1)) & (fy > ex + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-SB101-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (ex == ey + (p - 1)) & (fx > ey + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-SB101-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (ey == ex + (p - 1)) & (fy > ex + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-SB200-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx > ey + 3) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-SB200-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy > ex + 3) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-SB201-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx > ey + 3) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-SB201-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy > ex + 3) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-SB210-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx == ey + 3) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-SB210-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy == ex + 3) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ONE0-SB211-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx == ey + 3) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO1-ONE0-SB211-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy == ex + 3) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
