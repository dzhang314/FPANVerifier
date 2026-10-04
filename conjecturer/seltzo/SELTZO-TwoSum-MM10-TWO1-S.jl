function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM10},
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

    checker("SELTZO-TwoSum-MM10-TWO1-SE0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx + 1, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SE0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy + 1, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SE10-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SE10-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SE11-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SE11-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SE20-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx > fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SE20-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex) & (fy > fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SE21-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx > fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fy),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SE21-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex) & (fy > fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fx),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SE30-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SE30-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SE31-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy + 1, fy + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SE31-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx + 1, fx + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SE40-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 < fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SE40-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 < fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SE41-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, fx),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SE41-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, fy),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SA10-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx > fy) & (ex > fx + 2) & (ey > fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SA10-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy > fx) & (ey > fy + 2) & (ex > fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SA10A-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SA10A-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SA11-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx > fy + 1) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ex - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SA11-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy > fx + 1) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ey - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SA11A-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + (p - 3)) & (ey == fy + (p - 3)) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ex - 2, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SA11A-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + (p - 3)) & (ex == fx + (p - 3)) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ey - 2, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SA1A0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey > fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SA1A0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex > fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SA1A1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + 2) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 2, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SA1A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + 2) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 2, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SA1A2-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SA1A2-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SA1A3-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 3)) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SA1A3-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 3)) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SA1B0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx == fy) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SA1B0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy == fx) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SA1B1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx == fy) & (ex == fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SA1B1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy == fx) & (ey == fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SA1C0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 == fy) & (ex > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SA1C0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 == fx) & (ey > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SA1C1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 == fy) & (ex == fy + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SA1C1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 == fx) & (ey == fx + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SA20-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex == ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SA20-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey == ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SA21-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 2) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SA21-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 2) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex < fy + (p - 2)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey < fx + (p - 2)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S1A0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex < fy + (p - 2)) & (fx == ey + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S1A0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey < fx + (p - 2)) & (fy == ex + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S1A1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S1A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S1B0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 2)) & (fx > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S1B0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 2)) & (fy > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S1B1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 2)) & (fx < ey + 2) & (fx + 1 > ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S1B1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 2)) & (fy < ex + 2) & (fy + 1 > ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S1B2-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 2)) & (fx < ey + 2) & (fx + 1 > ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S1B2-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 2)) & (fy < ex + 2) & (fy + 1 > ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S1C0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S1C0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S1C10-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 1)) & (fx == ey + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S1C10-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 1)) & (fy == ex + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S1C11-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 1)) & (fx == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S1C11-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 1)) & (fy == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S1C2-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 1)) & (fx == ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S1C2-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 1)) & (fy == ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S2-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < fy + (p - 2)) & (fx < ey) & (fx > fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S2-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < fx + (p - 2)) & (fy < ex) & (fy > fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S2AB-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex > ey + 2) & (ex < fy + (p - 2)) & (fx + 1 == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S2AB-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey > ex + 2) & (ey < fx + (p - 2)) & (fy + 1 == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S2C0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S2C0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S2C1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S2C1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S2E-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 2)) & (ex > ey + 1) & (fx < ey) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S2E-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 2)) & (ey > ex + 1) & (fy < ex) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S2BE-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 2)) & (ex > ey + 1) & (fx == fy + 1) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S2BE-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 2)) & (ey > ex + 1) & (fy == fx + 1) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S2ABE0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 2)) & (fx == fy + 1) & (fx + 1 == ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S2ABE0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 2)) & (fy == fx + 1) & (fy + 1 == ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S2F-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S2F-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (fy < ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S3-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex < ey + (p - 1)) & (fx > ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S3-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey < ex + (p - 1)) & (fy > ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S3A0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S3A0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S3A1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S3A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S3B-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S3B-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S3AB00-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + p) & (fx == ey + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S3AB00-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + p) & (fy == ex + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S3AB01-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + p) & (fx == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S3AB01-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + p) & (fy == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S3AB1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + p) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S3AB1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + p) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S4-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S4-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (fy < ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-S4A-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-S4A-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (fy < ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SB1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SB1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SB20-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SB20-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-SB21-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-SB21-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

end
