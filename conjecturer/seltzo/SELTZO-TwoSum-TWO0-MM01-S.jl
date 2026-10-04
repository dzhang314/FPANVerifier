function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO0},
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

    checker("SELTZO-TwoSum-TWO0-MM01-SE0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx + 1, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-SE0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy + 1, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-SE10-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx == fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-SE10-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy == fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-SE11-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx == fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx + 1, fx - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-SE11-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy == fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy + 1, fy - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-SE20-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx > fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-SE20-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy > fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-SE21-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx == fy + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-SE21-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy == fx + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-SE22-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx > fy + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fx, fy + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-SE22-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy > fx + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fy, fx + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-SE30-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx + 1 == fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fy + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-SE30-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy + 1 == fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fx + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-SE31-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx + 1 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fy + 1, fy - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-SE31-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy + 1 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fx + 1, fx - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-SE40-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx + 1 < fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fy, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-SE40-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy + 1 < fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fx, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-SE41-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx + 2 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fy, fy + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-SE41-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy + 2 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fx, fx + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-SE42-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx + 2 < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, fy, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-SE42-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy + 2 < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, fx, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx > fy) & (fx < ey) & (ex < fy + (p - 3)) & (fy + 2 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > ex) & (fy > fx) & (fy < ex) & (ey < fx + (p - 3)) & (fx + 2 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S1A0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx > fy + 2) & (fx < ey) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S1A0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > ex) & (fy > fx + 2) & (fy < ex) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S1A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx == fy + 2) & (ex == fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S1A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > ex) & (fy == fx + 2) & (ey == fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S1A2-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx == fy + 1) & (ex == fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S1A2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > ex) & (fy == fx + 1) & (ey == fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S1B-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S1B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > ex) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S1ACD-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == fy + 1) & (fx + 1 == ey) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fx - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S1ACD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == fx + 1) & (fy + 1 == ex) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fy - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S1D0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex < fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 2, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S1D0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex) & (ey < fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 2, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S1D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex < fy + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S1D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex) & (ey < fx + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S1CD-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx + 1 == ey) & (ex < fy + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S1CD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy + 1 == ex) & (ey < fx + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S1AD0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 2, fy + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S1AD0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 2, fx + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S1AD1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S1AD1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S2-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx < fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > ex) & (fy < fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S2A0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx + 2 < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S2A0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > ex) & (fy + 2 < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S2A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx + 2 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 3),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S2A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > ex) & (fy + 2 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 3),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S2A2-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx + 1 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S2A2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > ex) & (fy + 1 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx > fy + 2) & (fx < ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy > fx + 2) & (fy < ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3A0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == fy + 2) & (fx < ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3A0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == fx + 2) & (fy < ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == fy + 2) & (fx < ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == fx + 2) & (fy < ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3B-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey) & (fx > fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex) & (fy > fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3AB0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey) & (fx == fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3AB0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex) & (fy == fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3AB1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey) & (fx == fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3AB1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex) & (fy == fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3C-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx > fy + 2) & (fx < ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy > fx + 2) & (fy < ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3BC-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3BC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3E0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == fy + 1) & (fx + 1 < ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3E0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == fx + 1) & (fy + 1 < ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3E1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == fy + 1) & (fx + 1 == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3E1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == fx + 1) & (fy + 1 == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3D0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx < ey) & (ex > fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 1, 0, ex - p, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3D0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy < ex) & (ey > fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 1, 0, ey - p, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx < ey) & (ex == fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 0, 0, ex - p, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy < ex) & (ey == fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 0, 0, ey - p, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3D2-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx < ey) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3D2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy < ex) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3DA0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx < ey) & (ex > fy + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, ex - p, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3DA0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy < ex) & (ey > fx + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, ey - p, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3DA1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx < ey) & (ex == fy + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ex - p, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3DA1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy < ex) & (ey == fx + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ey - p, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3DA2-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx < ey) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3DA2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy < ex) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3DB0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex > fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, fx - 1),
            SELTZORange(sy, 1, 0, ex - p, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3DB0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex) & (ey > fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, fy - 1),
            SELTZORange(sx, 1, 0, ey - p, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3DB1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, fx - 1),
            SELTZORange(sy, 0, 0, ex - p, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3DB1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, fy - 1),
            SELTZORange(sx, 0, 0, ey - p, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3DB2-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3DB2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3DAB0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex > fy + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 1, 0, ex - p, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3DAB0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex) & (ey > fx + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 1, 0, ey - p, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3DAB1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, ex - p, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3DAB1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, ey - p, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S3DAB2-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S3DAB2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S4-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S4A-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S4A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S4B-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S4B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S4AB-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S4AB-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S4C0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S4C0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S4C1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S4C1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S4D0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S4D0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S4D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S4D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S4D2-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S4D2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S4E0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx > ey + 2) & (ex > fy + p) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S4E0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy > ex + 2) & (ey > fx + p) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S4E1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey + 2) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S4E1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex + 2) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-S4E2-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-S4E2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-SB-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-SB-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
