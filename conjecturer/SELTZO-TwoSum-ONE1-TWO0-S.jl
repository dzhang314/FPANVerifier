function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
    ::Val{TWO0},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ONE1-TWO0-SE0-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx + 1 < fy) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - 1, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SE0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex) & (fy + 1 < fx) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - 1, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SE1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx + 1 < fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - 1, fy - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SE1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex) & (fy + 1 < fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - 1, fx - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SE2-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - 1, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SE2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - 1, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SE3-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SE3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex) & (fy == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SE4-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - 1, fy),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SE4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex) & (fy == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - 1, fx),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SE5-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx > fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SE5-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex) & (fy > fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SE6-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx > fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fy + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SE6-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex) & (fy > fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fx + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SE7-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey) & (fx == fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, ex),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SE7-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex) & (fy == fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, ey),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SA10-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx > fy + 1) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SA10-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy > fx + 1) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SA11-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx > fy + 1) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SA11-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy > fx + 1) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SA12-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy + 1) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SA12-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx + 1) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SA13-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy + 1) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fy - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SA13-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx + 1) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fx - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SA141-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SA141-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SA142-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 1 == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SA142-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 1 == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SA15-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SA15-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SA16-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx > fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SA16-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy > fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SA17-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SA17-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SA18-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy - 1, fy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SA18-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx - 1, fx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SA20-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx > fy) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SA20-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy > fx) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SA21-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx > fy) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SA21-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy > fx) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx > ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy > ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S1A-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx > fy + 1) & (fx < ey + 1) & (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S1A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy > fx + 1) & (fy < ex + 1) & (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S1AC-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == fy + 1) & (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S1AC-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == fx + 1) & (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S1AB-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx > fy + 1) & (ex == fy + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S1AB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy > fx + 1) & (ey == fx + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S1ABC-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == fy + 1) & (ex == fy + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S1ABC-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == fx + 1) & (ey == fx + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S2-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S2A-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S2A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S2AB-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S2AB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S2C-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx < ey + 1) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S2C-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy < ex + 1) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S2BC-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx < ey + 1) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S2BC-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy < ex + 1) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S3-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex > fy + p) & (ex < ey + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey > fx + p) & (ey < ex + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S3A-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S3A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S3B-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex < ey + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S3B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey < ex + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S3AB-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex > fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S3AB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey > fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S4B-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S4B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S5-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx > fy) & (fx < ey) & (ex > ey + 2) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S5-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy > fx) & (fy < ex) & (ey > ex + 2) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S5B-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx > fy) & (fx < ey + 2) & (ex > ey + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S5B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy > fx) & (fy < ex + 2) & (ey > ex + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S5C1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == fy) & (ex > ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S5C1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == fx) & (ey > ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S5C2-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx + 1 == fy) & (ex > ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S5C2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy + 1 == fx) & (ey > ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S5BC-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == fy) & (ex > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S5BC-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == fx) & (ey > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S6-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx < ey + 1) & (ex > fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S6-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy < ex + 1) & (ey > fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-S6B-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx < ey + 1) & (ex > fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-S6B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy < ex + 1) & (ey > fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SB20-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (fx > ey + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SB20-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (fy > ex + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SB21-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (fx > ey + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SB21-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (fy > ex + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SB22-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (fx == ey + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SB22-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (fy == ex + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-SB23-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (fx == ey + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-SB23-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (fy == ex + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

end
