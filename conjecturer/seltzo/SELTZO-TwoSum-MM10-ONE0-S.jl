function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM10},
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

    checker("SELTZO-TwoSum-MM10-ONE0-SE0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < fy) & (ex == ey) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ex - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SE0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < fx) & (ey == ex) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ey - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SE1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < fy) & (ex == ey) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ex - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SE1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < fx) & (ey == ex) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ey - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SE2-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy) & (ex == ey) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, ex - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SE2-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx) & (ey == ex) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, ey - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SE3-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy) & (ex == ey) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, ex - 1, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SE3-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx) & (ey == ex) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, ey - 1, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SE4-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy + 1) & (ex == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, ex - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SE4-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx + 1) & (ey == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, ey - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SE5-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > fy + 1) & (ex == ey) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, ex - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SE5-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > fx + 1) & (ey == ex) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, ey - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SE6-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > fy + 2) & (ex == ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, ex - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SE6-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > fx + 2) & (ey == ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, ey - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SE7-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy + 2) & (ex == ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, ex - 1, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SE7-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx + 2) & (ey == ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, ey - 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA100-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx + 1 < fy) & (ex == ey + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy - 1, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA100-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy + 1 < fx) & (ey == ex + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx - 1, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA101-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx + 1 < fy) & (ex == ey + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy - 1, fx),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA101-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy + 1 < fx) & (ey == ex + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx - 1, fy),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA110-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx + 1 == fy) & (ex == ey + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, ex - (p - 2)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA110-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy + 1 == fx) & (ey == ex + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, ey - (p - 2)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA111-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx + 1 == fy) & (ex == ey + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA111-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy + 1 == fx) & (ey == ex + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA120-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy) & (ex == ey + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 2, fx - 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA120-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx) & (ey == ex + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 2, fy - 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA121-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy) & (ex == ey + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA121-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx) & (ey == ex + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA13-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy + 1) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fy, fx),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA13-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx + 1) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fx, fy),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA14-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > fy + 1) & (ex == ey + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx, fy),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA14-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > fx + 1) & (ey == ex + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy, fx),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA15-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (ey == fy + (p - 3)) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA15-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (ex == fx + (p - 3)) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA16-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (ey == fy + (p - 3)) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fx),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA16-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (ex == fx + (p - 3)) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fy),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA17-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (ey == fy + (p - 2)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA17-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (ex == fx + (p - 2)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA18-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (ey == fy + (p - 2)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fx),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA18-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (ex == fx + (p - 2)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fy),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA201-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA201-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA202-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy + 1) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA202-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx + 1) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA22-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > fy + 1) & (fx < ey) & (ex == ey + 2) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA22-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > fx + 1) & (fy < ex) & (ey == ex + 2) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA22A0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex == ey + 2) & (ex == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA22A0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex) & (ey == ex + 2) & (ey == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA22A1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (ex == fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA22A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (ey == fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA22B0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex == ey + 2) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 2),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA22B0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex) & (ey == ex + 2) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 2),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA22B1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA22B1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA231-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex < fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA231-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex) & (ey < fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA232-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex < fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA232-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey < fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SA23B0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fy + 2),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SA23B0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fx + 2),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey) & (fx > fy + 1) & (ex > ey + 2) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex) & (fy > fx + 1) & (ey > ex + 2) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S1A1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S1A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S1A2-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == fy + 1) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S1A2-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == fx + 1) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S1C0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey + 1) & (ex > ey + 2) & (ex == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S1C0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex + 1) & (ey > ex + 2) & (ey == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S1C1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (ex == fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S1C1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (ey == fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S1D0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey + 1) & (ex > ey + 2) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S1D0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex + 1) & (ey > ex + 2) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S1D1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey + 1) & (ex > ey + 2) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S1D1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex + 1) & (ey > ex + 2) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S1E0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey + 1) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S1E0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex + 1) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S1E1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx < ey + 1) & (ex > ey + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S1E1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy < ex + 1) & (ey > ex + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S2-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > fx + 2) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 2, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S2-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > fy + 2) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 2, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S2A0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > fx + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 2, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S2A0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > fy + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 2, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S2A11-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S2A11-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S2A12-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S2A12-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S2B0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > fx + 2) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 2, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S2B0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > fy + 2) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 2, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S2B1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex == fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S2B1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey == fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S2C0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 2, ey + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S2C0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 2, ex + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S2D01-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 2, fx - 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S2D01-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 2, fy - 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S2D02-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 2, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S2D02-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 2, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S2D11-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > ey + 3) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 2, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S2D11-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > ex + 3) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 2, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S2D12-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ex > ey + 3) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 2, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S2D12-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ey > ex + 3) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 2, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S2D2-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S2D2-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S3-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S3-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S3E-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S3E-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S3B-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S3B-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S3D0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > ey + 2) & (ex < ey + p) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S3D0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > ex + 2) & (ey < ex + p) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-S3D1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (fx > ey + 2) & (ex < ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-S3D1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (fy > ex + 2) & (ey < ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SB0-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SB0-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-ONE0-SB1-X",
        (CLASS_X == MM10) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-ONE0-SB1-Y",
        (CLASS_Y == MM10) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
