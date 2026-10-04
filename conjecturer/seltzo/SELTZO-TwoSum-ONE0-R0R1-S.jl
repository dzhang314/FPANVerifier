function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
    ::Val{R0R1},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ONE0-R0R1-SE0-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx < fy + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, ex - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SE0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy < fx + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, ey - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SE1-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx < fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SE1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy < fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SE2-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, ex - 1, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SE2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, ey - 1, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SE3-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ex - 1, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SE3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ey - 1, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SE4-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx > fy + 1) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ex - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SE4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy > fx + 1) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ey - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SE5-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx > fy + 1) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ex - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SE5-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy > fx + 1) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ey - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA10-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx < fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 2, fy, fx),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA10-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy < fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 2, fx, fy),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA11-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 2, fy, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA11-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 2, fx, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA12-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx == fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 2, fx - 1, fx),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA12-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy == fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 2, fy - 1, fy),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA13-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 2, ex - (p - 2), ex + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA13-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 2, ey - (p - 2), ey + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA14-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, ey - (p - 1), ey - (p - 2)),
            SELTZORange(sy, 0, 0, ey - p, ey - (p + p), ey - p))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA14-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, ex - (p - 1), ex - (p - 2)),
            SELTZORange(sx, 0, 0, ex - p, ex - (p + p), ex - p))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA15-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx > fy + 1) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fx - 1, ey - (p - 2)),
            SELTZORange(sy, 0, 0, ey - p, ey - (p + p), ey - p))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA15-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy > fx + 1) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fy - 1, ex - (p - 2)),
            SELTZORange(sx, 0, 0, ex - p, ex - (p + p), ex - p))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA16-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx > fy + 1) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fx - 1, fx),
            SELTZORange(sy, 0, 0, ey - p, ey - (p + p), ey - p))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA16-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy > fx + 1) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fy - 1, fy),
            SELTZORange(sx, 0, 0, ex - p, ex - (p + p), ex - p))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA17-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (ex == fx + (p - 2)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey + 1, fy, fy + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA17-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (ey == fy + (p - 2)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex + 1, fx, fx + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA20-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx < fy + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA20-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy < fx + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA21-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx < fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ex - (p - 3)),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA21-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy < fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ey - (p - 3)),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA22-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA22-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA23-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ex - 2, ey),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA23-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ey - 2, ex),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA24-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx > fy + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ex - 2, fy + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA24-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy > fx + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ey - 2, fx + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA25-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx > fy + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - 2, fx),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA25-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy > fx + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - 2, fy),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA26-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx > fy + 1) & (ey == fy + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - 2, fx),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA26-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy > fx + 1) & (ex == fx + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - 2, fy),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA33-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (ex > fx + 1) & (ex < fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ey, fx, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA33-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (ey > fy + 1) & (ey < fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ex, fy, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA34-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (ex == fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA34-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (ey == fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA35-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (ex == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fx + 1, fx + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA35-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (ey == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fy + 1, fy + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA36-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (fx < fy + 1) & (ey > fy + 2) & (ex > fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ey, ex, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA36-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (fy < fx + 1) & (ex > fx + 2) & (ey > fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ex, ey, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA37-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (fx == fy + 1) & (ey > fy + 3) & (ex > fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey, ex, ex + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA37-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (fy == fx + 1) & (ex > fx + 3) & (ey > fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex, ey, ey + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA38-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (fx < fy) & (ex == fx + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, ex, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA38-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (fy < fx) & (ey == fy + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, ey, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA39-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (fx == fy) & (ex == fx + (p - 3)) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA39-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (fy == fx) & (ey == fy + (p - 3)) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA40-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (fx + 1 < fy) & (ex == fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, ex, fx + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA40-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (fy + 1 < fx) & (ey == fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, ey, fy + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-SA41-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (fx + 1 == fy) & (ex == fx + (p - 2)) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, ex, ex + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-SA41-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (fy + 1 == fx) & (ey == fy + (p - 2)) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, ey, ey + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S1-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex > fy + (p + 1)) & (ex < ey + (p - 2)) & (ex == fx + (p - 2)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey > fx + (p + 1)) & (ey < ex + (p - 2)) & (ey == fy + (p - 2)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S2A0-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 < ey) & (fx + p == ey) & (ex + 1 > fy) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey, ex + 1, fx + 2),
            SELTZORange(sy, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S2A0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 < ex) & (fy + p == ex) & (ey + 1 > fx) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex, ey + 1, fy + 2),
            SELTZORange(sx, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S2A1-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 < ey) & (fx + p == ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(sy, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S2A1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 < ex) & (fy + p == ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(sx, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S2B0-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 < ey) & (fx + p == ey) & (ex < fy) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey, fy + 1, fx + 2),
            SELTZORange(sy, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S2B0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 < ex) & (fy + p == ex) & (ey < fx) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex, fx + 1, fy + 2),
            SELTZORange(sx, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S2B1-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (fx + p == ey) & (ex < fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fy, fx + 2),
            SELTZORange(sy, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S2B1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (fy + p == ex) & (ey < fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fx, fy + 2),
            SELTZORange(sx, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S2C0-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (fx + p < ey) & (ex + 3 < ey) & (ex > fy) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey, ex + 1, fy + 1),
            SELTZORange(~sy, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S2C0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (fy + p < ex) & (ey + 3 < ex) & (ey > fx) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex, ey + 1, fx + 1),
            SELTZORange(~sx, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S2C1-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (fx + p < ey) & (ex + 3 < ey) & (ex == fy) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey, ex + 1, ex + 2),
            SELTZORange(~sy, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S2C1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (fy + p < ex) & (ey + 3 < ex) & (ey == fx) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex, ey + 1, ey + 2),
            SELTZORange(~sx, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S3-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (ex < ey + (p - 1)) & (fx > ey) & (ex > fx + 1) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey > fx + p) & (ey < ex + (p - 1)) & (fy > ex) & (ey > fy + 1) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S3C-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (ex < ey + (p - 1)) & (fx == ey) & (ex > fx + 2) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S3C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey > fx + p) & (ey < ex + (p - 1)) & (fy == ex) & (ey > fy + 2) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S3CE-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (fx == ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S3CE-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (fy == ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S3D0-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx < ey) & (ey == fy + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 1, 0, ex - p, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S3D0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy < ex) & (ex == fx + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 1, 0, ey - p, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S3D3-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx < ey) & (ey == fy + (p - 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 1, 0, fx - 2, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S3D3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy < ex) & (ex == fx + (p - 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 1, 0, fy - 2, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S3E-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex < ey + (p - 1)) & (fx > ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, ey),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S3E-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey < ex + (p - 1)) & (fy > ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, ex),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S3F-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx == fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S3F-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy == fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S3G0-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (ex == fy + (p + 1)) & (fx < ey) & (ey < fy + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ex - p, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S3G0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (ey == fx + (p + 1)) & (fy < ex) & (ex < fx + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ey - p, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S3G3-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (ex == fy + (p + 1)) & (fx < ey) & (ey < fy + (p - 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, ex - p, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S3G3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (ey == fx + (p + 1)) & (fy < ex) & (ex < fx + (p - 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, ey - p, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S3H0-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (ex == fy + (p + 2)) & (fx < ey) & (ey < fy + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 1, 0, ex - p, ex - (p + 2), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S3H0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (ey == fx + (p + 2)) & (fy < ex) & (ex < fx + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 1, 0, ey - p, ey - (p + 2), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S4-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex < fy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey < fx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-S4A-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex < fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-S4A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey < fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

end
