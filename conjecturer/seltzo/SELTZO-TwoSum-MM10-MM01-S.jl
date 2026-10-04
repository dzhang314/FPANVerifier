function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM10},
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

    checker("SELTZO-TwoSum-MM10-MM01-SE0-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey) & (fx > fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM01-SE0-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex) & (fy > fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM01-SE11-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey) & (fx == fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM01-SE11-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex) & (fy == fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM01-SE12-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey) & (fx == fy + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM01-SE12-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex) & (fy == fx + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM01-SE2-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey) & (ey == fy + (p - 3)) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM01-SE2-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex) & (ex == fx + (p - 3)) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA10-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx > fy + 1) & (ex == ey + 1) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA10-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy > fx + 1) & (ey == ex + 1) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA11-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx > fy + 2) & (ex == ey + 1) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA11-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy > fx + 2) & (ey == ex + 1) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA12-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx > fy + 2) & (ex == ey + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA12-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy > fx + 2) & (ey == ex + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA13-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == fy + 2) & (ex == ey + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA13-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == fx + 2) & (ey == ex + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA14-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == fy + 1) & (ex == ey + 1) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, fx - 2),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA14-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == fx + 1) & (ey == ex + 1) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, fy - 2),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA151-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == fy + 1) & (ex == ey + 1) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA151-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == fx + 1) & (ey == ex + 1) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA152-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == fy + 2) & (ex == ey + 1) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fx),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA152-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == fx + 2) & (ey == ex + 1) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fy),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA16-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == fy + 1) & (ex == ey + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fy, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA16-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == fx + 1) & (ey == ex + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fx, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA17-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == fy) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - (p - 1), ex), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA17-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == fx) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - (p - 1), ey), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA18-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx + 1 == fy) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA18-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy + 1 == fx) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA20-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx < ey) & (fx > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA20-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy < ex) & (fy > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA21-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx < ey) & (ex == fy + (p - 2)) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA21-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy < ex) & (ey == fx + (p - 2)) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA221-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == fy + 1) & (ex == ey + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA221-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == fx + 1) & (ey == ex + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA222-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == fy + 2) & (ex == ey + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA222-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == fx + 2) & (ey == ex + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA23-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx < ey) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA23-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy < ex) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA24-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx == fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx),
            SELTZORange(~sy, 0, 0, fx - 3, fx - (p + 3), fx - 3))
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA24-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy == fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy),
            SELTZORange(~sx, 0, 0, fy - 3, fy - (p + 3), fy - 3))
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA25-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx == ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - 3, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA25-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy == ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - 3, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA26-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == ey + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ex - 3, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA26-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex) & (ey == ex + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ey - 3, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-SA27-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == ey + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 3, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-SA27-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex) & (ey == ex + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 3, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-S1-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx > ey + 2) & (ex > fy + p) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-S1-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy > ex + 2) & (ey > fx + p) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-S1A-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey + 2) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 3),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-S1A-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex + 2) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 3),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-S1B-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-S1B-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-S1C-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-S1C-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-S1D-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-S1D-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-S1E-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-S1E-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-S2-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx < ey) & (fx > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-S2-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy < ex) & (fy > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-S2A-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex > ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-S2A-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey > ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-S2D-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx + 1 == fy) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-S2D-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy + 1 == fx) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-S2B0-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx < ey + 1) & (ex == fy + (p - 2)) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-S2B0-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy < ex + 1) & (ey == fx + (p - 2)) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-S2B11-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx == fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-S2B11-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy == fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-S2B12-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx == fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-S2B12-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy == fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-S2C0-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx < ey + 1) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-S2C0-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy < ex + 1) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-S2C1-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx == fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, fx - 3, fx - (p + 3), fx - 3))
    end
    checker("SELTZO-TwoSum-MM10-MM01-S2C1-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy == fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, fy - 3, fy - (p + 3), fy - 3))
    end

    checker("SELTZO-TwoSum-MM10-MM01-S3-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx < ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-S3-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy < ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-S3B0-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx < ey + 1) & (ex == fy + p) & (fx > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-S3B0-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy < ex + 1) & (ey == fx + p) & (fy > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-S3B1-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx < ey + 1) & (ex == fy + p) & (fx == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx),
            SELTZORange(sy, 0, 0, gx - 3, gx - (p + 3), gx - 3))
    end
    checker("SELTZO-TwoSum-MM10-MM01-S3B1-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy < ex + 1) & (ey == fx + p) & (fy == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy),
            SELTZORange(sx, 0, 0, gy - 3, gy - (p + 3), gy - 3))
    end

    checker("SELTZO-TwoSum-MM10-MM01-S4-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-S4-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-S4A-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex < fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey + 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-S4A-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey < fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex + 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-S4AC-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-S4AC-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-S4ABC-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM01-S4ABC-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM01-S4AD-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 2, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-S4AD-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 2, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-S4ABD-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-S4ABD-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-S4AE0-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + p) & (ex > fx + 2) & (fx > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 2, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-S4AE0-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + p) & (ey > fy + 2) & (fy > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 2, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-S4AE1-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + p) & (fx == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 2, ey + 2),
            SELTZORange(sy, 0, 0, ey - 3, ey - (p + 3), ey - 3))
    end
    checker("SELTZO-TwoSum-MM10-MM01-S4AE1-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + p) & (fy == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 2, ex + 2),
            SELTZORange(sx, 0, 0, ex - 3, ex - (p + 3), ex - 3))
    end

    checker("SELTZO-TwoSum-MM10-MM01-S4ABE-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-S4ABE-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-MM01-SB-X",
        (CLASS_X == MM10) & (CLASS_Y == MM01) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-MM01-SB-Y",
        (CLASS_Y == MM10) & (CLASS_X == MM01) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
