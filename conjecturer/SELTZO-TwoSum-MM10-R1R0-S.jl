function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM10},
    ::Val{R1R0},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-MM10-R1R0-SA10-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA10-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA11-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA11-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA12-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA12-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA13-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA13-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA14-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx > fy + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA14-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy > fx + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA15-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx > fy + 2) & (ey == fy + (p - 2)) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, ex - (p - 3)),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA15-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy > fx + 2) & (ex == fx + (p - 2)) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, ey - (p - 3)),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA16-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx > fy + 2) & (ey == fy + (p - 2)) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fx),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA16-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy > fx + 2) & (ex == fx + (p - 2)) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fy),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA17-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx > fy + 2) & (ey == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA17-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy > fx + 2) & (ex == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA18-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx > fy + 2) & (ey == fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA18-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy > fx + 2) & (ex == fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA20-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA20-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA21-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA21-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA22-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx > fy + 2) & (fx < ey) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA22-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy > fx + 2) & (fy < ex) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA23-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx > fy + 2) & (fx == ey) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA23-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy > fx + 2) & (fy == ex) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA22A0-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < ey) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA22A0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < ex) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA22A1-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < ey) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA22A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < ex) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA23A0-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == ey) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA23A0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == ex) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA22B0-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < ey) & (ex == fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ex - (p - 2)),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA22B0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < ex) & (ey == fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ey - (p - 2)),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA22B1-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < ey) & (ex == fy + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA22B1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < ex) & (ey == fx + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SA23B0-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == ey) & (ex == fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, ex - (p - 2)),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SA23B0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == ex) & (ey == fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, ey - (p - 2)),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S1A-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S1A-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S1B-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey + 1) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S1B-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex + 1) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S1-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey) & (fx > fy + 2) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex) & (fy > fx + 2) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S1C0-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey + 1) & (fx > fy + 2) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S1C0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex + 1) & (fy > fx + 2) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S1C1-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey + 1) & (fx > fy + 2) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S1C1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex + 1) & (fy > fx + 2) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S1D0-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey + 1) & (ex == fy + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ex - (p - 2)),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S1D0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex + 1) & (ey == fx + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ey - (p - 2)),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S1D1-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey + 1) & (ex == fy + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S1D1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex + 1) & (ey == fx + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S1E-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey + 1) & (ex < ey + p) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S1E-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex + 1) & (ey < ex + p) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S2-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx == ey + 1) & (ex > fx + 2) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S2-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy == ex + 1) & (ey > fy + 2) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S2A0-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx == ey + 1) & (ex > fx + 2) & (ex < fx + (p - 3)) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx + 1, ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S2A0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy == ex + 1) & (ey > fy + 2) & (ey < fy + (p - 3)) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy + 1, ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S2A1-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == fx + 2) & (fx == ey + 1) & (ex < fx + (p - 3)) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S2A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == fy + 2) & (fy == ex + 1) & (ey < fy + (p - 3)) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S2A2-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx == ey + 1) & (ex > fx + 2) & (ex == fx + (p - 3)) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S2A2-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy == ex + 1) & (ey > fy + 2) & (ey == fy + (p - 3)) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S2B0-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx == ey + 1) & (ex > fx + 2) & (ex < fx + (p - 3)) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, ex - (p - 2)),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S2B0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy == ex + 1) & (ey > fy + 2) & (ey < fy + (p - 3)) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, ey - (p - 2)),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S2B1-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == fx + 2) & (fx == ey + 1) & (ex < fx + (p - 3)) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ex - (p - 2)),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S2B1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == fy + 2) & (fy == ex + 1) & (ey < fy + (p - 3)) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ey - (p - 2)),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S2C0-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx == ey + 1) & (ex > fx + 2) & (ex == fx + (p - 3)) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S2C0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy == ex + 1) & (ey > fy + 2) & (ey == fy + (p - 3)) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S2D0-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx == ey + 1) & (ex > fx + 2) & (ex < ey + p) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S2D0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy == ex + 1) & (ey > fy + 2) & (ey < ex + p) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S2D1-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == fx + 2) & (fx == ey + 1) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S2D1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == fy + 2) & (fy == ex + 1) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S3-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx > ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S3-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy > ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S3E-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S3E-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S3B-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex < ey + (p - 1)) & (fx > ey + 1) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ex - (p - 2)),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S3B-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey < ex + (p - 1)) & (fy > ex + 1) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ey - (p - 2)),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S3C-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx == ey + 2) & (ex < ey + p) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S3C-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy == ex + 2) & (ey < ex + p) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-S3D-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx > ey + 2) & (ex < ey + p) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-S3D-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy > ex + 2) & (ey < ex + p) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM10-R1R0-SB-X",
        (CLASS_X == MM10) & (CLASS_Y == R1R0) &
        (ex == ey + (p - 1)) & (fx > ey + 1) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM10-R1R0-SB-Y",
        (CLASS_Y == MM10) & (CLASS_X == R1R0) &
        (ey == ex + (p - 1)) & (fy > ex + 1) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
