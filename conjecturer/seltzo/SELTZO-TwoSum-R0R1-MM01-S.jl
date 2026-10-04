function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
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

    checker("SELTZO-TwoSum-R0R1-MM01-SA10-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx > fy) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SA10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy > fx) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SA11-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SA11-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SA12-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx > fy) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fy + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SA12-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy > fx) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fx + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SA13-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SA13-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SA14-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx > fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SA14-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy > fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SA15-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SA15-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SA16-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SA16-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SA17-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 1 == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SA17-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 1 == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SA18-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 1 == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SA18-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 1 == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SA20-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx + 1 > fy) & (fx < ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SA20-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy + 1 > fx) & (fy < ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SA21-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx == ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SA21-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy == ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SA22-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx == fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SA22-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy == fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SA23-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx > fy) & (fx < ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SA23-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy > fx) & (fy < ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SA24-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SA24-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SA25-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx == fy) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SA25-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy == fx) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SA26-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx > fy) & (fx < ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SA26-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy > fx) & (fy < ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SA27-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SA27-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx + 1 > fy) & (fx < ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy + 1 > fx) & (fy < ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S1A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > ey + 1) & (fx + 1 == fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S1A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > ex + 1) & (fy + 1 == fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S1B-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > ey + 1) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S1B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > ex + 1) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S1C0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx > fy) & (fx < ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S1C0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy > fx) & (fy < ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S1C1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx == fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S1C1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy == fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S1C2-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > ey + 1) & (fx + 1 == fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S1C2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > ex + 1) & (fy + 1 == fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S1D0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx > fy) & (fx < ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S1D0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy > fx) & (fy < ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S1D1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx == fy) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S1D1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy == fx) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S1E0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (fx > fy + 1) & (fx < ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S1E0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (fy > fx + 1) & (fy < ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S1E1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (fx == fy + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S1E1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (fy == fx + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S2-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (fx + 1 > ey) & (ex < fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (fy + 1 > ex) & (ey < fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S2A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S2A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S2B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (fx > ey) & (ex == fy + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S2B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (fy > ex) & (ey == fx + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S2B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (fx > ey) & (ex == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S2B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (fy > ex) & (ey == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S2C0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (fx > ey) & (ex == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S2C0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (fy > ex) & (ey == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S2C1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (fx > ey) & (ex == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S2C1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (fy > ex) & (ey == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S2D0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (fx > ey) & (ex == fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S2D0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (fy > ex) & (ey == fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S2D1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S2D1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S3-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (fx < ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (fy < ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S3A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S3A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S4-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex < ey + p) & (fx > ey) & (ex > fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey < ex + p) & (fy > ex) & (ey > fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-S4A-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex < ey + p) & (ex > fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-S4A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey < ex + p) & (ey > fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SB0-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SB0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-MM01-SB1-X",
        (CLASS_X == R0R1) & (CLASS_Y == MM01) &
        (ex == ey + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-MM01-SB1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == MM01) &
        (ey == ex + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
