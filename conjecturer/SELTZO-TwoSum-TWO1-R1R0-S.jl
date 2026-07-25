function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO1},
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

    checker("SELTZO-TwoSum-TWO1-R1R0-SA10-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx > fy + 2) & (ex == ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SA10-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy > fx + 2) & (ey == ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-SA11-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == fy) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SA11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == fx) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-SA12-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == fy + 1) & (ex == ey + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fy, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SA12-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == fx + 1) & (ey == ex + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fx, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-SA13-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == fy + 1) & (ex == ey + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fy, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SA13-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == fx + 1) & (ey == ex + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fx, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-SA14-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == fy + 2) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SA14-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == fx + 2) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-SA15-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx > fy + 2) & (ex == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SA15-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy > fx + 2) & (ey == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-SA16-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == fy + 3) & (ex == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fx),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SA16-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == fx + 3) & (ey == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fy),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-SA17-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx > fy + 3) & (ex == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SA17-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy > fx + 3) & (ey == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-SA20-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx > fy + 2) & (fx < ey) & (ex == ey + 2) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SA20-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy > fx + 2) & (fy < ex) & (ey == ex + 2) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-SA21-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == fy + 2) & (fx == ey) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SA21-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == fx + 2) & (fy == ex) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-SA22-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == fy + 1) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SA22-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == fx + 1) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-SA23-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == fy + 2) & (fx < ey) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SA23-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == fx + 2) & (fy < ex) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-SA24-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx > fy + 2) & (fx == ey) & (ex == ey + 2) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SA24-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy > fx + 2) & (fy == ex) & (ey == ex + 2) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-SA25-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex == ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SA25-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex) & (ey == ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-SA26-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx < ey) & (ex == ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SA26-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy < ex) & (ey == ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-SA27-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex == ey + 2) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SA27-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex) & (ey == ex + 2) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-SA28-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx < ey) & (ex == ey + 2) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SA28-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy < ex) & (ey == ex + 2) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-S1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx > fy + 2) & (fx < ey) & (ex > ey + 2) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-S1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy > fx + 2) & (fy < ex) & (ey > ex + 2) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-S1A-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == fy + 2) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-S1A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == fx + 2) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-S1B-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == fy + 1) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-S1B-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == fx + 1) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-S1C-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex > ey + 3) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-S1C-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey > ex + 3) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-S2-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx < ey + 1) & (ex > ey + 2) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-S2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy < ex + 1) & (ey > ex + 2) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-S2A-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx < ey + 1) & (ex > ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-S2A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy < ex + 1) & (ey > ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-S2AB0-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex > ey + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-S2AB0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey > ex + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-S2AB1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex == ey + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-S2AB1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey == ex + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-S2AC-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-S2AC-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-S2B0-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex > ey + 3) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-S2B0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey > ex + 3) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-S2B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex == ey + 3) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-S2B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey == ex + 3) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-S2C0-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey + 2) & (ex > fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-S2C0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex + 2) & (ey > fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-S2C1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey + 2) & (ex > fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-S2C1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex + 2) & (ey > fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO1-R1R0-SB-X",
        (CLASS_X == TWO1) & (CLASS_Y == R1R0) &
        (fx == ey + 3) & (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO1-R1R0-SB-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R1R0) &
        (fy == ex + 3) & (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
