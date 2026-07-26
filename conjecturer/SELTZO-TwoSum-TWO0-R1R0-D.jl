function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO0},
    ::Val{R1R0},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-TWO0-R1R0-DE0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-DE0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-DE1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fy - 3, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-DE1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fx - 3, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-DE20-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx == fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-DE20-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy == fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-DE21-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-DE21-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-DE30-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx == fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy, ex - (p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-DE30-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy == fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx, ey - (p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-DE31-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx == fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fy, fy - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-DE31-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy == fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fx, fx - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-DE4-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-DE4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-DE5-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fx, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-DE5-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fy, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-DA0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx > fy + 1) & (ex > fx + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-DA0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy > fx + 1) & (ey > fy + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-DA1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (ex > fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-DA1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (ey > fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-DA2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx > fy + 1) & (ex == fx + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-DA2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy > fx + 1) & (ey == fy + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-DA3-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-DA3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-DA5-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-DA5-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-DA6-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-DA6-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey) & (fx > fy + 2) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex) & (fy > fx + 2) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D1A-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < ey) & (fx > fy + 2) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D1A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < ex) & (fy > fx + 2) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D1B-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D1B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D1AB0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == fy + 2) & (fx < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D1AB0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == fx + 2) & (fy < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D1AB1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == fy + 2) & (fx == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D1AB1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == fx + 2) & (fy == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D1C-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D1C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D1AC-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D1AC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D1AD-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == ey) & (fx > fy + 2) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D1AD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == ex) & (fy > fx + 2) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D1E-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey + 1) & (fx > fy + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D1E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex + 1) & (fy > fx + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D1AE-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < ey) & (fx > fy + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D1AE-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < ex) & (fy > fx + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D1ADE-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == ey) & (fx > fy + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D1ADE-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == ex) & (fy > fx + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D2A-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey + 3) & (fx == ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D2A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex + 3) & (fy == ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D2E-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D2E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D2AE-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey + 3) & (fx == ey + 1) & (fx > fy + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D2AE-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex + 3) & (fy == ex + 1) & (fy > fx + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D2ACE-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey + 3) & (fx == ey + 1) & (fx > fy + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D2ACE-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex + 3) & (fy == ex + 1) & (fy > fx + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D3-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey + 1) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex + 1) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D3E-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey + 1) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx - 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D3E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex + 1) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy - 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D3AE-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < ey) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D3AE-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < ex) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D3ABE-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == ey) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D3ABE-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == ex) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D4A-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey + 2) & (ex > fy + (p + 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D4A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex + 2) & (ey > fx + (p + 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D4AC-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey + 2) & (ex > fy + (p + 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D4AC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex + 2) & (ey > fx + (p + 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D4AE-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey + 2) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D4AE-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex + 2) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D4B-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex > ey + 3) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D4B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey > ex + 3) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D4BE-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex > ey + 3) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx - 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D4BE-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey > ex + 3) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy - 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D4BC-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex == ey + 3) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D4BC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey == ex + 3) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-D4BCE-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex == ey + 3) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-D4BCE-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey == ex + 3) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-TWO0-R1R0-DB-X",
        (CLASS_X == TWO0) & (CLASS_Y == R1R0) &
        (ex == ey + p) & (fx == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-TWO0-R1R0-DB-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R1R0) &
        (ey == ex + p) & (fy == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
