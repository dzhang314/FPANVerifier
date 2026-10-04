function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM01},
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

    checker("SELTZO-TwoSum-MM01-R1R0-DE0-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-DE0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-DE1-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fy - 2, fy - 2), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-DE1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fx - 2, fx - 2), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-DE2-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-DE2-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-DE3-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy, fy - p, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-DE3-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx, fx - p, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-DE4-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fx, fx - p, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-DE4-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fy, fy - p, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-DE5-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fx, fx - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-DE5-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fy, fy - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-DA0-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx > fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-DA0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy > fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-DA1-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx > fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-DA1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy > fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-DA2-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-DA2-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-DA3-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-DA3-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-DA4-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-DA4-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D1-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey) & (fx > fy + 2) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex) & (fy > fx + 2) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D1A-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < ey) & (fx > fy + 2) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D1A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < ex) & (fy > fx + 2) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D1B-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D1B-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D1AB-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D1AB-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D1C-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D1C-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D1AC-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D1AC-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D1AD-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == ey) & (fx > fy + 2) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D1AD-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == ex) & (fy > fx + 2) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D1E0-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey + 1) & (fx > fy + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D1E0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex + 1) & (fy > fx + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D1E1-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx == fy + 3) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D1E1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy == fx + 3) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D1AE0-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < ey) & (fx > fy + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D1AE0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < ex) & (fy > fx + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D1AE1-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < ey) & (fx == fy + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D1AE1-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < ex) & (fy == fx + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D1ADE0-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == ey) & (fx > fy + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D1ADE0-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == ex) & (fy > fx + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D2-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx > ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D2-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy > ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D2A-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey + 3) & (fx == ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D2A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex + 3) & (fy == ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D2E-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D2E-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D2AE-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey + 3) & (fx == ey + 1) & (fx > fy + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx + 1, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D2AE-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex + 3) & (fy == ex + 1) & (fy > fx + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy + 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D2ABE-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey + 3) & (fx == fy + 3) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D2ABE-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex + 3) & (fy == fx + 3) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D2ACE-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey + 3) & (fx == ey + 1) & (fx > fy + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D2ACE-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex + 3) & (fy == ex + 1) & (fy > fx + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D3-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D3-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D3A-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < ey) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D3A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < ex) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D3AB-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == ey) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D3AB-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == ex) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D4-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx > ey + 2) & (ex > fy + p) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D4-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy > ex + 2) & (ey > fx + p) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D4A-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx == ey + 2) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D4A-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy == ex + 2) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D4B-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex > ey + 3) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D4B-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey > ex + 3) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM01-R1R0-D4BC-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex == ey + 3) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM01-R1R0-D4BC-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey == ex + 3) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-MM01-R1R0-DB-X",
        (CLASS_X == MM01) & (CLASS_Y == R1R0) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-MM01-R1R0-DB-Y",
        (CLASS_Y == MM01) & (CLASS_X == R1R0) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
