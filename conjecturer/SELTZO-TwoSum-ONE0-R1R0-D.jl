function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
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

    checker("SELTZO-TwoSum-ONE0-R1R0-DA0-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx > fy + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-DA0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy > fx + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-DA1-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx > fy + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-DA1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy > fx + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-DA2-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-DA2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-DA3-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-DA3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-D1-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx > fy + 1) & (fx < ey) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-D1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy > fx + 1) & (fy < ex) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-D1A-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx > fy + 1) & (fx < ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-D1A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy > fx + 1) & (fy < ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-D1B-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-D1B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-D1AB-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-D1AB-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-D2-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex > fy + (p + 1)) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-D2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey > fx + (p + 1)) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-D2A-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == fy + (p + 1)) & (ex > ey + 2) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-D2A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == fx + (p + 1)) & (ey > ex + 2) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-D2AC-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == fy + (p + 1)) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-D2AC-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == fx + (p + 1)) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-D2AD-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == fy + (p + 1)) & (ex == ey + 2) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-D2AD-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == fx + (p + 1)) & (ey == ex + 2) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-D2B-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (ex > ey + 2) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-D2B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == fx + p) & (ey > ex + 2) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-D2BC-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-D2BC-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-D2BD-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (ex == ey + 2) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-D2BD-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == fx + p) & (ey == ex + 2) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-D2C0-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex > fy + (p + 1)) & (fx == ey + 1) & (ex > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-D2C0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey > fx + (p + 1)) & (fy == ex + 1) & (ey > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-D2C1-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == fy + (p + 2)) & (fx == ey + 1) & (ex == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-D2C1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == fx + (p + 2)) & (fy == ex + 1) & (ey == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE0-R1R0-DB-X",
        (CLASS_X == ONE0) & (CLASS_Y == R1R0) &
        (ex == ey + p) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE0-R1R0-DB-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R1R0) &
        (ey == ex + p) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
