function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{POW2},
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

    checker("SELTZO-TwoSum-POW2-R1R0-DA1-X",
        (CLASS_X == POW2) & (CLASS_Y == R1R0) &
        (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy + 1, fy - (p - 1), fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-R1R0-DA1-Y",
        (CLASS_Y == POW2) & (CLASS_X == R1R0) &
        (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx + 1, fx - (p - 1), fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-R1R0-DA20-X",
        (CLASS_X == POW2) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (ex < fy + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-R1R0-DA20-Y",
        (CLASS_Y == POW2) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (ey < fx + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-R1R0-DA21-X",
        (CLASS_X == POW2) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex - 1, fy + 1, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-R1R0-DA21-Y",
        (CLASS_Y == POW2) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey - 1, fx + 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-R1R0-D1-X",
        (CLASS_X == POW2) & (CLASS_Y == R1R0) &
        (ex > fy + (p + 1)) & (ex < ey + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-POW2-R1R0-D1-Y",
        (CLASS_Y == POW2) & (CLASS_X == R1R0) &
        (ey > fx + (p + 1)) & (ey < ex + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-POW2-R1R0-D2-X",
        (CLASS_X == POW2) & (CLASS_Y == R1R0) &
        (ex < fy + (p + 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-R1R0-D2-Y",
        (CLASS_Y == POW2) & (CLASS_X == R1R0) &
        (ey < fx + (p + 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-R1R0-D2A-X",
        (CLASS_X == POW2) & (CLASS_Y == R1R0) &
        (ex == fy + (p + 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-R1R0-D2A-Y",
        (CLASS_Y == POW2) & (CLASS_X == R1R0) &
        (ey == fx + (p + 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-R1R0-DB-X",
        (CLASS_X == POW2) & (CLASS_Y == R1R0) &
        (ex == ey + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ey + p),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-POW2-R1R0-DB-Y",
        (CLASS_Y == POW2) & (CLASS_X == R1R0) &
        (ey == ex + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ex + p),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
