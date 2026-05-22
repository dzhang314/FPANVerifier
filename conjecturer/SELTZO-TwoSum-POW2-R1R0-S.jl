function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{POW2},
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

    checker("SELTZO-TwoSum-POW2-R1R0-S1-X",
        (CLASS_X == POW2) & (CLASS_Y == R1R0) &
        (ex > fy + p) & (ex > ey + 2) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-POW2-R1R0-S1-Y",
        (CLASS_Y == POW2) & (CLASS_X == R1R0) &
        (ey > fx + p) & (ey > ex + 2) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-POW2-R1R0-S1A0-X",
        (CLASS_X == POW2) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-R1R0-S1A0-Y",
        (CLASS_Y == POW2) & (CLASS_X == R1R0) &
        (ey == fx + p) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-R1R0-S1A1-X",
        (CLASS_X == POW2) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-R1R0-S1A1-Y",
        (CLASS_Y == POW2) & (CLASS_X == R1R0) &
        (ey == fx + p) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-R1R0-S1B-X",
        (CLASS_X == POW2) & (CLASS_Y == R1R0) &
        (ex == fy + (p + 1)) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-POW2-R1R0-S1B-Y",
        (CLASS_Y == POW2) & (CLASS_X == R1R0) &
        (ey == fx + (p + 1)) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-POW2-R1R0-SB-X",
        (CLASS_X == POW2) & (CLASS_Y == R1R0) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-POW2-R1R0-SB-Y",
        (CLASS_Y == POW2) & (CLASS_X == R1R0) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
