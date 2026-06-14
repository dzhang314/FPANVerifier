function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R1R0},
    ::Val{POW2},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R1R0-POW2-S1-X",
        (CLASS_X == R1R0) & (CLASS_Y == POW2) &
        (fx + 1 < ey) & (ex + 1 > ey) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-POW2-S1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == POW2) &
        (fy + 1 < ex) & (ey + 1 > ex) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-POW2-S1A-X",
        (CLASS_X == R1R0) & (CLASS_Y == POW2) &
        (fx + 1 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-POW2-S1A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == POW2) &
        (fy + 1 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-POW2-S1B-X",
        (CLASS_X == R1R0) & (CLASS_Y == POW2) &
        (fx == ey) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-POW2-S1B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == POW2) &
        (fy == ex) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-POW2-S1C-X",
        (CLASS_X == R1R0) & (CLASS_Y == POW2) &
        (fx + 1 < ey) & (ex + 1 > ey) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-POW2-S1C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == POW2) &
        (fy + 1 < ex) & (ey + 1 > ex) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex), pos_zero)
    end

end
