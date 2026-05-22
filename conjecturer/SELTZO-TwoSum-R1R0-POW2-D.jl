function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R1R0},
    ::Val{POW2},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R1R0-POW2-DE0-X",
        (CLASS_X == R1R0) & (CLASS_Y == POW2) &
        (ex == ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-POW2-DE0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == POW2) &
        (ey == ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-POW2-DE1-X",
        (CLASS_X == R1R0) & (CLASS_Y == POW2) &
        (ex == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - (p - 1), fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-POW2-DE1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == POW2) &
        (ey == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - (p - 1), fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-POW2-D1-X",
        (CLASS_X == R1R0) & (CLASS_Y == POW2) &
        (fx + 1 > ey) & (ex < ey + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-POW2-D1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == POW2) &
        (fy + 1 > ex) & (ey < ex + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-POW2-D1A-X",
        (CLASS_X == R1R0) & (CLASS_Y == POW2) &
        (fx + 1 == ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-POW2-D1A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == POW2) &
        (fy + 1 == ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-POW2-D1B-X",
        (CLASS_X == R1R0) & (CLASS_Y == POW2) &
        (ex == ey + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-POW2-D1B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == POW2) &
        (ey == ex + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-POW2-D1C-X",
        (CLASS_X == R1R0) & (CLASS_Y == POW2) &
        (fx + 1 > ey) & (ex < ey + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-POW2-D1C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == POW2) &
        (fy + 1 > ex) & (ey < ex + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-POW2-D1AC-X",
        (CLASS_X == R1R0) & (CLASS_Y == POW2) &
        (ey == fx + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-POW2-D1AC-Y",
        (CLASS_Y == R1R0) & (CLASS_X == POW2) &
        (ex == fy + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-POW2-D1BC-X",
        (CLASS_X == R1R0) & (CLASS_Y == POW2) &
        (ex == ey + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-POW2-D1BC-Y",
        (CLASS_Y == R1R0) & (CLASS_X == POW2) &
        (ey == ex + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fy + 1), pos_zero)
    end

end
