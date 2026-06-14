function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
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

    checker("SELTZO-TwoSum-R0R1-POW2-DE0-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (ex == ey) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-POW2-DE0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (ey == ex) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-POW2-DE1-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (ex == ey) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fx - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-POW2-DE1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (ey == ex) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fy - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-POW2-D1-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (fx + 1 < ey) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-POW2-D1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (fy + 1 < ex) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-POW2-D1A-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (fx + 1 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-POW2-D1A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (fy + 1 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-POW2-D1B-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (fx == ey) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-POW2-D1B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (fy == ex) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-POW2-D1C-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (fx + 1 < ey) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-POW2-D1C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (fy + 1 < ex) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-POW2-DB0-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (ex == ey + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey, ey - p, ey))
    end
    checker("SELTZO-TwoSum-R0R1-POW2-DB0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (ey == ex + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, ex, ex - p, ex))
    end

    checker("SELTZO-TwoSum-R0R1-POW2-DB1-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (ex == ey + p) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, ey, ey - p, ey))
    end
    checker("SELTZO-TwoSum-R0R1-POW2-DB1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (ey == ex + p) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, ex, ex - p, ex))
    end

end
