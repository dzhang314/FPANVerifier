function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
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

    checker("SELTZO-TwoSum-R0R1-POW2-SE0-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (ex == ey) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-POW2-SE0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (ey == ex) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-POW2-SE1-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (ex == ey) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, ex + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-POW2-SE1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (ey == ex) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, ey + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-POW2-S1-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (fx + 1 > ey) & (ex < ey + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx + 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-POW2-S1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (fy + 1 > ex) & (ey < ex + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy + 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-POW2-S1A-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (fx + 1 == ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx + 1, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-POW2-S1A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (fy + 1 == ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy + 1, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-POW2-S1B-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (fx + 1 > ey) & (ex < ey + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-POW2-S1B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (fy + 1 > ex) & (ey < ex + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-POW2-S1AB-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (fx + 1 == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-POW2-S1AB-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (fy + 1 == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-POW2-SB10-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (ex == ey + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-POW2-SB10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (ey == ex + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-POW2-SB11-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (ex == ey + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-POW2-SB11-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (ey == ex + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-POW2-SB20-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (ex == ey + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey, ey - p, ey))
    end
    checker("SELTZO-TwoSum-R0R1-POW2-SB20-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (ey == ex + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex, ex - p, ex))
    end

    checker("SELTZO-TwoSum-R0R1-POW2-SB21-X",
        (CLASS_X == R0R1) & (CLASS_Y == POW2) &
        (ex == ey + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey, ey - p, ey))
    end
    checker("SELTZO-TwoSum-R0R1-POW2-SB21-Y",
        (CLASS_Y == R0R1) & (CLASS_X == POW2) &
        (ey == ex + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex, ex - p, ex))
    end

end
