function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R1R0},
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

    checker("SELTZO-TwoSum-R1R0-R1R0-SE0-X",
        (CLASS_X == R1R0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx > fy) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-SE0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy > fx) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-SE1",
        (CLASS_X == R1R0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, fx + 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-SE2-X",
        (CLASS_X == R1R0) & (CLASS_Y == R1R0) &
        (ex == ey) & (fx > fy) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-SE2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R1R0) &
        (ey == ex) & (fy > fx) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S1-X",
        (CLASS_X == R1R0) & (CLASS_Y == R1R0) &
        (ex < fy + (p - 1)) & (fx + 1 < ey) & (ex > ey) & (fx > fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R1R0) &
        (ey < fx + (p - 1)) & (fy + 1 < ex) & (ey > ex) & (fy > fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S1A-X",
        (CLASS_X == R1R0) & (CLASS_Y == R1R0) &
        (ex == fy + (p - 1)) & (fx + 1 < ey) & (ex > ey) & (fx > fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S1A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R1R0) &
        (ey == fx + (p - 1)) & (fy + 1 < ex) & (ey > ex) & (fy > fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S1B-X",
        (CLASS_X == R1R0) & (CLASS_Y == R1R0) &
        (ex < fy + (p - 1)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S1B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R1R0) &
        (ey < fx + (p - 1)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S1AB-X",
        (CLASS_X == R1R0) & (CLASS_Y == R1R0) &
        (ex == fy + (p - 1)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S1AB-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R1R0) &
        (ey == fx + (p - 1)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S2-X",
        (CLASS_X == R1R0) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx < fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R1R0) &
        (ey > ex) & (fy < fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S2A-X",
        (CLASS_X == R1R0) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fx + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S2A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R1R0) &
        (ey > ex) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fy + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S2B-X",
        (CLASS_X == R1R0) & (CLASS_Y == R1R0) &
        (ex > ey) & (fx < fy) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S2B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R1R0) &
        (ey > ex) & (fy < fx) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S3-X",
        (CLASS_X == R1R0) & (CLASS_Y == R1R0) &
        (ex > fy + (p - 1)) & (fx < ey) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R1R0) &
        (ey > fx + (p - 1)) & (fy < ex) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S4-X",
        (CLASS_X == R1R0) & (CLASS_Y == R1R0) &
        (ex > fy + p) & (fx > ey + 1) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S4-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R1R0) &
        (ey > fx + p) & (fy > ex + 1) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
