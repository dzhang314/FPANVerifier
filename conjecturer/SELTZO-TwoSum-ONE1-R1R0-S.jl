function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
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

    checker("SELTZO-TwoSum-ONE1-R1R0-SA0-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx > fy + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-SA0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy > fx + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-SA1-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-SA1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-SA2-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx + (p - 3) > ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-SA2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy + (p - 3) > ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-SA3-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (ex == ey + 1) & (fx + (p - 3) > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-SA3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == fx + p) & (ey == ex + 1) & (fy + (p - 3) > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-SA4-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (fx + (p - 3) == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, ex + 1),
            SELTZORange(sy, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-SA4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == fx + p) & (fy + (p - 3) == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, ey + 1),
            SELTZORange(sx, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-SA5-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-SA5-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-S1-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex < fy + p) & (fx < ey) & (ex > ey + 2) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-S1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey < fx + p) & (fy < ex) & (ey > ex + 2) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-S1A-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-S1A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-S1B-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx > fy + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-S1B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy > fx + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-S1AB-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ex - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-S1AB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ey - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-S2-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex > fy + p) & (ex > ey + 2) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-S2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey > fx + p) & (ey > ex + 2) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-S2A0-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (ex > ey + 2) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-S2A0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == fx + p) & (ey > ex + 2) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-S2A1-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-S2A1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == fx + p) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-S2A2-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-S2A2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-S2B-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == fy + (p + 1)) & (ex == ey + 2) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-S2B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == fx + (p + 1)) & (ey == ex + 2) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-S2C0-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex > fy + p) & (fx == ey + 1) & (ex > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-S2C0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey > fx + p) & (fy == ex + 1) & (ey > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-S2C1-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex > fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-S2C1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey > fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-S2D-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex > fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-S2D-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (fy == ex) & (ey > fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-SB-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == ey + p) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-SB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == ex + p) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
