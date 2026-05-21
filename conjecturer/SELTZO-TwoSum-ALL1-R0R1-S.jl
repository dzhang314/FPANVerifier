function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
    ::Val{R0R1},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ALL1-R0R1-SE0-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, ex - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-SE0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, ey - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-SE1-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, ex - 1, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-SE1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, ey - 1, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-S1-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex > fy + (p + 1)) & (ex < ey + (p - 2)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-S1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey > fx + (p + 1)) & (ey < ex + (p - 2)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-S1A-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex == fy + (p + 1)) & (ex < ey + (p - 2)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 0, 0, ex - p, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-S1A-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey == fx + (p + 1)) & (ey < ex + (p - 2)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 0, 0, ey - p, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-S1B-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex > fy + (p + 1)) & (ex == ey + (p - 2)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(~sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-S1B-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey > fx + (p + 1)) & (ey == ex + (p - 2)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(~sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-S1C-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (ex < ey + (p - 2)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 1, 0, ex - p, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-S1C-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (ey < ex + (p - 2)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 1, 0, ey - p, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-S1AB-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex == fy + (p + 1)) & (ex == ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ex - p, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-S1AB-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey == fx + (p + 1)) & (ey == ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ey - p, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-S1BC-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 2)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(~sy, 1, 0, ex - p, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-S1BC-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey == ex + (p - 2)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(~sx, 1, 0, ey - p, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-S2-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex < fy + (p - 1)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-S2-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey < fx + (p - 1)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-S2A-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex == fy + (p - 1)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-S2A-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey == fx + (p - 1)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-S2B0-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (ex > ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-S2B0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey == fx + p) & (ey > ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-S2B1-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-S2B1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-S2C-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex < fy + (p - 1)) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-S2C-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey < fx + (p - 1)) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-S2AC-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex == fy + (p - 1)) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-S2AC-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey == fx + (p - 1)) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-S2BC-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-S2BC-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey == fx + p) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-SB10-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ex + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-SB10-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ey + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-SB11-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ex + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-SB11-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ey + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-SB20-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey + 1, ex + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-SB20-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex + 1, ey + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-SB21-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey + 1, ex + 1),
            SELTZORange(~sy, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-SB21-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex + 1, ey + 1),
            SELTZORange(~sx, 0, 0, ex - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-SB22-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey + 1, ex + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-SB22-Y",
        (CLASS_Y == ALL1) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex + 1, ey + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

end
