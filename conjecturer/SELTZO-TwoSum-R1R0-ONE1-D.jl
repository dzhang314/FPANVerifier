function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R1R0},
    ::Val{ONE1},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R1R0-ONE1-DE0-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 1 < fy) & (ex > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DE0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 1 < fx) & (ey > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DE1-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 1 < fy) & (ex == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DE1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 1 < fx) & (ey == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DE2-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 1 == fy) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DE2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 1 == fx) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DE30-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 1 > fy) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DE30-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 1 > fx) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DE31-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == ey) & (ex > fy + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DE31-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == ex) & (ey > fx + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DE32-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == ey) & (ex > fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DE32-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == ex) & (ey > fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DE41-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == ey) & (ey == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fy - p, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DE41-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == ex) & (ex == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fx - p, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DE42-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == ey) & (ey == fy + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy + 1, fy - (p - 1), fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DE42-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == ex) & (ex == fx + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx + 1, fx - (p - 1), fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DA100-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex < fy + (p - 1)) & (fx + 1 > fy) & (ex == ey + 1) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DA100-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey < fx + (p - 1)) & (fy + 1 > fx) & (ey == ex + 1) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DA101-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex < fy + (p - 1)) & (ex == ey + 1) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DA101-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey < fx + (p - 1)) & (ey == ex + 1) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DA102-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DA102-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DA11-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (fx + 1 == fy) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DA11-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (fy + 1 == fx) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DA120-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == fy + (p - 1)) & (ex == ey + 1) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DA120-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == fx + (p - 1)) & (ey == ex + 1) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DA121-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == fy + (p - 1)) & (ex == ey + 1) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DA121-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == fx + (p - 1)) & (ey == ex + 1) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DA201-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex < fy + (p - 1)) & (ex == ey + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DA201-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey < fx + (p - 1)) & (ey == ex + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DA202-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex < fy + (p - 1)) & (ex == ey + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DA202-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey < fx + (p - 1)) & (ey == ex + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DA21-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == fy + (p - 1)) & (ex == ey + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DA21-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == fx + (p - 1)) & (ey == ex + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DA22-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == fy + (p - 1)) & (ex == ey + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DA22-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == fx + (p - 1)) & (ey == ex + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-D1-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex < fy + (p - 1)) & (ex > ey + 1) & (fx + 1 > fy) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-D1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey < fx + (p - 1)) & (ey > ex + 1) & (fy + 1 > fx) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-D1A-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex < fy + (p - 1)) & (fx + 1 == ey) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-D1A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey < fx + (p - 1)) & (fy + 1 == ex) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-D1B-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == fy + (p - 1)) & (ex > ey + 1) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-D1B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == fx + (p - 1)) & (ey > ex + 1) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-D1C-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (fx + 1 == fy) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-D1C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (fy + 1 == fx) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-D1AB-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == fy + (p - 1)) & (fx + 1 == ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-D1AB-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == fx + (p - 1)) & (fy + 1 == ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-D2-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex > fy + (p - 1)) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-D2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey > fx + (p - 1)) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-D2A-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex > fy + (p - 1)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-D2A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey > fx + (p - 1)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-D3-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (fx + 1 > ey) & (ex < fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-D3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (fy + 1 > ex) & (ey < fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-D3A-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex < fy + (p - 1)) & (ex > ey + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-D3A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey < fx + (p - 1)) & (ey > ex + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-D3B-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == fy + (p - 1)) & (fx < fy + (p - 3)) & (fx + 1 > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx + 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-D3B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == fx + (p - 1)) & (fy < fx + (p - 3)) & (fy + 1 > ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy + 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-D3AB-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == fy + (p - 1)) & (fx == fy + (p - 3)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-D3AB-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == fx + (p - 1)) & (fy == fx + (p - 3)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-D4-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex > fy + (p - 1)) & (ex < ey + (p - 1)) & (fx + 1 > ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-D4-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey > fx + (p - 1)) & (ey < ex + (p - 1)) & (fy + 1 > ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-D4A-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex > fy + (p - 1)) & (ex < ey + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-D4A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey > fx + (p - 1)) & (ey < ex + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DB10-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1)) & (fx < ey + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DB10-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1)) & (fy < ex + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DB11-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1)) & (fx == ey + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ex - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DB11-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1)) & (fy == ex + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ey - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DB20-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == ey + p) & (fx < ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DB20-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == ex + p) & (fy < ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-R1R0-ONE1-DB21-X",
        (CLASS_X == R1R0) & (CLASS_Y == ONE1) &
        (ex == ey + p) & (fx == ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ex - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-R1R0-ONE1-DB21-Y",
        (CLASS_Y == R1R0) & (CLASS_X == ONE1) &
        (ey == ex + p) & (fy == ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ey - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
