function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
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

    checker("SELTZO-TwoSum-ONE1-R1R0-DA10-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy + 1, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-DA10-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx + 1, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-DA11-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx + 1, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-DA11-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy + 1, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-DA12-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-DA12-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-DA13-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-DA13-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-DA14-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fy + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-DA14-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fx + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-DA2-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-DA2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D1-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx < ey) & (ex < fy + (p + 1)) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy < ex) & (ey < fx + (p + 1)) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D1A-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx > fy + 1) & (ex > fx + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D1A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy > fx + 1) & (ey > fy + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D1B-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (fx == fy + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D1B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (fy == fx + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D1C-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex < fy + (p + 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D1C-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (fy == ex) & (ey < fx + (p + 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D1BD-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (fx == fy + 1) & (ex > ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D1BD-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (fy == fx + 1) & (ey > ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D1CD-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex > ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D1CD-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (fy == ex) & (ey > ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D1AB-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx + 1 < ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D1AB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy + 1 < ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D2-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex > fy + (p + 1)) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey > fx + (p + 1)) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D2A0-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == fy + (p + 1)) & (ex > ey + 2) & (fx < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D2A0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == fx + (p + 1)) & (ey > ex + 2) & (fy < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D2A1-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == fy + (p + 1)) & (ex == ey + 2) & (fx < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex - 1, fx, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D2A1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == fx + (p + 1)) & (ey == ex + 2) & (fy < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey - 1, fy, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D2B-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D2B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (fy == ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D2AB-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D2AB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (fy == ex) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D3-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex < fy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey < fx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D3A-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fy + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D3A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fx + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D3B-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D3B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == fx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D3AB-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy + 1, fy + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D3AB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx + 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D4-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex > fy + p) & (ex < ey + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey > fx + p) & (ey < ex + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-D4A-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex > fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-D4A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey > fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ONE1-R1R0-DB-X",
        (CLASS_X == ONE1) & (CLASS_Y == R1R0) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ONE1-R1R0-DB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R1R0) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
