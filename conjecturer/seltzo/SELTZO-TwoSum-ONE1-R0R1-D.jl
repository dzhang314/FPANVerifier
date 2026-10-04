function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
    ::Val{R0R1},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ONE1-R0R1-DE-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey) & (ex < fx + (p - 2)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx - 1, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-DE-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex) & (ey < fy + (p - 2)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy - 1, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-D1-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex < fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fy, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-D1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (fy == ex) & (ey < fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fx, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-D1A-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex > fy + (p + 1)) & (fx == ey) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-D1A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey > fx + (p + 1)) & (fy == ex) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-D2-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx > ey) & (ex < ey + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-D2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy > ex) & (ey < ex + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-D2A-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (fx > ey) & (ex < ey + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-D2A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (fy > ex) & (ey < ex + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-DA-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex < fy + p) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx - 1, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-DA-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey < fx + p) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy - 1, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-DA2-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx < fy) & (ex > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-DA2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy < fx) & (ey > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-DA3-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (fx < fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-DA3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (fy < fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-DA4-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, ey - (p - 1), ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-DA4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, ex - (p - 1), ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-DA5-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-DA5-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-DA6-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-DA6-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-D3-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (ex < fy + (p + 1)) & (fx < ey) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-D3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (ey < fx + (p + 1)) & (fy < ex) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-D4A-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-D4A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-D5-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-D5-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-D6-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx + 1 < ey) & (fx > fy) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-D6-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy + 1 < ex) & (fy > fx) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-D7-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex > fy + (p + 1)) & (fx + 1 < ey) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-D7-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey > fx + (p + 1)) & (fy + 1 < ex) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-D10-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex < fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-D10-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey < fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-D11-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == fy + (p + 1)) & (fx < ey) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-D11-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == fx + (p + 1)) & (fy < ex) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-D12-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex > fy + (p + 1)) & (fx + 1 == ey) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, fx),
            SELTZORange(sy, 1, 0, fy, fx - (p - 1), fx - (p - 2)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-D12-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey > fx + (p + 1)) & (fy + 1 == ex) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, fy),
            SELTZORange(sx, 1, 0, fx, fy - (p - 1), fy - (p - 2)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-DB1-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-DB1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-DB2-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex > ey + 2) & (fx == ey) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fy, ex - 1),
            SELTZORange(~sy, 0, 0, fx - (p - 1), fx - (p + p - 1), fx - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-DB2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey > ex + 2) & (fy == ex) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fx, ey - 1),
            SELTZORange(~sx, 0, 0, fy - (p - 1), fy - (p + p - 1), fy - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-DB3-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ex < fy + (p + p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-DB3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ey < fx + (p + p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-DB4-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-DB4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

end
