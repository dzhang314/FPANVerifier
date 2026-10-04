function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO1},
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

    checker("SELTZO-TwoSum-TWO1-ONE1-DA0-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fy - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-DA0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fx - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-DA1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-DA1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-DA2-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-DA2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-DA30-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-DA30-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ex > fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ey > fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D1A1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex > fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D1A1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == ex) & (ey > fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D1A2-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex > fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D1A2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey > fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D2-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx + 1 < ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy + 1 < ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D2A-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D2A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D3-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx < fy) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D3-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy < fx) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D3A-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx < fy) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ey - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D3A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy < fx) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ex - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D3B-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == fy) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D3B-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == fx) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D4-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx + 1 < ey) & (fx > fy + 1) & (ex > ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D4-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy + 1 < ex) & (fy > fx + 1) & (ey > ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D4A-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx + 1 < ey) & (fx == fy + 1) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D4A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy + 1 < ex) & (fy == fx + 1) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D4B-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx + 1 < ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D4B-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy + 1 < ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D4C-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (fx > fy + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D4C-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (fy > fx + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D4AC-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D4AC-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D4BC-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D4BC-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D5-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D5-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D5A-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D5A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D5B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D5B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D5B2-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D5B2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D5AB1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D5AB1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-D5AB2-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-D5AB2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-DB1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-DB1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-DB2-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-DB2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
