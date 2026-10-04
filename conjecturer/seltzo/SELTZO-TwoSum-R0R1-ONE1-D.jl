function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
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

    checker("SELTZO-TwoSum-R0R1-ONE1-D1-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == fy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-D1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == fx + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DE-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DE-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DE2-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 2 < fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fy - 1, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DE2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 2 < fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fx - 1, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DE3-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fy - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DE3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fx - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DE4-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy) & (fx + (p - 2) > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DE4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx) & (fy + (p - 2) > ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DE5-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DE5-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DE6-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 2 == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fx + 1, ex - (p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DE6-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 2 == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fy + 1, ey - (p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DE7-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx == fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DE7-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex) & (fy == fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DA1-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx + 1 < ey) & (fx > fy) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, fx, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DA1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy + 1 < ex) & (fy > fx) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, fy, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DA2-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy - 1, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DA2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx - 1, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DA3-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (ex == fy + (p - 1)) & (fx > fy) & (fx < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DA3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (ey == fx + (p - 1)) & (fy > fx) & (fy < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DA4-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy) & (fx + (p - 2) > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, fx - 1, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DA4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx) & (fy + (p - 2) > ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, fy - 1, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DA5-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex + 1 == ey) & (ey > fy + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, ex - 1, fy, ey - p), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DA5-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey + 1 == ex) & (ex > fx + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, ey - 1, fx, ex - p), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DA6-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (ex == fx + (p - 1)) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, fx - 2, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DA6-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (ey == fy + (p - 1)) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, fy - 2, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DA7-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        ((ex == ey + 1) &(fx + 1 == fy))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DA7-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        ((ey == ex + 1) &(fy + 1 == fx))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-D2-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex > fy + p) & (fx > ey) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-D2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey > fx + p) & (fy > ex) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-D3-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex > fy + p) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-D3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey > fx + p) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-D4A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1)) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-D4A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1)) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-D5-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx + 1 < ey) & (ex < fy + (p - 1)) & (fx + 1 > fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-D5-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy + 1 < ex) & (ey < fx + (p - 1)) & (fy + 1 > fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-D6-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex > ey + 2) & (fx < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-D6-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey > ex + 2) & (fy < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-D6A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 2) & (fx < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ey - 1, ey - (p - 3)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-D6A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 2) & (fy < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ex - 1, ex - (p - 3)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-D5A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-D5A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-D5D-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-D5D-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-D5E-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, fy + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-D5E-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, fx + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-D5B-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx + 1 < ey) & (ex == fy + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-D5B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy + 1 < ex) & (ey == fx + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-D5C-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ex - p, ex - (p - 1)),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-D5C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ey - p, ey - (p - 1)),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-D7A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex > fy + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-D7A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (fy == ex) & (ey > fx + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-D7B-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-D7B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-D7C-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (ex == fy + (p - 1)) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-D7C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (ey == fx + (p - 1)) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DB1-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DB1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DB2-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DB2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DB3-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DB3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == fx + p) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DB4-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (fx > ey) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DB4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == fx + p) & (fy > ex) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DB5-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, ex),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DB5-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, ey),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DB6-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 2)) & (fx > ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DB6-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + (p - 2)) & (fy > ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DB7-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (fx == ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DB7-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == fx + p) & (fy == ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DB8-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex + p == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 1, ey, fy - 1, fy),
            SELTZORange(sy, 0, 0, fx + 1, fx - (p - 3), fx - (p - 3)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DB8-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey + p == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 1, ex, fx - 1, fx),
            SELTZORange(sx, 0, 0, fy + 1, fy - (p - 3), fy - (p - 3)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DB9-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == fy) & (ey < fy + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ey, ey - p, ey),
            SELTZORange(~sy, 0, 0, fx, fx - p, fx))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DB9-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == fx) & (ex < fx + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 0, ex, ex - p, ex),
            SELTZORange(~sx, 0, 0, fy, fy - p, fy))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DB10-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == fy + 1) & (ey > fy + 2) & (fx + (p - 2) == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey - 1, fy - 1, fy),
            SELTZORange(~sy, 0, 0, fx, fx - p, fx))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DB10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == fx + 1) & (ex > fx + 2) & (fy + (p - 2) == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex - 1, fx - 1, fx),
            SELTZORange(~sx, 0, 0, fy, fy - p, fy))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DB11-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (fx + p == ey) & (ex + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 1, ey, ex - 1, ex),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DB11-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (fy + p == ex) & (ey + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 1, ex, ey - 1, ey),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DB12-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex + (p - 1) == ey) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sy, 0, 0, fx, fx - p, fx))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DB12-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey + (p - 1) == ex) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sx, 0, 0, fy, fy - p, fy))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-DB13-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (fx == ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy, ex),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-DB13-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == fx + p) & (fy == ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx, ey),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

end
