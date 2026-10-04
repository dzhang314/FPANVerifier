function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
    ::Val{TWO1},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ONE1-TWO1-DE0-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy, fy - 2, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-DE0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx, fx - 2, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-DE1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy, fy - p, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-DE1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx, fx - p, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-DE2-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy - 1, fy - (p + 1), fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-DE2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx - 1, fx - (p + 1), fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-DE3-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy - 1, fy - (p + 1), fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-DE3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx - 1, fx - (p + 1), fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-DE4-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy + 1, fy - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-DE4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx + 1, fx - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-DE5-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx - 1, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-DE5-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy - 1, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-DA0-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-DA0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-DA1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-DA1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-DA2-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fy - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-DA2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fx - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-DA3-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-DA3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-DA4-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 < fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fy, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-DA4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 < fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fx, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-DA5-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 < fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 2, fy - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-DA5-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 < fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 2, fx - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex < ey + (p - 1)) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy > ex) & (ey < ex + (p - 1)) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D1A0-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D1A0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D1A1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fy, ex - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D1A1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fx, ey - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D1A2-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ex - p, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D1A2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ey - p, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D2-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D2A-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, fx),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D2A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, fy),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D2B-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D2B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy < ex) & (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D3-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D3A-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D3A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D3B-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D3B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D3AB-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D3AB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D3C-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D3C-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D3AC-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D3AC-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D3D-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, ey),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D3D-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, ex),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D3AD-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 2, ey),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D3AD-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 2, ex),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D4-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx < ey) & (fx > fy) & (ex > ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy < ex) & (fy > fx) & (ey > ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D4A-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D4A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D4B-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D4B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy < ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D4AB-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, fy, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D4AB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, fx, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D4C-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D4C-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy < ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D5-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx + 1 < fy) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D5-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy + 1 < fx) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D5A1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx + 1 == fy) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D5A1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy + 1 == fx) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D5A2-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == fy) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D5A2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == fx) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D5B-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx + 1 < fy) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D5B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy + 1 < fx) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D5AB1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx + 1 == fy) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ey - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D5AB1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy + 1 == fx) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ex - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-D5AB2-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == fy) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ey - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-D5AB2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == fx) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ex - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-DB1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-DB1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-DB20-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-DB20-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-DB21-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-DB21-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

end
