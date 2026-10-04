function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
    ::Val{ONE0},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ONE1-ONE0-DA1-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fy, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-DA1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fx, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-DA2-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fy, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-DA2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fx, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-DA3-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fx, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-DA3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fy, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-DA3A-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fx - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-DA3A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fy - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-DA4-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, ey - (p - 1), ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-DA4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, ex - (p - 1), ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-DA4A-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx == fy + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-DA4A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy == fx + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-DA4B-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx == fy + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-DA4B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy == fx + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-DA5-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (ex > fx + 2) & (ex < fy + p) & (fx > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-DA5-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (ey > fy + 2) & (ey < fx + p) & (fy > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-DA5A-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx < ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-DA5A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy < ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-DA6A-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx == ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-DA6A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy == ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-DA7-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-DA7-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D1-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex > fy + p) & (fx > ey + 1) & (ex < ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey > fx + p) & (fy > ex + 1) & (ey < ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D1A-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D1A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D1B-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D1B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D1C-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex == fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D1C-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (fy < ex) & (ey == fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D1D-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex == fy + (p + 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D1D-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (fy < ex) & (ey == fx + (p + 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D1E-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex < ey + p) & (fx > ey + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D1E-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey < ex + p) & (fy > ex + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D1F-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == fy + p) & (fx < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, fx - (p - 1), fx - (p + p - 1), fx - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D1F-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == fx + p) & (fy < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, fy - (p - 1), fy - (p + p - 1), fy - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D1G-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex == fy + (p + 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D1G-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (fy < ex) & (ey == fx + (p + 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D2-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx < ey) & (ex < fy + p) & (fx > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy < ex) & (ey < fx + p) & (fy > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D3A-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex > fy + (p + 1)) & (fx < fy + (p - 2)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D3A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey > fx + (p + 1)) & (fy < fx + (p - 2)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D3B-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (fx < ey) & (ex > fy + (p + 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D3B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (fy < ex) & (ey > fx + (p + 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D3C-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex > fy + (p + 1)) & (fx < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy, fx - (p - 1), fx - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D3C-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (fy == ex) & (ey > fx + (p + 1)) & (fy < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx, fy - (p - 1), fy - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D3D-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex > ey + 3) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D3D-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (fy == ex) & (ey > ex + 3) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D3E-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx == fy) & (fx + 1 < ey) & (ex < fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D3E-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy == fx) & (fy + 1 < ex) & (ey < fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D3F-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex > ey + 1) & (fx == ey) & (ex < fy + p) & (ey > fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D3F-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey > ex + 1) & (fy == ex) & (ey < fx + p) & (ex > fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D3G0-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == fy + (p + 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 1, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, fx - p, fx - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D3G0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == fx + (p + 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 1, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, fy - p, fy - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D3G1-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == fy + (p + 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 1, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D3G1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == fx + (p + 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 1, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D4-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D4A-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D4A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D4B-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (fx == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D4B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (fy == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D4C-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fy, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D4C-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fx, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-D4D-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex == fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fy + 1, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-D4D-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey == fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fx + 1, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-DB-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ex < fx + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-DB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ey < fy + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ONE0-DBB-X",
        (CLASS_X == ONE1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx > ey + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-ONE0-DBB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy > ex + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
