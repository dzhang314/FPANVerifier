function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
    ::Val{MM10},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ONE0-MM10-DA0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx + 1 > fy) & (ex == ey + 1) & (ex > fy + 3) & (ex > fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-DA0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy + 1 > fx) & (ey == ex + 1) & (ey > fx + 3) & (ey > fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-DA1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex > fx + 2) & (ex < fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-DA1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey > fy + 2) & (ey < fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-DA21-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == fy) & (ex == ey + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx),
            SELTZORange(~sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-DA21-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == fx) & (ey == ex + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy),
            SELTZORange(~sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-DA22-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (ex == ey + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-DA22-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == fx + 1) & (ey == ex + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-DA3-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx + 1 == fy) & (ex == ey + 1) & (ex > fx + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-DA3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy + 1 == fx) & (ey == ex + 1) & (ey > fy + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-DA4-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx + 1 < fy) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-DA4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy + 1 < fx) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-DA5-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ex == fx + 2) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 2, fy - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-DA5-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ey == fy + 2) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 2, fx - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-DA61-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == fy) & (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy, fy - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-DA61-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == fx) & (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx, fx - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-DA62-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy - 1, fy - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-DA62-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == fx + 1) & (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx - 1, fx - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D1B-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D1B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D1C-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D1C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D1D00-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == fy + p) & (fx > ey) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D1D00-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == fx + p) & (fy > ex) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D1D01-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D1D01-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D1D02-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D1D02-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D1D1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx + 1 > ey) & (ex == ey + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fy + 2),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D1D1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy + 1 > ex) & (ey == ex + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fx + 2),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D2B1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey) & (ex < fy + (p - 2)) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D2B1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex) & (ey < fx + (p - 2)) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D2BC1-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (fx + 1 == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D2BC1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (fy + 1 == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D2BC2-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (fx == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D2BC2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (fy == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D2BD-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == ey + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D2BD-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex) & (ey == ex + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D2C-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + (p - 2)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D2C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + (p - 2)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D2D-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + (p - 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D2D-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + (p - 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D2E0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D2E0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D3-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx < ey) & (fx + 1 > fy) & (ex < fy + (p - 2)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy < ex) & (fy + 1 > fx) & (ey < fx + (p - 2)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D3A-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx + 1 == fy) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D3A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy + 1 == fx) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D3B0-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx < ey) & (fx > fy + 1) & (ex == fy + (p - 2)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D3B0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy < ex) & (fy > fx + 1) & (ey == fx + (p - 2)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D3B11-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (fx == fy) & (ex == fy + (p - 2)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D3B11-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (fy == fx) & (ey == fx + (p - 2)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D3B12-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx + 1 < ey) & (fx == fy + 1) & (ex == fy + (p - 2)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D3B12-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy + 1 < ex) & (fy == fx + 1) & (ey == fx + (p - 2)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D3B2-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (ex == fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D3B2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == fx + 1) & (ey == fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D3C00-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx < ey) & (fx > fy + 1) & (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D3C00-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy < ex) & (fy > fx + 1) & (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D3C01-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (ex == fy + (p - 1)) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D3C01-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == fx + 1) & (ey == fx + (p - 1)) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D3C02-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (ex == fy + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D3C02-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == fx + 1) & (ey == fx + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D3C10-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx < ey) & (fx > fy + 1) & (ex == ey + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D3C10-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy < ex) & (fy > fx + 1) & (ey == ex + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D3C11-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == fy + 1) & (ex == ey + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D3C11-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == fx + 1) & (ey == ex + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D3D00-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx < ey) & (fx > fy + 2) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D3D00-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy < ex) & (fy > fx + 2) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D3D01-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == fy + 2) & (ex == fy + p) & (ey > fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D3D01-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == fx + 2) & (ey == fx + p) & (ex > fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D3D02-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == fy + 2) & (ex == fy + p) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D3D02-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == fx + 2) & (ey == fx + p) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D3D10-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx < ey) & (fx > fy + 2) & (ex == ey + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 2),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D3D10-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy < ex) & (fy > fx + 2) & (ey == ex + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 2),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D3D11-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == fy + 2) & (ex == ey + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D3D11-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == fx + 2) & (ey == ex + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D4-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx > ey) & (ex > fy + p) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy > ex) & (ey > fx + p) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D5-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx < ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D5-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy < ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-D5A-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-D5A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-DB10-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx > ey + 1) & (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-DB10-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy > ex + 1) & (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-DB11-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey + 1) & (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-DB11-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex + 1) & (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-DB20-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx > ey + 2) & (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-DB20-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy > ex + 2) & (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-DB21-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey + 2) & (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 3),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-DB21-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex + 2) & (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 3),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-DB22-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx > ey + 2) & (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-DB22-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy > ex + 2) & (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-MM10-DB23-X",
        (CLASS_X == ONE0) & (CLASS_Y == MM10) &
        (fx == ey + 2) & (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 3),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-MM10-DB23-Y",
        (CLASS_Y == ONE0) & (CLASS_X == MM10) &
        (fy == ex + 2) & (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 3),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

end
