function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
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

    checker("SELTZO-TwoSum-R0R1-ONE0-DE0-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == ey) & (ex == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, ex - 2, ex - (p + 2), ex - 2), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DE0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == ex) & (ey == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, ey - 2, ey - (p + 2), ey - 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DE1-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == ey) & (ex == fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, ex - 2, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DE1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == ex) & (ey == fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, ey - 2, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DE2-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 1 == fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, ex - 1, ex - (p + 1), ex - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DE2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 1 == fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, ey - 1, ey - (p + 1), ey - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DE3-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 1 == fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, ex - 1, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DE3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 1 == fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, ey - 1, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DE4-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 1 > fy) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, ex - 1, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DE4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 1 > fx) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, ey - 1, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DE5-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 1 > fy) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, ex - 1, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DE5-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 1 > fx) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, ey - 1, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DE6-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 1 < fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, ex - 1, fy - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DE6-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 1 < fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, ey - 1, fx - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DE7-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == ey) & (fx + 1 < fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, ex - 1, fy, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DE7-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == ex) & (fy + 1 < fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, ey - 1, fx, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DA10-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + 1 == ey) & (ex == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 1, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DA10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + 1 == ex) & (ey == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 1, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DA11-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + 1 == ey) & (ex == fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ex + 1, fx, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DA11-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + 1 == ex) & (ey == fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 0, ey + 1, fy, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DA13-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + 1 == ey) & (fx + 1 == fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ex + 1, ex - 1, fx + 2),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DA13-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + 1 == ex) & (fy + 1 == fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 0, ey + 1, ey - 1, fy + 2),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DA14-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + 1 == ey) & (fx + 1 > fy) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ex + 1, ex - 1, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DA14-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + 1 == ex) & (fy + 1 > fx) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 0, ey + 1, ey - 1, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D2-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + 1 < ey) & (fx + p > ey) & (ex > fy) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 1, ey, ex, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + 1 < ex) & (fy + p > ex) & (ey > fx) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 1, ex, ey, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D3-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex < ey + p) & (fx > ey + 1) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey < ex + p) & (fy > ex + 1) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D3A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx > ey) & (ex == fy + p) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D3A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy > ex) & (ey == fx + p) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D3B-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 2)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D3B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 2)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D3C-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ey == fy + (p - 2)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D3C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ex == fx + (p - 2)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D3D0-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx == ey + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D3D0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy == ex + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D3D1-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx == ey + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 1, 0, fy, ey - p, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D3D1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy == ex + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 1, 0, fx, ex - p, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D3E0-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx == ey + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D3E0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy == ex + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D3E1-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx == ey + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 1, 0, fy, ey - p, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D3E1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy == ex + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 1, 0, fx, ex - p, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D4-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fy - 1, fy),
            SELTZORange(~sy, 0, 0, fx - (p - 1), fx - (p + p - 1), fx - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fx - 1, fx),
            SELTZORange(~sx, 0, 0, fy - (p - 1), fy - (p + p - 1), fy - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D5-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex > fy + (p + 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ex - p, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, fy, fx - (p - 1), fx - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D5-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy == ex) & (ey > fx + (p + 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ey - p, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, fx, fy - (p - 1), fy - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D5A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == fy + (p + 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ex - (p + 1), ex - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D5A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == fx + (p + 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ey - (p + 1), ey - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D5B-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == ey + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ex - (p + 1), ex - 1),
            SELTZORange(sy, 1, 0, fy - 1, fy - (p - 2), fy - (p - 3)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D5B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == ex + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ey - (p + 1), ey - 1),
            SELTZORange(sx, 1, 0, fx - 1, fx - (p - 2), fx - (p - 3)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D5C-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx == ey) & (ex == ey + (p - 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, fx),
            SELTZORange(~sy, 1, 0, fy, ey - p, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D5C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy == ex) & (ey == ex + (p - 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, fy),
            SELTZORange(~sx, 1, 0, fx, ex - p, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D6-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx + 1 < ey) & (ex < fy + (p - 1)) & (fx + 1 > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D6-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy + 1 < ex) & (ey < fx + (p - 1)) & (fy + 1 > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D7-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx + 1 == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D7-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy + 1 == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D8-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == fy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D8-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == fx + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D11-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx + 1 == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D11-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy + 1 == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D13-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx + 1 < ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D13-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy + 1 < ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-D14-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx < ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-D14-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy < ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DB10-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + (p - 1) == ey) & (ex < fx + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sy, 1, 0, fx, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DB10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + (p - 1) == ex) & (ey < fy + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sx, 1, 0, fy, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DB11-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + (p - 1) == ey) & (ex < fx + (p - 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sy, 1, 0, fx, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DB11-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + (p - 1) == ex) & (ey < fy + (p - 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sx, 1, 0, fy, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DB12-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + (p - 1) == ey) & (ex == fx + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sy, 0, 0, fx, fx - p, fx))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DB12-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + (p - 1) == ex) & (ey == fy + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sx, 0, 0, fy, fy - p, fy))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DB13-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + (p - 1) == ey) & (ex == fx + (p - 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sy, 0, 0, fx, fx - p, fx))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DB13-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + (p - 1) == ex) & (ey == fy + (p - 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sx, 0, 0, fy, fy - p, fy))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DB20-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + p == ey) & (ex > fx + 2) & (ex < fx + (p - 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey, fy, fy + 1),
            SELTZORange(sy, 1, 0, ex - 1, fx, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DB20-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + p == ex) & (ey > fy + 2) & (ey < fy + (p - 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex, fx, fx + 1),
            SELTZORange(sx, 1, 0, ey - 1, fy, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DB21-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + p == ey) & (ex == fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey, fy, fy + 1),
            SELTZORange(sy, 0, 0, ex - 1, ex - (p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DB21-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + p == ex) & (ey == fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex, fx, fx + 1),
            SELTZORange(sx, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-DB22-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + p == ey) & (ex == fx + (p - 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey, fy, fy + 1),
            SELTZORange(sy, 1, 0, ex - 1, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-DB22-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + p == ex) & (ey == fy + (p - 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex, fx, fx + 1),
            SELTZORange(sx, 1, 0, ey - 1, ey - p, ey - (p - 1)))
    end

end
