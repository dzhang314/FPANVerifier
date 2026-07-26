function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
    ::Val{ONE0},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R0R1-ONE0-S1-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx > ey) & (ex > fy + p) & (ex < ey + p) & (ex > fx + 2) & (ey > fy + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy > ex) & (ey > fx + p) & (ey < ex + p) & (ey > fy + 2) & (ex > fx + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S1B-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx > ey) & (ex > fy + p) & (ex < ey + p) & (ex > fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S1B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy > ex) & (ey > fx + p) & (ey < ex + p) & (ey > fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S1C0-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (fx > ey) & (ex > fx + 2) & (ex < fx + p) & (ey > fy + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S1C0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (fy > ex) & (ey > fy + 2) & (ey < fy + p) & (ex > fx + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S1C4-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ex == fx + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S1C4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ey == fy + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S1C5-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ex > fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S1C5-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ey > fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S1C6-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ex == fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S1C6-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ey == fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S1D-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex > fy + p) & (ex > ey + 3) & (ex < ey + p) & (ex == fx + 2) & (ey > fy + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S1D-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey > fx + p) & (ey > ex + 3) & (ey < ex + p) & (ey == fy + 2) & (ex > fx + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S2-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (ex < fy + (p - 1)) & (fx < ey + 1) & (fx + 1 > fy) & (ey > fy + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (ey < fx + (p - 1)) & (fy < ex + 1) & (fy + 1 > fx) & (ex > fx + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S2A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx + 1 == fy) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S2A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy + 1 == fx) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S3-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex > ey + 3) & (ex < ey + (p - 3)) & (fx > ey) & (ex < fy + (p - 1)) & (ex > fx + 2) & (ex < fx + (p - 1)) & (ey > fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey > ex + 3) & (ey < ex + (p - 3)) & (fy > ex) & (ey < fx + (p - 1)) & (ey > fy + 2) & (ey < fy + (p - 1)) & (ex > fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S3A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (ex < fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S3A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (ey < fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S3AB-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == fy + (p - 1)) & (ex > ey + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S3AB-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == fx + (p - 1)) & (ey > ex + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S3B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == fy + (p - 1)) & (fx + 1 > ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S3B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == fx + (p - 1)) & (fy + 1 > ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S3B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == fy + (p - 1)) & (ex > ey + 2) & (fx < ey) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S3B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == fx + (p - 1)) & (ey > ex + 2) & (fy < ex) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S3BD-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex == fy + (p - 1)) & (ex > ey + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S3BD-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey == fx + (p - 1)) & (ey > ex + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S4A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx + p == ey) & (ex + 1 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fy - 1, ex),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S4A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy + p == ex) & (ey + 1 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fx - 1, ey),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S4B-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx + p == ey) & (ex + 1 == fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, ex - 1, ex),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S4B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy + p == ex) & (ey + 1 == fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, ey - 1, ey),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S4C-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx + p == ey) & (ex == fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, fx + 1, ey + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S4C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy + p == ex) & (ey == fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, fy + 1, ex + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S4E0-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx + p == ey) & (ex > fy) & (ex < fx + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S4E0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy + p == ex) & (ey > fx) & (ey < fy + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S4E1-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx + p == ey) & (ex > fy) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S4E1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy + p == ex) & (ey > fx) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S5B-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx + (p + 2) < ey) & (ex > fy) & (ex < fx + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sy, 1, 0, ey - p, fx, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S5B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy + (p + 2) < ex) & (ey > fx) & (ey < fy + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sx, 1, 0, ex - p, fy, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S6A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + 1 < ey) & (fx + (p - 1) == ey) & (ex > fy) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(sy, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S6A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + 1 < ex) & (fy + (p - 1) == ex) & (ey > fx) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(sx, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S6A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx + (p - 1) == ey) & (ex == fy) & (ex > fx + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, fx, ey + 1),
            SELTZORange(sy, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S6A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy + (p - 1) == ex) & (ey == fx) & (ey > fy + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, fy, ex + 1),
            SELTZORange(sx, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S6B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + 1 < ey) & (fx + (p - 2) > ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sy, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S6B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + 1 < ex) & (fy + (p - 2) > ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sx, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S6B1-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx + (p - 2) == ey) & (ex > fx + 1) & (ex < fx + (p - 3)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, ex, ex),
            SELTZORange(sy, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S6B1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy + (p - 2) == ex) & (ey > fy + 1) & (ey < fy + (p - 3)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, ey, ey),
            SELTZORange(sx, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S7A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx < ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S7A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy < ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S7A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx == ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S7A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy == ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S7C-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (fx > ey) & (fx < ey + (p - 2)) & (ex == fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S7C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (fy > ex) & (fy < ex + (p - 2)) & (ey == fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S8-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + 1 < ey) & (fx + 1 > fy) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey + 1, ex, fy),
            SELTZORange(sy, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S8-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + 1 < ex) & (fy + 1 > fx) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex + 1, ey, fx),
            SELTZORange(sx, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S8A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + 1 < ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(sy, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S8A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + 1 < ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(sx, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S9-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + 1 < ey) & (fx + 1 < fy) & (ex > fy) & (fx + (p - 1) > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey + 1, ex - 1, fx + 1),
            SELTZORange(sy, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S9-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + 1 < ex) & (fy + 1 < fx) & (ey > fx) & (fy + (p - 1) > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex + 1, ey - 1, fy + 1),
            SELTZORange(sx, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-S9A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + 1 < ey) & (ex == fy) & (fx + (p - 1) > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey + 1, fx, fx + 1),
            SELTZORange(sy, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-S9A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + 1 < ex) & (ey == fx) & (fy + (p - 1) > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex + 1, fy, fy + 1),
            SELTZORange(sx, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-SB10-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + (p - 1) == ey) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fy - 1, fy),
            SELTZORange(sy, 1, 0, fx, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-SB10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + (p - 1) == ex) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fx - 1, fx),
            SELTZORange(sx, 1, 0, fy, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-SB11-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + (p - 1) == ey) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fy - 1, fy),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-SB11-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + (p - 1) == ex) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fx - 1, fx),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-SB20-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + p == ey) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sy, 1, 0, ex - 1, fx, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-SB20-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + p == ex) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sx, 1, 0, ey - 1, fy, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-SB21-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + p == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sy, 0, 0, ex - 1, ex - (p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-SB21-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + p == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sx, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE0-SB22-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE0) &
        (ex + p == ey) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sy, 1, 0, ex - 1, fx - 1, fx))
    end
    checker("SELTZO-TwoSum-R0R1-ONE0-SB22-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE0) &
        (ey + p == ex) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sx, 1, 0, ey - 1, fy - 1, fy))
    end

end
