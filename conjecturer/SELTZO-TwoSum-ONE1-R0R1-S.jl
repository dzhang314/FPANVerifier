function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
    ::Val{R0R1},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ONE1-R0R1-S1-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex < ey + (p - 1)) & (fx > ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-S1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey < ex + (p - 1)) & (fy > ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-S2-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx > ey) & (ex < ey + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-S2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy > ex) & (ey < ex + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-S3-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx < ey) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-S3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy < ex) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-S4-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx == ey) & (fx < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-S4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy == ex) & (fy < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-S5-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx < fy + (p - 1)) & (fx > fy) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-S5-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy < fx + (p - 1)) & (fy > fx) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-S10-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx == fy + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-S10-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy == fx + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-S11-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (ex < fy + p) & (fx < ey) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-S11-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (ey < fx + p) & (fy < ex) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SA2-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx < fy + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SA2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy < fx + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SA3-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fy + p) & (fx < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SA3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fx + p) & (fy < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SA4-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (ex == fx + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SA4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (ey == fy + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SA5-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SA5-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SA6-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy, fy + 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SA6-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx, fx + 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SA7-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fx + 2) & (fx > fy + 2) & (fx < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 3, fy + 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SA7-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fy + 2) & (fy > fx + 2) & (fy < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 3, fx + 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SA8-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 3, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SA8-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 3, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SA91-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fx + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SA91-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fy + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SA92-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fx + 3) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SA92-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fy + 3) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SA10-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (ex == fx + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ex - 1),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SA10-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (ey == fy + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ey - 1),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SA11-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (ex == fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SA11-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (ey == fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SA12-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (ex == fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ex - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SA12-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (ey == fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ey - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SA13-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex > fx + 2) & (fx > fy + 1) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ex - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SA13-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey > fy + 2) & (fy > fx + 1) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ey - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SB0-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (ex == fy + p) & (fx < ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SB0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (ey == fx + p) & (fy < ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SB2-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (fx > ey + 1) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SB2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (fy > ex + 1) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SB3-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx > ey) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SB3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy > ex) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SB4-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (fx == ey + 2) & (fy + 2 < ey) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SB4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + p) & (fy == ex + 2) & (fx + 2 < ex) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SB8-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (ex == fx + (p - 2)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SB8-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == fx + p) & (ey == fy + (p - 2)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SB9-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 2)) & (ex == fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fx - p, fx - (p + p), fx - p))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SB9-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + (p - 2)) & (ey == fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fy - p, fy - (p + p), fy - p))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SB10-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ex == fx + (p - 2)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SB10-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ey == fy + (p - 2)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SB11-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ex == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SB11-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ey == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SB12-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ex == fx + (p - 2)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, ey - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SB12-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ey == fy + (p - 2)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, ex - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-R0R1-SB13-X",
        (CLASS_X == ONE1) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (ex == fy + p) & (ex == fx + (p - 2)) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-R0R1-SB13-Y",
        (CLASS_Y == ONE1) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (ey == fx + p) & (ey == fy + (p - 2)) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

end
