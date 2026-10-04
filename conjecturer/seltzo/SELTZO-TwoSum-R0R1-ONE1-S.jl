function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
    ::Val{ONE1},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R0R1-ONE1-SE0-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 1 > fy) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx + 1, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SE0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 1 > fx) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy + 1, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SE1-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey) & (ex == fy + (p - 2)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SE1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex) & (ey == fx + (p - 2)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SE2-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx + 2, fx + 2),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SE2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy + 2, fy + 2),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SE3-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey) & (fx + 1 < fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SE3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex) & (fy + 1 < fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SE4-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey) & (ex == fx + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, fy),
            SELTZORange(sy, 0, 0, fx, fx - p, fx))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SE4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex) & (ey == fy + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, fx),
            SELTZORange(sx, 0, 0, fy, fy - p, fy))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SA10-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex + 1 == ey) & (fx + 3 == ey) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fx, fy),
            SELTZORange(~sy, 0, 0, fx - (p - 3), fx - (p + p - 3), fx - (p - 3)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SA10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey + 1 == ex) & (fy + 3 == ex) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fy, fx),
            SELTZORange(~sx, 0, 0, fy - (p - 3), fy - (p + p - 3), fy - (p - 3)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SA11-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex + 1 == ey) & (fx + 1 == fy) & (fy + 3 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, ex - 1, fx + 2),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SA11-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey + 1 == ex) & (fy + 1 == fx) & (fx + 3 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, ey - 1, fy + 2),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SA20-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (ex < fy + (p - 1)) & (fx + 1 > fy) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SA20-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (ey < fx + (p - 1)) & (fy + 1 > fx) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SA21-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, fx + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SA21-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, fy + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SA22-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx + 2 < ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SA22-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy + 2 < ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SA23-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (ey < fy + (p - 2)) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - 3, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SA23-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (ex < fx + (p - 2)) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - 3, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SA24-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx + 2 == ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ex - 3, ex - 2), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SA24-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy + 2 == ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ey - 3, ey - 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SA25-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (ex < fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, fy),
            SELTZORange(~sy, 0, 0, fx - (p - 3), fx - (p + p - 3), fx - (p - 3)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SA25-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (ey < fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, fx),
            SELTZORange(~sx, 0, 0, fy - (p - 3), fy - (p + p - 3), fy - (p - 3)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SA26-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy - 1, ex + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SA26-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx - 1, ey + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SA27-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex == fy + (p - 1)) & (fx == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fy, ex + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SA27-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey == fx + (p - 1)) & (fy == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fx, ey + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SA301-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 2) & (ey < fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SA301-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 2) & (ex < fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SA302-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 2) & (ey < fy + (p - 3)) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SA302-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 2) & (ex < fx + (p - 3)) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SA311-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 2) & (ey == fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SA311-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 2) & (ex == fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SA312-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 2) & (ey == fy + (p - 3)) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SA312-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 2) & (ex == fx + (p - 3)) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SA321-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 2) & (ey == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, ey),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SA321-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 2) & (ex == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, ex),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SA322-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + 2) & (ey == fy + (p - 2)) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SA322-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + 2) & (ex == fx + (p - 2)) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S1A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S1A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S2-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex > fy + p) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey > fx + p) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S2A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S2A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == fx + p) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S2B-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx + 1 < ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S2B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy + 1 < ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S3-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex > fy + p) & (fx + 1 > ey) & (ex < ey + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey > fx + p) & (fy + 1 > ex) & (ey < ex + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S3A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fx + 2),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S3A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fy + 2),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S3B-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (fx + 1 > ey) & (ex == fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, ey),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S3B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (fy + 1 > ex) & (ey == fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, ex),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S3C-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex > ey) & (ex < ey + (p - 1)) & (ex > fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S3C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey > ex) & (ey < ex + (p - 1)) & (ey > fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S3AB-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex > ey + 2) & (fx + 1 == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 2, fx + 2),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S3AB-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey > ex + 2) & (fy + 1 == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 2, fy + 2),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S3BC-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex > ey + 2) & (ex == fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S3BC-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey > ex + 2) & (ey == fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S4-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (fx + 1 > ey) & (ex < fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S4-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (fy + 1 > ex) & (ey < fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S4A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex > ey + 2) & (fx + 1 == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx + 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S4A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey > ex + 2) & (fy + 1 == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy + 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S4B-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (fx + 1 > ey) & (ex == fy + (p - 1)) & (fx < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx + 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S4B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (fy + 1 > ex) & (ey == fx + (p - 1)) & (fy < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy + 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S4C-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex > ey + 2) & (fx < fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S4C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey > ex + 2) & (fy < fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S4AB-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx + 2, fx + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S4AB-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy + 2, fy + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S4BC-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == fy + (p - 1)) & (fx == fy + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S4BC-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == fx + (p - 1)) & (fy == fx + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S5-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (fx + 1 < ey) & (fx + 1 > fy) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S5-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (fy + 1 < ex) & (fy + 1 > fx) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S6A-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == fy + 1) & (ey > fy + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S6A-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == fx + 1) & (ex > fx + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S6B-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == fy) & (ey > fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(sy, 0, 0, fx, fx - p, fx))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S6B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == fx) & (ex > fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(sx, 0, 0, fy, fy - p, fy))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-S6C-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (fx + p == ey) & (ex == fy) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey, ex + 1, fx + 2),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-S6C-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (fy + p == ex) & (ey == fx) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex, ey + 1, fy + 2),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SB10-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex + (p - 1) == ey) & (ex + 1 == fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey, fy, fy + 1),
            SELTZORange(sy, 1, 0, fx, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SB10-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey + (p - 1) == ex) & (ey + 1 == fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex, fx, fx + 1),
            SELTZORange(sx, 1, 0, fy, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SB11-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex + (p - 1) == ey) & (ey < fy + (p - 2)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey, fy, ex + 1),
            SELTZORange(sy, 0, 0, fx, fx - p, fx))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SB11-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey + (p - 1) == ex) & (ex < fx + (p - 2)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex, fx, ey + 1),
            SELTZORange(sx, 0, 0, fy, fy - p, fy))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SB2-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (fx + p == ey) & (ey < fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sy, 0, 0, fx - (p - 3), fx - (p + p - 3), fx - (p - 3)))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SB2-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (fy + p == ex) & (ex < fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sx, 0, 0, fy - (p - 3), fy - (p + p - 3), fy - (p - 3)))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SB30-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SB30-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SB31-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SB31-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SB40-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SB40-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-R0R1-ONE1-SB41-X",
        (CLASS_X == R0R1) & (CLASS_Y == ONE1) &
        (ex == ey + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-R0R1-ONE1-SB41-Y",
        (CLASS_Y == R0R1) & (CLASS_X == ONE1) &
        (ey == ex + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
