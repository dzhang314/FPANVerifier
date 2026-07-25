function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R1R0},
    ::Val{MM01},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R1R0-MM01-S1-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx + 2 < fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > ex) & (fy + 2 < fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S1A-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx + 2 < fy) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S1A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > ex) & (fy + 2 < fx) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S1B-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S1B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > ex) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S2-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx + 2 > fy) & (ex < fy + (p - 3)) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > ex) & (fy + 2 > fx) & (ey < fx + (p - 3)) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S2A-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx + 1 > fy) & (ex == fy + (p - 3)) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S2A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > ex) & (fy + 1 > fx) & (ey == fx + (p - 3)) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S2B-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx > fy) & (ex == fy + (p - 2)) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S2B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy > fx) & (ey == fx + (p - 2)) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S2C-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx > fy) & (ex == fy + (p - 1)) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S2C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy > fx) & (ey == fx + (p - 1)) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S2E-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx == fy) & (ex > fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S2E-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy == fx) & (ey > fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S2F-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx + 1 == ey) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S2F-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > ex) & (fy + 1 == ex) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S2AD-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx + 1 == fy) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S2AD-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > ex) & (fy + 1 == fx) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S2AF-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > ey) & (fx + 1 == ey) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S2AF-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > ex) & (fy + 1 == ex) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S2BD-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx + 1 == fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(~sy, 0, 0, fx, fx - p, fx))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S2BD-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy + 1 == fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(~sx, 0, 0, fy, fy - p, fy))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S2BF-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx + 1 == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S2BF-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy + 1 == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S2BG-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S2BG-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S2CF-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx + 1 == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S2CF-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy + 1 == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S2CG-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S2CG-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S3-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > fy + (p - 1)) & (fx < ey) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > fx + (p - 1)) & (fy < ex) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S3B-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S3B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S3C-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (ex > fy + (p - 1)) & (fx < ey) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S3C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (ey > fx + (p - 1)) & (fy < ex) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S3AB-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S3AB-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S4-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex > fy + p) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S4-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey > fx + p) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S4A-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex > fy + p) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S4A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey > fx + p) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S4B-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx > ey + 1) & (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S4B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy > ex + 1) & (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S4AB-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx == ey + 1) & (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S4AB-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy == ex + 1) & (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S4C-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx > ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S4C-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy > ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S4D-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx > ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S4D-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy > ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-MM01-S4E-X",
        (CLASS_X == R1R0) & (CLASS_Y == MM01) &
        (fx > ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-MM01-S4E-Y",
        (CLASS_Y == R1R0) & (CLASS_X == MM01) &
        (fy > ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx), pos_zero)
    end

end
