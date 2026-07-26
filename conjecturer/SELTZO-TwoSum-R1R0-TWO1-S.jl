function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R1R0},
    ::Val{TWO1},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R1R0-TWO1-SE0-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 < fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-SE0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 < fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-SE1-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, ex - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-SE1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, ey - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-SE2-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-SE2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-SE3-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, ex - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-SE3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, ey - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-SE4-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex == ey) & (ex == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, ex - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-SE4-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey == ex) & (ey == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, ey - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S1-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex + 1 > ey) & (fx + 1 < ey) & (fx + 1 > fy) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey + 1 > ex) & (fy + 1 < ex) & (fy + 1 > fx) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S1A-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S1A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S1B0-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (fx > fy) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S1B0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (fy > fx) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S1B1-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx == fy) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S1B1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy == fx) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S1AB-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S1AB-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S1C0-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex > ey) & (fx + 1 == fy) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S1C0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey > ex) & (fy + 1 == fx) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S1C1-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex > ey) & (fx + 1 == fy) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S1C1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey > ex) & (fy + 1 == fx) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S1D-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex > ey) & (fx + 2 == fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S1D-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey > ex) & (fy + 2 == fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S2-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex > ey) & (fx + 2 < fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey > ex) & (fy + 2 < fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S2A-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex > ey) & (fx + 2 < fy) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S2A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey > ex) & (fy + 2 < fx) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S3-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex > fy + (p - 1)) & (fx + 1 < ey) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey > fx + (p - 1)) & (fy + 1 < ex) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S3A0-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex > fy + (p - 1)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S3A0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey > fx + (p - 1)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S3A1-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fy + 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S3A1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fx + 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S3A2-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy + 1, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S3A2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx + 1, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S3B-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex > fy + (p - 1)) & (fx + 1 < ey) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S3B-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey > fx + (p - 1)) & (fy + 1 < ex) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S3C0-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (fx > fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S3C0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (fy > fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S3C1-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (fx == fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S3C1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (fy == fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S3D0-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (fx > fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S3D0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (fy > fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S3D1-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx + 1 == fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S3D1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy + 1 == fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S3E-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx == fy) & (ex > fy + (p - 3)) & (ex < fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S3E-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy == fx) & (ey > fx + (p - 3)) & (ey < fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S4-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex > fy + p) & (fx > ey) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S4-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey > fx + p) & (fy > ex) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S4A-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex > fy + p) & (fx == ey) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S4A-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey > fx + p) & (fy == ex) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S4B0-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S4B0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy > ex) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S4B1-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey - 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S4B1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex - 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S4B2-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S4B2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy > ex) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S4B3-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fy, ex),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S4B3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fx, ey),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S4C0-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S4C0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy > ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S4C1-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S4C1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S4C2-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S4C2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S4D0-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S4D0-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy > ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-S4D1-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-S4D1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-SB10-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-SB10-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey == ex + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-SB11-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 1)) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey - 1, ex),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-SB11-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey == ex + (p - 1)) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex - 1, ey),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-SB20-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (fx > ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-SB20-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey == ex + p) & (fy > ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-SB21-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (fx == ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, ex),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-SB21-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey == ex + p) & (fy == ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, ey),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-SB22-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (fx > ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-SB22-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey == ex + p) & (fy > ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-R1R0-TWO1-SB23-X",
        (CLASS_X == R1R0) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (fx == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, ex),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-R1R0-TWO1-SB23-Y",
        (CLASS_Y == R1R0) & (CLASS_X == TWO1) &
        (ey == ex + p) & (fy == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, ey),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

end
