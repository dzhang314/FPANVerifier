function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO0},
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

    checker("SELTZO-TwoSum-TWO0-R0R1-SA10-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx < fy) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey + 1, fy, fx - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SA10-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy < fx) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex + 1, fx, fy - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SA11-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx + (p - 2) > ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SA11-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy + (p - 2) > ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SA12-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx == fy) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey + 1, fx - 2, fx - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SA12-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy == fx) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex + 1, fy - 2, fy - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SA13-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx < fy) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, fy, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SA13-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy < fx) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, fx, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SA14-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx == fy) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SA14-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy == fx) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SA15-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, fy, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SA15-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, fx, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SA16-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SA16-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SA2A-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (ex == fy) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ey, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SA2A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (ey == fx) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ex, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SA2B-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (fx == fy + 1) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey, ex, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SA2B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (fy == fx + 1) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex, ey, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SA2D0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (ex > fy) & (fx < fy) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, ex, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SA2D0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (ey > fx) & (fy < fx) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, ey, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SA2D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (ex == fy) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SA2D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (ey == fx) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SA2D2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (fx == fy) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SA2D2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (fy == fx) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SA2E0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (ex > fy) & (fx < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ey, ex, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SA2E0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (ey > fx) & (fy < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ex, ey, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SA2E1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (ex == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ey, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SA2E1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (ey == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ex, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SA2E2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (fx == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey, ex, ex + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SA2E2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (fy == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex, ey, ey + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SA2F-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (fx < fy + 1) & (ey > fy + 2) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ey, ex, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SA2F-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (fy < fx + 1) & (ex > fx + 2) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ex, ey, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SA3A-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ey == fy + (p - 2)) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SA3A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ex == fx + (p - 2)) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 3) & (ex < ey + (p - 1)) & (ex > fy + p) & (fx > ey + 1) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 3) & (ey < ex + (p - 1)) & (ey > fx + p) & (fy > ex + 1) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S1A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx == ey) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S1A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy == ex) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S1A2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx == ey + 1) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S1A2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy == ex + 1) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S1C-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 3) & (ex < ey + (p - 1)) & (fx > ey + 1) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S1C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 3) & (ey < ex + (p - 1)) & (fy > ex + 1) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S1AC1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (fx == ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S1AC1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (fy == ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S1AC2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S1AC2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S1CD-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex > ey + 1) & (ex < fx + (p - 3)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(~sy, 1, 0, ex - p, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S1CD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey > ex + 1) & (ey < fy + (p - 3)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(~sx, 1, 0, ey - p, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S1E-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S1E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S1AE1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S1AE1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S1AE2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S1AE2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S1DE0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx + 1 < ey) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S1DE0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy + 1 < ex) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S1DE1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx + 1 == ey) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S1DE1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy + 1 == ex) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S1DE2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx + 1 < ey) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S1DE2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy + 1 < ex) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S1DE3-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx + 1 == ey) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S1DE3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy + 1 == ex) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + (p - 1) > ey) & (fx + p < ey) & (ex < fy) & (ex < fx + (p - 3)) & (ey > fy + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey, fy + 1, ex + 1),
            SELTZORange(~sy, 1, 0, fx, fx - 2, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + (p - 1) > ex) & (fy + p < ex) & (ey < fx) & (ey < fy + (p - 3)) & (ex > fx + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex, fx + 1, ey + 1),
            SELTZORange(~sx, 1, 0, fy, fy - 2, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S2A0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (fx + p == ey) & (ex < fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey, fy + 1, fx + 2),
            SELTZORange(sy, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S2A0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (fy + p == ex) & (ey < fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex, fx + 1, fy + 2),
            SELTZORange(sx, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S2A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (fx + p == ey) & (ex < fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fy, fx + 2),
            SELTZORange(sy, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S2A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (fy + p == ex) & (ey < fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fx, fy + 2),
            SELTZORange(sx, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S2A2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (fx + p == ey) & (ex == fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fy, fx + 2),
            SELTZORange(sy, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S2A2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (fy + p == ex) & (ey == fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fx, fy + 2),
            SELTZORange(sx, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S2B-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + (p - 1) > ey) & (fx + p < ey) & (ex < fy) & (ex == fx + (p - 3)) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey, fy + 1, ex + 1),
            SELTZORange(~sy, 1, 0, fx, fx - 3, fx - 2))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S2B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + (p - 1) > ex) & (fy + p < ex) & (ey < fx) & (ey == fy + (p - 3)) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex, fx + 1, ey + 1),
            SELTZORange(~sx, 1, 0, fy, fy - 3, fy - 2))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S2C-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (fx + (p - 1) == ey) & (ex + 2 < ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ey, fy, fx + 1),
            SELTZORange(sy, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S2C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (fy + (p - 1) == ex) & (ey + 2 < ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ex, fx, fy + 1),
            SELTZORange(sx, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S2D-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + p > ey) & (fx + p < ey) & (ex < fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sy, 1, 0, fx, fx - 2, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S2D-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + p > ex) & (fy + p < ex) & (ey < fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sx, 1, 0, fy, fy - 2, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S2BD-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + p > ey) & (fx + p < ey) & (ex == fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sy, 1, 0, fx, fx - 3, fx - 2))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S2BD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + p > ex) & (fy + p < ex) & (ey == fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sx, 1, 0, fy, fy - 3, fy - 2))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S3A0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex < ey + (p - 2)) & (fx > ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S3A0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey < ex + (p - 2)) & (fy > ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S3A2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (fx == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S3A2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (fy == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S3B-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex < fy + p) & (fx == ey) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S3B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey < fx + p) & (fy == ex) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S4-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx < fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy < fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S4D0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S4D0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S4A-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx == fy) & (ey > fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(sy, 1, 0, fx - 3, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S4A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy == fx) & (ex > fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(sx, 1, 0, fy - 3, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S4B-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx == fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx - 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S4B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy == fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy - 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S4C0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx == fy + 2) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fy + 2),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S4C0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy == fx + 2) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fx + 2),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S4C1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx == fy + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fy + 1, fy + 2),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S4C1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy == fx + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fx + 1, fx + 2),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S4BD-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx == fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S4BD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy == fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S4D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == fy + (p - 1)) & (fx + 1 == ey) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S4D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == fx + (p - 1)) & (fy + 1 == ex) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S4E0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == fy + (p + 1)) & (fx + 1 < ey) & (ey < fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S4E0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == fx + (p + 1)) & (fy + 1 < ex) & (ex < fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S4E1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == fy + (p + 1)) & (fx + 1 == ey) & (ey < fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy + 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S4E1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == fx + (p + 1)) & (fy + 1 == ex) & (ex < fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx + 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S4E2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == fy + (p + 1)) & (fx + 1 < ey) & (ey < fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, fy + 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S4E2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == fx + (p + 1)) & (fy + 1 < ex) & (ex < fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, fx + 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S4E3-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == fy + (p + 1)) & (fx + 1 == ey) & (ey < fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy + 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S4E3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == fx + (p + 1)) & (fy + 1 == ex) & (ex < fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx + 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S4F0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx < fy + (p - 2)) & (ey == fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S4F0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy < fx + (p - 2)) & (ex == fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S4F2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (fx == fy + (p - 2)) & (ey == fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(~sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S4F2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (fy == fx + (p - 2)) & (ex == fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(~sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S5-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx + 1 < ey) & (fx > fy + 2) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fy + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S5-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy + 1 < ex) & (fy > fx + 2) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fx + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S5A-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx + 1 == ey) & (fx > fy + 2) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fy + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S5A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy + 1 == ex) & (fy > fx + 2) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fx + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S5B-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx + 1 < ey) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S5B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy + 1 < ex) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S5AB-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx + 1 == ey) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S5AB-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy + 1 == ex) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S6-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > fy + (p + 1)) & (fx + 1 < ey) & (ex < fx + (p - 3)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(~sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S6-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > fx + (p + 1)) & (fy + 1 < ex) & (ey < fy + (p - 3)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(~sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S6A-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > fy + (p + 1)) & (fx + 1 == ey) & (ex < fx + (p - 3)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(~sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S6A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > fx + (p + 1)) & (fy + 1 == ex) & (ey < fy + (p - 3)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(~sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S6B-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > fy + (p + 1)) & (fx + 1 < ey) & (ex == fx + (p - 3)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S6B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > fx + (p + 1)) & (fy + 1 < ex) & (ey == fy + (p - 3)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S6C-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx + 1 < ey) & (ex < fx + (p - 3)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(~sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S6C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy + 1 < ex) & (ey < fy + (p - 3)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(~sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-S6AB-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > fy + (p + 1)) & (fx + 1 == ey) & (ex == fx + (p - 3)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(~sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-S6AB-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > fx + (p + 1)) & (fy + 1 == ex) & (ey == fy + (p - 3)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(~sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SB10-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SB10-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SB12-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SB12-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SB20-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SB20-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SB21-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SB21-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-SB22-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-SB22-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
