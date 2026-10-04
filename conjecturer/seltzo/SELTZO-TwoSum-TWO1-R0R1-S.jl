function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO1},
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

    checker("SELTZO-TwoSum-TWO1-R0R1-SA0-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx > fy + 2) & (ex > fx + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SA0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy > fx + 2) & (ey > fy + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SA1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx > fy + 3) & (ex == fx + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SA1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy > fx + 3) & (ey == fy + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SA2-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy + 3) & (ex == fx + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 3, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SA2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx + 3) & (ey == fy + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 3, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SA3-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SA3-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SA41-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SA41-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SA42-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SA42-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SA5-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy + 2) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SA5-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx + 2) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SA6-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx < fy + 2) & (ey > fy + 2) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SA6-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy < fx + 2) & (ex > fx + 2) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SA7-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ey == fy + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SA7-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ex == fx + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SA8-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ey == fy + 2) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 2, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SA8-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ex == fx + 2) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 2, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SA9-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ey == fy + 2) & (ex == fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SA9-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ex == fx + 2) & (ey == fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SA11-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ey == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SA11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ex == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SA12-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ey == fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SA12-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ex == fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ex > fy + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ey > fx + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1D-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ex > fy + p) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1D-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ey > fx + p) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1A01-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex > fy + p) & (ex > fx + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1A01-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex) & (ey > fx + p) & (ey > fy + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1A02-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex > fy + p) & (ex > fx + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1A02-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey > fx + p) & (ey > fy + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1AD01-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex > fy + p) & (ex > fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1AD01-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex) & (ey > fx + p) & (ey > fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1AD02-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex > fy + p) & (ex > fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1AD02-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey > fx + p) & (ey > fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1A1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex > fy + p) & (ex == fx + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1A1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey > fx + p) & (ey == fy + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1AD11-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex > fy + p) & (ex == fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1AD11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex) & (ey > fx + p) & (ey == fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1AD12-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex > fy + p) & (ex == fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1AD12-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey > fx + p) & (ey == fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1B0-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx > ey + 1) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1B0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy > ex + 1) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx > ey + 2) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy > ex + 2) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1B2-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey + 2) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1B2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex + 2) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1AB0-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + p) & (fx > fy + 3) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1AB0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + p) & (fy > fx + 3) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1AB1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + p) & (ex == fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1AB1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + p) & (ey == fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1AB2-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx + 1 > ey) & (fx == fy + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1AB2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy + 1 > ex) & (fy == fx + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1C0-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex < fy + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1C0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey < fx + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1C1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx + 1 > ey) & (fx < ey + 2) & (fx > fy + 2) & (ex < fy + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1C1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy + 1 > ex) & (fy < ex + 2) & (fy > fx + 2) & (ey < fx + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S1C2-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey) & (ey == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S1C2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex) & (ex == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S2-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx < ey) & (ex > fy + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy < ex) & (ey > fx + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S2A-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx < ey) & (ex > fy + p) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S2A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy < ex) & (ey > fx + p) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S3-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx < ey) & (fx > fy + 2) & (ex > ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S3-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy < ex) & (fy > fx + 2) & (ey > ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S3A0-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx < ey) & (fx > fy + 3) & (ex > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S3A0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy < ex) & (fy > fx + 3) & (ey > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S3A1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == fy + 3) & (fx + 1 < ey) & (ex > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S3A1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == fx + 3) & (fy + 1 < ex) & (ey > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S3A2-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == fy + 3) & (fx + 1 == ey) & (ex > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S3A2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == fx + 3) & (fy + 1 == ex) & (ey > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S3B01-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == fy + 1) & (fx + 1 < ey) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S3B01-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == fx + 1) & (fy + 1 < ex) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S3B02-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == fy + 2) & (fx + 1 < ey) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S3B02-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == fx + 2) & (fy + 1 < ex) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S3B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == fy + 2) & (fx + 1 == ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S3B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == fx + 2) & (fy + 1 == ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S3B2-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == fy + 2) & (fx + 1 == ey) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S3B2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == fx + 2) & (fy + 1 == ex) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S3C01-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex > ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S3C01-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey > ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S3C02-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex > ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S3C02-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy == ex) & (ey > ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-S3C1-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex == ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-S3C1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey == ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SB10-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (fx > ey + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SB10-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (fy > ex + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SB11-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (fx == ey + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SB11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (fy == ex + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SB12-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (fx > ey + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SB12-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (fy > ex + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SB13-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (fx == ey + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SB13-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (fy == ex + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SB20-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (fx == ey + 3) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SB20-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + p) & (fy == ex + 3) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SB21-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (fx == ey + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SB21-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + p) & (fy == ex + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-R0R1-SB22-X",
        (CLASS_X == TWO1) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (fx == ey + 3) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-TWO1-R0R1-SB22-Y",
        (CLASS_Y == TWO1) & (CLASS_X == R0R1) &
        (ey == ex + p) & (fy == ex + 3) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
