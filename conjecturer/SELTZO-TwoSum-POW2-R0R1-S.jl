function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{POW2},
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

    checker("SELTZO-TwoSum-POW2-R0R1-SA0-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-SA0-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-SA1-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-SA1-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-SA2-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, ey),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-SA2-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, ex),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-S1-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (ex < ey + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-S1-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey > fx + p) & (ey < ex + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-S1A-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (ex < ey + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-S1A-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (ey < ex + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-S2-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex < fy + p) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-S2-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey < fx + p) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-S2A0-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (ex > ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-S2A0-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == fx + p) & (ey > ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-S2A1-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 3),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-S2A1-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 3),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-SB10-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-SB10-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-SB11-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-SB11-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-SB20-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-SB20-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-SB21-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-SB21-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 0, 0, ex - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-SB22-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-SB22-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

end
