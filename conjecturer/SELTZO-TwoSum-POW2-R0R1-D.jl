function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{POW2},
    ::Val{R0R1},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-POW2-R0R1-DA0-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-R0R1-DA0-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-R0R1-DA1-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-R0R1-DA1-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, ex - (p - 1), ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-R0R1-DA2-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-R0R1-DA2-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-R0R1-D1-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex > fy + (p + 1)) & (ex < ey + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-D1-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey > fx + (p + 1)) & (ey < ex + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-D1A-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (ex < ey + p) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-D1A-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey > fx + p) & (ey < ex + p) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-D2-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex < fy + (p + 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-D2-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey < fx + (p + 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-D2A-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == fy + (p + 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-D2A-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == fx + (p + 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-D2B-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex < fy + (p + 1)) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-D2B-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey < fx + (p + 1)) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-DB10-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, ex - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-DB10-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, ey - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-DB11-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, ex - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-DB11-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == ex + p) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, ey - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-DB20-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == ey + (p + 1)) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ex - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-DB20-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == ex + (p + 1)) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ey - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-DB21-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == ey + (p + 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ex - 1),
            SELTZORange(~sy, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-DB21-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == ex + (p + 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ey - 1),
            SELTZORange(~sx, 0, 0, ex - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-R0R1-DB22-X",
        (CLASS_X == POW2) & (CLASS_Y == R0R1) &
        (ex == ey + (p + 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ex - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-R0R1-DB22-Y",
        (CLASS_Y == POW2) & (CLASS_X == R0R1) &
        (ey == ex + (p + 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ey - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

end
