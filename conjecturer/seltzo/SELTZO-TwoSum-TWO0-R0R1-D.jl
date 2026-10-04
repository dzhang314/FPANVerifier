function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO0},
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

    checker("SELTZO-TwoSum-TWO0-R0R1-DE0-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx > fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DE0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy > fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DE1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DE1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DE2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ex - (p + 1), ex - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DE2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ey - (p + 1), ey - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DE3-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey) & (ey == fy + 2) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DE3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex) & (ex == fx + 2) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DE4-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx > fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DE4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy > fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DE5-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx + 1 > fy) & (fx < fy + 2) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DE5-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy + 1 > fx) & (fy < fx + 2) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DE61-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DE61-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DE62-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy + 1) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DE62-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx + 1) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DE8-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DE8-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DE9-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DE9-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DE10-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx < fy) & (ex > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DE10-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy < fx) & (ey > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DE11-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx + 1 == fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 2, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DE11-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy + 1 == fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 2, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DE12-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx < fy) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DE12-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex) & (fy < fx) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DA10-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx + 1 == ey) & (fx > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DA10-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy + 1 == ex) & (fy > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DA11-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx + 1 == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fy, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DA11-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy + 1 == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fx, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DA12-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx + 1 == ey) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, ey - p, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DA12-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy + 1 == ex) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, ex - p, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DA14-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx + 1 == ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 3, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DA14-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy + 1 == ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 3, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DA15-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx + 2 < ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DA15-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy + 2 < ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DA16-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx + 2 < ey) & (fx < fy + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DA16-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy + 2 < ex) & (fy < fx + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DA171-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx + 2 == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DA171-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy + 2 == ex) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DA172-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx + 2 == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DA172-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy + 2 == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DA19-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx + 1 < ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DA19-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy + 1 < ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DA20-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx + 1 < ey) & (fx > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DA20-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy + 1 < ex) & (fy > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DA21-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx + 1 < ey) & (fx > fy + 3) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DA21-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy + 1 < ex) & (fy > fx + 3) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DA22-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy + 3) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DA22-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx + 3) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DA01-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (ey == fy + 2) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey - 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DA01-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (ex == fx + 2) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex - 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DA02-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (ey == fy + 2) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 1, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DA02-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (ex == fx + 2) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 1, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DA03-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (ey == fy + 3) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DA03-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (ex == fx + 3) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex < ey + (p - 1)) & (ex > fy + p) & (fx > ey + 1) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey < ex + (p - 1)) & (ey > fx + p) & (fy > ex + 1) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-D1A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx == ey) & (ex > fx + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-D1A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy == ex) & (ey > fy + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-D1A2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx == ey + 1) & (ex > fx + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-D1A2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy == ex + 1) & (ey > fy + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-D2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + (p - 1) > ey) & (fx + p < ey) & (ex + 1 < fy) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 1, ey, fy, ex + 1),
            SELTZORange(sy, 1, 0, fx, fx - 2, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-D2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + (p - 1) > ex) & (fy + p < ex) & (ey + 1 < fx) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 1, ex, fx, ey + 1),
            SELTZORange(sx, 1, 0, fy, fy - 2, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-D2B-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex + p > ey) & (fx + p < ey) & (ex + 1 < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 1, ey, fy, ex + 1),
            SELTZORange(sy, 1, 0, fx, fx - 3, fx - 2))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-D2B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey + p > ex) & (fy + p < ex) & (ey + 1 < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 1, ex, fx, ey + 1),
            SELTZORange(sx, 1, 0, fy, fy - 3, fy - 2))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-D3A-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx < ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-D3A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy < ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-D3B1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex > fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-D3B1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (fy == ex) & (ey > fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-D3B2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex > fx + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-D3B2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey > fy + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-D3D-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ex < fx + (p - 3)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-D3D-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ey < fy + (p - 3)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-D4-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (ex < fy + p) & (fx > fy + 2) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-D4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (ey < fx + p) & (fy > fx + 2) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-D4A-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (fx == fy + 2) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-D4A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (fy == fx + 2) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-D4B-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 1) & (ex < fy + (p - 1)) & (fx == fy + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-D4B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 1) & (ey < fx + (p - 1)) & (fy == fx + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-D4C-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (ex > ey + 1) & (fx > fy + 3) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-D4C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == fx + p) & (ey > ex + 1) & (fy > fx + 3) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-D5A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 2) & (ex < fx + (p - 2)) & (ey == fy + 2) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey - 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-D5A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 2) & (ey < fy + (p - 2)) & (ex == fx + 2) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex - 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-D5A2-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 2) & (ex < fx + (p - 2)) & (ey == fy + 2) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-D5A2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 2) & (ey < fy + (p - 2)) & (ex == fx + 2) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-D5A3-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex > ey + 2) & (ex < fx + (p - 2)) & (ey == fy + 3) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-D5A3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey > ex + 2) & (ey < fy + (p - 2)) & (ex == fx + 3) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DB10-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (fx > ey + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DB10-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (fy > ex + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DB12-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (fx == ey + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DB12-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (fy == ex + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DB14-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (fx > ey + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DB14-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (fy > ex + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DB15-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (fx == ey + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DB15-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (fy == ex + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DB20-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (fx == ey + 3) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DB20-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + p) & (fy == ex + 3) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DB21-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (fx == ey + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DB21-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + p) & (fy == ex + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-R0R1-DB22-X",
        (CLASS_X == TWO0) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (fx == ey + 3) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-TWO0-R0R1-DB22-Y",
        (CLASS_Y == TWO0) & (CLASS_X == R0R1) &
        (ey == ex + p) & (fy == ex + 3) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
