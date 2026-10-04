function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM10},
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

    checker("SELTZO-TwoSum-MM10-R0R1-DE0-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fx - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DE0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fy - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DE1-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fx - p, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DE1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fy - p, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DE2-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fy - p, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DE2-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fx - p, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DE3-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy - 1, fy - (p + 1), fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DE3-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx - 1, fx - (p + 1), fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DE4-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DE4-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DE5-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fy, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DE5-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fx, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DA10-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx > fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DA10-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy > fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DA11-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx > fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DA11-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy > fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DA12-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DA12-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DA13-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DA13-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DA14-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DA14-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DA15-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx < fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DA15-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy < fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DA16-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx < fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DA16-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy < fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DA2-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (fx < fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DA2-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (fy < fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D1-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx > fy) & (fx + 1 < ey) & (ex > ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy > fx) & (fy + 1 < ex) & (ey > ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D1A0-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (fx < fy + 3) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D1A0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (fy < fx + 3) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D1A1-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx > fy + 2) & (fx + 1 == ey) & (ex > ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D1A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy > fx + 2) & (fy + 1 == ex) & (ey > ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D1B0-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx > fy + 3) & (fx + 1 < ey) & (ex > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D1B0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy > fx + 3) & (fy + 1 < ex) & (ey > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D1B1-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx == fy + 3) & (fx + 1 < ey) & (ex > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D1B1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy == fx + 3) & (fy + 1 < ex) & (ey > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D1AB0-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx > fy + 3) & (fx + 1 == ey) & (ex > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D1AB0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy > fx + 3) & (fy + 1 == ex) & (ey > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D1AB1-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx == fy + 3) & (fx + 1 == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D1AB1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy == fx + 3) & (fy + 1 == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D2-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx + 1 < ey) & (ex > fy + (p + 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D2-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy + 1 < ex) & (ey > fx + (p + 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D2A-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex > fy + (p + 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, ex - (p - 1)),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D2A-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey > fx + (p + 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, ey - (p - 1)),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D2B-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx + 1 < ey) & (ex > ey + 1) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D2B-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy + 1 < ex) & (ey > ex + 1) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D2AB-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex > ey + 1) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, ex - (p - 1)),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D2AB-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey > ex + 1) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 1, ey - (p - 1)),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D2C0-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx + 1 < ey) & (ex == fy + (p + 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D2C0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy + 1 < ex) & (ey == fx + (p + 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D2C1-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx + 1 == ey) & (ex == fy + (p + 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, fx - 1, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D2C1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy + 1 == ex) & (ey == fx + (p + 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, fy - 1, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D3-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ex - p, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D3-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ey - p, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D4-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx > ey + 1) & (ex > fy + p) & (ex < ey + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D4-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy > ex + 1) & (ey > fx + p) & (ey < ex + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D4A0-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx > ey + 1) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D4A0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy > ex + 1) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D4A1-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx > ey + 2) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D4A1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy > ex + 2) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D4A2-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx == ey + 2) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D4A2-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy == ex + 2) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D4B-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D4B-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D5-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex < fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D5-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey < fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D5A-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D5A-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D5B-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D5B-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D5AB-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx == ey + 1) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D5AB-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy == ex + 1) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D6-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex < fy + p) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D6-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy == ex) & (ey < fx + p) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D6A-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex < fy + p) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fy, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D6A-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy == ex) & (ey < fx + p) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fx, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D6B0-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex == fy + p) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 2, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D6B0-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy == ex) & (ey == fx + p) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 2, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D6B1-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex == fy + p) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D6B1-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy == ex) & (ey == fx + p) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D6C-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex > fy + p) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 2, ey - 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D6C-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy == ex) & (ey > fx + p) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 2, ex - 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-D6BC-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (fx == ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 2, ey - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-D6BC-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (fy == ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 2, ex - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DB10-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (fx > ey + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DB10-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (fy > ex + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DB11-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (fx == ey + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DB11-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (fy == ex + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DB12-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (fx > ey + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DB12-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (fy > ex + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DB13-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + (p - 1)) & (fx == ey + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DB13-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + (p - 1)) & (fy == ex + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DB20-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (fx == ey + 3) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DB20-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + p) & (fy == ex + 3) & (ex > fx + 2) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DB21-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (fx == ey + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DB21-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + p) & (fy == ex + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 0, 0, ex - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-R0R1-DB22-X",
        (CLASS_X == MM10) & (CLASS_Y == R0R1) &
        (ex == ey + p) & (fx == ey + 3) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-MM10-R0R1-DB22-Y",
        (CLASS_Y == MM10) & (CLASS_X == R0R1) &
        (ey == ex + p) & (fy == ex + 3) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
