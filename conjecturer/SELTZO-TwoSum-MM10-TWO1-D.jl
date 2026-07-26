function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM10},
    ::Val{TWO1},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-MM10-TWO1-DE1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DE1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DE2-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DE2-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DE3-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DE3-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DE4-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DE4-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DE50-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DE50-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DE51-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fx, fx - 3, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DE51-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fy, fy - 3, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DE6-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DE6-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DA10-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 < ey) & (fx > fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, fx, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DA10-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 < ex) & (fy > fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, fy, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DA11-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx == fy + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DA11-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy == fx + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DA12-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DA12-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DA13-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DA13-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DA14-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 < fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 2, fy - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DA14-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 < fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 2, fx - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DA15-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 < fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DA15-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 < fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DA16-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DA16-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DA17-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ey == fy + (p - 3)) & (fx == fy + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DA17-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ex == fx + (p - 3)) & (fy == fx + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DA19-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ey == fy + (p - 3)) & (ex > fx + 2) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DA19-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ex == fx + (p - 3)) & (ey > fy + 2) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DA20-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + 2) & (fx < fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ey - 1, ey - (p - 3)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DA20-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + 2) & (fy < fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ex - 1, ex - (p - 3)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex < ey + (p - 1)) & (fx > ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey < ex + (p - 1)) & (fy > ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D1A-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D1A-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D1B0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D1B0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D1B1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 2, fx - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D1B1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 2, fy - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D1C0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D1C0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D1C1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + p) & (fx > ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D1C1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + p) & (fy > ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D1C2-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + p) & (fx == ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D1C2-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + p) & (fy == ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D1BC0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + p) & (fx == ey + 1) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D1BC0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + p) & (fy == ex + 1) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D1BC10-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + p) & (fx == ey) & (fx > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D1BC10-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + p) & (fy == ex) & (fy > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D1BC11-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + p) & (fx == ey) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D1BC11-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + p) & (fy == ex) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D10-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex < fy + (p - 2)) & (fx == ey + 1) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D10-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey < fx + (p - 2)) & (fy == ex + 1) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D11-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex < fy + (p - 2)) & (fx == ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D11-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey < fx + (p - 2)) & (fy == ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D12-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex < fy + (p - 2)) & (fx == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D12-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey < fx + (p - 2)) & (fy == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D20-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 2)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D20-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 2)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D21-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 2)) & (fx == ey + 1) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D21-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 2)) & (fy == ex + 1) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D22-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 2)) & (fx == ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D22-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 2)) & (fy == ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D23-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 2)) & (fx == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D23-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 2)) & (fy == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D3-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex > ey + 2) & (fx < fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D3-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey > ex + 2) & (fy < fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D400-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < fy + (p - 2)) & (fx > fy + 1) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D400-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < fx + (p - 2)) & (fy > fx + 1) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D401-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex < fy + (p - 2)) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D401-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey < fx + (p - 2)) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D41-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (fx > fy + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D41-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (fy > fx + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D50-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex == fy + (p - 2)) & (fx > fy + 2) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D50-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey == fx + (p - 2)) & (fy > fx + 2) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D51-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex > ey) & (ex == fy + (p - 2)) & (fx > fy + 2) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D51-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey > ex) & (ey == fx + (p - 2)) & (fy > fx + 2) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D52-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 2)) & (ex > ey + 1) & (fx == fy + 2) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D52-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 2)) & (ey > ex + 1) & (fy == fx + 2) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D53-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex == fy + (p - 2)) & (fx == fy + 2) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 2, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D53-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey == fx + (p - 2)) & (fy == fx + 2) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 2, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D54-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 2)) & (ex > ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D54-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 2)) & (ey > ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D6-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex > fy + (p + 1)) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D6-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey > fx + (p + 1)) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D6E-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex > fy + (p + 1)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 2, ex - (p - 1)),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D6E-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey > fx + (p + 1)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 2, ey - (p - 1)),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D6C-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p + 1)) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D6C-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p + 1)) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D6D-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p + 1)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 2, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D6D-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p + 1)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 2, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D6F0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + p) & (fx + 1 < ey) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D6F0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + p) & (fy + 1 < ex) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D6F1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + p) & (fx + 1 < ey) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D6F1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + p) & (fy + 1 < ex) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D6EF0-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + p) & (fx + 1 == ey) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 2, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D6EF0-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + p) & (fy + 1 == ex) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 2, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D6EF1-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + p) & (fx + 1 == ey) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 2, fx),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D6EF1-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + p) & (fy + 1 == ex) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 2, fy),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D60-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D60-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D61-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex == fy + (p - 1)) & (fx > fy + 2) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D61-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey == fx + (p - 1)) & (fy > fx + 2) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D62-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex == fy + (p - 1)) & (fx == fy + 2) & (fx < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D62-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey == fx + (p - 1)) & (fy == fx + 2) & (fy < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D63-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 1)) & (fx == ey + 1) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D63-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 1)) & (fy == ex + 1) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D640-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 1)) & (fx == ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D640-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 1)) & (fy == ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-D641-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 1)) & (fx == ey) & (ex > ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ex - (p + 1), ex - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-TWO1-D641-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == fx + (p - 1)) & (fy == ex) & (ey > ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ey - (p + 1), ey - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DB10-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 1)) & (fx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DB10-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + (p - 1)) & (fy > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DB11-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 1)) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DB11-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + (p - 1)) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DB20-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (fx > ey + 3) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DB20-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + p) & (fy > ex + 3) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DB21-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (fx > ey + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DB21-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + p) & (fy > ex + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DB22-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (fx == ey + 3) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DB22-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + p) & (fy == ex + 3) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-MM10-TWO1-DB23-X",
        (CLASS_X == MM10) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (fx == ey + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-MM10-TWO1-DB23-Y",
        (CLASS_Y == MM10) & (CLASS_X == TWO1) &
        (ey == ex + p) & (fy == ex + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

end
