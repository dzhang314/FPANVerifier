function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO0},
    ::Val{MM01},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-TWO0-MM01-DE0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DE0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DE1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DE1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DE2-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DE2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DE3-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx + 2 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DE3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy + 2 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DE40-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx == fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fy, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DE40-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy == fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fx, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DE41-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx == fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fy, fy - 3, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DE41-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy == fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fx, fx - 3, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DE5-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fx, fy - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DE5-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fy, fx - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DE6-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fx, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DE6-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fy, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DA10-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DA10-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DA11-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DA11-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DA12-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DA12-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DA13-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx == fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DA13-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy == fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DA14-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx > fy + 1) & (ex == fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DA14-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy > fx + 1) & (ey == fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DA15-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DA15-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DA16-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx > fy + 1) & (ex > fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DA16-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy > fx + 1) & (ey > fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DA17-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + 1) & (fx > fy + 1) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DA17-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + 1) & (fy > fx + 1) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DA20-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DA20-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DA21-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (fx > fy) & (ex > fx + 2) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DA21-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + 2) & (fy > fx) & (ey > fy + 2) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DA22-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (ex == fx + 2) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DA22-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + 2) & (ey == fy + 2) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DA23-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (ey == gy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DA23-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + 2) & (ex == gx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DA24-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (ey == gy + (p - 3)) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DA24-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + 2) & (ex == gx + (p - 3)) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DA25-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (ey == gy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DA25-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + 2) & (ex == gx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DA26-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (ey == fy + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DA26-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + 2) & (ex == fx + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DA27-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + 2) & (ey == fy + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DA27-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + 2) & (ex == fx + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D1C-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D1C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D2-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (fy < fx) & (fx < ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > ex + 2) & (fx < fy) & (fy < ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D2B-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > ey + 3) & (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D2B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > ex + 3) & (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D2C0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (ex == fy + (p - 2)) & (fy + 1 < fx) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D2C0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > ex + 2) & (ey == fx + (p - 2)) & (fx + 1 < fy) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D2C1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (ex == fy + (p - 2)) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D2C1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > ex + 2) & (ey == fx + (p - 2)) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D2BC0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == fy + (p - 2)) & (fx == ey + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D2BC0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == fx + (p - 2)) & (fy == ex + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D2BC1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == fy + (p - 2)) & (fx == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D2BC1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == fx + (p - 2)) & (fy == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D2D-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == fy + (p - 2)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D2D-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == fx + (p - 2)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D3-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > ey + 2) & (ex == fy + (p - 1)) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > ex + 2) & (ey == fx + (p - 1)) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D3DA-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == fy + (p - 1)) & (fx == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D3DA-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == fx + (p - 1)) & (fy == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D3D-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == fy + (p - 1)) & (fx == ey + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D3D-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == fx + (p - 1)) & (fy == ex + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D3E0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == fy + (p - 1)) & (fx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D3E0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == fx + (p - 1)) & (fy > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D3E1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == fy + (p - 1)) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D3E1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == fx + (p - 1)) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D4-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == fy + p) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == fx + p) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D4DA-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == fy + p) & (fx == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D4DA-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == fx + p) & (fy == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D4D-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == fy + p) & (fx == ey + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D4D-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == fx + p) & (fy == ex + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D4E0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == fy + p) & (fx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D4E0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == fx + p) & (fy > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D4E1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == fy + p) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D4E1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == fx + p) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D5-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > fy + p) & (fx < ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D5-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > fx + p) & (fy < ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D5D-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D5D-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D5E0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex > fy + p) & (fx == ey + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D5E0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey > fx + p) & (fy == ex + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D5E1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == fy + (p + 1)) & (fx == ey + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D5E1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == fx + (p + 1)) & (fy == ex + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-D5F-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex < ey + p) & (ex > fy + p) & (fx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-D5F-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey < ex + p) & (ey > fx + p) & (fy > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DB0-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + p) & (fx > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DB0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + p) & (fy > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-MM01-DB1-X",
        (CLASS_X == TWO0) & (CLASS_Y == MM01) &
        (ex == ey + p) & (fx == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-MM01-DB1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == MM01) &
        (ey == ex + p) & (fy == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
