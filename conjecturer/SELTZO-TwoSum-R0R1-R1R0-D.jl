function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R0R1},
    ::Val{R1R0},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R0R1-R1R0-D1-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (ex < fy + p) & (fx + 1 < ey) & (fx > fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-D1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (ey < fx + p) & (fy + 1 < ex) & (fy > fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-D3-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex > fy + (p + 1)) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-D3-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey > fx + (p + 1)) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-DA11-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (ex < fy + p) & (fx > fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, fy, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-DA11-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (ey < fx + p) & (fy > fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, fx, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-DA12-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy + 1, fx, ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-DA12-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx + 1, fy, ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-DA13-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy + 1, ey - (p - 1), ey - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-DA13-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx + 1, ex - (p - 1), ex - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-DA14-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-DA14-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == fx + p) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-DA21-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx < fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey + 1, fy + 1, ey - (p - 3)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-DA21-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy < fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex + 1, fx + 1, ex - (p - 3)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-DA22-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx > fy) & (ey < fy + (p - 2)) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey + 1, fx + 1, ey - (p - 3)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-DA22-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy > fx) & (ex < fx + (p - 2)) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex + 1, fy + 1, ex - (p - 3)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-DA23-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (ex == fy + (p + 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex - 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-DA23-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (ey == fx + (p + 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey - 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-DA24-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + 2) & (fx + 1 < ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-DA24-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + 2) & (fy + 1 < ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-D1A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex < fy + p) & (fx + 1 == ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-D1A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey < fx + p) & (fy + 1 == ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-D1B0-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex > ey + 2) & (ex == fy + p) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-D1B0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey > ex + 2) & (ey == fx + p) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-D1AB0-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (fx + 1 == ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-D1AB0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == fx + p) & (fy + 1 == ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-D1AB1-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == fy + p) & (fx == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fy, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-D1AB1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == fx + p) & (fy == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fx, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-D2B-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex < ey + p) & (ex > fy + (p + 1)) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-D2B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey < ex + p) & (ey > fx + (p + 1)) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-D3A0-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (fx == ey) & (ex > fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ex - p, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-D3A0-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (fy == ex) & (ey > fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ey - p, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-D3A1-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == fy + (p + 1)) & (fx == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, fy, ex - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-D3A1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == fx + (p + 1)) & (fy == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, fx, ey - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-D3B-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == fy + (p + 1)) & (fx < ey) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-D3B-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == fx + (p + 1)) & (fy < ex) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R0R1-R1R0-DB1-X",
        (CLASS_X == R0R1) & (CLASS_Y == R1R0) &
        (ex == ey + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, ex),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R0R1-R1R0-DB1-Y",
        (CLASS_Y == R0R1) & (CLASS_X == R1R0) &
        (ey == ex + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, ey),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
