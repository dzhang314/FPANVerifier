function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
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

    checker("SELTZO-TwoSum-ONE0-R0R1-DA10-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx < fy + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy + 1, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA10-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy < fx + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx + 1, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA11-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA11-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA12-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fx, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA12-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fy, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA13-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 1 == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 1, ex, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA13-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 1 == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 1, ey, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA20-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx > fy + 1) & (ey < fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - 2, fy + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA20-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy > fx + 1) & (ex < fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - 2, fx + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA21-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx > fy + 1) & (ey < fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA21-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy > fx + 1) & (ex < fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA22-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx > fy + 1) & (ey == fy + (p - 1)) & (ex > fx + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - 2, fy + 2),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA22-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy > fx + 1) & (ex == fx + (p - 1)) & (ey > fy + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - 2, fx + 2),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA23-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (fx == fy + (p - 2)) & (ey == fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy + 2),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA23-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (fy == fx + (p - 2)) & (ex == fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx + 2),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA24-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey + 1) & (ex == fx + (p - 2)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - 2, fx + 1),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA24-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex + 1) & (ey == fy + (p - 2)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - 2, fy + 1),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA30-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (fx < fy + 1) & (ey == fy + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey - 1, fy, ey - (p - 1)),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA30-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (fy < fx + 1) & (ex == fx + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex - 1, fx, ex - (p - 1)),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA31-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (fx < fy + 1) & (ey > fy + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ey - 1, fy + 1, ey - (p - 1)),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA31-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (fy < fx + 1) & (ex > fx + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 0, ex - 1, fx + 1, ex - (p - 1)),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA32-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (fx > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ex + 1, fx, ex - (p - 3)),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA32-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (fy > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 0, ey + 1, fy, ey - (p - 3)),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA33-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (ex == fx + (p - 3)) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey - 1, fy, fy + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA33-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (ey == fy + (p - 3)) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex - 1, fx, fx + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA34-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (fx < fy + 1) & (ex == fx + (p - 3)) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ey - 1, fy + 1, fy + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA34-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (fy < fx + 1) & (ey == fy + (p - 3)) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 0, ex - 1, fx + 1, fx + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA35-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (fx + (p - 2) == fy) & (ex == fx + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ey, ey - p, ey),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA35-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (fy + (p - 2) == fx) & (ey == fy + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 0, ex, ex - p, ex),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA36-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (fx + (p - 3) == fy) & (ex == fx + (p - 2)) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey - 1, fy, fy + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA36-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (fy + (p - 3) == fx) & (ey == fy + (p - 2)) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex - 1, fx, fx + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA37-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 2 == ey) & (fx < fy + 1) & (ex == fx + (p - 2)) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ey - 1, fy + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA37-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 2 == ex) & (fy < fx + 1) & (ey == fy + (p - 2)) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 0, ex - 1, fx + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA41-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (fx == fy + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA41-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (fy == fx + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA42-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (fx == ey) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA42-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (fy == ex) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA44-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (fx == ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA44-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (fy == ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DA45-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == ey + 2) & (fx == ey) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DA45-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == ex + 2) & (fy == ex) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D1-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx > ey) & (ex < ey + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy > ex) & (ey < ex + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D1A-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx == ey) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, ey + 1),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D1A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy == ex) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, ex + 1),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D1B-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (fx > ey) & (ex < ey + (p - 1)) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D1B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (fy > ex) & (ey < ex + (p - 1)) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D1AB-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (fx == ey) & (ex > ey + 2) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, ey + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D1AB-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (fy == ex) & (ey > ex + 2) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, ex + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D1C0-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx > ey) & (ex > ey + 2) & (ex < ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D1C0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy > ex) & (ey > ex + 2) & (ey < ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D1C10-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (ex == ey + (p - 2)) & (fx > ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D1C10-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == fx + p) & (ey == ex + (p - 2)) & (fy > ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D1C11-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (ex == ey + (p - 2)) & (fx == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D1C11-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == fx + p) & (ey == ex + (p - 2)) & (fy == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D1AC-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx == ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D1AC-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy == ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D2-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (fx < ey) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey > fx + p) & (fy < ex) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy),
            SELTZORange(sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D2A-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (fx < ey) & (ex > ey + 1) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D2A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (fy < ex) & (ey > ex + 1) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D2B0-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx < ey) & (fx > fy + 2) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D2B0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy < ex) & (fy > fx + 2) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D2B10-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx < ey) & (fx == fy + 2) & (ex > ey + 1) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D2B10-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy < ex) & (fy == fx + 2) & (ey > ex + 1) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D2B11-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == fy + p) & (fx + 1 == ey) & (fx == fy + 2) & ((ex == ey + (p - 3)) & (ey == fy + 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D2B11-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == fx + p) & (fy + 1 == ex) & (fy == fx + 2) & ((ey == ex + (p - 3)) & (ex == fx + 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D3A-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex < fy + p) & (fx == fy + 1) & (ex > ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D3A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey < fx + p) & (fy == fx + 1) & (ey > ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D3B-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex < fy + p) & (fx == fy + 1) & (ex > ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D3B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey < fx + p) & (fy == fx + 1) & (ey > ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D4-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (fx + (p + 1) < ey) & (ex > fy) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(sy, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (fy + (p + 1) < ex) & (ey > fx) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(sx, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D4A0-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (fx + (p + 1) == ey) & (ex > fy) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 1, ey - 1, ex, fy + 1),
            SELTZORange(~sy, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D4A0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (fy + (p + 1) == ex) & (ey > fx) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 1, ex - 1, ey, fx + 1),
            SELTZORange(~sx, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D4A1-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (fx + (p + 1) == ey) & (ex == fy) & (ex > fx + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 1, ey - 1, fx, ey - 1),
            SELTZORange(~sy, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D4A1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (fy + (p + 1) == ex) & (ey == fx) & (ey > fy + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 1, ex - 1, fy, ex - 1),
            SELTZORange(~sx, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D4B-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (fx + (p + 1) < ey) & (ex > fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(sy, 1, 0, fx, fx - 2, fx - 1))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D4B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (fy + (p + 1) < ex) & (ey > fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(sx, 1, 0, fy, fy - 2, fy - 1))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D5B-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (fx + (p - 1) == ey) & (ex == fy) & (ex + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ey, ey - p, ey),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D5B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (fy + (p - 1) == ex) & (ey == fx) & (ey + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 0, ex, ex - p, ex),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D5C-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (fx + p == ey) & (ex == fy) & (ex + 2 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 1, ey - 1, ey - (p + 1), ey - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D5C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (fy + p == ex) & (ey == fx) & (ey + 2 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 1, ex - 1, ex - (p + 1), ex - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D6-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + p > ey) & (ex + 1 < fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 1, ey, fy, ex + 1),
            SELTZORange(sy, 1, 0, fx, fx - 2, fx - 1))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D6-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + p > ex) & (ey + 1 < fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 1, ex, fx, ey + 1),
            SELTZORange(sx, 1, 0, fy, fy - 2, fy - 1))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D6B-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex == fy) & (ex + 3 < ey) & (ex == fx + (p - 2)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey - 1, ey - p, ey - (p - 1)),
            SELTZORange(sy, 1, 0, fx, fx - 2, fx - 1))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D6B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey == fx) & (ey + 3 < ex) & (ey == fy + (p - 2)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex - 1, ex - p, ex - (p - 1)),
            SELTZORange(sx, 1, 0, fy, fy - 2, fy - 1))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-D7A-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + 3 == ey) & (ex == fx + (p - 2)) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 1, ex + 2, ex, fy + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-D7A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + 3 == ex) & (ey == fy + (p - 2)) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 1, ey + 2, ey, fx + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DB30-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + p == ey) & (fx < fy) & (ex < fx + (p - 2)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ey, fy, ey - (p - 2)),
            SELTZORange(sy, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DB30-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + p == ex) & (fy < fx) & (ey < fy + (p - 2)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 0, ex, fx, ex - (p - 2)),
            SELTZORange(sx, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-R0R1-DB31-X",
        (CLASS_X == ONE0) & (CLASS_Y == R0R1) &
        (ex + p == ey) & (fx < fy) & (ex == fx + (p - 2)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ey, fy, ey - (p - 2)),
            SELTZORange(sy, 1, 0, fx, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-R0R1-DB31-Y",
        (CLASS_Y == ONE0) & (CLASS_X == R0R1) &
        (ey + p == ex) & (fy < fx) & (ey == fy + (p - 2)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 0, ex, fx, ex - (p - 2)),
            SELTZORange(sx, 1, 0, fy, ey - p, ey - (p - 1)))
    end

end
