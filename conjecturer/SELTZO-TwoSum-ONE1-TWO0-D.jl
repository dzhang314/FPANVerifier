function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
    ::Val{TWO0},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ONE1-TWO0-DA10-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fy, ex - p), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-DA10-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fx, ey - p), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-DA11-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy - 2, ex - p), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-DA11-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx - 2, ey - p), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-DA12-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fy - 3, ex - p), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-DA12-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fx - 3, ey - p), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-DA13-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy + 1, fy - 1, ex - p), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-DA13-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx + 1, fx - 1, ey - p), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-DA14-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy + 1, ex - p, ex - p), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-DA14-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx + 1, ey - p, ey - p), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-DA15-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 2 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fy - 2, ex - p), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-DA15-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 2 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fx - 2, ey - p), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-DA16-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 2 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fy - 3, ex - p), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-DA16-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 2 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fx - 3, ey - p), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-DA20-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fy, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-DA20-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fx, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-DA21-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fy + 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-DA21-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fx + 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-DA22-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fy + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-DA22-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fx + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-DA23-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx > fy) & (fx < ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-DA23-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy > fx) & (fy < ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-DA24-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx == fy + 1) & (ey == fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fy + 2, fy + 2),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-DA24-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy == fx + 1) & (ex == fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fx + 2, fx + 2),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-DA26-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx > fy + 1) & (fx < ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-DA26-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy > fx + 1) & (fy < ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-DA27-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx == ey) & (ey == fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-DA27-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy == ex) & (ex == fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx < ey) & (fx + 1 > fy) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy < ex) & (fy + 1 > fx) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D1A-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D1A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D1B-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D1B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D1C0-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx < ey) & (fx > fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D1C0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy < ex) & (fy > fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D1C1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx == fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fy + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D1C1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy == fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fx + 2),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D1BC-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D1BC-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D2-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D2B-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fy, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D2B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fx, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D2C0-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy + 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D2C0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx + 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D2C1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fy + 1, fy + 2),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D2C1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fx + 1, fx + 2),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D2C1A-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fy + 1, fy + 2),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D2C1A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fx + 1, fx + 2),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D2D-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex > fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D2D-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey > fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D2DA-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex > fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D2DA-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey > fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D3-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D3B-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D3B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D3C-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fy + 2),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D3C-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fx + 2),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D4-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex > fy + p) & (ex < ey + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey > fx + p) & (ey < ex + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D4A-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex < ey + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D4A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey < ex + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D5-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex > fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D5-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey > fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D5A-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex > fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D5A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey > fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D5B-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex == fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fy + 2),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D5B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey == fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fx + 2),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D5AB-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex == fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fy + 2),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D5AB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey == fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fx + 2),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D5C-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D5C-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D5AC-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D5AC-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D5D-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex > fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D5D-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey > fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D5AD-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex > fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D5AD-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey > fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D5BD-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 2),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D5BD-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 2),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D5ABD-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 2),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D5ABD-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 2),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D5CD-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + p) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D5CD-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + p) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D5CDE-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + p) & (ey == fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fy, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D5CDE-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + p) & (ex == fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fx, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-D5ACD-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fy + p) & (ey > fy + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-D5ACD-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fx + p) & (ex > fx + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-DB0-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-DB0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-TWO0-DB1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ONE1-TWO0-DB1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

end
