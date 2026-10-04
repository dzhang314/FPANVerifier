function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
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

    checker("SELTZO-TwoSum-ONE0-TWO1-DE1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx < fy + 1) & (fx + 2 > fy) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy + 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DE1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy < fx + 1) & (fy + 2 > fx) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx + 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DE2-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 < fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DE2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 < fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DE3-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey) & (ex == fx + 2) & (ey > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ex - 3, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DE3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex) & (ey == fy + 2) & (ex > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ey - 3, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DE4-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx < fy + 1) & (fx + 2 > fy) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ex - 3, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DE4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy < fx + 1) & (fy + 2 > fx) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, ey - 3, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DE5-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 == fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DE5-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 == fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DE6-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey) & (ex == fx + 2) & (ey == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 3, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DE6-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex) & (ey == fy + 2) & (ex == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 3, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DE7-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey) & (ex == fx + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 2, ex - p, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DE7-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex) & (ey == fy + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 2, ey - p, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DE8-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey) & (ex == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 2, fx - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DE8-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex) & (ey == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 2, fy - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA10-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 1 == ey) & (fx + 2 < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fy, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA10-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 1 == ex) & (fy + 2 < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fx, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA11-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 1 == ey) & (fx + 2 == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fy, fy - 3, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA11-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 1 == ex) & (fy + 2 == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fx, fx - 3, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA12-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 1 == ey) & (fx + 2 == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fy, gy - 3, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA12-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 1 == ex) & (fy + 2 == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fx, gx - 3, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA13-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 1 == ey) & (fx + 1 == fy) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fx + 2, ex - (p - 1), ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA13-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 1 == ex) & (fy + 1 == fx) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fy + 2, ey - (p - 1), ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA14-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 1 == ey) & (fx + 1 == fy) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 1, fx + 2, ex - (p - 1), ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA14-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 1 == ex) & (fy + 1 == fx) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 1, fy + 2, ey - (p - 1), ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA15-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 1 == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fx + 1, fx - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA15-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 1 == ex) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fy + 1, fy - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA16-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 1 == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fx, fx - 3, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA16-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 1 == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fy, fy - 3, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA17-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 1 == ey) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fx, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA17-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 1 == ex) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fy, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA20-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 > fy) & (ex > fx + 2) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA20-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 > fx) & (ey > fy + 2) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA22-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 == fy) & (ex > fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA22-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 == fx) & (ey > fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA23-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 == fy) & (ex == fy + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 2, ey - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA23-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 == fx) & (ey == fx + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 2, ex - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA24-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ey == fy + (p - 3)) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA24-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ex == fx + (p - 3)) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA25-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ex == fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA25-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ey == fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA26-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ex == fx + (p - 2)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA26-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ey == fy + (p - 2)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA27-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA27-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA28-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 3, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA28-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 3, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA29-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA29-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA210-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ex == fx + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA210-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ey == fy + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA30-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 2 == ey) & (fx > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ex + 1, fx, fy - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA30-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 2 == ex) & (fy > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 0, ey + 1, fy, fx - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA31-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 2 == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ex + 1, fx + 1, fx - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA31-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 2 == ex) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 0, ey + 1, fy + 1, fy - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA32-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 2 == ey) & (fx + 1 == fy) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ex + 1, fx + 2, fx + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA32-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 2 == ex) & (fy + 1 == fx) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 0, ey + 1, fy + 2, fy + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA34-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 2 == ey) & (ey == fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ex + 1, fy - 2, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA34-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 2 == ex) & (ex == fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ey + 1, fx - 2, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA35-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 2 == ey) & (ey > fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 0, ex + 1, fy, fx + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA35-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 2 == ex) & (ex > fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 0, ey + 1, fx, fy + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA40-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + 2) & (ex == fx + 2) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA40-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + 2) & (ey == fy + 2) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA41-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + 2) & (ex == fx + 2) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA41-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + 2) & (ey == fy + 2) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DA42-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + 2) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DA42-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + 2) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex < ey + (p - 1)) & (fx > ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey < ex + (p - 1)) & (fy > ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D2-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D3-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D4-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx < ey) & (fy < fx + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy < ex) & (fx < fy + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D5-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D5-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy < ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D5A-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex == fy + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D5A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy < ex) & (ey == fx + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D5AB0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (ex == fy + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D5AB0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (ey == fx + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D5AB1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (ex == fy + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D5AB1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (ey == fx + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D6-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D6-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy > ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D6A-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D6A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D7-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex < ey + (p - 2)) & (fx > ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D7-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey < ex + (p - 2)) & (fy > ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D7A-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D7A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D7B0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 2)) & (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D7B0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + (p - 2)) & (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D7B1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 2)) & (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D7B1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + (p - 2)) & (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D8-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex == fy + (p - 2)) & (fx > fy + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D8-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy < ex) & (ey == fx + (p - 2)) & (fy > fx + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D8A0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex == fy + (p - 2)) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D8A0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey == fx + (p - 2)) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D8A1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex == fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D8A1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey == fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D9-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex == fy + (p - 1)) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D9-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy < ex) & (ey == fx + (p - 1)) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D9A0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex == fy + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D9A0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey == fx + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D9A1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex == fy + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D9A1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey == fx + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D10-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D10-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy > ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D10A-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + (p - 2)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D10A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + (p - 2)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D11-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == fy) & (fx + (p - 3) > ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D11-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == fx) & (fy + (p - 3) > ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D12A0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + (p + 1) == ey) & (ex > fy) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 1, ey - 1, ex, fx + 2),
            SELTZORange(~sy, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D12A0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + (p + 1) == ex) & (ey > fx) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 1, ex - 1, ey, fy + 2),
            SELTZORange(~sx, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D12A1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + (p + 1) == ey) & (ex == fy) & (fx + 3 < gy) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 1, ey - 1, fy - 2, fx + 2),
            SELTZORange(~sy, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D12A1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + (p + 1) == ex) & (ey == fx) & (fy + 3 < gx) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 1, ex - 1, fx - 2, fy + 2),
            SELTZORange(~sx, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D12AB0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + (p + 1) == ey) & (ex > fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 1, ey - 1, ex, fx + 2),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D12AB0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + (p + 1) == ex) & (ey > fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 1, ex - 1, ey, fy + 2),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D12AB1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + (p + 1) == ey) & (ex == fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 1, ey - 1, fy - 2, fx + 2),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D12AB1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + (p + 1) == ex) & (ey == fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 1, ex - 1, fx - 2, fy + 2),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D13B-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + (p - 1) == ey) & (ex + 1 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 1, ey, fy, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D13B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + (p - 1) == ex) & (ey + 1 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 1, ex, fx, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D13AB-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + (p - 1) == ey) & (ex + 1 == fy) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 1, ey, fy - 1, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D13AB-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + (p - 1) == ex) & (ey + 1 == fx) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 1, ex, fx - 1, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D13AC-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + p == ey) & (ex + 1 == fy) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 0, 1, ey, fy - 1, fx + 2),
            SELTZORange(~sy, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D13AC-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + p == ex) & (ey + 1 == fx) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 0, 1, ex, fx - 1, fy + 2),
            SELTZORange(~sx, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D13CD-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + p == ey) & (ex == fy) & (fx + 3 < gy) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 1, ey - 1, fy - 2, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D13CD-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + p == ex) & (ey == fx) & (fy + 3 < gx) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 1, ex - 1, fx - 2, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D14-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + 1 < fy) & (ex + 2 < ey) & (ex > fy) & (fx + p > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey - 1, ex, fx),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D14-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + 1 < fx) & (ey + 2 < ex) & (ey > fx) & (fy + p > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex - 1, ey, fy),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D14A-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + 1 == fy) & (ex + 2 < ey) & (ex > fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey - 1, ex, fx + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D14A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + 1 == fx) & (ey + 2 < ex) & (ey > fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex - 1, ey, fy + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D14B-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + 2 < fy) & (ex == fy) & (fx + p > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey - 1, ex - 2, fx),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D14B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + 2 < fx) & (ey == fx) & (fy + p > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex - 1, ey - 2, fy),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-D15A-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == fy) & (ex + 2 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 0, ey - 1, ex, fx - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-D15A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == fx) & (ey + 2 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sy, 1, 0, ex - 1, ey, fy - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DB10-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 1)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DB10-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + (p - 1)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DB11-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 1)) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DB11-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + (p - 1)) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DB20-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (fx > ey + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DB20-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + p) & (fy > ex + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DB21-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (fx > ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DB21-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + p) & (fy > ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DB22-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (fx == ey + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DB22-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + p) & (fy == ex + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-DB23-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (fx == ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-DB23-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + p) & (fy == ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

end
