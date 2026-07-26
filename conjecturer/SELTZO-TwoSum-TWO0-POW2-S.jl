function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO0},
    ::Val{POW2},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-TWO0-POW2-S1-X",
        (CLASS_X == TWO0) & (CLASS_Y == POW2) &
        (fx > ey + 1) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-POW2-S1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == POW2) &
        (fy > ex + 1) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-POW2-S1A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == POW2) &
        (fx == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-POW2-S1A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == POW2) &
        (fy == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-POW2-S1A2-X",
        (CLASS_X == TWO0) & (CLASS_Y == POW2) &
        (fx == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-POW2-S1A2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == POW2) &
        (fy == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-POW2-S2-X",
        (CLASS_X == TWO0) & (CLASS_Y == POW2) &
        (ex + 1 > ey) & (fx + 1 < ey) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-POW2-S2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == POW2) &
        (ey + 1 > ex) & (fy + 1 < ex) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-POW2-S2A0-X",
        (CLASS_X == TWO0) & (CLASS_Y == POW2) &
        (fx + 1 == ey) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-POW2-S2A0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == POW2) &
        (fy + 1 == ex) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-POW2-S2A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == POW2) &
        (fx + 1 == ey) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-POW2-S2A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == POW2) &
        (fy + 1 == ex) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-POW2-S2B-X",
        (CLASS_X == TWO0) & (CLASS_Y == POW2) &
        (ex + 1 > ey) & (fx + 1 < ey) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-POW2-S2B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == POW2) &
        (ey + 1 > ex) & (fy + 1 < ex) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-POW2-SB-X",
        (CLASS_X == TWO0) & (CLASS_Y == POW2) &
        (ex == ey + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-POW2-SB-Y",
        (CLASS_Y == TWO0) & (CLASS_X == POW2) &
        (ey == ex + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy - 1), pos_zero)
    end

end
