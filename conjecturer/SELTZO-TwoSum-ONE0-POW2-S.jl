function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
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

    checker("SELTZO-TwoSum-ONE0-POW2-S1-X",
        (CLASS_X == ONE0) & (CLASS_Y == POW2) &
        (fx < ey) & (ex + 1 > ey) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-POW2-S1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == POW2) &
        (fy < ex) & (ey + 1 > ex) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-POW2-S1A-X",
        (CLASS_X == ONE0) & (CLASS_Y == POW2) &
        (fx == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-POW2-S1A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == POW2) &
        (fy == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-POW2-S1B0-X",
        (CLASS_X == ONE0) & (CLASS_Y == POW2) &
        (fx + 1 < ey) & (ex + 1 > ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx + 1),
            SELTZORange(sy, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end
    checker("SELTZO-TwoSum-ONE0-POW2-S1B0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == POW2) &
        (fy + 1 < ex) & (ey + 1 > ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy + 1),
            SELTZORange(sx, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end

    checker("SELTZO-TwoSum-ONE0-POW2-S1B1-X",
        (CLASS_X == ONE0) & (CLASS_Y == POW2) &
        (fx + 1 == ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, ex + 1),
            SELTZORange(sy, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end
    checker("SELTZO-TwoSum-ONE0-POW2-S1B1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == POW2) &
        (fy + 1 == ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, ey + 1),
            SELTZORange(sx, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end

    checker("SELTZO-TwoSum-ONE0-POW2-S2-X",
        (CLASS_X == ONE0) & (CLASS_Y == POW2) &
        (fx > ey) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-POW2-S2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == POW2) &
        (fy > ex) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-POW2-SB1-X",
        (CLASS_X == ONE0) & (CLASS_Y == POW2) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-POW2-SB1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == POW2) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-POW2-SB2-X",
        (CLASS_X == ONE0) & (CLASS_Y == POW2) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey, ey - p, ey))
    end
    checker("SELTZO-TwoSum-ONE0-POW2-SB2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == POW2) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex, ex - p, ex))
    end

end
