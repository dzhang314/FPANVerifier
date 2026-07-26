function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM01},
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

    checker("SELTZO-TwoSum-MM01-POW2-S1-X",
        (CLASS_X == MM01) & (CLASS_Y == POW2) &
        (fx + 1 < ey) & (ex + 1 > ey) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-POW2-S1-Y",
        (CLASS_Y == MM01) & (CLASS_X == POW2) &
        (fy + 1 < ex) & (ey + 1 > ex) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-POW2-S1A-X",
        (CLASS_X == MM01) & (CLASS_Y == POW2) &
        (fx + 1 == ey) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-POW2-S1A-Y",
        (CLASS_Y == MM01) & (CLASS_X == POW2) &
        (fy + 1 == ex) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-POW2-S1B-X",
        (CLASS_X == MM01) & (CLASS_Y == POW2) &
        (fx + 1 < ey) & (ex + 1 > ey) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-POW2-S1B-Y",
        (CLASS_Y == MM01) & (CLASS_X == POW2) &
        (fy + 1 < ex) & (ey + 1 > ex) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-POW2-S1AB-X",
        (CLASS_X == MM01) & (CLASS_Y == POW2) &
        (fx + 1 == ey) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-POW2-S1AB-Y",
        (CLASS_Y == MM01) & (CLASS_X == POW2) &
        (fy + 1 == ex) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-POW2-S2A1-X",
        (CLASS_X == MM01) & (CLASS_Y == POW2) &
        (fx == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-POW2-S2A1-Y",
        (CLASS_Y == MM01) & (CLASS_X == POW2) &
        (fy == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-POW2-S2A2-X",
        (CLASS_X == MM01) & (CLASS_Y == POW2) &
        (fx == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-POW2-S2A2-Y",
        (CLASS_Y == MM01) & (CLASS_X == POW2) &
        (fy == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-POW2-SB1-X",
        (CLASS_X == MM01) & (CLASS_Y == POW2) &
        (ex == ey + (p - 1)) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-POW2-SB1-Y",
        (CLASS_Y == MM01) & (CLASS_X == POW2) &
        (ey == ex + (p - 1)) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fy), pos_zero)
    end

end
