function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{POW2},
    ::Val{MM01},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-POW2-MM01-S1-X",
        (CLASS_X == POW2) & (CLASS_Y == MM01) &
        (ex > fy + p) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-POW2-MM01-S1-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM01) &
        (ey > fx + p) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-POW2-MM01-S1A-X",
        (CLASS_X == POW2) & (CLASS_Y == MM01) &
        (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-POW2-MM01-S1A-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM01) &
        (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-POW2-MM01-S2A-X",
        (CLASS_X == POW2) & (CLASS_Y == MM01) &
        (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-POW2-MM01-S2A-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM01) &
        (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-POW2-MM01-S3A0-X",
        (CLASS_X == POW2) & (CLASS_Y == MM01) &
        (ex == fy + (p - 2)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-MM01-S3A0-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM01) &
        (ey == fx + (p - 2)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-MM01-S3A1-X",
        (CLASS_X == POW2) & (CLASS_Y == MM01) &
        (ex == fy + (p - 2)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-MM01-S3A1-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM01) &
        (ey == fx + (p - 2)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-MM01-SB-X",
        (CLASS_X == POW2) & (CLASS_Y == MM01) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-POW2-MM01-SB-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM01) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
