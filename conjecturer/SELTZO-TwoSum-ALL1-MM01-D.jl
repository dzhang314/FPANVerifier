function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
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

    checker("SELTZO-TwoSum-ALL1-MM01-DE-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM01) &
        (ex == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-MM01-DE-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM01) &
        (ey == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-MM01-DA0-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM01) &
        (ex + 1 == ey) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 1, ex, fy, ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-MM01-DA0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM01) &
        (ey + 1 == ex) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 1, ey, fx, ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-MM01-DA1-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM01) &
        (ex + 1 == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 1, ex, fy - 1, ex - (p - 2)), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-MM01-DA1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM01) &
        (ey + 1 == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 1, ey, fx - 1, ey - (p - 2)), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-MM01-DG-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM01) &
        (ex > fy + p) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ALL1-MM01-DG-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM01) &
        (ey > fx + p) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ALL1-MM01-DGA-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM01) &
        (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ALL1-MM01-DGA-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM01) &
        (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ALL1-MM01-DGB-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM01) &
        (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ALL1-MM01-DGB-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM01) &
        (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ALL1-MM01-DGC0-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM01) &
        (ex == fy + (p - 2)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-MM01-DGC0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM01) &
        (ey == fx + (p - 2)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-MM01-DGC1-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM01) &
        (ex == fy + (p - 2)) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fy, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-MM01-DGC1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM01) &
        (ey == fx + (p - 2)) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fx, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-MM01-DB-X",
        (CLASS_X == ALL1) & (CLASS_Y == MM01) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ALL1-MM01-DB-Y",
        (CLASS_Y == ALL1) & (CLASS_X == MM01) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
