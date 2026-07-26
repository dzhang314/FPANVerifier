function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM01},
    ::Val{POW2},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-MM01-POW2-DE0-X",
        (CLASS_X == MM01) & (CLASS_Y == POW2) &
        (ex == ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-POW2-DE0-Y",
        (CLASS_Y == MM01) & (CLASS_X == POW2) &
        (ey == ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-POW2-DE1-X",
        (CLASS_X == MM01) & (CLASS_Y == POW2) &
        (ex == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-POW2-DE1-Y",
        (CLASS_Y == MM01) & (CLASS_X == POW2) &
        (ey == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-POW2-DG-X",
        (CLASS_X == MM01) & (CLASS_Y == POW2) &
        (fx > ey + 1) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-POW2-DG-Y",
        (CLASS_Y == MM01) & (CLASS_X == POW2) &
        (fy > ex + 1) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-POW2-DGA01-X",
        (CLASS_X == MM01) & (CLASS_Y == POW2) &
        (fx == ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-POW2-DGA01-Y",
        (CLASS_Y == MM01) & (CLASS_X == POW2) &
        (fy == ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-POW2-DGA02-X",
        (CLASS_X == MM01) & (CLASS_Y == POW2) &
        (fx == ey + 1) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-POW2-DGA02-Y",
        (CLASS_Y == MM01) & (CLASS_X == POW2) &
        (fy == ex + 1) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-POW2-DGA11-X",
        (CLASS_X == MM01) & (CLASS_Y == POW2) &
        (fx + 1 == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-POW2-DGA11-Y",
        (CLASS_Y == MM01) & (CLASS_X == POW2) &
        (fy + 1 == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-POW2-DGA12-X",
        (CLASS_X == MM01) & (CLASS_Y == POW2) &
        (fx == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-POW2-DGA12-Y",
        (CLASS_Y == MM01) & (CLASS_X == POW2) &
        (fy == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-POW2-DGB0-X",
        (CLASS_X == MM01) & (CLASS_Y == POW2) &
        (fx > ey + 2) & (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-POW2-DGB0-Y",
        (CLASS_Y == MM01) & (CLASS_X == POW2) &
        (fy > ex + 2) & (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fy - 1), pos_zero)
    end

end
