function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO0},
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

    checker("SELTZO-TwoSum-TWO0-POW2-DE1-X",
        (CLASS_X == TWO0) & (CLASS_Y == POW2) &
        (ex == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 2, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-POW2-DE1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == POW2) &
        (ey == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 2, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-POW2-DA1-X",
        (CLASS_X == TWO0) & (CLASS_Y == POW2) &
        (ex == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-POW2-DA1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == POW2) &
        (ey == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-POW2-DGA01-X",
        (CLASS_X == TWO0) & (CLASS_Y == POW2) &
        (fx == ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx + 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-POW2-DGA01-Y",
        (CLASS_Y == TWO0) & (CLASS_X == POW2) &
        (fy == ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy + 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-POW2-DGA02-X",
        (CLASS_X == TWO0) & (CLASS_Y == POW2) &
        (fx == ey + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-POW2-DGA02-Y",
        (CLASS_Y == TWO0) & (CLASS_X == POW2) &
        (fy == ex + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-POW2-DGA11-X",
        (CLASS_X == TWO0) & (CLASS_Y == POW2) &
        (fx == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-POW2-DGA11-Y",
        (CLASS_Y == TWO0) & (CLASS_X == POW2) &
        (fy == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-POW2-DGA12-X",
        (CLASS_X == TWO0) & (CLASS_Y == POW2) &
        (fx == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-POW2-DGA12-Y",
        (CLASS_Y == TWO0) & (CLASS_X == POW2) &
        (fy == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-POW2-DB11-X",
        (CLASS_X == TWO0) & (CLASS_Y == POW2) &
        (ex == ey + (p - 1)) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-POW2-DB11-Y",
        (CLASS_Y == TWO0) & (CLASS_X == POW2) &
        (ey == ex + (p - 1)) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-POW2-DB21-X",
        (CLASS_X == TWO0) & (CLASS_Y == POW2) &
        (ex == ey + p) & (fx == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey, ey - p, ey))
    end
    checker("SELTZO-TwoSum-TWO0-POW2-DB21-Y",
        (CLASS_Y == TWO0) & (CLASS_X == POW2) &
        (ey == ex + p) & (fy == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex, ex - p, ex))
    end

end
