function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
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

    checker("SELTZO-TwoSum-ONE0-POW2-DE1-X",
        (CLASS_X == ONE0) & (CLASS_Y == POW2) &
        (ex == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-POW2-DE1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == POW2) &
        (ey == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-POW2-DA1-X",
        (CLASS_X == ONE0) & (CLASS_Y == POW2) &
        (ex == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-POW2-DA1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == POW2) &
        (ey == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-POW2-DGA0-X",
        (CLASS_X == ONE0) & (CLASS_Y == POW2) &
        (fx == ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-POW2-DGA0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == POW2) &
        (fy == ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-POW2-DGA1-X",
        (CLASS_X == ONE0) & (CLASS_Y == POW2) &
        (ex == ey + 2) & (fx == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-POW2-DGA1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == POW2) &
        (ey == ex + 2) & (fy == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-POW2-DB11-X",
        (CLASS_X == ONE0) & (CLASS_Y == POW2) &
        (ex == ey + (p - 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ex - (p - 2), ex - (p - 3)), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-POW2-DB11-Y",
        (CLASS_Y == ONE0) & (CLASS_X == POW2) &
        (ey == ex + (p - 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ey - (p - 2), ey - (p - 3)), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-POW2-DB21-X",
        (CLASS_X == ONE0) & (CLASS_Y == POW2) &
        (ex == ey + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey, ey - p, ey))
    end
    checker("SELTZO-TwoSum-ONE0-POW2-DB21-Y",
        (CLASS_Y == ONE0) & (CLASS_X == POW2) &
        (ey == ex + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex, ex - p, ex))
    end

end
