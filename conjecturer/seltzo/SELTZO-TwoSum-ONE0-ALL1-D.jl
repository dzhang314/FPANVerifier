function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
    ::Val{ALL1},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ONE0-ALL1-DA0-X",
        (CLASS_X == ONE0) & (CLASS_Y == ALL1) &
        (ex == ey + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ALL1-DA0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ALL1) &
        (ey == ex + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ALL1-DA1-X",
        (CLASS_X == ONE0) & (CLASS_Y == ALL1) &
        (ex == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ALL1-DA1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ALL1) &
        (ey == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ALL1-DG-X",
        (CLASS_X == ONE0) & (CLASS_Y == ALL1) &
        (fx < ey + 1) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ALL1-DG-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ALL1) &
        (fy < ex + 1) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ALL1-DGA0-X",
        (CLASS_X == ONE0) & (CLASS_Y == ALL1) &
        (fx == ey + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fx - p, fx - (p + p), fx - p))
    end
    checker("SELTZO-TwoSum-ONE0-ALL1-DGA0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ALL1) &
        (fy == ex + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fy - p, fy - (p + p), fy - p))
    end

    checker("SELTZO-TwoSum-ONE0-ALL1-DGA1-X",
        (CLASS_X == ONE0) & (CLASS_Y == ALL1) &
        (fx == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ex - 1),
            SELTZORange(~sy, 0, 0, fx - p, fx - (p + p), fx - p))
    end
    checker("SELTZO-TwoSum-ONE0-ALL1-DGA1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ALL1) &
        (fy == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ey - 1),
            SELTZORange(~sx, 0, 0, fy - p, fy - (p + p), fy - p))
    end

    checker("SELTZO-TwoSum-ONE0-ALL1-DGB0-X",
        (CLASS_X == ONE0) & (CLASS_Y == ALL1) &
        (ex == ey + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ALL1-DGB0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ALL1) &
        (ey == ex + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ALL1-DGB1-X",
        (CLASS_X == ONE0) & (CLASS_Y == ALL1) &
        (ex == ey + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 1, ey),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ALL1-DGB1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ALL1) &
        (ey == ex + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 1, ex),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ALL1-DB-X",
        (CLASS_X == ONE0) & (CLASS_Y == ALL1) &
        (ex == ey + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ALL1-DB-Y",
        (CLASS_Y == ONE0) & (CLASS_X == ALL1) &
        (ey == ex + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

end
