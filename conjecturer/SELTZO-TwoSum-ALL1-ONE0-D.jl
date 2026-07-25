function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
    ::Val{ONE0},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ALL1-ONE0-DE-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, fy - p, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-DE-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, fx - p, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-D1A0-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == fy + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-D1A0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == fx + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-D1A1-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == fy + (p - 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-D1A1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == fx + (p - 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-D3-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex > fy + p) & (ex < ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-D3-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey > fx + p) & (ey < ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-D3A-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex > fy + p) & (ex < ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, fy - 1))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-D3A-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey > fx + p) & (ey < ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, fx - 1))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-D3B-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-D3B-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-D3AB-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == fy + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ex - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-D3AB-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == fx + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ey - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-D3C-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-D3C-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-D3AC-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 1, 0, fy, ey - p, fy - 1))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-D3AC-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 1, 0, fx, ex - p, fx - 1))
    end

end
