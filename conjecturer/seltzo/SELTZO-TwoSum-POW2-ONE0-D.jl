function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{POW2},
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

    checker("SELTZO-TwoSum-POW2-ONE0-DA0-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fy, ex - p, ex - p), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-ONE0-DA0-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fx, ey - p, ey - p), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-ONE0-DA1-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, ex - (p + 1), ex - p), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-ONE0-DA1-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, ey - (p + 1), ey - p), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-ONE0-D1-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE0) &
        (ex > fy + (p + 1)) & (ex < ey + (p + 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-ONE0-D1-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE0) &
        (ey > fx + (p + 1)) & (ey < ex + (p + 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-ONE0-D1A-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE0) &
        (ex == fy + (p + 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fy + 2),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-ONE0-D1A-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE0) &
        (ey == fx + (p + 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fx + 2),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-ONE0-D1AB-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE0) &
        (ex == fy + (p + 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fy + 2),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-POW2-ONE0-D1AB-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE0) &
        (ey == fx + (p + 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fx + 2),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-POW2-ONE0-D1B-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE0) &
        (ex > fy + (p + 1)) & (ex < ey + (p + 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-POW2-ONE0-D1B-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE0) &
        (ey > fx + (p + 1)) & (ey < ex + (p + 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-POW2-ONE0-D2A0-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE0) &
        (ex == fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-ONE0-D2A0-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE0) &
        (ey == fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-ONE0-D2A1-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE0) &
        (ex == fy + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fy + 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-POW2-ONE0-D2A1-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE0) &
        (ey == fx + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fx + 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-POW2-ONE0-DB0-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE0) &
        (ex == ey + (p + 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ex - 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-ONE0-DB0-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE0) &
        (ey == ex + (p + 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ey - 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-ONE0-DB1-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE0) &
        (ex == ey + (p + 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ex - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-POW2-ONE0-DB1-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE0) &
        (ey == ex + (p + 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ey - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
