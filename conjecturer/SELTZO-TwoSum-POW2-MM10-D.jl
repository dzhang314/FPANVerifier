function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{POW2},
    ::Val{MM10},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-POW2-MM10-DA0-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-MM10-DA0-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-MM10-DA1-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-MM10-DA1-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-MM10-D1-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex > fy + (p + 1)) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-D1-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey > fx + (p + 1)) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-MM10-D1A0-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == fy + (p + 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ey),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-D1A0-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == fx + (p + 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ex),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-MM10-D1A1-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == fy + (p + 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ey),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-POW2-MM10-D1A1-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == fx + (p + 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ex),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-POW2-MM10-D2A0-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ey),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-D2A0-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ex),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-MM10-D2A1-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ey),
            SELTZORange(sy, 0, 0, ex - (p + 2), ex - (p + p + 2), ex - (p + 2)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-D2A1-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ex),
            SELTZORange(sx, 0, 0, ey - (p + 2), ey - (p + p + 2), ey - (p + 2)))
    end

    checker("SELTZO-TwoSum-POW2-MM10-D3A0-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-D3A0-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-MM10-D3A1-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, ey - 1, fy),
            SELTZORange(sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-D3A1-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, ex - 1, fx),
            SELTZORange(sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-POW2-MM10-DB1-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ex - (p + 1), ex - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-DB1-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ey - (p + 1), ey - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-MM10-DB20-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == ey + (p + 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ex - (p + 1), ex - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-DB20-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == ex + (p + 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ey - (p + 1), ey - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-MM10-DB21-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == ey + (p + 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ex - (p + 1), ex - 1),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-DB21-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == ex + (p + 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ey - (p + 1), ey - 1),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

end
