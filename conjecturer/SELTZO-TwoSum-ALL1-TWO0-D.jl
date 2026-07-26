function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
    ::Val{TWO0},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ALL1-TWO0-DE-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fy - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-DE-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fx - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-DA1-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy, fy),
            SELTZORange(~sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-DA1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx, fx),
            SELTZORange(~sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-DA2-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-DA2-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-DG-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex > fy + p) & (ex < ey + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-DG-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey > fx + p) & (ey < ex + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-DGA-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex > fy + p) & (ex < ey + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-DGA-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey > fx + p) & (ey < ex + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-DGB-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-DGB-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-DGAB-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-DGAB-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-DGC-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == fy + (p - 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-DGC-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == fx + (p - 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-DGD-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == fy + (p - 2)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-DGD-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == fx + (p - 2)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-DB0-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-DB0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-TWO0-DB1-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-ALL1-TWO0-DB1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

end
