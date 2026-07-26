function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
    ::Val{TWO1},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ALL1-TWO1-DE0-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO1) &
        (ex == ey) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-TWO1-DE0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO1) &
        (ey == ex) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-TWO1-DE1-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO1) &
        (ex == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy - 2, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-TWO1-DE1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO1) &
        (ey == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx - 2, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-TWO1-DA-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-TWO1-DA-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-TWO1-DG-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO1) &
        (ex > fy + p) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ALL1-TWO1-DG-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO1) &
        (ey > fx + p) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ALL1-TWO1-DGA-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO1) &
        (ex == fy + p) & (ex < ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ALL1-TWO1-DGA-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO1) &
        (ey == fx + p) & (ey < ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ALL1-TWO1-DGAB-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ALL1-TWO1-DGAB-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO1) &
        (ey == ex + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ALL1-TWO1-DGB-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO1) &
        (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ALL1-TWO1-DGB-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO1) &
        (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ALL1-TWO1-DGC-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-TWO1-DGC-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-TWO1-DB1-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ALL1-TWO1-DB1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO1) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ALL1-TWO1-DB20-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-ALL1-TWO1-DB20-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO1) &
        (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-ALL1-TWO1-DB21-X",
        (CLASS_X == ALL1) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-ALL1-TWO1-DB21-Y",
        (CLASS_Y == ALL1) & (CLASS_X == TWO1) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

end
