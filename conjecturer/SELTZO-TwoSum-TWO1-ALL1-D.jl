function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO1},
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

    checker("SELTZO-TwoSum-TWO1-ALL1-DA1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ALL1) &
        (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fx, fx - 2, ex - p), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ALL1-DA1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ALL1) &
        (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fy, fy - 2, ey - p), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ALL1-DA2-X",
        (CLASS_X == TWO1) & (CLASS_Y == ALL1) &
        (ex == ey + 2) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ALL1-DA2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ALL1) &
        (ey == ex + 2) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ALL1-D11-X",
        (CLASS_X == TWO1) & (CLASS_Y == ALL1) &
        (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ALL1-D11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ALL1) &
        (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ALL1-D12-X",
        (CLASS_X == TWO1) & (CLASS_Y == ALL1) &
        (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ALL1-D12-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ALL1) &
        (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ALL1-D1A-X",
        (CLASS_X == TWO1) & (CLASS_Y == ALL1) &
        (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 2, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ALL1-D1A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ALL1) &
        (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, fy - 2, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ALL1-D2-X",
        (CLASS_X == TWO1) & (CLASS_Y == ALL1) &
        (ex < ey + p) & (fx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ALL1-D2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ALL1) &
        (ey < ex + p) & (fy > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-ALL1-DB-X",
        (CLASS_X == TWO1) & (CLASS_Y == ALL1) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-ALL1-DB-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ALL1) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

end
