function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{POW2},
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

    checker("SELTZO-TwoSum-POW2-ALL1-DA1-X",
        (CLASS_X == POW2) & (CLASS_Y == ALL1) &
        (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - p, ex - (p + p), ex - p), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-ALL1-DA1-Y",
        (CLASS_Y == POW2) & (CLASS_X == ALL1) &
        (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - p, ey - (p + p), ey - p), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-ALL1-DA2-X",
        (CLASS_X == POW2) & (CLASS_Y == ALL1) &
        (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, ex - (p + 1), ex - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-ALL1-DA2-Y",
        (CLASS_Y == POW2) & (CLASS_X == ALL1) &
        (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, ey - (p + 1), ey - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-ALL1-DG-X",
        (CLASS_X == POW2) & (CLASS_Y == ALL1) &
        (ex > ey + 2) & (ex < ey + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-ALL1-DG-Y",
        (CLASS_Y == POW2) & (CLASS_X == ALL1) &
        (ey > ex + 2) & (ey < ex + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-ALL1-DB-X",
        (CLASS_X == POW2) & (CLASS_Y == ALL1) &
        (ex == ey + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ex - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-ALL1-DB-Y",
        (CLASS_Y == POW2) & (CLASS_X == ALL1) &
        (ey == ex + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ey - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

end
