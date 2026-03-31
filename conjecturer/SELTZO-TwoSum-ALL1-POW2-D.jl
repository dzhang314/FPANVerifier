function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
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

    checker("SELTZO-TwoSum-ALL1-POW2-DE-X",
        (CLASS_X == ALL1) & (CLASS_Y == POW2) &
        (ex == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-POW2-DE-Y",
        (CLASS_Y == ALL1) & (CLASS_X == POW2) &
        (ey == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-POW2-DB1-X",
        (CLASS_X == ALL1) & (CLASS_Y == POW2) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-POW2-DB1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == POW2) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-POW2-DB2-X",
        (CLASS_X == ALL1) & (CLASS_Y == POW2) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 0, 0, fx, fx - p, fx))
    end
    checker("SELTZO-TwoSum-ALL1-POW2-DB2-Y",
        (CLASS_Y == ALL1) & (CLASS_X == POW2) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 0, 0, fy, fy - p, fy))
    end

end
