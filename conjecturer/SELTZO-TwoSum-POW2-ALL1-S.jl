function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{POW2},
    ::Val{ALL1},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-POW2-ALL1-SA1-X",
        (CLASS_X == POW2) & (CLASS_Y == ALL1) &
        (ex == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx + 1, gx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-POW2-ALL1-SA1-Y",
        (CLASS_Y == POW2) & (CLASS_X == ALL1) &
        (ey == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy + 1, gy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-POW2-ALL1-SA2-X",
        (CLASS_X == POW2) & (CLASS_Y == ALL1) &
        (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-POW2-ALL1-SA2-Y",
        (CLASS_Y == POW2) & (CLASS_X == ALL1) &
        (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-POW2-ALL1-SG-X",
        (CLASS_X == POW2) & (CLASS_Y == ALL1) &
        (ex > ey + 2) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-POW2-ALL1-SG-Y",
        (CLASS_Y == POW2) & (CLASS_X == ALL1) &
        (ey > ex + 2) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-POW2-ALL1-SB-X",
        (CLASS_X == POW2) & (CLASS_Y == ALL1) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-POW2-ALL1-SB-Y",
        (CLASS_Y == POW2) & (CLASS_X == ALL1) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
