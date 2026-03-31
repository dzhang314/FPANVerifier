function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
    ::Val{POW2},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ALL1-POW2-SE-X",
        (CLASS_X == ALL1) & (CLASS_Y == POW2) &
        (ex == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end
    checker("SELTZO-TwoSum-ALL1-POW2-SE-Y",
        (CLASS_Y == ALL1) & (CLASS_X == POW2) &
        (ey == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end

    checker("SELTZO-TwoSum-ALL1-POW2-SG-X",
        (CLASS_X == ALL1) & (CLASS_Y == POW2) &
        (ex > ey) & (ex < ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end
    checker("SELTZO-TwoSum-ALL1-POW2-SG-Y",
        (CLASS_Y == ALL1) & (CLASS_X == POW2) &
        (ey > ex) & (ey < ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end

    checker("SELTZO-TwoSum-ALL1-POW2-SB1-X",
        (CLASS_X == ALL1) & (CLASS_Y == POW2) &
        (ex == ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, ex + 1),
            SELTZORange(sy, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end
    checker("SELTZO-TwoSum-ALL1-POW2-SB1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == POW2) &
        (ey == ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, ey + 1),
            SELTZORange(sx, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end

    checker("SELTZO-TwoSum-ALL1-POW2-SB2-X",
        (CLASS_X == ALL1) & (CLASS_Y == POW2) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx + 1, gx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-POW2-SB2-Y",
        (CLASS_Y == ALL1) & (CLASS_X == POW2) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy + 1, gy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-POW2-SB3-X",
        (CLASS_X == ALL1) & (CLASS_Y == POW2) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx + 1, gx + 1),
            SELTZORange(~sy, 0, 0, fx, fx - p, fx))
    end
    checker("SELTZO-TwoSum-ALL1-POW2-SB3-Y",
        (CLASS_Y == ALL1) & (CLASS_X == POW2) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy + 1, gy + 1),
            SELTZORange(~sx, 0, 0, fy, fy - p, fy))
    end

end
