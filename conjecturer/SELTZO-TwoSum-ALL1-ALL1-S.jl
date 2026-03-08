function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
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

    checker("SELTZO-TwoSum-ALL1-ALL1-SE",
        (ex == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, fx + 1, gx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-ALL1-SA-X",
        (ex == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ALL1-ALL1-SA-Y",
        (ey == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-ALL1-ALL1-SG-X",
        (ex > ey + 1) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(sy, 1, 0, fx, fy, fy + 1))
    end
    checker("SELTZO-TwoSum-ALL1-ALL1-SG-Y",
        (ey > ex + 1) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(sx, 1, 0, fy, fx, fx + 1))
    end

    checker("SELTZO-TwoSum-ALL1-ALL1-SB1-X",
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx + 1, gx + 1),
            SELTZORange(sy, 1, 0, fx, fy, fy + 1))
    end
    checker("SELTZO-TwoSum-ALL1-ALL1-SB1-Y",
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy + 1, gy + 1),
            SELTZORange(sx, 1, 0, fy, fx, fx + 1))
    end

    checker("SELTZO-TwoSum-ALL1-ALL1-SB2-X",
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx + 1, gx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-ALL1-ALL1-SB2-Y",
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy + 1, gy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
