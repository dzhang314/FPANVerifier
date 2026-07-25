function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
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

    checker("SELTZO-TwoSum-ONE1-ALL1-SE0-X",
        (CLASS_X == ONE1) & (CLASS_Y == ALL1) &
        (ex == ey) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ALL1-SE0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ALL1) &
        (ey == ex) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ALL1-SE1-X",
        (CLASS_X == ONE1) & (CLASS_Y == ALL1) &
        (ex == ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, ex),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ALL1-SE1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ALL1) &
        (ey == ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, ey),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ALL1-SA0-X",
        (CLASS_X == ONE1) & (CLASS_Y == ALL1) &
        (ex == ey + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ALL1-SA0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ALL1) &
        (ey == ex + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ALL1-SA1-X",
        (CLASS_X == ONE1) & (CLASS_Y == ALL1) &
        (ex == ey + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ALL1-SA1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ALL1) &
        (ey == ex + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ALL1-S1A0-X",
        (CLASS_X == ONE1) & (CLASS_Y == ALL1) &
        (fx == ey + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ALL1-S1A0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ALL1) &
        (fy == ex + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ALL1-S1A1-X",
        (CLASS_X == ONE1) & (CLASS_Y == ALL1) &
        (fx == ey + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ALL1-S1A1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ALL1) &
        (fy == ex + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ALL1-S1B1-X",
        (CLASS_X == ONE1) & (CLASS_Y == ALL1) &
        (ex == ey + p) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ALL1-S1B1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ALL1) &
        (ey == ex + p) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ALL1-S2-X",
        (CLASS_X == ONE1) & (CLASS_Y == ALL1) &
        (fx < ey + 1) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ALL1-S2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ALL1) &
        (fy < ex + 1) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ALL1-S2B0-X",
        (CLASS_X == ONE1) & (CLASS_Y == ALL1) &
        (fx < ey) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ALL1-S2B0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ALL1) &
        (fy < ex) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE1-ALL1-S2B1-X",
        (CLASS_X == ONE1) & (CLASS_Y == ALL1) &
        (fx == ey) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE1-ALL1-S2B1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == ALL1) &
        (fy == ex) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

end
