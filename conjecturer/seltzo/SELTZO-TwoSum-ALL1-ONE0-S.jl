function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
    ::Val{ONE0},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ALL1-ONE0-SE0-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == ey) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, fy, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-SE0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == ex) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, fx, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-SE1-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == ey) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-SE1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == ex) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-S1-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex > ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-S1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey > ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-S1A-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-S1A-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(sx, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-S1B-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-S1B-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fx),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-S1AB-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-S1AB-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-S2A-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-S2A-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-S3A0-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-S3A0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-S3A1-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == fy + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ex - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-S3A1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == fx + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ey - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-S4-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex > fy + (p + 1)) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-S4-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey > fx + (p + 1)) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-S4A-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == fy + (p + 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(sy, 0, 0, ex - p, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-S4A-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == fx + (p + 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(sx, 0, 0, ey - p, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-S4B-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == ey + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ex + 1),
            SELTZORange(sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-S4B-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == ex + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ey + 1),
            SELTZORange(sx, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-S4AB-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == ey + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ex + 1),
            SELTZORange(sy, 0, 0, ex - p, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-S4AB-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == ex + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ey + 1),
            SELTZORange(sx, 0, 0, ey - p, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-SB0-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey + 1, ex + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-SB0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex + 1, ey + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-ONE0-SB1-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey + 1, ex + 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, fy - 1))
    end
    checker("SELTZO-TwoSum-ALL1-ONE0-SB1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex + 1, ey + 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, fx - 1))
    end

end
