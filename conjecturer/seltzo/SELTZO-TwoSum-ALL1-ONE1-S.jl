function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
    ::Val{ONE1},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ALL1-ONE1-S1-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex > ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-S1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey > ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-ONE1-S1A-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex > ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-S1A-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey > ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-ONE1-S2A-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-S2A-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-ONE1-S3-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex > fy + p) & (ex < ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 1, 0, ex - p, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-S3-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey > fx + p) & (ey < ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 1, 0, ey - p, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-ALL1-ONE1-S3A-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (ex < ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-S3A-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey == fx + p) & (ey < ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ALL1-ONE1-S3B-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex > fy + p) & (ex == ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(~sy, 1, 0, ex - p, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-S3B-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey > fx + p) & (ey == ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(~sx, 1, 0, ey - p, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-ALL1-ONE1-S3AB-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (ex == ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-S3AB-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey == fx + p) & (ey == ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ALL1-ONE1-SB1-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-SB1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ALL1-ONE1-SB2-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey + 1, ex + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-SB2-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex + 1, ey + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
