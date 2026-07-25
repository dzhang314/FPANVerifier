function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
    ::Val{ONE1},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ALL1-ONE1-DE0-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex == ey) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-DE0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey == ex) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-ONE1-DE1-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fy - 1, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-DE1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fx - 1, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-ONE1-D1A-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-D1A-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-ONE1-D1AB-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-D1AB-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ALL1-ONE1-D2-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex > fy + p) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-D2-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey > fx + p) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ALL1-ONE1-D2A0-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (ex < ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-D2A0-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey == fx + p) & (ey < ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ALL1-ONE1-D2A1-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (ex == ey + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-D2A1-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey == fx + p) & (ey == ex + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ALL1-ONE1-D2B-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-D2B-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ALL1-ONE1-DB-X",
        (CLASS_X == ALL1) & (CLASS_Y == ONE1) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-ALL1-ONE1-DB-Y",
        (CLASS_Y == ALL1) & (CLASS_X == ONE1) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
