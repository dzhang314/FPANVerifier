function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
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

    checker("SELTZO-TwoSum-ONE1-POW2-DE-X",
        (CLASS_X == ONE1) & (CLASS_Y == POW2) &
        (ex == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fx - p, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-POW2-DE-Y",
        (CLASS_Y == ONE1) & (CLASS_X == POW2) &
        (ey == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fy - p, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-POW2-DA0-X",
        (CLASS_X == ONE1) & (CLASS_Y == POW2) &
        (ex == ey + 1) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-POW2-DA0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == POW2) &
        (ey == ex + 1) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-POW2-D1-X",
        (CLASS_X == ONE1) & (CLASS_Y == POW2) &
        (ex > ey + 1) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-POW2-D1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == POW2) &
        (ey > ex + 1) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-POW2-D1A-X",
        (CLASS_X == ONE1) & (CLASS_Y == POW2) &
        (fx + 1 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-POW2-D1A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == POW2) &
        (fy + 1 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-POW2-D2-X",
        (CLASS_X == ONE1) & (CLASS_Y == POW2) &
        (ex < ey + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-POW2-D2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == POW2) &
        (ey < ex + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-POW2-D2A-X",
        (CLASS_X == ONE1) & (CLASS_Y == POW2) &
        (fx == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-POW2-D2A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == POW2) &
        (fy == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-POW2-DB-X",
        (CLASS_X == ONE1) & (CLASS_Y == POW2) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-POW2-DB-Y",
        (CLASS_Y == ONE1) & (CLASS_X == POW2) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy - 1, fy), pos_zero)
    end

end
