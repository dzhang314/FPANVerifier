function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
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

    checker("SELTZO-TwoSum-ONE1-POW2-SE0-X",
        (CLASS_X == ONE1) & (CLASS_Y == POW2) &
        (ex == ey) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-POW2-SE0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == POW2) &
        (ey == ex) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-POW2-SE1-X",
        (CLASS_X == ONE1) & (CLASS_Y == POW2) &
        (ex == ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-POW2-SE1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == POW2) &
        (ey == ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-POW2-SA1-X",
        (CLASS_X == ONE1) & (CLASS_Y == POW2) &
        (ex == ey + 1) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-POW2-SA1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == POW2) &
        (ey == ex + 1) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-POW2-S1A0-X",
        (CLASS_X == ONE1) & (CLASS_Y == POW2) &
        (ex > ey + 2) & (fx == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-POW2-S1A0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == POW2) &
        (ey > ex + 2) & (fy == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-POW2-S1A1-X",
        (CLASS_X == ONE1) & (CLASS_Y == POW2) &
        (ex == ey + 2) & (fx == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ex - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-POW2-S1A1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == POW2) &
        (ey == ex + 2) & (fy == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ey - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-POW2-SB1-X",
        (CLASS_X == ONE1) & (CLASS_Y == POW2) &
        (ex == ey + (p - 1)) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-POW2-SB1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == POW2) &
        (ey == ex + (p - 1)) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fy + 1), pos_zero)
    end

end
