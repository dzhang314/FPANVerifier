function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{POW2},
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

    checker("SELTZO-TwoSum-POW2-ONE1-SG-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE1) &
        (ex > fy + (p - 1)) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-POW2-ONE1-SG-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE1) &
        (ey > fx + (p - 1)) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-POW2-ONE1-SGA0-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE1) &
        (ex == fy + (p - 1)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-ONE1-SGA0-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE1) &
        (ey == fx + (p - 1)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-ONE1-SGA1-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE1) &
        (ex == fy + (p - 1)) & (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-ONE1-SGA1-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE1) &
        (ey == fx + (p - 1)) & (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-ONE1-SB1-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-POW2-ONE1-SB1-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-POW2-ONE1-SB2-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE1) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-POW2-ONE1-SB2-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE1) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
