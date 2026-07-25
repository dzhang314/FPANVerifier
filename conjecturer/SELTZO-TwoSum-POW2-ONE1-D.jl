function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{POW2},
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

    checker("SELTZO-TwoSum-POW2-ONE1-DA1-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE1) &
        (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-ONE1-DA1-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE1) &
        (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-ONE1-D1-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE1) &
        (ex > fy + p) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-POW2-ONE1-D1-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE1) &
        (ey > fx + p) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-POW2-ONE1-D1A0-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE1) &
        (ex == fy + p) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-ONE1-D1A0-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE1) &
        (ey == fx + p) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-ONE1-D1A1-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE1) &
        (ex == ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex - 1, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-ONE1-D1A1-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE1) &
        (ey == ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey - 1, ex - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-ONE1-DB1-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE1) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, ex - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-POW2-ONE1-DB1-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE1) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, ey - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-POW2-ONE1-DB2-X",
        (CLASS_X == POW2) & (CLASS_Y == ONE1) &
        (ex == ey + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ex - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-POW2-ONE1-DB2-Y",
        (CLASS_Y == POW2) & (CLASS_X == ONE1) &
        (ey == ex + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ey - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
