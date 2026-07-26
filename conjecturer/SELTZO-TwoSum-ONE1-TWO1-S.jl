function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
    ::Val{TWO1},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ONE1-TWO1-SE0-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx > fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SE0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy > fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SE1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx > fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SE1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy > fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SE2-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SE2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SE3-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SE3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SE4-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SE4-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SE5-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fy + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SE5-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fx + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SE6-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 < fy) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fy, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SE6-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 < fx) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fx, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SE7-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 < fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fy, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SE7-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 < fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fx, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SE8-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 2 == fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SE8-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 2 == fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SA10-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 < ey) & (fx + 1 > fy) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SA10-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 < ex) & (fy + 1 > fx) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SA11-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 == ey) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SA11-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 == ex) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SA12-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 == fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SA12-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 == fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SA13-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 == fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SA13-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 == fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SA14-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx == fy) & (ey == fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SA14-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy == fx) & (ex == fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SA15-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 == ey) & (ey == fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SA15-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 == ex) & (ex == fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SA16-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx == fy) & (ey == fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SA16-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy == fx) & (ex == fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SA17-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx == fy + 1) & (ey == fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SA17-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy == fx + 1) & (ex == fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SA18-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx > fy + 1) & (fx + 1 < ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SA18-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy > fx + 1) & (fy + 1 < ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SA19-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (fx + 1 == ey) & (ey == fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SA19-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (fy + 1 == ex) & (ex == fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SA2-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + 2) & (fx == ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SA2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + 2) & (fy == ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex < ey + (p - 1)) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy > ex) & (ey < ex + (p - 1)) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S1A-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S1A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy > ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S1B-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S1B-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy > ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S1C0-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex == fy + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S1C0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy > ex) & (ey == fx + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S1C1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S1C1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S1C2-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S1C2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S2-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy < ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S2A-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S2A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S2B0-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx < ey) & (fx > fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S2B0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy < ex) & (fy > fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S2B10-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex == fy + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S2B10-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey == fx + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S2B11-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex > ey + 2) & (ex == fy + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S2B11-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey > ex + 2) & (ey == fx + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S2AB0-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S2AB0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S2AB1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == ey + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S2AB1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == ex + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S2C0-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx < ey) & (fx > fy + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S2C0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy < ex) & (fy > fx + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S2C1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx + 1 < ey) & (fx == fy + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S2C1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy + 1 < ex) & (fy == fx + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S2C2-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx + 1 == ey) & (fx == fy + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S2C2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy + 1 == ex) & (fy == fx + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S2AC-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S2AC-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S3-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx < ey) & (fx + 1 > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S3-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy < ex) & (fy + 1 > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S3A-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S3A-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S3B0-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx < ey) & (fx > fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S3B0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy < ex) & (fy > fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S3B10-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx == fy + 1) & (ex == fy + (p - 2)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S3B10-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy == fx + 1) & (ey == fx + (p - 2)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S3B11-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex > ey + 1) & (ex == fy + (p - 2)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S3B11-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey > ex + 1) & (ey == fx + (p - 2)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S3B2-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex > ey + 1) & (fx == fy) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S3B2-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey > ex + 1) & (fy == fx) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S3BC0-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex > ey + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S3BC0-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey > ex + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-S3BC1-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == ey + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-S3BC1-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == ex + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SB10-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 1)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SB10-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + (p - 1)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SB11-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 1)) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SB11-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + (p - 1)) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SB20-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (fx > ey + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SB20-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + p) & (fy > ex + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SB21-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (fx > ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SB21-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + p) & (fy > ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SB22-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (fx == ey + 2) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SB22-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + p) & (fy == ex + 2) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE1-TWO1-SB23-X",
        (CLASS_X == ONE1) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (fx == ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE1-TWO1-SB23-Y",
        (CLASS_Y == ONE1) & (CLASS_X == TWO1) &
        (ey == ex + p) & (fy == ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

end
