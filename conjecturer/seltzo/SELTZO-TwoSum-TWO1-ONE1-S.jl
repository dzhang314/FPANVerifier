function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO1},
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

    checker("SELTZO-TwoSum-TWO1-ONE1-SA0-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx > fy + 1) & (ex > fx + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-SA0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy > fx + 1) & (ey > fy + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-SA1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx > fy + 2) & (ex == fx + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-SA1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy > fx + 2) & (ey == fy + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-SA2-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy + 2) & (ex == fx + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 3, fx - 2), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-SA2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx + 2) & (ey == fy + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 3, fy - 2), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-SA31-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy) & (fx + 2 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-SA31-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx) & (fy + 2 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-SA32-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy + 1) & (fx + 2 < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-SA32-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx + 1) & (fy + 2 < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-SA41-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy) & (fx + 2 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-SA41-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx) & (fy + 2 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-SA42-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy + 1) & (fx + 2 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-SA42-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx + 1) & (fy + 2 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-SA5-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy + 1) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-SA5-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx + 1) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-SA6-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx > fy + 2) & (ex > fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-SA6-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy > fx + 2) & (ey > fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-SA7-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx == fy + 2) & (ex > fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-SA7-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy == fx + 2) & (ey > fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-SA8-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + 1) & (fx > fy + 2) & (ex == fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 2, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-SA8-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + 1) & (fy > fx + 2) & (ey == fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 2, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ex > fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ey > fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S1A01-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex > fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S1A01-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == ex) & (ey > fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S1A02-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex > fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S1A02-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey > fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S1A11-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex > fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S1A11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == ex) & (ey > fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S1A12-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex > fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S1A12-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey > fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S1B-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S1B-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S1AB0-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + (p - 1)) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S1AB0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + (p - 1)) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S1AB1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex == fy + (p - 1)) & (ex == fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S1AB1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey == fx + (p - 1)) & (ey == fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S1AB2-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + (p - 1)) & (ex > fx + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx + 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S1AB2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + (p - 1)) & (ey > fy + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy + 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S1C0-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex < fy + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx + 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S1C0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey < fx + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S1C1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex < fy + (p - 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S1C1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey < fx + (p - 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S2-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx < ey) & (ex > fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy < ex) & (ey > fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S3-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx < ey) & (fx > fy + 1) & (ex > ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S3-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy < ex) & (fy > fx + 1) & (ey > ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S3A0-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx < ey) & (fx > fy + 2) & (ex > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S3A0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy < ex) & (fy > fx + 2) & (ey > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S3A1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == fy + 2) & (fx + 1 < ey) & (ex > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S3A1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == fx + 2) & (fy + 1 < ex) & (ey > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S3A2-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == fy + 2) & (fx + 1 == ey) & (ex > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S3A2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == fx + 2) & (fy + 1 == ex) & (ey > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S3B01-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == fy) & (fx + 1 < ey) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S3B01-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == fx) & (fy + 1 < ex) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S3B02-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == fy + 1) & (fx + 1 < ey) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S3B02-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == fx + 1) & (fy + 1 < ex) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S3B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == fy + 1) & (fx + 1 == ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S3B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == fx + 1) & (fy + 1 == ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-S3B2-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (fx == fy + 1) & (fx + 1 == ey) & (ex == ey + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-S3B2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (fy == fx + 1) & (fy + 1 == ex) & (ey == ex + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-SB10-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1)) & (fx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-SB10-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1)) & (fy > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-SB11-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1)) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-SB11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1)) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-SB20-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + p) & (fx > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-SB20-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + p) & (fy > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-TWO1-ONE1-SB21-X",
        (CLASS_X == TWO1) & (CLASS_Y == ONE1) &
        (ex == ey + p) & (fx == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-TWO1-ONE1-SB21-Y",
        (CLASS_Y == TWO1) & (CLASS_X == ONE1) &
        (ey == ex + p) & (fy == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
