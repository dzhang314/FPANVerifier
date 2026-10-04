function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO0},
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

    checker("SELTZO-TwoSum-TWO0-ONE1-S1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex < ey + (p - 1)) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey < ex + (p - 1)) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S1A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S1A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S1A2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S1A2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S1B-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S1B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S1AB1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S1AB1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S1AB2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S1AB2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex > ey) & (fx < fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey > ex) & (fy < fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S2A0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex > ey) & (fx + 1 < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S2A0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey > ex) & (fy + 1 < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S2A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex > ey) & (fx + 1 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S2A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey > ex) & (fy + 1 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S2B01-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex > ey) & (fx == fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S2B01-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey > ex) & (fy == fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S2B02-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex > ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S2B02-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey > ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S2AB-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex > ey) & (fx == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S2AB-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey > ex) & (fy == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S3-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex > ey) & (fx + 1 < ey) & (fx > fy + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey > ex) & (fy + 1 < ex) & (fy > fx + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S3A-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (fx > fy + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S3A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (fy > fx + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S3B-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex > ey) & (fx + 1 < ey) & (ex == fy + (p - 2)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S3B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey > ex) & (fy + 1 < ex) & (ey == fx + (p - 2)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S3AB-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex == fy + (p - 2)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S3AB-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey == fx + (p - 2)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S3C-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 < ey) & (ex == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S3C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 < ex) & (ey == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S3AC-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex == fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S3AC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey == fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S3CD-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 < ey) & (ex == fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S3CD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 < ex) & (ey == fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S3ACD-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex == fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S3ACD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey == fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S4-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 < ey) & (ex > fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(~sy, 1, 0, ex - p, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 < ex) & (ey > fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(~sx, 1, 0, ey - p, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S4A-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 < ey) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S4A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 < ex) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S4B-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex > fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(~sy, 1, 0, ex - p, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S4B-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey > fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(~sx, 1, 0, ey - p, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S4C-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 < ey) & (ex > fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 1, 0, ex - p, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S4C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 < ex) & (ey > fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 1, 0, ey - p, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S4AB-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex == fy + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S4AB-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey == fx + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S4AC-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 < ey) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S4AC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 < ex) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S4BC-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex > fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(~sy, 1, 0, ex - p, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S4BC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey > fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(~sx, 1, 0, ey - p, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S4ABC-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx + 1 == ey) & (ex == fy + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(~sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S4ABC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy + 1 == ex) & (ey == fx + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(~sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S5-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S5-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S5A-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S5A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S5B1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S5B1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S5B2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S5B2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S5AB1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 2, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S5AB1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 2, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-S5AB2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-S5AB2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-SB1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-SB1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-TWO0-ONE1-SB2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE1) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-TWO0-ONE1-SB2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE1) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
