function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM01},
    ::Val{MM01},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-MM01-MM01-SE0",
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, fx + 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-SE1-X",
        (ex == ey) & (fx == fy + 1) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, fx + 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-SE1-Y",
        (ey == ex) & (fy == fx + 1) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, fy + 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-SE2-X",
        (ex == ey) & (fx == fy + 1) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-SE2-Y",
        (ey == ex) & (fy == fx + 1) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-SE3-X",
        (ex == ey) & (fx > fy + 1) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-SE3-Y",
        (ey == ex) & (fy > fx + 1) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-SE4-X",
        (ex == ey) & (fx > fy + 1) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-SE4-Y",
        (ey == ex) & (fy > fx + 1) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-S1-X",
        (ex > ey) & (fx > fy) & (fx < ey) & (fy + 2 < ey) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-S1-Y",
        (ey > ex) & (fy > fx) & (fy < ex) & (fx + 2 < ex) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-S1A-X",
        (ex > ey) & (fx < ey) & (fx > fy + 1) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-S1A-Y",
        (ey > ex) & (fy < ex) & (fy > fx + 1) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-S1B-X",
        (ex > ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-S1B-Y",
        (ey > ex) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-S1AC-X",
        (ex > ey) & (fx == fy + 1) & (fx + 1 < ey) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-S1AC-Y",
        (ey > ex) & (fy == fx + 1) & (fy + 1 < ex) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-S1CD-X",
        (fx == fy + 1) & (fx + 1 == ey) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-S1CD-Y",
        (fy == fx + 1) & (fy + 1 == ex) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-S1ACD-X",
        (fx == fy + 1) & (fx + 1 == ey) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-S1ACD-Y",
        (fy == fx + 1) & (fy + 1 == ex) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-S1D0-X",
        (fx == ey) & (ex < fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-S1D0-Y",
        (fy == ex) & (ey < fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-S1D1-X",
        (fx == ey) & (ex < fy + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey - 3, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-S1D1-Y",
        (fy == ex) & (ey < fx + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex - 3, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-S1AD0-X",
        (fx == ey) & (ex == fy + (p - 3)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-S1AD0-Y",
        (fy == ex) & (ey == fx + (p - 3)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-S1AD1-X",
        (fx == ey) & (ex == fy + (p - 3)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 3, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-S1AD1-Y",
        (fy == ex) & (ey == fx + (p - 3)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 3, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-S2-X",
        (ex > ey) & (fx < fy) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-S2-Y",
        (ey > ex) & (fy < fx) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-S2A0-X",
        (ex > ey) & (fx + 1 < fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-S2A0-Y",
        (ey > ex) & (fy + 1 < fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-S2A1-X",
        (ex > ey) & (fx + 1 == fy) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-S2A1-Y",
        (ey > ex) & (fy + 1 == fx) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-S3E-X",
        (fx == fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S3E-Y",
        (fy == fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S3A-X",
        (fx == fy + 2) & (fx < ey) & (ex > fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S3A-Y",
        (fy == fx + 2) & (fy < ex) & (ey > fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S3-X",
        (fx > fy + 2) & (fx < ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S3-Y",
        (fy > fx + 2) & (fy < ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S3AB-X",
        (fx == ey) & (fx == fy + 2) & (ex > fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S3AB-Y",
        (fy == ex) & (fy == fx + 2) & (ey > fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S3B-X",
        (fx == ey) & (fx > fy + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 2, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S3B-Y",
        (fy == ex) & (fy > fx + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 2, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S3C-X",
        (fx > fy + 2) & (fx < ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S3C-Y",
        (fy > fx + 2) & (fy < ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S3BC-X",
        (fx == ey) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 2, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S3BC-Y",
        (fy == ex) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 2, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S3D0-X",
        (fx < ey) & (ex > fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S3D0-Y",
        (fy < ex) & (ey > fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S3D1-X",
        (fx < ey) & (ex > fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S3D1-Y",
        (fy < ex) & (ey > fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S3BD0-X",
        (fx == ey) & (ex > fy + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S3BD0-Y",
        (fy == ex) & (ey > fx + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S3BD1-X",
        (fx == ey) & (ex > fy + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S3BD1-Y",
        (fy == ex) & (ey > fx + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S4A-X",
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-S4A-Y",
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-S4B-X",
        (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-S4B-Y",
        (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-S4AB-X",
        (fx == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-MM01-MM01-S4AB-Y",
        (fy == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-MM01-MM01-S4C0-X",
        (ex == fy + (p - 1)) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S4C0-Y",
        (ey == fx + (p - 1)) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S4C1-X",
        (ex == fy + (p - 1)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S4C1-Y",
        (ey == fx + (p - 1)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S4D0-X",
        (ex == fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, ey),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S4D0-Y",
        (ey == fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, ex),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S4D1-X",
        (ex == fy + p) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S4D1-Y",
        (ey == fx + p) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S4D2-X",
        (ex == fy + p) & (fx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S4D2-Y",
        (ey == fx + p) & (fy > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S4E0-X",
        (ex > fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, ey),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S4E0-Y",
        (ey > fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, ex),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S4E1-X",
        (ex > fy + p) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S4E1-Y",
        (ey > fx + p) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-S4E2-X",
        (ex > fy + p) & (fx > ey + 2) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-S4E2-Y",
        (ey > fx + p) & (fy > ex + 2) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-SB0-X",
        (ex == ey + p) & (fx > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-SB0-Y",
        (ey == ex + p) & (fy > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-MM01-MM01-SB1-X",
        (ex == ey + p) & (fx == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-MM01-MM01-SB1-Y",
        (ey == ex + p) & (fy == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
