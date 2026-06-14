function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R1R0},
    ::Val{R1R0},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R1R0-R1R0-SE0-X",
        (ex == ey) & (fx > fy) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-SE0-Y",
        (ey == ex) & (fy > fx) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey + 1, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-SE1",
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex + 1, fx + 1, fx + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-SE2-X",
        (ex == ey) & (fx > fy) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex + 1, fx + 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-SE2-Y",
        (ey == ex) & (fy > fx) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey + 1, fy + 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S1-X",
        (ex < fy + (p - 1)) & (fx + 1 < ey) & (ex > ey) & (fx > fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S1-Y",
        (ey < fx + (p - 1)) & (fy + 1 < ex) & (ey > ex) & (fy > fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S1A-X",
        (ex == fy + (p - 1)) & (fx + 1 < ey) & (ex > ey) & (fx > fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S1A-Y",
        (ey == fx + (p - 1)) & (fy + 1 < ex) & (ey > ex) & (fy > fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S1B-X",
        (ex < fy + (p - 1)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S1B-Y",
        (ey < fx + (p - 1)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S1AB-X",
        (ex == fy + (p - 1)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S1AB-Y",
        (ey == fx + (p - 1)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S1AC-X",
        (ex == fy + p) & (fx == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ex - p, ex), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S1AC-Y",
        (ey == fx + p) & (fy == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ey - p, ey), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S2-X",
        (ex > ey) & (fx < fy) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S2-Y",
        (ey > ex) & (fy < fx) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S2A-X",
        (ex > ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, ey, fx + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S2A-Y",
        (ey > ex) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, ex, fy + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S2B-X",
        (ex > ey) & (fx < fy) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S2B-Y",
        (ey > ex) & (fy < fx) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S3-X",
        (ex > fy + (p - 1)) & (fx < ey) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S3-Y",
        (ey > fx + (p - 1)) & (fy < ex) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S3B-X",
        (ex > fy + p) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S3B-Y",
        (ey > fx + p) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S3C-X",
        (ex > fy + p) & (fx < ey) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S3C-Y",
        (ey > fx + p) & (fy < ex) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S3AC-X",
        (ex == fy + p) & (fx + 1 < ey) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fx + 2),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S3AC-Y",
        (ey == fx + p) & (fy + 1 < ex) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fy + 2),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S3ABC-X",
        (ex == fy + p) & (fx + 1 == ey) & (ex == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S3ABC-Y",
        (ey == fx + p) & (fy + 1 == ex) & (ey == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S4-X",
        (ex > fy + p) & (fx > ey + 1) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S4-Y",
        (ey > fx + p) & (fy > ex + 1) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S4A-X",
        (ex > fy + p) & (fx == ey + 1) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S4A-Y",
        (ey > fx + p) & (fy == ex + 1) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S4B-X",
        (fx > ey + 1) & (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S4B-Y",
        (fy > ex + 1) & (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-S4AB-X",
        (fx == ey + 1) & (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-S4AB-Y",
        (fy == ex + 1) & (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
