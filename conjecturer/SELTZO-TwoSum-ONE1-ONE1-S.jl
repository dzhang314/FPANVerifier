function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE1},
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

    checker("SELTZO-TwoSum-ONE1-ONE1-SE0",
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-SE1-X",
        (ex == ey) & (fx > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-SE1-Y",
        (ey == ex) & (fy > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey + 1, fy, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-SE2-X",
        (ex == ey) & (fx > fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-SE2-Y",
        (ey == ex) & (fy > fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-SE3-X",
        (ex == ey) & (fx == fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fx, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-SE3-Y",
        (ey == ex) & (fy == fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fy, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-SA1-X",
        (ex == ey + 1) & (fx + 1 < ey) & (fx > fy) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-SA1-Y",
        (ey == ex + 1) & (fy + 1 < ex) & (fy > fx) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-SA1A0-X",
        (ex == ey + 1) & (fx + 1 == ey) & (fx > fy + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-SA1A0-Y",
        (ey == ex + 1) & (fy + 1 == ex) & (fy > fx + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-SA1A1-X",
        (ex == ey + 1) & (fx + 1 == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-SA1A1-Y",
        (ey == ex + 1) & (fy + 1 == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-SA1B0-X",
        (ex == ey + 1) & (fx + 1 < ey) & (ex == fy + (p - 1)) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-SA1B0-Y",
        (ey == ex + 1) & (fy + 1 < ex) & (ey == fx + (p - 1)) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-SA1B1-X",
        (ex == ey + 1) & (ex == fy + (p - 1)) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-SA1B1-Y",
        (ey == ex + 1) & (ey == fx + (p - 1)) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-SA1AB-X",
        (ex == ey + 1) & (fx + 1 == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-SA1AB-Y",
        (ey == ex + 1) & (fy + 1 == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-SA2-X",
        (ex == ey + 1) & (fx + 2 < ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-SA2-Y",
        (ey == ex + 1) & (fy + 2 < ex) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-SA2A-X",
        (ex == ey + 1) & (fx + 2 == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-SA2A-Y",
        (ey == ex + 1) & (fy + 2 == ex) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-S1-X",
        (fx > ey) & (ex < ey + (p - 1)) & (ex > fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-S1-Y",
        (fy > ex) & (ey < ex + (p - 1)) & (ey > fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-S1A0-X",
        (ex == ey + (p - 1)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-S1A0-Y",
        (ey == ex + (p - 1)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-S1A1-X",
        (ex == ey + (p - 1)) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-S1A1-Y",
        (ey == ex + (p - 1)) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-S1B-X",
        (fx > ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-S1B-Y",
        (fy > ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-S2-X",
        (fx < ey) & (ex > fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-S2-Y",
        (fy < ex) & (ey > fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-S2A0-X",
        (fx == ey) & (ex > ey + 2) & (ex > fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-S2A0-Y",
        (fy == ex) & (ey > ex + 2) & (ey > fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-S2A1-X",
        (ex == ey + 2) & (fx == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ex - 1),
            SELTZORange(sy, 0, 0, fy, fy - p, fy))
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-S2A1-Y",
        (ey == ex + 2) & (fy == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ey - 1),
            SELTZORange(sx, 0, 0, fx, fx - p, fx))
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-S2B-X",
        (ex > ey + 1) & (fx < ey) & (fx > fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-S2B-Y",
        (ey > ex + 1) & (fy < ex) & (fy > fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-S2BC0-X",
        (ex > ey + 1) & (fx == fy + 1) & (ex == fy + (p - 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-S2BC0-Y",
        (ey > ex + 1) & (fy == fx + 1) & (ey == fx + (p - 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-S2BC1-X",
        (fx + 1 == ey) & (fx == fy + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, fx + 2), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-S2BC1-Y",
        (fy + 1 == ex) & (fy == fx + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, fy + 2), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-S2AB0-X",
        (fx == ey) & (ex > ey + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-S2AB0-Y",
        (fy == ex) & (ey > ex + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-S2AB1-X",
        (fx == ey) & (ex == ey + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-S2AB1-Y",
        (fy == ex) & (ey == ex + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-S3-X",
        (ex > ey + 1) & (ex < fy + (p - 1)) & (fx > fy) & (fx < ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-S3-Y",
        (ey > ex + 1) & (ey < fx + (p - 1)) & (fy > fx) & (fy < ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-S3A-X",
        (ex > ey + 1) & (ex < fy + (p - 1)) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, fx + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-S3A-Y",
        (ey > ex + 1) & (ey < fx + (p - 1)) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, fy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-S3B-X",
        (ex == ey + 2) & (fx == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-S3B-Y",
        (ey == ex + 2) & (fy == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-SB0-X",
        (ex == ey + p) & (fx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-SB0-Y",
        (ey == ex + p) & (fy > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

    checker("SELTZO-TwoSum-ONE1-ONE1-SB1-X",
        (ex == ey + p) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, fy))
    end
    checker("SELTZO-TwoSum-ONE1-ONE1-SB1-Y",
        (ey == ex + p) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx - 1, fx))
    end

end
