function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
    ::Val{ONE0},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ONE0-ONE0-DE0",
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, pos_zero, pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-DE1-X",
        (ex == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 0, 0, fy, fy - p, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-DE1-Y",
        (ey == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 0, 0, fx, fx - p, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-DE2-X",
        (ex == ey) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sx, 1, 0, fx - 1, fy - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-DE2-Y",
        (ey == ex) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(~sy, 1, 0, fy - 1, fx - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-DA0-X",
        (ex == ey + 1) & (fx > fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-DA0-Y",
        (ey == ex + 1) & (fy > fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-DA1-X",
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, ey - p, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-DA1-Y",
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, ex - p, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-DA2-X",
        (ex == ey + 1) & (fx < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy - 1, fx),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-DA2-Y",
        (ey == ex + 1) & (fy < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx - 1, fy),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D1-X",
        (ex > fy + p) & (fx > ey + 1) & (ex < ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D1-Y",
        (ey > fx + p) & (fy > ex + 1) & (ey < ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D1A0-X",
        (ex == ey + p) & (fx > ey + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D1A0-Y",
        (ey == ex + p) & (fy > ex + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D1A1-X",
        (ex == ey + p) & (fx == ey + 2) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D1A1-Y",
        (ey == ex + p) & (fy == ex + 2) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D1B-X",
        (ex > fy + p) & (fx == ey + 1) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 2, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D1B-Y",
        (ey > fx + p) & (fy == ex + 1) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 2, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D1C-X",
        (fx > ey + 1) & (ex < ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D1C-Y",
        (fy > ex + 1) & (ey < ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D1D-X",
        (ex == fy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D1D-Y",
        (ey == fx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D1AC0-X",
        (ex == ey + p) & (fx > ey + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D1AC0-Y",
        (ey == ex + p) & (fy > ex + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D1AC1-X",
        (ex == ey + p) & (fx == ey + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D1AC1-Y",
        (ey == ex + p) & (fy == ex + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D1BC0-X",
        (ex > ey + 3) & (fx == ey + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 2, fx + 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D1BC0-Y",
        (ey > ex + 3) & (fy == ex + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 2, fy + 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D1BC1-X",
        (ex == ey + 3) & (fx == ey + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D1BC1-Y",
        (ey == ex + 3) & (fy == ex + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D1BD-X",
        (ex == fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D1BD-Y",
        (ey == fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D2-X",
        (ex == fy + (p - 1)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D2-Y",
        (ey == fx + (p - 1)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D2A-X",
        (ex == fy + (p - 1)) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D2A-Y",
        (ey == fx + (p - 1)) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D3-X",
        (ex > ey + 2) & (fx < ey) & (ex < fy + (p - 1)) & (fx > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D3-Y",
        (ey > ex + 2) & (fy < ex) & (ey < fx + (p - 1)) & (fy > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D3A-X",
        (ex == ey + 2) & (fx > fy) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D3A-Y",
        (ey == ex + 2) & (fy > fx) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D3B-X",
        (ex > ey + 2) & (fx < ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D3B-Y",
        (ey > ex + 2) & (fy < ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D3C-X",
        (ex > ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D3C-Y",
        (ey > ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D3AB-X",
        (ex == ey + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D3AB-Y",
        (ey == ex + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D3AC-X",
        (ex == ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ex - 1),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D3AC-Y",
        (ey == ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ey - 1),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D4-X",
        (fx < ey + 1) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D4-Y",
        (fy < ex + 1) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D4A-X",
        (ex > ey + 2) & (fx < ey + 1) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx),
            SELTZORange(~sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D4A-Y",
        (ey > ex + 2) & (fy < ex + 1) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy),
            SELTZORange(~sx, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D4B-X",
        (ex > ey + 2) & (fx < ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D4B-Y",
        (ey > ex + 2) & (fy < ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-ONE0-D4AB-X",
        (ex == ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx),
            SELTZORange(sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-ONE0-ONE0-D4AB-Y",
        (ey == ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy),
            SELTZORange(sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

end
