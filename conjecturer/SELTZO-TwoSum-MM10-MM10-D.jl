function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{MM10},
    ::Val{MM10},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-MM10-MM10-DE0-X",
        (ex == ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fx - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM10-DE0-Y",
        (ey == ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fy - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM10-DE1-X",
        (ex == ey) & (fx == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, fx, fy - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM10-DE1-Y",
        (ey == ex) & (fy == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, fy, fx - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM10-DE2-X",
        (ex == ey) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, fy, fy - 2, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM10-DE2-Y",
        (ey == ex) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, fx, fx - 2, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM10-DE3",
        (ex == ey) & (fx == fy)
    ) do lemma
        add_case!(lemma, pos_zero, pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM10-DA10-X",
        (ex == ey + 1) & (fx + 1 < fy) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM10-DA10-Y",
        (ey == ex + 1) & (fy + 1 < fx) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM10-DA11-X",
        (ex == ey + 1) & (fx + 1 < fy) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fy - 1, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM10-DA11-Y",
        (ey == ex + 1) & (fy + 1 < fx) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fx - 1, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM10-DA12-X",
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fx, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM10-DA12-Y",
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fy, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM10-DA13-X",
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, ey - p, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM10-DA13-Y",
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, ex - p, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM10-DA14-X",
        (ex == ey + 1) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM10-DA14-Y",
        (ey == ex + 1) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM10-DA15-X",
        (ex == ey + 1) & (fx > fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-MM10-MM10-DA15-Y",
        (ey == ex + 1) & (fy > fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-MM10-MM10-DA20-X",
        (ex == ey + 2) & (fx < fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-DA20-Y",
        (ey == ex + 2) & (fy < fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-DA21-X",
        (ex == ey + 2) & (ex == fy + (p - 1)) & (fx > fy + 2) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-DA21-Y",
        (ey == ex + 2) & (ey == fx + (p - 1)) & (fy > fx + 2) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-DA22-X",
        (ex == ey + 2) & (ex == fy + (p - 1)) & (fx > fy + 2) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 2, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-DA22-Y",
        (ey == ex + 2) & (ey == fx + (p - 1)) & (fy > fx + 2) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 2, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-DA23-X",
        (ex == ey + 2) & (ex == fy + (p - 1)) & (fx == fy + 2) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-DA23-Y",
        (ey == ex + 2) & (ey == fx + (p - 1)) & (fy == fx + 2) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-DA25-X",
        (ex == ey + 2) & (ex == fy + (p - 1)) & (fx == ey) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 2, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-DA25-Y",
        (ey == ex + 2) & (ey == fx + (p - 1)) & (fy == ex) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 2, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D10-X",
        (ex < fy + (p - 2)) & (fx == ey + 1) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D10-Y",
        (ey < fx + (p - 2)) & (fy == ex + 1) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D11-X",
        (ex < fy + (p - 2)) & (fx == ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 2, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D11-Y",
        (ey < fx + (p - 2)) & (fy == ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 2, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D12-X",
        (ex < fy + (p - 2)) & (fx == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fy - 2, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D12-Y",
        (ey < fx + (p - 2)) & (fy == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fx - 2, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D20-X",
        (ex == fy + (p - 2)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D20-Y",
        (ey == fx + (p - 2)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D21-X",
        (ex == fy + (p - 2)) & (fx == ey + 1) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D21-Y",
        (ey == fx + (p - 2)) & (fy == ex + 1) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D22-X",
        (ex == fy + (p - 2)) & (fx == ey) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D22-Y",
        (ey == fx + (p - 2)) & (fy == ex) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D23-X",
        (ex == fy + (p - 2)) & (fx == ey) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D23-Y",
        (ey == fx + (p - 2)) & (fy == ex) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D30-X",
        (ex == fy + (p - 1)) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D30-Y",
        (ey == fx + (p - 1)) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D31-X",
        (ex == fy + (p - 1)) & (fx == ey + 1) & (fx > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D31-Y",
        (ey == fx + (p - 1)) & (fy == ex + 1) & (fy > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D320-X",
        (ex == fy + (p - 1)) & (fx == ey) & (fx > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D320-Y",
        (ey == fx + (p - 1)) & (fy == ex) & (fy > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D321-X",
        (ex == fy + (p - 1)) & (fx == ey) & (ex > ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ex - (p + 1), ex - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D321-Y",
        (ey == fx + (p - 1)) & (fy == ex) & (ey > ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ey - (p + 1), ey - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D40-X",
        (ex == fy + p) & (fx > ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D40-Y",
        (ey == fx + p) & (fy > ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D41-X",
        (ex == fy + p) & (fx > ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D41-Y",
        (ey == fx + p) & (fy > ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D42-X",
        (ex == fy + p) & (fx == ey + 2) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D42-Y",
        (ey == fx + p) & (fy == ex + 2) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D430-X",
        (ex == fy + p) & (fx == ey + 1) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D430-Y",
        (ey == fx + p) & (fy == ex + 1) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D431-X",
        (ex == fy + p) & (fx == ey + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fy + 2),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D431-Y",
        (ey == fx + p) & (fy == ex + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fx + 2),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D440-X",
        (ex == fy + p) & (fx == ey) & (ey > fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D440-Y",
        (ey == fx + p) & (fy == ex) & (ex > fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D441-X",
        (ex == fy + p) & (fx == ey) & (ey == fy + 3) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ex - p, ex),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D441-Y",
        (ey == fx + p) & (fy == ex) & (ex == fx + 3) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ey - p, ey),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D442-X",
        (ex == fy + p) & (fx == ey) & (ey > fy + 3) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 2, fy + 2),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D442-Y",
        (ey == fx + p) & (fy == ex) & (ex > fx + 3) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 2, fx + 2),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D50-X",
        (ex < ey + (p - 1)) & (ex > fy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D50-Y",
        (ey < ex + (p - 1)) & (ey > fx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D51-X",
        (ex < ey + (p - 1)) & (ex > fy + p) & (fx == ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fx),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D51-Y",
        (ey < ex + (p - 1)) & (ey > fx + p) & (fy == ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fy),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D52-X",
        (ex < ey + (p - 1)) & (ex > fy + p) & (fx == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 2, fx - 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D52-Y",
        (ey < ex + (p - 1)) & (ey > fx + p) & (fy == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 2, fy - 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D6-X",
        (ex > ey + 2) & (fx < fy + 1) & (fx + 2 > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D6-Y",
        (ey > ex + 2) & (fy < fx + 1) & (fy + 2 > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D700-X",
        (ex > ey + 1) & (ex < fy + (p - 2)) & (fx > fy + 1) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D700-Y",
        (ey > ex + 1) & (ey < fx + (p - 2)) & (fy > fx + 1) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D701-X",
        (ex > ey + 1) & (ex < fy + (p - 2)) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D701-Y",
        (ey > ex + 1) & (ey < fx + (p - 2)) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D71-X",
        (ex > ey + 1) & (ex < fy + (p - 2)) & (fx + 1 == ey) & (fx > fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 2, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D71-Y",
        (ey > ex + 1) & (ey < fx + (p - 2)) & (fy + 1 == ex) & (fy > fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 2, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D80-X",
        (ex > ey + 1) & (ex == fy + (p - 2)) & (fx > fy + 2) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D80-Y",
        (ey > ex + 1) & (ey == fx + (p - 2)) & (fy > fx + 2) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D81-X",
        (ex > ey + 1) & (ex == fy + (p - 2)) & (fx > fy + 2) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D81-Y",
        (ey > ex + 1) & (ey == fx + (p - 2)) & (fy > fx + 2) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D82-X",
        (ex > ey + 1) & (ex == fy + (p - 2)) & (fx == fy + 2) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D82-Y",
        (ey > ex + 1) & (ey == fx + (p - 2)) & (fy == fx + 2) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D83-X",
        (ex > ey + 1) & (ex == fy + (p - 2)) & (fx == fy + 2) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 2, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D83-Y",
        (ey > ex + 1) & (ey == fx + (p - 2)) & (fy == fx + 2) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 2, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D84-X",
        (ex > ey + 1) & (ex == fy + (p - 2)) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D84-Y",
        (ey > ex + 1) & (ey == fx + (p - 2)) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D9-X",
        (ex > fy + (p + 1)) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ex - (p - 1)),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D9-Y",
        (ey > fx + (p + 1)) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ey - (p - 1)),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D9E-X",
        (ex > fy + (p + 1)) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 2, ex - (p - 1)),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D9E-Y",
        (ey > fx + (p + 1)) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 2, ey - (p - 1)),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D90-X",
        (ex > ey + 2) & (ex == fy + (p - 1)) & (fx > fy + 2) & (fx + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D90-Y",
        (ey > ex + 2) & (ey == fx + (p - 1)) & (fy > fx + 2) & (fy + 1 < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D91-X",
        (ex > ey + 2) & (ex == fy + (p - 1)) & (fx > fy + 2) & (fx + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 2, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D91-Y",
        (ey > ex + 2) & (ey == fx + (p - 1)) & (fy > fx + 2) & (fy + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 2, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D92-X",
        (ex > ey + 2) & (ex == fy + (p - 1)) & (fx == fy + 2) & (fx < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D92-Y",
        (ey > ex + 2) & (ey == fx + (p - 1)) & (fy == fx + 2) & (fy < ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D9A0-X",
        (ex == fy + p) & (fx + 1 < ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D9A0-Y",
        (ey == fx + p) & (fy + 1 < ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D9A1-X",
        (ex == fy + p) & (fx + 1 < ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D9A1-Y",
        (ey == fx + p) & (fy + 1 < ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D9B0-X",
        (ex == fy + p) & (fx + 1 == ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 2, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D9B0-Y",
        (ey == fx + p) & (fy + 1 == ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 2, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D9B1-X",
        (ex == fy + p) & (fx + 1 == ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 2, fy + 1),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D9B1-Y",
        (ey == fx + p) & (fy + 1 == ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 2, fx + 1),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D9C0-X",
        (ex == fy + (p + 1)) & (fx + 1 < ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D9C0-Y",
        (ey == fx + (p + 1)) & (fy + 1 < ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D9C1-X",
        (ex == fy + (p + 1)) & (fx + 1 < ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, fy + 2),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D9C1-Y",
        (ey == fx + (p + 1)) & (fy + 1 < ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, fx + 2),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D9D0-X",
        (ex == fy + (p + 1)) & (fx + 1 == ey) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 2, fy + 2),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D9D0-Y",
        (ey == fx + (p + 1)) & (fy + 1 == ex) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 2, fx + 2),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-D9D1-X",
        (ex == fy + (p + 1)) & (fx + 1 == ey) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 2, fy + 2),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-MM10-MM10-D9D1-Y",
        (ey == fx + (p + 1)) & (fy + 1 == ex) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 2, fx + 2),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-MM10-MM10-DB10-X",
        (ex == ey + (p - 1)) & (fx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-DB10-Y",
        (ey == ex + (p - 1)) & (fy > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-DB11-X",
        (ex == ey + (p - 1)) & (fx == ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-DB11-Y",
        (ey == ex + (p - 1)) & (fy == ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-DB20-X",
        (ex == ey + p) & (fx > ey + 3) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-DB20-Y",
        (ey == ex + p) & (fy > ex + 3) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-DB21-X",
        (ex == ey + p) & (fx > ey + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-DB21-Y",
        (ey == ex + p) & (fy > ex + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-DB22-X",
        (ex == ey + p) & (fx == ey + 3) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-DB22-Y",
        (ey == ex + p) & (fy == ex + 3) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-MM10-MM10-DB23-X",
        (ex == ey + p) & (fx == ey + 3) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fx),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-MM10-MM10-DB23-Y",
        (ey == ex + p) & (fy == ex + 3) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fy),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

end
