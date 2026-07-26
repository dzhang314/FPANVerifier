function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO1},
    ::Val{TWO0},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-TWO1-TWO0-SA10-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx > fy + 1) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA10-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy > fx + 1) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SA11-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx > fy + 1) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA11-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy > fx + 1) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SA12-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx > fy + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA12-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy > fx + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SA13-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA13-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SA14-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy + 1) & (ey < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fx - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA14-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx + 1) & (ex < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fy - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SA15-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy + 1) & (ey == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA15-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx + 1) & (ex == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SA16-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, fx - 1, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA16-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, fy - 1, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SA17-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA17-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SA18-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA18-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SA19-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 1) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fy, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA19-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 1) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fx, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SA20-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx < ey) & (fx > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA20-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy < ex) & (fy > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SA21-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx < ey) & (fx > fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA21-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy < ex) & (fy > fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SA22-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx == fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA22-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy == fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SA23-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx < ey) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA23-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy < ex) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SA24-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx == fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, fx),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA24-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy == fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, fy),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SA25-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx == ey) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA25-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy == ex) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SA26-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fy + 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA26-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fx + 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SA27-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, ex - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SA27-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, ey - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex < ey + p) & (fx > ey + 2) & (ex > fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey < ex + p) & (fy > ex + 2) & (ey > fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S1F-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex < ey + p) & (fx > ey + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S1F-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey < ex + p) & (fy > ex + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S1A0-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex < ey + p) & (fx == ey + 2) & (ex > fy + p) & (ex > fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S1A0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey < ex + p) & (fy == ex + 2) & (ey > fx + p) & (ey > fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S1A1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex < ey + p) & (fx == ey + 2) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S1A1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey < ex + p) & (fy == ex + 2) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S1A2-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey + 2) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S1A2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex + 2) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S1B0-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex > fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S1B0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey > fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S1B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx + 1 > ey) & (fx < ey + 2) & (ex > fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S1B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy + 1 > ex) & (fy < ex + 2) & (ey > fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S1C0-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx > ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S1C0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy > ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S1C1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S1C1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S1D-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S1D-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S1E-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S1E-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S2-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx < ey) & (fx > fy) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy < ex) & (fy > fx) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S2A-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S2A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S2D-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex > ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S2D-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey > ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S2B0-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx < ey + 1) & (fx > fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S2B0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy < ex + 1) & (fy > fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S2B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx == fy + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S2B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy == fx + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S2C0-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx < ey + 1) & (fx > fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S2C0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy < ex + 1) & (fy > fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S2C1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex > ey + 2) & (fx == fy + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S2C1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey > ex + 2) & (fy == fx + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S3-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex > fy + p) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S3-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey > fx + p) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S3A-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx < ey) & (ex > fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S3A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy < ex) & (ey > fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S3B0-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex > ey + 3) & (fx < ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx - 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S3B0-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey > ex + 3) & (fy < ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy - 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S3B1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 3) & (fx < ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey + 1, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S3B1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 3) & (fy < ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex + 1, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S4A-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex > ey + 3) & (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S4A-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey > ex + 3) & (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S4AB-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 3) & (fx == ey + 1) & (ex < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S4AB-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 3) & (fy == ex + 1) & (ey < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S4AC-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex > ey + 3) & (fx == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S4AC-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey > ex + 3) & (fy == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S4ABC1-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey) & (ex == fx + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S4ABC1-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex) & (ey == fy + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S4ABC2-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (fx == ey + 1) & (ex == fx + 2) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S4ABC2-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (fy == ex + 1) & (ey == fy + 2) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S4AD-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex > ey + 3) & (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S4AD-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey > ex + 3) & (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S4ABD-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 3) & (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fy + 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S4ABD-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 3) & (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fx + 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S4AE-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex > ey + 3) & (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, fx - 1),
            SELTZORange(sy, 1, 0, fy - 2, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S4AE-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey > ex + 3) & (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, fy - 1),
            SELTZORange(sx, 1, 0, fx - 2, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-S4ABE-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + 3) & (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-S4ABE-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + 3) & (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SB20-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ex < fx + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SB20-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ey < fy + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SB21-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ex < fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SB21-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ey < fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SB22-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ex == fx + (p - 3)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SB22-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ey == fy + (p - 3)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO1-TWO0-SB23-X",
        (CLASS_X == TWO1) & (CLASS_Y == TWO0) &
        (ex == ey + p) & (ex == fx + (p - 3)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO1-TWO0-SB23-Y",
        (CLASS_Y == TWO1) & (CLASS_X == TWO0) &
        (ey == ex + p) & (ey == fy + (p - 3)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 3, fx - 2))
    end

end
