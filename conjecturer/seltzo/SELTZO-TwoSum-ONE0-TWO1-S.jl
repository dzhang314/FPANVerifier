function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ONE0},
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

    checker("SELTZO-TwoSum-ONE0-TWO1-SE0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SE0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SE1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx == fy) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, ex),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SE1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy == fx) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, ey),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SE2-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SE2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SE3-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey) & (ex < gy + (p - 3)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SE3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex) & (ey < gx + (p - 3)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy + 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SE4-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey) & (ex == gy + (p - 3)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex + 1, ex - 1, fx + 2),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SE4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex) & (ey == gx + (p - 3)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey + 1, ey - 1, fy + 2),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SA10-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx > fy + 1) & (ex + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fx - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SA10-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy > fx + 1) & (ey + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fy - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SA11-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == fy + 1) & (ex + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, fy - 2, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SA11-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == fx + 1) & (ey + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, fx - 2, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SA12-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == fy) & (ex + 1 == ey) & (ex < gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 2, fx - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SA12-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == fx) & (ey + 1 == ex) & (ey < gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 2, fy - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SA13-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == fy) & (ex + 1 == ey) & (ex == gy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 2, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SA13-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == fx) & (ey + 1 == ex) & (ey == gx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 2, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SA14-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + 1 == fy) & (ex + 1 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 2, fx + 1, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SA14-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + 1 == fx) & (ey + 1 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 2, fy + 1, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SA15-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + 1 < fy) & (ex + 1 == ey) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 2, fy, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SA15-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + 1 < fx) & (ey + 1 == ex) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 2, fx, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SA16-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + 1 < fy) & (ex + 1 == ey) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 2, fy, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SA16-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + 1 < fx) & (ey + 1 == ex) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 2, fx, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SA17-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + 2 < fy) & (ex + 1 == ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 2, fy, fy - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SA17-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + 2 < fx) & (ey + 1 == ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 2, fx, fx - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SA18-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + 2 == fy) & (ex + 1 == ey) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 2, fy, fy),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SA18-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + 2 == fx) & (ey + 1 == ex) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 2, fx, fx),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SA21-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == fy) & (ex + 2 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, ex, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SA21-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == fx) & (ey + 2 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, ey, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SA22-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + 1 == fy) & (ex + 2 == ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, ex, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SA22-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + 1 == fx) & (ey + 2 == ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, ey, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SA23-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 2 == ey) & (ey == fy + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, ex - 1, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SA23-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 2 == ex) & (ex == fx + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, ey - 1, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SA24-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 2 == ey) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ey, ex - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SA24-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 2 == ex) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ex, ey - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SA25-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 2 == ey) & (ey == fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ey, ex - 1, fy - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SA25-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 2 == ex) & (ex == fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ex, ey - 1, fx - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SA27-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 2 == ey) & (ey > fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ey, ex, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SA27-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 2 == ex) & (ex > fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ex, ey, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SA28-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 2 == ey) & (ey > fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ey, ex, fy - 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SA28-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 2 == ex) & (ex > fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ex, ey, fx - 1),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 1 > ey) & (fx < ey) & (ex < fy + (p - 3)) & (fx > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 1 > ex) & (fy < ex) & (ey < fx + (p - 3)) & (fy > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S1A-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx < ey) & (fx > fy) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fy),
            SELTZORange(sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S1A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy < ex) & (fy > fx) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fx),
            SELTZORange(sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S1B-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, fy - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S1B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, fx - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S1AB-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, fy, fy),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S1AB-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, fx, fx),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S1AC-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex > ey) & (fx == fy) & (ex == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S1AC-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey > ex) & (fy == fx) & (ey == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, ex),
            SELTZORange(sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S2-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx > ey) & (ex > fy + p) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx - 1, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S2-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy > ex) & (ey > fx + p) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy - 1, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S2A0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, ey),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S2A0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, ex),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S2A1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, ey),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S2A1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, ex),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S2B-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex > fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ex - p, ex),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S2B-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey > fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ey - p, ey),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S2AB-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S2AB-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S2C0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, ey),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S2C0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, ex),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S2C1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 2, ey),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S2C1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 2, ex),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S2BC-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ex - (p - 1), ex + 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S2BC-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ey - (p - 1), ey + 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S2D0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx > ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S2D0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy > ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S2D1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == ey + 1) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx - 2, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S2D1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == ex + 1) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy - 2, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S2BD-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx == ey) & (ex == fy + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, fy, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S2BD-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy == ex) & (ey == fx + (p - 2))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, fx, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S3-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex > fy + (p + 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 1, 0, ex - p, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S3-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy < ex) & (ey > fx + (p + 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 1, 0, ey - p, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S3A0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex == fy + (p + 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ex - p, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S3A0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy < ex) & (ey == fx + (p + 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ey - p, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S3A1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex == fy + (p + 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, ex - p, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S3A1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy < ex) & (ey == fx + (p + 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, ey - p, fx - 1, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S3B0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex == fy + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S3B0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy < ex) & (ey == fx + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S3B1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex == fy + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 0, 0, ex - (p + 1), ex - (p + p + 1), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S3B1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy < ex) & (ey == fx + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 0, 0, ey - (p + 1), ey - (p + p + 1), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S3C-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex > fy + (p + 1)) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey),
            SELTZORange(~sy, 1, 0, ex - p, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S3C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy < ex) & (ey > fx + (p + 1)) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex),
            SELTZORange(~sx, 1, 0, ey - p, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S3D0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex == fy + (p - 1)) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey - 1, fx),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S3D0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy < ex) & (ey == fx + (p - 1)) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex - 1, fy),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S3E0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex == fy + (p - 2)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S3E0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy < ex) & (ey == fx + (p - 2)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S3E1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx < ey) & (ex == fy + (p - 2)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex + 1, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S3E1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy < ex) & (ey == fx + (p - 2)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey + 1, ex - 1, ex), pos_zero)
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S4-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + p < ey) & (ex + (p - 1) > ey) & (ex + 2 < fy) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sy, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S4-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + p < ex) & (ey + (p - 1) > ex) & (ey + 2 < fx) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sx, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S4A-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + p == ey) & (ex + 2 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey, fy, ex + 1),
            SELTZORange(sy, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S4A-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + p == ex) & (ey + 2 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex, fx, ey + 1),
            SELTZORange(sx, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S4AB-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + p == ey) & (ex + 2 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey, fy, ex + 3),
            SELTZORange(sy, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S4AB-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + p == ex) & (ey + 2 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex, fx, ey + 3),
            SELTZORange(sx, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S4C-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + p < ey) & (ex + (p - 1) > ey) & (ex + 2 < fy) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sy, 1, 0, fx, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S4C-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + p < ex) & (ey + (p - 1) > ex) & (ey + 2 < fx) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sx, 1, 0, fy, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S4D-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + (p - 1) == ey) & (ex + 2 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S4D-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + (p - 1) == ex) & (ey + 2 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S4BD-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + (p - 1) == ey) & (ex + 2 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S4BD-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + (p - 1) == ex) & (ey + 2 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S5-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + (p - 1) > ey) & (ex + 2 < ey) & (fx + 1 < fy) & (ex > fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey, ex + 1, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S5-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + (p - 1) > ex) & (ey + 2 < ex) & (fy + 1 < fx) & (ey > fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex, ey + 1, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S5E0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + (p - 1) > ey) & (ex + 3 < ey) & (ex + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey, ex + 2, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S5E0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + (p - 1) > ex) & (ey + 3 < ex) & (ey + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex, ey + 2, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S5E1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + (p - 1) > ey) & (ex + 3 == ey) & (ex + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ey, ex + 1, fx),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S5E1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + (p - 1) > ex) & (ey + 3 == ex) & (ey + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ex, ey + 1, fy),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S5F-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex + 2 < ey) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey, ex + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S5F-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey + 2 < ex) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ex, ey + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S5G0-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + p == ey) & (ex + 3 < ey) & (ex + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey, ex + 2, ex),
            SELTZORange(sy, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S5G0-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + p == ex) & (ey + 3 < ex) & (ey + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ex, ey + 2, ey),
            SELTZORange(sx, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S5G1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (fx + p == ey) & (ex + 3 == ey) & (ex + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ey, ex + 1, ex),
            SELTZORange(sy, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S5G1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (fy + p == ex) & (ey + 3 == ex) & (ey + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ex, ey + 1, ey),
            SELTZORange(sx, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-S6-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex > ey) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, fy),
            SELTZORange(~sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-S6-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey > ex) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey + 1, ex, fx),
            SELTZORange(~sx, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SB1-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SB1-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SB20-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SB20-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-ONE0-TWO1-SB21-X",
        (CLASS_X == ONE0) & (CLASS_Y == TWO1) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx - 1, fx),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-ONE0-TWO1-SB21-Y",
        (CLASS_Y == ONE0) & (CLASS_X == TWO1) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy - 1, fy),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

end
