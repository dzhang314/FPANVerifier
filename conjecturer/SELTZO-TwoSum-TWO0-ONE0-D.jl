function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{TWO0},
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

    checker("SELTZO-TwoSum-TWO0-ONE0-DA1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx > fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-DA1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy > fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-DA231-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx == fy) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx - 1, fx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-DA231-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy == fx) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy - 1, fy - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-DA232-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx == fy + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ey, fx, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-DA232-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy == fx + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ex, fy, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-DA21-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx == fy + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ey, fx - 1, fx), pos_zero)
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-DA21-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy == fx + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ex, fy - 1, fy), pos_zero)
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-DA4-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx + 1 == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-DA4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy + 1 == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-DA5-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + 1) & (fx + 1 < fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy - 1, fx - 1),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-DA5-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + 1) & (fy + 1 < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx - 1, fy - 1),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx < ey) & (fx > fy + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy < ex) & (fy > fx + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D1A-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx < ey) & (fx > fy + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D1A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy < ex) & (fy > fx + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D1BC0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D1BC0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D1BC1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D1BC1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D1ABC0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx == fy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D1ABC0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy == fx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D1ABC1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx == fy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D1ABC1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy == fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D1AC-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx == ey) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx - 1, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D1AC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy == ex) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy - 1, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D1E-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx < ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D1E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy < ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D1AE-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx < ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D1AE-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy < ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D1ADE0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx == ey) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy - 2, fy - (p + 2), fy - 2))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D1ADE0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy == ex) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx - 2, fx - (p + 2), fx - 2))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D2A-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey + 3) & (fx == ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 2, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D2A-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex + 3) & (fy == ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 2, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D2AC-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + 3) & (fx == ey + 1) & (ex < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D2AC-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + 3) & (fy == ex + 1) & (ey < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D2E0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx > ey + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D2E0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy > ex + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D2AE0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey + 3) & (fx == ey + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 2, fx + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D2AE0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex + 3) & (fy == ex + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 2, fy + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D2AE1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey + 3) & (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 2, fx - 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D2AE1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex + 3) & (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 2, fy - 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D2ACE-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + 3) & (fx == ey + 1) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(~sy, 0, 0, fy - 3, fy - (p + 3), fy - 3))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D2ACE-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + 3) & (fy == ex + 1) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(~sx, 0, 0, fx - 3, fx - (p + 3), fx - 3))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D3-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx < ey + 1) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy < ex + 1) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D3D-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx < ey + 1) & (ex > fy + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D3D-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy < ex + 1) & (ey > fx + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D3C-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex > ey + 2) & (fx < ey + 1) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx - 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D3C-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey > ex + 2) & (fy < ex + 1) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy - 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D3ACD-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx < ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D3ACD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy < ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D3ABCD-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + 2) & (fx == ey) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, fx - 1),
            SELTZORange(sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D3ABCD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + 2) & (fy == ex) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, fy - 1),
            SELTZORange(sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D4-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx > ey + 2) & (ex > fy + p) & (ex < ey + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D4-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy > ex + 2) & (ey > fx + p) & (ey < ex + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D4E-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx > ey + 2) & (ex < ey + p) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D4E-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy > ex + 2) & (ey < ex + p) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D4AB0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ex > fx + 2) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D4AB0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ey > fy + 2) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D4AB1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > fx + 2) & (ex > fy + p) & (ey < fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D4AB1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > fy + 2) & (ey > fx + p) & (ex < fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D4A1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ex == fx + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D4A1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ey == fy + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D4ABE0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ex > fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D4ABE0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ey > fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D4ABE1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D4ABE1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D4ABCE0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ex == fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D4ABCE0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ey == fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D4ABCE1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex == fx + 2) & (ey == fy + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, fx - 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D4ABCE1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey == fy + 2) & (ex == fx + (p - 2))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, fy - 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D4D0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx > ey + 2) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D4D0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy > ex + 2) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D4BD0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx == ey + 2) & (ex > ey + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 2, fx + 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D4BD0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy == ex + 2) & (ey > ex + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 2, fy + 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D4BD1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex > ey + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 2, fx - 1),
            SELTZORange(sy, 1, 0, fy - 1, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D4BD1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey > ex + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 2, fy - 1),
            SELTZORange(sx, 1, 0, fx - 1, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-D4BCD-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (fx == ey + 1) & (ex == ey + 3) & (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey),
            SELTZORange(sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-D4BCD-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (fy == ex + 1) & (ey == ex + 3) & (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex),
            SELTZORange(sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-DB0-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ey < fy + (p - 2)) & (fx > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-DB0-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ex < fx + (p - 2)) & (fy > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-DB1-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ey < fy + (p - 2)) & (fx == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 0, 0, fy, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-DB1-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ex < fx + (p - 2)) & (fy == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 0, 0, fx, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-DB2-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ey == fy + (p - 2)) & (fx > ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-DB2-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ex == fx + (p - 2)) & (fy > ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 2),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-TWO0-ONE0-DB3-X",
        (CLASS_X == TWO0) & (CLASS_Y == ONE0) &
        (ex == ey + p) & (ey == fy + (p - 2)) & (fx == ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, fx + 1),
            SELTZORange(~sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-TWO0-ONE0-DB3-Y",
        (CLASS_Y == TWO0) & (CLASS_X == ONE0) &
        (ey == ex + p) & (ex == fx + (p - 2)) & (fy == ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, fy + 1),
            SELTZORange(~sx, 1, 0, fx, fx - 2, fx - 1))
    end

end
