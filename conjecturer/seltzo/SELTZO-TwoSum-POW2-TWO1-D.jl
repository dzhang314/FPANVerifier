function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{POW2},
    ::Val{TWO1},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-POW2-TWO1-DA0-X",
        (CLASS_X == POW2) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ey - 1, fy, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-TWO1-DA0-Y",
        (CLASS_Y == POW2) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ex - 1, fx, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-TWO1-DA1-X",
        (CLASS_X == POW2) & (CLASS_Y == TWO1) &
        (ex == ey + 1) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ey - 1, fy - 1, fy - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-TWO1-DA1-Y",
        (CLASS_Y == POW2) & (CLASS_X == TWO1) &
        (ey == ex + 1) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ex - 1, fx - 1, fx - 1), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-TWO1-D1-X",
        (CLASS_X == POW2) & (CLASS_Y == TWO1) &
        (ex > fy + (p + 1)) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-POW2-TWO1-D1-Y",
        (CLASS_Y == POW2) & (CLASS_X == TWO1) &
        (ey > fx + (p + 1)) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-POW2-TWO1-D1A-X",
        (CLASS_X == POW2) & (CLASS_Y == TWO1) &
        (ex == fy + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ey),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-POW2-TWO1-D1A-Y",
        (CLASS_Y == POW2) & (CLASS_X == TWO1) &
        (ey == fx + (p + 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ex),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-POW2-TWO1-D2A-X",
        (CLASS_X == POW2) & (CLASS_Y == TWO1) &
        (ex == fy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, fy + 1),
            SELTZORange(~sy, 0, 0, fy - 1, fy - (p + 1), fy - 1))
    end
    checker("SELTZO-TwoSum-POW2-TWO1-D2A-Y",
        (CLASS_Y == POW2) & (CLASS_X == TWO1) &
        (ey == fx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, fx + 1),
            SELTZORange(~sx, 0, 0, fx - 1, fx - (p + 1), fx - 1))
    end

    checker("SELTZO-TwoSum-POW2-TWO1-D3A0-X",
        (CLASS_X == POW2) & (CLASS_Y == TWO1) &
        (ex > ey + 2) & (ex == fy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, ey, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-TWO1-D3A0-Y",
        (CLASS_Y == POW2) & (CLASS_X == TWO1) &
        (ey > ex + 2) & (ey == fx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, ex, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-TWO1-D3A1-X",
        (CLASS_X == POW2) & (CLASS_Y == TWO1) &
        (ex == ey + 2) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex - 1, ey - 1, fy), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-TWO1-D3A1-Y",
        (CLASS_Y == POW2) & (CLASS_X == TWO1) &
        (ey == ex + 2) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey - 1, ex - 1, fx), pos_zero)
    end

    checker("SELTZO-TwoSum-POW2-TWO1-DB1-X",
        (CLASS_X == POW2) & (CLASS_Y == TWO1) &
        (ex == ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey - 1, ex - 1),
            SELTZORange(sy, 1, 0, fy, fy - 2, fy - 1))
    end
    checker("SELTZO-TwoSum-POW2-TWO1-DB1-Y",
        (CLASS_Y == POW2) & (CLASS_X == TWO1) &
        (ey == ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex - 1, ey - 1),
            SELTZORange(sx, 1, 0, fx, fx - 2, fx - 1))
    end

    checker("SELTZO-TwoSum-POW2-TWO1-DB20-X",
        (CLASS_X == POW2) & (CLASS_Y == TWO1) &
        (ex == ey + (p + 1)) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ex - 1),
            SELTZORange(~sy, 1, 0, ey - 1, fy, fy - 1))
    end
    checker("SELTZO-TwoSum-POW2-TWO1-DB20-Y",
        (CLASS_Y == POW2) & (CLASS_X == TWO1) &
        (ey == ex + (p + 1)) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ey - 1),
            SELTZORange(~sx, 1, 0, ex - 1, fx, fx - 1))
    end

    checker("SELTZO-TwoSum-POW2-TWO1-DB21-X",
        (CLASS_X == POW2) & (CLASS_Y == TWO1) &
        (ex == ey + (p + 1)) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex - 1, ey, ex - 1),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, fy - 1))
    end
    checker("SELTZO-TwoSum-POW2-TWO1-DB21-Y",
        (CLASS_Y == POW2) & (CLASS_X == TWO1) &
        (ey == ex + (p + 1)) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey - 1, ex, ey - 1),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, fx - 1))
    end

end
