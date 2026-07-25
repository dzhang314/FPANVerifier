function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{POW2},
    ::Val{MM10},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-POW2-MM10-S1-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex > fy + p) & (ex < ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, ey),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-S1-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey > fx + p) & (ey < ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, ex),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-MM10-S1A0-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ey > fy + 2) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ex - (p - 2)),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-S1A0-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == fx + p) & (ex > fx + 2) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ey - (p - 2)),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-MM10-S1A1-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(~sy, 0, 0, fy - 1, ey - (p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-S1A1-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == fx + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(~sx, 0, 0, fx - 1, ex - (p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-MM10-S1A2-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == fy + p) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ex - (p - 2)),
            SELTZORange(~sy, 1, 0, fy - 1, fy - 3, fy - 2))
    end
    checker("SELTZO-TwoSum-POW2-MM10-S1A2-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == fx + p) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ey - (p - 2)),
            SELTZORange(~sx, 1, 0, fx - 1, fx - 3, fx - 2))
    end

    checker("SELTZO-TwoSum-POW2-MM10-S2A0-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(sy, 1, 0, ex - (p + 1), ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-S2A0-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(sx, 1, 0, ey - (p + 1), ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-MM10-S2A1-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == fy + (p - 1)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(sy, 0, 0, ex - (p + 1), ex - (p + (p + 1)), ex - (p + 1)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-S2A1-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == fx + (p - 1)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(sx, 0, 0, ey - (p + 1), ey - (p + (p + 1)), ey - (p + 1)))
    end

    checker("SELTZO-TwoSum-POW2-MM10-S3A0-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (ey < fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-S3A0-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (ex < fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, fx + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-MM10-S3A1-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == fy + (p - 2)) & (ey == fy + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, fy),
            SELTZORange(sy, 0, 0, ex - p, ex - (p + p), ex - p))
    end
    checker("SELTZO-TwoSum-POW2-MM10-S3A1-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == fx + (p - 2)) & (ex == fx + (p - 3))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, fx),
            SELTZORange(sx, 0, 0, ey - p, ey - (p + p), ey - p))
    end

    checker("SELTZO-TwoSum-POW2-MM10-SB1-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, ey + 1),
            SELTZORange(sy, 0, 0, fy, fy - 2, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-SB1-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, ex + 1),
            SELTZORange(sx, 0, 0, fx, fx - 2, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-MM10-SB20-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ex - (p - 1), ex - (p - 2)),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-SB20-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == ex + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ey - (p - 1), ey - (p - 2)),
            SELTZORange(~sx, 1, 0, ex - 1, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-POW2-MM10-SB21-X",
        (CLASS_X == POW2) & (CLASS_Y == MM10) &
        (ex == ey + p) & (ey == fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ex - (p - 1), ex - (p - 2)),
            SELTZORange(~sy, 0, 0, ey - 1, fy - 1, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-POW2-MM10-SB21-Y",
        (CLASS_Y == POW2) & (CLASS_X == MM10) &
        (ey == ex + p) & (ex == fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ey - (p - 1), ey - (p - 2)),
            SELTZORange(~sx, 0, 0, ex - 1, fx - 1, ex - (p - 1)))
    end

end
