function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{POW2},
    ::Val{POW2},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    # Difference of two powers of two (equal exponent case).
    checker("SELTZO-TwoSum-POW2-POW2-DE",
        (ex == ey)
    ) do lemma
        add_case!(lemma, pos_zero, pos_zero)
    end

    # Difference of two powers of two (adjacent case).
    checker("SELTZO-TwoSum-POW2-POW2-DA-X",
        (ex == ey + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx - 1, gx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-POW2-DA-Y",
        (ey == ex + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy - 1, gy - 1), pos_zero)
    end

    # Difference of two powers of two (general case).
    checker("SELTZO-TwoSum-POW2-POW2-DG-X",
        (ex > ey + 1) & (ex < ey + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey - 1, ey), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-POW2-DG-Y",
        (ey > ex + 1) & (ey < ex + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex - 1, ex), pos_zero)
    end

    # Difference of two powers of two (boundary case).
    checker("SELTZO-TwoSum-POW2-POW2-DB-X",
        (ex == ey + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, fx - 1, gx - 1), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-POW2-DB-Y",
        (ey == ex + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, fy - 1, gy - 1), pos_zero)
    end

end
