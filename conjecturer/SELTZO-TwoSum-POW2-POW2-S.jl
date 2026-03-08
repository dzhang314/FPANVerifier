function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{POW2},
    ::Val{POW2},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    # Sum of two powers of two (equal exponent case).
    checker("SELTZO-TwoSum-POW2-POW2-SE",
        (ex == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex + 1, fx + 1, gx + 1), pos_zero)
    end

    # Sum of two powers of two (boundary case).
    checker("SELTZO-TwoSum-POW2-POW2-SB-X",
        (ex == ey + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-POW2-POW2-SB-Y",
        (ey == ex + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, ex + 1), pos_zero)
    end

    # Remaining POW2-POW2-S lemmas have been subsumed by L lemmas.

end
