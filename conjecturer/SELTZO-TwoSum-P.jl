function check_seltzo_two_sum_lemmas_p!(
    checker::LemmaChecker,
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)
    same_sign = (sx == sy)
    diff_sign = (sx != sy)
    x_pow2 = (CLASS_X == POW2)
    y_pow2 = (CLASS_Y == POW2)

    # Lemmas in family P apply to situations where the smaller addend
    # fits entirely inside the mantissa of a power of two.

    # Larger addend is a power of two (general case).
    checker("SELTZO-TwoSum-PS-G-X",
        same_sign & x_pow2 & (~tby) &
        (ex > ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-PS-G-Y",
        same_sign & y_pow2 & (~tbx) &
        (ey > ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gx), pos_zero)
    end

    # Larger addend is a power of two (adjacent leading 0).
    checker("SELTZO-TwoSum-PS-A0-X",
        same_sign & x_pow2 & (~lby) & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-PS-A0-Y",
        same_sign & y_pow2 & (~lbx) & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, gx), pos_zero)
    end

    # Larger addend is a power of two (adjacent leading 1).
    checker("SELTZO-TwoSum-PS-A1-X",
        same_sign & x_pow2 & lby & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-PS-A1-Y",
        same_sign & y_pow2 & lbx & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx, gx), pos_zero)
    end

end
