function check_seltzo_two_sum_lemmas_a!(
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
    x_all1 = (CLASS_X == ALL1)
    y_all1 = (CLASS_Y == ALL1)

    # Lemmas in family A apply to situations where the smaller addend
    # fits entirely inside the mantissa of an all-ones number.

    # Larger addend is an all-ones number (general case).
    checker("SELTZO-TwoSum-AD-G-X",
        diff_sign & x_all1 & (~tby) &
        (ex > ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-AD-G-Y",
        diff_sign & y_all1 & (~tbx) &
        (ey > ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, gx), pos_zero)
    end

    # Larger addend is an all-ones number (adjacent leading 0).
    checker("SELTZO-TwoSum-AD-A0-X",
        diff_sign & x_all1 & (~lby) & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-AD-A0-Y",
        diff_sign & y_all1 & (~lbx) & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, gx), pos_zero)
    end

    # Larger addend is an all-ones number (adjacent leading 1).
    checker("SELTZO-TwoSum-AD-A1-X",
        diff_sign & x_all1 & lby & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-AD-A1-Y",
        diff_sign & y_all1 & lbx & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx, gx), pos_zero)
    end

end
