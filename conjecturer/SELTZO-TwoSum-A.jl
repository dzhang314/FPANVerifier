function check_seltzo_two_sum_lemmas_a!(
    checker::LemmaChecker,
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)
    same_sign = (sx == sy)
    diff_sign = (sx != sy)
    x_all1 = (CLASS_X == ALL1)
    y_all1 = (CLASS_Y == ALL1)

    # Lemmas in family A apply to situations where the smaller addend
    # fits entirely inside the mantissa of an all-ones number.

    checker("SELTZO-TwoSum-AD-G0-X",
        diff_sign & x_all1 & (~tby) &
        (ex > ey + 1) & (fx + 1 < gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-AD-G0-Y",
        diff_sign & y_all1 & (~tbx) &
        (ey > ex + 1) & (fy + 1 < gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-AD-G1-X",
        diff_sign & x_all1 & tby & (~y_all1) &
        (ex > ey + 1) & (fx + 1 < gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-AD-G1-Y",
        diff_sign & y_all1 & tbx & (~x_all1) &
        (ey > ex + 1) & (fy + 1 < gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-AD-A00-X",
        diff_sign & x_all1 & (~lby) & (~tby) &
        (ex == ey + 1) & (fx + 1 < gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-AD-A00-Y",
        diff_sign & y_all1 & (~lbx) & (~tbx) &
        (ey == ex + 1) & (fy + 1 < gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-AD-A01-X",
        diff_sign & x_all1 & (~lby) & tby &
        (ex == ey + 1) & (fx + 1 < gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey - 1, gy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-AD-A01-Y",
        diff_sign & y_all1 & (~lbx) & tbx &
        (ey == ex + 1) & (fy + 1 < gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex - 1, gx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-AD-A10-X",
        diff_sign & x_all1 & lby & (~tby) &
        (ex == ey + 1) & (fx + 1 < gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-AD-A10-Y",
        diff_sign & y_all1 & lbx & (~tbx) &
        (ey == ex + 1) & (fy + 1 < gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-AD-A11-X",
        diff_sign & x_all1 & lby & tby & (~y_all1) &
        (ex == ey + 1) & (fx + 1 < gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fy, gy),
            SELTZORange(sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-AD-A11-Y",
        diff_sign & y_all1 & lbx & tbx & (~x_all1) &
        (ey == ex + 1) & (fy + 1 < gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fx, gx),
            SELTZORange(sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

end
