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

    checker("SELTZO-TwoSum-AD-G0-X",
        diff_sign & x_all1 & (~tby) &
        (ex > ey + 1) & (fx + 1 < gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-AD-G1-X",
        diff_sign & x_all1 & tby & (~y_all1) &
        (ex > ey + 1) & (fx + 1 < gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-AD-A00-X",
        diff_sign & x_all1 & (~lby) & (~tby) &
        (ex == ey + 1) & (fx + 1 < gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-AD-A10-X",
        diff_sign & x_all1 & lby & (~tby) &
        (ex == ey + 1) & (fx + 1 < gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy, gy), pos_zero)
    end

end
