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
    x_all1 = (CLASS_X == ALL1)
    y_all1 = (CLASS_Y == ALL1)

    # Lemmas in family P apply to situations where the smaller addend
    # fits entirely inside the mantissa of a power of two.

    checker("SELTZO-TwoSum-PS-G0-X",
        same_sign & x_pow2 & (~tby) &
        (ex > ey + 1) & (fx + 1 < gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-PS-G1-X",
        same_sign & x_pow2 & tby & (~y_all1) &
        (ex > ey + 1) & (fx + 1 < gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-PS-A00-X",
        same_sign & x_pow2 & (~lby) & (~tby) &
        (ex == ey + 1) & (fx + 1 < gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-PS-A10-X",
        same_sign & x_pow2 & lby & (~tby) &
        (ex == ey + 1) & (fx + 1 < gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-PD-G0-X",
        diff_sign & x_pow2 & (~tby) & (~y_pow2) &
        (ex > ey + 2) & (fx < gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-PD-G1-X",
        diff_sign & x_pow2 & tby & (~y_all1) &
        (ex > ey + 2) & (fx < gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-PD-A00-X",
        diff_sign & x_pow2 & (~lby) & (~tby) & (~y_pow2) &
        (ex == ey + 2) & (fx < gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, ey - 1, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-PD-A01-X",
        diff_sign & x_pow2 & (~lby) & tby &
        (ex == ey + 2) & (fx < gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, ey - 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-PD-A11-X",
        diff_sign & x_pow2 & lby & tby & (~y_all1) &
        (ex == ey + 2) & (fx < gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex - 1, fy, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

end
