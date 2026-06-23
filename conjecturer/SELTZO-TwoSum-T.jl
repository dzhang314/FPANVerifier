function check_seltzo_two_sum_lemmas_t!(
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
    x_pow2 = (CLASS_X == POW2)
    y_pow2 = (CLASS_Y == POW2)
    x_all1 = (CLASS_X == ALL1)
    y_all1 = (CLASS_Y == ALL1)
    x_r1r0 = (CLASS_X == R1R0)
    y_r1r0 = (CLASS_Y == R1R0)

    # Lemmas in family T apply to situations where the smaller addend
    # fits entirely inside the trailing bits of the larger addend.

    checker("SELTZO-TwoSum-TS-G00-X",
        same_sign & (~lbx) & (~tbx) & (~x_pow2) & (~tby) &
        (gx > ey) & (ex < gy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-TS-G01-X",
        (~lbx) & (~tbx) & tby & (~y_all1) &
        (gx > ey) & (ex < gy + (p - 1)) & ((fx > gx) | (same_sign & (~x_pow2)))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TS-G10-X",
        same_sign & lbx & (~tbx) & (~tby) &
        (gx > ey) & (ex < gy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-TS-G11-X",
        lbx & (~tbx) & tby & (~y_all1) &
        (gx > ey) & (ex < gy + (p - 1)) & ((fx > gx) | (same_sign & (fx > ey)))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    ############################################################################

    checker("SELTZO-TwoSum-TD-G00-X",
        diff_sign & (~lbx) & tbx & (~tby) &
        (gx > ey) & (ex < gy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-TD-G01-X",
        diff_sign & (~lbx) & tbx & tby & (~y_all1) &
        (gx > ey) & (ex < gy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-TD-G10-X",
        diff_sign & lbx & tbx & (~x_all1) & (~tby) &
        (gx > ey) & (ex < gy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-TD-G11-X",
        diff_sign & lbx & tbx & (~x_all1) & tby & (~y_all1) &
        (gx > ey) & (ex < gy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

end
