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

    # Lemmas in family T apply to situations where the smaller addend
    # fits entirely inside the trailing bits of the larger addend.

    # Larger addend has leading zeros (general case).
    checker("SELTZO-TwoSum-TS-L0-G-X",
        same_sign & (~lbx) & (~tbx) & (~x_pow2) & (~tby) &
        (gx > ey) & (gy + (p - 1) > ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-TS-L0-G-Y",
        same_sign & (~lby) & (~tby) & (~y_pow2) & (~tbx) &
        (gy > ex) & (gx + (p - 1) > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, gx), pos_zero)
    end

    # Larger addend has leading ones (general case).
    checker("SELTZO-TwoSum-TS-L1-G-X",
        same_sign & lbx & (~tbx) & (~tby) &
        (min(fx, gx) > ey) & (gy + (p - 1) > ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-TS-L1-G-Y",
        same_sign & lby & (~tby) & (~tbx) &
        (min(fy, gy) > ex) & (gx + (p - 1) > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, gx), pos_zero)
    end

    # Larger addend has leading zeros (general case).
    checker("SELTZO-TwoSum-TD-L0-G-X",
        diff_sign & (~lbx) & tbx & (~tby) &
        (min(fx, gx) > ey) & (gy + (p - 1) > ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-TD-L0-G-Y",
        diff_sign & (~lby) & tby & (~tbx) &
        (min(fy, gy) > ex) & (gx + (p - 1) > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, gx), pos_zero)
    end

    # Larger addend has leading ones (general case).
    checker("SELTZO-TwoSum-TD-L1-G-X",
        diff_sign & lbx & tbx & (~x_all1) & (~tby) &
        (gx > ey) & (gy + (p - 1) > ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-TD-L1-G-Y",
        diff_sign & lby & tby & (~y_all1) & (~tbx) &
        (gy > ex) & (gx + (p - 1) > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, gx), pos_zero)
    end

end
