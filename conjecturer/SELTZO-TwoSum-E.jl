function check_seltzo_two_sum_lemmas_e!(
    checker::LemmaChecker,
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)
    diff_sign = (sx != sy)

    checker("SELTZO-TwoSum-E-T0-X",
        diff_sign & lbx & (~lby) & (~xor(tbx, tby)) &
        (ex == ey) & (gx > fy) & (ex > fx + 2) & (fx > gx) & (fy + 1 > gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-E-T0-Y",
        diff_sign & lby & (~lbx) & (~xor(tby, tbx)) &
        (ex == ey) & (gy > fx) & (ey > fy + 2) & (fy > gy) & (fx + 1 > gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-E-T1-X",
        diff_sign & lbx & (~lby) & xor(tbx, tby) &
        (ex == ey) & (gx > fy) & (ex > fx + 2) & (fx > gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, ey - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-E-T1-Y",
        diff_sign & lby & (~lbx) & xor(tby, tbx) &
        (ex == ey) & (gy > fx) & (ey > fy + 2) & (fy > gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, ex - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-E-A00-X",
        diff_sign & (~lbx) & (~tbx) & (~lby) & (~tby) &
        (ex == ey + 1) & (gx > fy) & (ex > fx + 2) & (fx > gx) & (fy > gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex - 1, fx, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-E-A00-Y",
        diff_sign & (~lby) & (~tby) & (~lbx) & (~tbx) &
        (ey == ex + 1) & (gy > fx) & (ey > fy + 2) & (fy > gy) & (fx > gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey - 1, fy, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-E-A10-X",
        diff_sign & lbx & (~tbx) & lby & (~tby) &
        (ex == ey + 1) & (gx > fy) & (ex > fx + 2) & (fx > gx) & (fy > gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, fx, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-E-A10-Y",
        diff_sign & lby & (~tby) & lbx & (~tbx) &
        (ey == ex + 1) & (gy > fx) & (ey > fy + 2) & (fy > gy) & (fx > gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, fy, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-E-A01-X",
        diff_sign & (~lbx) & tbx & (~lby) & tby &
        (ex == ey + 1) & (gx > fy) & (ex > fx + 2) & (fx > gx) & (fy > gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex - 1, fx, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-E-A01-Y",
        diff_sign & (~lby) & tby & (~lbx) & tbx &
        (ey == ex + 1) & (gy > fx) & (ey > fy + 2) & (fy > gy) & (fx > gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey - 1, fy, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-E-A11-X",
        diff_sign & lbx & tbx & lby & tby &
        (ex == ey + 1) & (gx > fy) & (ex > fx + 2) & (fx > gx) & (fy > gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex - 1, fx, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-E-A11-Y",
        diff_sign & lby & tby & lbx & tbx &
        (ey == ex + 1) & (gy > fx) & (ey > fy + 2) & (fy > gy) & (fx > gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey - 1, fy, gx), pos_zero)
    end

end
