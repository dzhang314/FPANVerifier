function check_seltzo_two_sum_lemmas_q!(
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

    checker("SELTZO-TwoSum-QA-L1T0-W1-X",
        diff_sign & lbx & (~tbx) & (~lby) & tby & (gx < fx) & (fx == ey) & (ex > ey + 2) & (ex < gy + (p - 1)) & (gy < gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-QA-L1T0-W0-X",
        diff_sign & lbx & (~tbx) & lby & (~tby) & (gx < fx) & (fx == ey) & (ex > ey + 2) & (ex < gy + (p - 1)) & (gy < gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, gy),
            pos_zero)
    end

    checker("SELTZO-TwoSum-QA-L1T1-W1-X",
        diff_sign & lbx & tbx & (~lby) & tby & (gx < fx) & (fx == ey) & (ex > ey + 2) & (ex < gy + (p - 1)) & (gy < gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-QA-L1T1-W0-X",
        diff_sign & lbx & tbx & lby & (~tby) & (gx < fx) & (fx == ey) & (ex > ey + 2) & (ex < gy + (p - 1)) & (gy < gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, gy),
            pos_zero)
    end

    checker("SELTZO-TwoSum-QA-L0T0-W1-X",
        same_sign & (~lbx) & (~tbx) & (~lby) & tby & (gx < fx) & (fx == ey) & (ex > ey + 2) & (ex < gy + (p - 1)) & (gy < gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-QA-L0T0-W0-X",
        same_sign & (~lbx) & (~tbx) & lby & (~tby) & (gx < fx) & (fx == ey) & (ex > ey + 2) & (ex < gy + (p - 1)) & (gy < gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, gy),
            pos_zero)
    end

    checker("SELTZO-TwoSum-QA-L0T1-W1-X",
        same_sign & (~lbx) & tbx & (~lby) & tby & (gx < fx) & (fx == ey) & (ex > ey + 2) & (ex < gy + (p - 1)) & (gy < gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-QA-L0T1-W0-X",
        same_sign & (~lbx) & tbx & lby & (~tby) & (gx < fx) & (fx == ey) & (ex > ey + 2) & (ex < gy + (p - 1)) & (gy < gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, gy),
            pos_zero)
    end

    checker("SELTZO-TwoSum-QC-ONE1-X",
        diff_sign & (~lbx) & (~tbx) & (gx == fx) & lby & tby & (gy != fy) &
        (fx == ey) & (ex < gy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, fx - 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-QB-L1T1-X",
        diff_sign & lbx & tbx & (gx == fx - 1) & lby & (~tby) & (fy < gy + 2) &
        (fx > ey) & (ex < fx + 3) & (gx < ey + 1) & (ex < gy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-QB-L0T0-X",
        same_sign & (~lbx) & (~tbx) & (gx == fx - 1) & lby & (~tby) & (fy < gy + 2) &
        (fx > ey) & (ex < fx + 3) & (gx < ey + 1) & (ex < gy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-QB-L1T0-X",
        diff_sign & lbx & (~tbx) & (gx == fx - 1) & lby & (~tby) & (fy < gy + 2) &
        (fx > ey) & (ex < fx + 3) & (gx < ey + 1) & (ex < gy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-QB-L0T1-X",
        same_sign & (~lbx) & tbx & (gx == fx - 1) & lby & (~tby) & (fy < gy + 2) &
        (fx > ey) & (ex < fx + 3) & (gx < ey + 1) & (ex < gy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, gy), pos_zero)
    end

end
