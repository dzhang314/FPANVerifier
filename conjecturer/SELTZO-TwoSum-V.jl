function check_seltzo_two_sum_lemmas_v!(
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

    checker("SELTZO-TwoSum-VS-G00-X",
        same_sign & (~lbx) & (~tbx) & (~tby) &
        (fx == ey) & (ex > ey + 2) & (ex < gy + (p - 1)) & (gx > gy) & (fx + 1 > gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx + 1, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-VS-G00-Y",
        same_sign & (~lby) & (~tby) & (~tbx) &
        (fy == ex) & (ey > ex + 2) & (ey < gx + (p - 1)) & (gy > gx) & (fy + 1 > gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy + 1, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-VS-G01-X",
        same_sign & (~lbx) & (~tbx) & tby &
        (fx == ey) & (ex > ey + 2) & (ex < gy + (p - 1)) & (gx > gy) & (fx + 1 > gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx + 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-VS-G01-Y",
        same_sign & (~lby) & (~tby) & tbx &
        (fy == ex) & (ey > ex + 2) & (ey < gx + (p - 1)) & (gy > gx) & (fy + 1 > gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy + 1, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-VS-G10-X",
        same_sign & (~lbx) & tbx & (~tby) &
        (fx == ey) & (ex > ey + 2) & (ex < gy + (p - 1)) & (gx > gy) & (fx > gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx + 1, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-VS-G10-Y",
        same_sign & (~lby) & tby & (~tbx) &
        (fy == ex) & (ey > ex + 2) & (ey < gx + (p - 1)) & (gy > gx) & (fy > gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy + 1, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-VS-G11-X",
        same_sign & (~lbx) & tbx & tby &
        (fx == ey) & (ex > ey + 2) & (ex < gy + (p - 1)) & (gx > gy) & (fx > gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx + 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-VS-G11-Y",
        same_sign & (~lby) & tby & tbx &
        (fy == ex) & (ey > ex + 2) & (ey < gx + (p - 1)) & (gy > gx) & (fy > gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy + 1, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-VD-G00-X",
        diff_sign & lbx & (~tbx) & (~tby) &
        (fx == ey) & (ex > ey + 2) & (ex < gy + (p - 1)) & (gx > gy) & (fx > gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-VD-G00-Y",
        diff_sign & lby & (~tby) & (~tbx) &
        (fy == ex) & (ey > ex + 2) & (ey < gx + (p - 1)) & (gy > gx) & (fy > gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-VD-G01-X",
        diff_sign & lbx & (~tbx) & tby &
        (fx == ey) & (ex > ey + 2) & (ex < gy + (p - 1)) & (gx > gy) & (fx > gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-VD-G01-Y",
        diff_sign & lby & (~tby) & tbx &
        (fy == ex) & (ey > ex + 2) & (ey < gx + (p - 1)) & (gy > gx) & (fy > gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-VD-G10-X",
        diff_sign & lbx & tbx & (~tby) &
        (fx == ey) & (ex > ey + 2) & (ex < gy + (p - 1)) & (gx > gy) & (fx + 1 > gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx + 1, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-VD-G10-Y",
        diff_sign & lby & tby & (~tbx) &
        (fy == ex) & (ey > ex + 2) & (ey < gx + (p - 1)) & (gy > gx) & (fy + 1 > gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy + 1, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-VD-G11-X",
        diff_sign & lbx & tbx & tby &
        (fx == ey) & (ex > ey + 2) & (ex < gy + (p - 1)) & (gx > gy) & (fx + 1 > gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx + 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-VD-G11-Y",
        diff_sign & lby & tby & tbx &
        (fy == ex) & (ey > ex + 2) & (ey < gx + (p - 1)) & (gy > gx) & (fy + 1 > gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy + 1, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

end
