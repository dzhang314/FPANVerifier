function check_seltzo_two_sum_lemmas_r!(
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

    checker("SELTZO-TwoSum-R-L0-X",
        (~lbx) & (~tbx) & tby & (~y_all1) &
        (gx > ey) & (ex < gy + (p - 1)) & ((fx > gx) | (same_sign & (~x_pow2)))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R-L0-Y",
        (~lby) & (~tby) & tbx & (~x_all1) &
        (gy > ex) & (ey < gx + (p - 1)) & ((fy > gy) | (same_sign & (~y_pow2)))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-R-L1-X",
        lbx & (~tbx) & tby & (~y_all1) &
        (gx > ey) & (ex < gy + (p - 1)) & ((fx > gx) | (same_sign & (fx > ey)))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-R-L1-Y",
        lby & (~tby) & tbx & (~x_all1) &
        (gy > ex) & (ey < gx + (p - 1)) & ((fy > gy) | (same_sign & (fy > ex)))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-RS-POW2-X",
        same_sign & x_pow2 & tby & (~y_all1) &
        (gx > ey + 1) & (ex < gy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-RS-POW2-Y",
        same_sign & y_pow2 & tbx & (~x_all1) &
        (gy > ex + 1) & (ey < gx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-RD-L0-X",
        diff_sign & (~lbx) & tbx & tby & (~y_all1) &
        (gx > ey) & (ex < gy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-RD-L0-Y",
        diff_sign & (~lby) & tby & tbx & (~x_all1) &
        (gy > ex) & (ey < gx + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-RD-L1-X",
        diff_sign & lbx & tbx & (~x_all1) & tby & (~y_all1) &
        (gx > ey) & (ex < gy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-RD-L1-Y",
        diff_sign & lby & tby & (~y_all1) & tbx & (~x_all1) &
        (gy > ex) & (ey < gx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-RD-A-X",
        diff_sign & (~tbx) & tby & (~y_all1) &
        (gx > ey + 1) & (ex < gy + (p - 1)) & (fx == gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-RD-A-Y",
        diff_sign & (~tby) & tbx & (~x_all1) &
        (gy > ex + 1) & (ey < gx + (p - 1)) & (fy == gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-RD-B0-X",
        diff_sign & (~tbx) & tby & (~y_all1) &
        (gx > ey) & (ex < gy + (p - 1)) & (ex > fx + 2) & (fx + 1 == gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-RD-B0-Y",
        diff_sign & (~tby) & tbx & (~x_all1) &
        (gy > ex) & (ey < gx + (p - 1)) & (ey > fy + 2) & (fy + 1 == gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-RD-B1-X",
        diff_sign & (~tbx) & tby & (~y_all1) &
        (gx > ey + 1) & (ex < gy + (p - 1)) & (ex == fx + 2) & (fx + 1 == gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-RD-B1-Y",
        diff_sign & (~tby) & tbx & (~x_all1) &
        (gy > ex + 1) & (ey < gx + (p - 1)) & (ey == fy + 2) & (fy + 1 == gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-RD-POW2-T0-X",
        diff_sign & x_pow2 & (~tby) & (~y_pow2) &
        (gx > ey + 2) & (ex < gy + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-RD-POW2-T0-Y",
        diff_sign & y_pow2 & (~tbx) & (~x_pow2) &
        (gy > ex + 2) & (ey < gx + p)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-RD-POW2-T1-X",
        diff_sign & x_pow2 & tby & (~y_all1) &
        (gx > ey + 2) & (ex < gy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-RD-POW2-T1-Y",
        diff_sign & y_pow2 & tbx & (~x_all1) &
        (gy > ex + 2) & (ey < gx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-RD-ALL1-X",
        diff_sign & x_all1 & tby & (~y_all1) &
        (gx > ey + 1) & (ex < gy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-RD-ALL1-Y",
        diff_sign & y_all1 & tbx & (~x_all1) &
        (gy > ex + 1) & (ey < gx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

end
