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
    x_r1r0 = (CLASS_X == R1R0)
    y_r1r0 = (CLASS_Y == R1R0)

    ############################################################################

    # Larger addend has leading zeros (boundary case).
    checker("SELTZO-TwoSum-TS-L0-B-X",
        same_sign & (~lbx) & (~tbx) & (~x_pow2) & (y_pow2 | y_r1r0) &
        (fx > ey) & (gx > ey + 1) & (ex == gy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, ey + 1), pos_zero)
    end

    # Larger addend has leading ones (adjacent leading 0).
    checker("SELTZO-TwoSum-TS-L1-A0-X",
        same_sign & lbx & (~tbx) & (~lby) & (~tby) &
        (fx == ey) & (ex < gy + (p - 1)) & (gx == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, gy), pos_zero)
    end

    # Larger addend has leading ones (adjacent leading 1).
    checker("SELTZO-TwoSum-TS-L1-A1-X",
        same_sign & lbx & (~tbx) & lby & (~tby) &
        (fx == ey) & (ex < gy + (p - 1)) & (gx == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy, gy), pos_zero)
    end

    # Larger addend has leading ones (boundary case).
    checker("SELTZO-TwoSum-TS-L1-B-X",
        same_sign & lbx & (~tbx) & (y_pow2 | y_r1r0) &
        (fx > ey) & (gx > ey + 1) & (ex == gy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, ey + 1), pos_zero)
    end

    # Larger addend has leading zeros (adjacent leading 0).
    checker("SELTZO-TwoSum-TD-L0-A0-X",
        diff_sign & (~lbx) & tbx & (~lby) & (~tby) &
        (fx == ey) & (ex < gy + (p - 1)) & (gx == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, gy), pos_zero)
    end

    # Larger addend has leading zeros (adjacent leading 1).
    checker("SELTZO-TwoSum-TD-L0-A1-X",
        diff_sign & (~lbx) & tbx & lby & (~tby) &
        (fx == ey) & (ex < gy + (p - 1)) & (gx == fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy, gy), pos_zero)
    end

    # Larger addend has leading zeros (boundary case).
    checker("SELTZO-TwoSum-TD-L0-B-X",
        diff_sign & (~lbx) & tbx & (y_pow2 | y_r1r0) &
        (fx > ey) & (gx > ey + 1) & (ex == gy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey + 1), pos_zero)
    end

    # Larger addend has leading ones (boundary case).
    checker("SELTZO-TwoSum-TD-L1-B-X",
        diff_sign & lbx & tbx & (~x_all1) & (y_pow2 | y_r1r0) &
        (fx > ey) & (gx > ey + 1) & (ex == gy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TD-L0-BU-X",
        diff_sign & (~lbx) & (~tbx) & (gx < fx) & (gx == ey + 1) &
        (~lby) & (~tby) & (fy < gy + 2) & (gy != fy) & (gy == ex - (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, gy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TD-L1-BU-X",
        diff_sign & lbx & (~tbx) & (gx < fx) & (gx == ey + 1) &
        (~lby) & (~tby) & (fy < gy + 2) & (gy != fy) & (gy == ex - (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, gy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TS-L0-BU-X",
        same_sign & (~lbx) & tbx & (gx < fx) & (gx == ey + 1) &
        (~lby) & (~tby) & (fy < gy + 2) & (gy != fy) & (gy == ex - (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, gy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TS-L1-BU-X",
        same_sign & lbx & tbx & (gx < fx) & (gx == ey + 1) &
        (~lby) & (~tby) & (fy < gy + 2) & (gy != fy) & (gy == ex - (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, gy + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-RD-A-X",
        diff_sign & (~tbx) & tby & (~y_all1) &
        (gx > ey + 1) & (ex < gy + (p - 1)) & (fx == gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-RD-B0-X",
        diff_sign & (~tbx) & tby & (~y_all1) &
        (gx > ey) & (ex < gy + (p - 1)) & (ex > fx + 2) & (fx + 1 == gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-RD-B1-X",
        diff_sign & (~tbx) & tby & (~y_all1) &
        (gx > ey + 1) & (ex < gy + (p - 1)) & (ex == fx + 2) & (fx + 1 == gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-RS-L0-R1R0-X",
        same_sign & (~lbx) & (~tbx) & (~x_pow2) & y_r1r0 &
        (ex > gy + (p - 1)) & (ex < ey + p) & (gx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, gy, gy - p, gy))
    end

    checker("SELTZO-TwoSum-RS-L0-ALL1-X",
        same_sign & (~lbx) & (~tbx) & (~x_pow2) & y_all1 &
        (ex < ey + p) & (gx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-RS-L1-R1R0-X",
        same_sign & lbx & (~tbx) & y_r1r0 &
        (ex > gy + (p - 1)) & (ex < ey + p) & (gx > ey + 1) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, gy, gy - p, gy))
    end

    checker("SELTZO-TwoSum-RS-L1-ALL1-X",
        same_sign & lbx & (~tbx) & y_all1 &
        (ex < ey + p) & (gx > ey + 1) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-RD-L0-R1R0-X",
        diff_sign & (~lbx) & tbx & y_r1r0 &
        (ex > gy + p) & (ex < ey + p) & (gx > ey + 1) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, gy, gy - p, gy))
    end

    checker("SELTZO-TwoSum-RD-L0-ALL1-X",
        diff_sign & (~lbx) & tbx & y_all1 &
        (ex < ey + p) & (gx > ey + 1) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-RD-L1-R1R0-X",
        diff_sign & lbx & tbx & (~x_all1) & y_r1r0 &
        (ex > gy + p) & (ex < ey + p) & (gx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, gy, gy - p, gy))
    end

    checker("SELTZO-TwoSum-RD-L1-ALL1-X",
        diff_sign & lbx & tbx & (~x_all1) & y_all1 &
        (ex < ey + p) & (gx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-RD-L0-R1R0-A-X",
        diff_sign & (~lbx) & tbx & y_r1r0 &
        (ex == gy + p) & (gx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, gy, gy - p, gy))
    end

    checker("SELTZO-TwoSum-RD-L1-R1R0-A-X",
        diff_sign & lbx & tbx & (~x_all1) & y_r1r0 &
        (ex == gy + p) & (gx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, gy, gy - p, gy))
    end

    checker("SELTZO-TwoSum-RS-A-X",
        same_sign & (~tbx) & tby & (~lby) &
        (gx == ey + 1) & (ex < gy + (p - 1)) & (fx == ey) & (gy + 1 < ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

end
