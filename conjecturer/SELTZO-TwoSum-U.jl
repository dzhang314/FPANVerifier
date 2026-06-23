function check_seltzo_two_sum_lemmas_u!(
    checker::LemmaChecker,
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
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
    x_r0r1 = (CLASS_X == R0R1)
    y_r0r1 = (CLASS_Y == R0R1)

    checker("SELTZO-TwoSum-US-L0-R0R1-X",
        same_sign & (~lbx) & (~tbx) & (~x_pow2) & y_r0r1 & (ex == ey + p) & (gx > ey + 2) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-US-L0-R0R1-A-X",
        same_sign & (~lbx) & (~tbx) & (~x_pow2) & y_r0r1 & (ex == ey + p) & (gx > ey + 2) & (fy == ey - 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-US-L0-R0R1-B-X",
        same_sign & (~lbx) & (~tbx) & (~x_pow2) & y_r0r1 & (ex == ey + p) & (gx > ey + 2) & (fy == ey - (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-US-L1-R0R1-X",
        same_sign & lbx & (~tbx) & y_r0r1 & (ex == ey + p) & (gx > ey + 2) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-US-L1-R0R1-A-X",
        same_sign & lbx & (~tbx) & y_r0r1 & (ex == ey + p) & (gx > ey + 2) & (fy == ey - 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-US-L1-R0R1-B-X",
        same_sign & lbx & (~tbx) & y_r0r1 & (ex == ey + p) & (gx > ey + 2) & (fy == ey - (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-UD-L0-R0R1-X",
        diff_sign & (~lbx) & tbx & y_r0r1 & (ex == ey + p) & (gx > ey + 2) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-UD-L0-R0R1-A-X",
        diff_sign & (~lbx) & tbx & y_r0r1 & (ex == ey + p) & (gx > ey + 2) & (fy == ey - 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-UD-L0-R0R1-B-X",
        diff_sign & (~lbx) & tbx & y_r0r1 & (ex == ey + p) & (gx > ey + 2) & (fy == ey - (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-UD-L1-R0R1-X",
        diff_sign & lbx & tbx & (~x_all1) & y_r0r1 & (ex == ey + p) & (gx > ey + 2) & (ey > fy + 2) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-UD-L1-R0R1-A-X",
        diff_sign & lbx & tbx & (~x_all1) & y_r0r1 & (ex == ey + p) & (gx > ey + 2) & (fy == ey - 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - 1, ey - (p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-UD-L1-R0R1-B-X",
        diff_sign & lbx & tbx & (~x_all1) & y_r0r1 & (ex == ey + p) & (gx > ey + 2) & (fy == ey - (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 1, 0, ey - 1, fy - 1, ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-US-L0-R1R0-X",
        same_sign & (~lbx) & (~tbx) & (~x_pow2) & y_r1r0 & (ex == ey + p) & (gx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, gy, gy - p, gy))
    end

    checker("SELTZO-TwoSum-US-L0-ALL1-X",
        same_sign & (~lbx) & (~tbx) & (~x_pow2) & y_all1 & (ex == ey + p) & (gx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-US-L1-R1R0-X",
        same_sign & lbx & (~tbx) & y_r1r0 & (ex == ey + p) & (gx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, gy, gy - p, gy))
    end

    checker("SELTZO-TwoSum-US-L1-ALL1-X",
        same_sign & lbx & (~tbx) & y_all1 & (ex == ey + p) & (gx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-US-L0-POW2R1R0-X",
        same_sign & (~lbx) & tbx & (y_pow2 | y_r1r0) & (ex == ey + p) & (gx < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, gx),
            SELTZORange(~sy, 0, 0, gy, gy - p, gy))
    end

    checker("SELTZO-TwoSum-US-L1-POW2R1R0-X",
        same_sign & lbx & tbx & (y_pow2 | y_r1r0) & (ex == ey + p) & (gx < fx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, gx),
            SELTZORange(~sy, 0, 0, gy, gy - p, gy))
    end

    checker("SELTZO-TwoSum-UD-L0-POW2R1R0-X",
        diff_sign & (~lbx) & tbx & (y_pow2 | y_r1r0) & (ex == ey + p) & (gx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, gy, gy - p, gy))
    end

    checker("SELTZO-TwoSum-UD-L0-ALL1-X",
        diff_sign & (~lbx) & tbx & y_all1 & (ex == ey + p) & (gx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

    checker("SELTZO-TwoSum-UD-L1-POW2R1R0-X",
        diff_sign & lbx & tbx & (~x_all1) & (y_pow2 | y_r1r0) & (ex == ey + p) & (gx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, gy, gy - p, gy))
    end

    checker("SELTZO-TwoSum-UD-L1-ALL1-X",
        diff_sign & lbx & tbx & (~x_all1) & y_all1 & (ex == ey + p) & (gx > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 2),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end

end
