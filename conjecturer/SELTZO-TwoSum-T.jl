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

    checker("SELTZO-TwoSum-TS0-G00-X",
        same_sign & (~lbx) & (~tbx) & (~x_pow2) & (~tby) &
        (gx > ey) & (ex < gy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-TS0-G00-Y",
        same_sign & (~lby) & (~tby) & (~y_pow2) & (~tbx) &
        (gy > ex) & (ey < gx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-TS0-G01-X",
        (~lbx) & (~tbx) & tby & (~y_all1) &
        (gx > ey) & (ex < gy + (p - 1)) & ((fx > gx) | (same_sign & (~x_pow2)))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TS0-G01-Y",
        (~lby) & (~tby) & tbx & (~x_all1) &
        (gy > ex) & (ey < gx + (p - 1)) & ((fy > gy) | (same_sign & (~y_pow2)))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TS0-G10-X",
        same_sign & lbx & (~tbx) & (~tby) &
        (gx > ey) & (ex < gy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-TS0-G10-Y",
        same_sign & lby & (~tby) & (~tbx) &
        (gy > ex) & (ey < gx + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-TS0-G11-X",
        lbx & (~tbx) & tby & (~y_all1) &
        (gx > ey) & (ex < gy + (p - 1)) & ((fx > gx) | (same_sign & (fx > ey)))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TS0-G11-Y",
        lby & (~tby) & tbx & (~x_all1) &
        (gy > ex) & (ey < gx + (p - 1)) & ((fy > gy) | (same_sign & (fy > ex)))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TS0-A00-X",
        same_sign & lbx & (~tbx) & (~lby) & (~tby) &
        (gx == ey + 1) & (ex < gy + (p - 1)) & (fx == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-TS0-A00-Y",
        same_sign & lby & (~tby) & (~lbx) & (~tbx) &
        (gy == ex + 1) & (ey < gx + (p - 1)) & (fy == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-TS0-A01-X",
        same_sign & (~tbx) & (~lby) & tby &
        (gx == ey + 1) & (ex < gy + (p - 1)) & (fx < gx) & (ey > gy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey - 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TS0-A01-Y",
        same_sign & (~tby) & (~lbx) & tbx &
        (gy == ex + 1) & (ey < gx + (p - 1)) & (fy < gy) & (ex > gx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex - 1, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TS0-A10-X",
        same_sign & lbx & (~tbx) & lby & (~tby) &
        (gx == ey + 1) & (ex < gy + (p - 1)) & (fx == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-TS0-A10-Y",
        same_sign & lby & (~tby) & lbx & (~tbx) &
        (gy == ex + 1) & (ey < gx + (p - 1)) & (fy == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-TS0-B0-X",
        same_sign & (~lbx) & (~tbx) & (y_pow2 | y_r1r0) &
        (gx > ey + 1) & (ex == gy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TS0-B0-Y",
        same_sign & (~lby) & (~tby) & (x_pow2 | x_r1r0) &
        (gy > ex + 1) & (ey == gx + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TS0-B1-X",
        same_sign & lbx & (~tbx) & (y_pow2 | y_r1r0) &
        (gx > ey + 1) & (ex == gy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TS0-B1-Y",
        same_sign & lby & (~tby) & (x_pow2 | x_r1r0) &
        (gy > ex + 1) & (ey == gx + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TS0-ALL1-L0-X",
        same_sign & (~lbx) & (~tbx) & (~x_pow2) & y_all1 &
        (gx > ey + 1) & (ex < gy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TS0-ALL1-L0-Y",
        same_sign & (~lby) & (~tby) & (~y_pow2) & x_all1 &
        (gy > ex + 1) & (ey < gx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TS0-ALL1-L1-X",
        same_sign & lbx & (~tbx) & y_all1 &
        (gx > ey + 1) & (ex < gy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TS0-ALL1-L1-Y",
        same_sign & lby & (~tby) & x_all1 &
        (gy > ex + 1) & (ey < gx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TS0-R1R0-L0-X",
        same_sign & (~lbx) & (~tbx) & (~x_pow2) & y_r1r0 &
        (gx > ey + 1) & (ex > gy + (p - 1)) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, gy, gy - p, gy))
    end
    checker("SELTZO-TwoSum-TS0-R1R0-L0-Y",
        same_sign & (~lby) & (~tby) & (~y_pow2) & x_r1r0 &
        (gy > ex + 1) & (ey > gx + (p - 1)) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, gx, gx - p, gx))
    end

    checker("SELTZO-TwoSum-TS0-R1R0-L1-X",
        same_sign & lbx & (~tbx) & y_r1r0 &
        (gx > ey + 1) & (ex > gy + (p - 1)) & (fx > ey + 1) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, gy, gy - p, gy))
    end
    checker("SELTZO-TwoSum-TS0-R1R0-L1-Y",
        same_sign & lby & (~tby) & x_r1r0 &
        (gy > ex + 1) & (ey > gx + (p - 1)) & (fy > ex + 1) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, gx, gx - p, gx))
    end

    checker("SELTZO-TwoSum-TS1-L0-X",
        same_sign & (~lbx) & tbx & (~lby) & (~tby) &
        (gx == ey + 1) & (ex == gy + (p - 1)) & (fx > gx) & (fy < gy + 2) & (fy != gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, gy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TS1-L0-Y",
        same_sign & (~lby) & tby & (~lbx) & (~tbx) &
        (gy == ex + 1) & (ey == gx + (p - 1)) & (fy > gy) & (fx < gx + 2) & (fx != gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, gx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TS1-L1-X",
        same_sign & lbx & tbx & (~lby) & (~tby) &
        (gx == ey + 1) & (ex == gy + (p - 1)) & (fx > gx) & (fy < gy + 2) & (fy != gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, gy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TS1-L1-Y",
        same_sign & lby & tby & (~lbx) & (~tbx) &
        (gy == ex + 1) & (ey == gx + (p - 1)) & (fy > gy) & (fx < gx + 2) & (fx != gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, gx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TD0-L0-X",
        diff_sign & (~lbx) & (~tbx) & (~lby) & (~tby) &
        (gx == ey + 1) & (ex == gy + (p - 1)) & (fx > gx) & (fy < gy + 2) & (gy != fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, gy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TD0-L0-Y",
        diff_sign & (~lby) & (~tby) & (~lbx) & (~tbx) &
        (gy == ex + 1) & (ey == gx + (p - 1)) & (fy > gy) & (fx < gx + 2) & (gx != fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, gx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TD0-L1-X",
        diff_sign & lbx & (~tbx) & (~lby) & (~tby) &
        (gx == ey + 1) & (ex == gy + (p - 1)) & (fx > gx) & (fy < gy + 2) & (gy != fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, gy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TD0-L1-Y",
        diff_sign & lby & (~tby) & (~lbx) & (~tbx) &
        (gy == ex + 1) & (ey == gx + (p - 1)) & (fy > gy) & (fx < gx + 2) & (gx != fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, gx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TD0-A-X",
        diff_sign & (~tbx) & tby & (~y_all1) &
        (gx > ey + 1) & (ex < gy + (p - 1)) & (fx == gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx - 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TD0-A-Y",
        diff_sign & (~tby) & tbx & (~x_all1) &
        (gy > ex + 1) & (ey < gx + (p - 1)) & (fy == gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy - 1, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TD0-B0-X",
        diff_sign & (~tbx) & tby & (~y_all1) &
        (gx > ey) & (ex < gy + (p - 1)) & (ex > fx + 2) & (fx + 1 == gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TD0-B0-Y",
        diff_sign & (~tby) & tbx & (~x_all1) &
        (gy > ex) & (ey < gx + (p - 1)) & (ey > fy + 2) & (fy + 1 == gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TD0-B1-X",
        diff_sign & (~tbx) & tby & (~y_all1) &
        (gx > ey + 1) & (ex < gy + (p - 1)) & (ex == fx + 2) & (fx + 1 == gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TD0-B1-Y",
        diff_sign & (~tby) & tbx & (~x_all1) &
        (gy > ex + 1) & (ey < gx + (p - 1)) & (ey == fy + 2) & (fy + 1 == gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TD1-G00-X",
        diff_sign & (~lbx) & tbx & (~tby) &
        (gx > ey) & (ex < gy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fx, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-TD1-G00-Y",
        diff_sign & (~lby) & tby & (~tbx) &
        (gy > ex) & (ey < gx + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fy, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-TD1-G01-X",
        diff_sign & (~lbx) & tbx & tby & (~y_all1) &
        (gx > ey) & (ex < gy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TD1-G01-Y",
        diff_sign & (~lby) & tby & tbx & (~x_all1) &
        (gy > ex) & (ey < gx + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TD1-G10-X",
        diff_sign & lbx & tbx & (~x_all1) & (~tby) &
        (gx > ey) & (ex < gy + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fx, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-TD1-G10-Y",
        diff_sign & lby & tby & (~y_all1) & (~tbx) &
        (gy > ex) & (ey < gx + (p - 1))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fy, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-TD1-G11-X",
        diff_sign & lbx & tbx & (~x_all1) & tby & (~y_all1) &
        (gx > ey) & (ex < gy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TD1-G11-Y",
        diff_sign & lby & tby & (~y_all1) & tbx & (~x_all1) &
        (gy > ex) & (ey < gx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TD1-A00-X",
        diff_sign & (~lbx) & tbx & (~lby) & (~tby) &
        (gx == ey + 1) & (ex < gy + (p - 1)) & (fx == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-TD1-A00-Y",
        diff_sign & (~lby) & tby & (~lbx) & (~tbx) &
        (gy == ex + 1) & (ey < gx + (p - 1)) & (fy == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-TD1-A01-X",
        diff_sign & (~lbx) & tbx & (~lby) & tby &
        (gx == ey + 1) & (ex < gy + (p - 1)) & (fx == ey) & (ey > gy + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey - 1, gy),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TD1-A01-Y",
        diff_sign & (~lby) & tby & (~lbx) & tbx &
        (gy == ex + 1) & (ey < gx + (p - 1)) & (fy == ex) & (ex > gx + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex - 1, gx),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TD1-A10-X",
        diff_sign & (~lbx) & tbx & lby & (~tby) &
        (gx == ey + 1) & (ex < gy + (p - 1)) & (fx == ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-TD1-A10-Y",
        diff_sign & (~lby) & tby & lbx & (~tbx) &
        (gy == ex + 1) & (ey < gx + (p - 1)) & (fy == ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx, gx), pos_zero)
    end

    checker("SELTZO-TwoSum-TD1-B0-X",
        diff_sign & (~lbx) & tbx & (y_pow2 | y_r1r0) &
        (gx > ey + 1) & (ex == gy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fx, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TD1-B0-Y",
        diff_sign & (~lby) & tby & (x_pow2 | x_r1r0) &
        (gy > ex + 1) & (ey == gx + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fy, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TD1-B1-X",
        diff_sign & lbx & tbx & (y_pow2 | y_r1r0) &
        (gx > ey + 1) & (ex == gy + (p - 1)) & (fx > ey)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx, ey + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-TD1-B1-Y",
        diff_sign & lby & tby & (x_pow2 | x_r1r0) &
        (gy > ex + 1) & (ey == gx + (p - 1)) & (fy > ex)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy, ex + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-TD1-ALL1-L0-X",
        diff_sign & (~lbx) & tbx & y_all1 &
        (gx > ey + 1) & (ex < gy + p) & (fx > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TD1-ALL1-L0-Y",
        diff_sign & (~lby) & tby & x_all1 &
        (gy > ex + 1) & (ey < gx + p) & (fy > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TD1-ALL1-L1-X",
        diff_sign & lbx & tbx & (~x_all1) & y_all1 &
        (gx > ey + 1) & (ex < gy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-TD1-ALL1-L1-Y",
        diff_sign & lby & tby & (~y_all1) & x_all1 &
        (gy > ex + 1) & (ey < gx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-TD1-R1R0-L0-X",
        diff_sign & (~lbx) & tbx & y_r1r0 &
        (gx > ey + 1) & (ex > gy + p) & (fx > ey + 1) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, gy, gy - p, gy))
    end
    checker("SELTZO-TwoSum-TD1-R1R0-L0-Y",
        diff_sign & (~lby) & tby & x_r1r0 &
        (gy > ex + 1) & (ey > gx + p) & (fy > ex + 1) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, gx, gx - p, gx))
    end

    checker("SELTZO-TwoSum-TD1-R1R0-L1-X",
        diff_sign & lbx & tbx & (~x_all1) & y_r1r0 &
        (gx > ey + 1) & (ex > gy + p) & (ex < ey + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, fx, ey + 1),
            SELTZORange(~sy, 0, 0, gy, gy - p, gy))
    end
    checker("SELTZO-TwoSum-TD1-R1R0-L1-Y",
        diff_sign & lby & tby & (~y_all1) & x_r1r0 &
        (gy > ex + 1) & (ey > gx + p) & (ey < ex + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, fy, ex + 1),
            SELTZORange(~sx, 0, 0, gx, gx - p, gx))
    end

    checker("SELTZO-TwoSum-TD1-R1R0-B0-X",
        diff_sign & (~lbx) & tbx & y_r1r0 &
        (gx > ey + 1) & (ex == gy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, gy, gy - p, gy))
    end
    checker("SELTZO-TwoSum-TD1-R1R0-B0-Y",
        diff_sign & (~lby) & tby & x_r1r0 &
        (gy > ex + 1) & (ey == gx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, gx, gx - p, gx))
    end

    checker("SELTZO-TwoSum-TD1-R1R0-B1-X",
        diff_sign & lbx & tbx & (~x_all1) & y_r1r0 &
        (gx > ey + 1) & (ex == gy + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx, ey + 1),
            SELTZORange(sy, 0, 0, gy, gy - p, gy))
    end
    checker("SELTZO-TwoSum-TD1-R1R0-B1-Y",
        diff_sign & lby & tby & (~y_all1) & x_r1r0 &
        (gy > ex + 1) & (ey == gx + p)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy, ex + 1),
            SELTZORange(sx, 0, 0, gx, gx - p, gx))
    end

end
