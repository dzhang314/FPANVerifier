function check_seltzo_two_sum_lemmas_l!(
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

    # Lemmas in family L apply to situations where the smaller addend
    # fits entirely inside the leading bits of the larger addend.

    checker("SELTZO-TwoSum-LS-T00-X",
        same_sign & (~lbx) & (~tbx) & (~tby) &
        (ex > ey + 1) & (fx < gy) & (gx < gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LS-T00-Y",
        same_sign & (~lby) & (~tby) & (~tbx) &
        (ey > ex + 1) & (fy < gx) & (gy < gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-LS-T01-X",
        same_sign & (~lbx) & (~tbx) & tby & (~y_all1) &
        (ex > ey + 1) & (fx < gy) & (gx < gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex, ey, gx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-LS-T01-Y",
        same_sign & (~lby) & (~tby) & tbx & (~x_all1) &
        (ey > ex + 1) & (fy < gx) & (gy < gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 0, ey, ex, gy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-LS-T10-X",
        same_sign & (~lbx) & tbx & (~tby) &
        (ex > ey + 1) & (fx < gy) & (gx < gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LS-T10-Y",
        same_sign & (~lby) & tby & (~tbx) &
        (ey > ex + 1) & (fy < gx) & (gy < gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-LS-T11-X",
        same_sign & (~lbx) & tbx & tby & (~y_all1) &
        (ex > ey + 1) & (fx < gy) & (gx < gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex, ey, gx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-LS-T11-Y",
        same_sign & (~lby) & tby & tbx & (~x_all1) &
        (ey > ex + 1) & (fy < gx) & (gy < gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 0, 1, ey, ex, gy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-LS-A00-X",
        same_sign & (~lbx) & (~tbx) & (~lby) & (~tby) &
        (ex == ey + 1) & (fx < gy) & (gx < gy) & (~y_pow2 | (fx + 1 < gy))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LS-A00-Y",
        same_sign & (~lby) & (~tby) & (~lbx) & (~tbx) &
        (ey == ex + 1) & (fy < gx) & (gy < gx) & (~x_pow2 | (fy + 1 < gx))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-LS-A01-X",
        same_sign & (~lbx) & (~tbx) & lby & (~tby) &
        (ex == ey + 1) & (fx < gy) & (gx < gy) & (fx < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LS-A01-Y",
        same_sign & (~lby) & (~tby) & lbx & (~tbx) &
        (ey == ex + 1) & (fy < gx) & (gy < gx) & (fy < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-LS-A10-X",
        same_sign & (~lbx) & tbx & (~lby) & (~tby) &
        (ex == ey + 1) & (fx < gy) & (gx < gy) & (~y_pow2 | (fx + 1 < gy))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LS-A10-Y",
        same_sign & (~lby) & tby & (~lbx) & (~tbx) &
        (ey == ex + 1) & (fy < gx) & (gy < gx) & (~x_pow2 | (fy + 1 < gx))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-LS-A11-X",
        same_sign & (~lbx) & tbx & lby & (~tby) &
        (ex == ey + 1) & (fx < gy) & (gx < gy) & (fx < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LS-A11-Y",
        same_sign & (~lby) & tby & lbx & (~tbx) &
        (ey == ex + 1) & (fy < gx) & (gy < gx) & (fy < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-LD-L0-T00-X",
        diff_sign & (~lbx) & (~tbx) & (~x_pow2) & lby & (~tby) &
        (ex > ey + 2) & (fx < gy) & (gx < ey + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LD-L0-T00-Y",
        diff_sign & (~lby) & (~tby) & (~y_pow2) & lbx & (~tbx) &
        (ey > ex + 2) & (fy < gx) & (gy < ex + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-LD-L0-T01-X",
        diff_sign & (~lbx) & (~tbx) & (~x_pow2) & tby &
        (ex > ey + 2) & (fx < gy) & (gx < ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, gx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-LD-L0-T01-Y",
        diff_sign & (~lby) & (~tby) & (~y_pow2) & tbx &
        (ey > ex + 2) & (fy < gx) & (gy < ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, gy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-LD-L0-T10-X",
        diff_sign & (~lbx) & tbx & lby & (~tby) &
        (ex > ey + 2) & (fx < gy) & (gx < ey + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)), pos_zero)
    end
    checker("SELTZO-TwoSum-LD-L0-T10-Y",
        diff_sign & (~lby) & tby & lbx & (~tbx) &
        (ey > ex + 2) & (fy < gx) & (gy < ex + 3)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)), pos_zero)
    end

    checker("SELTZO-TwoSum-LD-L0-T11-X",
        diff_sign & (~lbx) & tbx & tby &
        (ex > ey + 2) & (fx < gy) & (gx < ey + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex - 1, ey, ex - (p - 1)),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-LD-L0-T11-Y",
        diff_sign & (~lby) & tby & tbx &
        (ey > ex + 2) & (fy < gx) & (gy < ex + 3)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey - 1, ex, ey - (p - 1)),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-LD-L1-T00-X",
        diff_sign & lbx & (~tbx) & (~tby) &
        (ex > ey + 1) & (fx < gy) & (gx < gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LD-L1-T00-Y",
        diff_sign & lby & (~tby) & (~tbx) &
        (ey > ex + 1) & (fy < gx) & (gy < gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-LD-L1-T01-X",
        diff_sign & lbx & (~tbx) & tby & (~y_all1) &
        (ex > ey + 1) & (fx < gy) & (gx < gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey, gx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-LD-L1-T01-Y",
        diff_sign & lby & (~tby) & tbx & (~x_all1) &
        (ey > ex + 1) & (fy < gx) & (gy < gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex, gy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-LD-L1-T10-X",
        diff_sign & lbx & tbx & (~tby) &
        (ex > ey + 1) & (fx < gy) & (gx < gy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LD-L1-T10-Y",
        diff_sign & lby & tby & (~tbx) &
        (ey > ex + 1) & (fy < gx) & (gy < gx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-LD-L1-T11-X",
        diff_sign & lbx & tbx & tby & (~y_all1) &
        (ex > ey + 1) & (fx < gy) & (gx < gy)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, gx),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-LD-L1-T11-Y",
        diff_sign & lby & tby & tbx & (~x_all1) &
        (ey > ex + 1) & (fy < gx) & (gy < gx)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 1, ey, ex, gy),
            SELTZORange(~sx, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-LD-A00-X",
        diff_sign & lbx & (~tbx) & (~lby) & (~tby) &
        (ex == ey + 1) & (fx < gy) & (gx < gy) & (~y_pow2 | (fx + 1 < gy))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LD-A00-Y",
        diff_sign & lby & (~tby) & (~lbx) & (~tbx) &
        (ey == ex + 1) & (fy < gx) & (gy < gx) & (~x_pow2 | (fy + 1 < gx))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-LD-A01-X",
        diff_sign & lbx & (~tbx) & lby & (~tby) &
        (ex == ey + 1) & (fx < gy) & (gx < gy) & (fx < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fy, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LD-A01-Y",
        diff_sign & lby & (~tby) & lbx & (~tbx) &
        (ey == ex + 1) & (fy < gx) & (gy < gx) & (fy < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fx, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-LD-A10-X",
        diff_sign & lbx & tbx & (~lby) & (~tby) &
        (ex == ey + 1) & (fx < gy) & (gx < gy) & (~y_pow2 | (fx + 1 < gy))
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LD-A10-Y",
        diff_sign & lby & tby & (~lbx) & (~tbx) &
        (ey == ex + 1) & (fy < gx) & (gy < gx) & (~x_pow2 | (fy + 1 < gx))
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, gy), pos_zero)
    end

    checker("SELTZO-TwoSum-LD-A11-X",
        diff_sign & lbx & tbx & lby & (~tby) &
        (ex == ey + 1) & (fx < gy) & (gx < gy) & (fx < fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LD-A11-Y",
        diff_sign & lby & tby & lbx & (~tbx) &
        (ey == ex + 1) & (fy < gx) & (gy < gx) & (fy < fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx, gy), pos_zero)
    end

end
