function check_seltzo_two_sum_lemmas_l!(
    checker::LemmaChecker,
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

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

    # Larger addend is a power of two (general case).
    checker("SELTZO-TwoSum-LS-POW2-G-X",
        same_sign & x_pow2 & (~tby) &
        (ex > ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-LS-POW2-G-Y",
        same_sign & y_pow2 & (~tbx) &
        (ey > ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gx), pos_zero)
    end

    # Larger addend is a power of two (adjacent case 1).
    checker("SELTZO-TwoSum-LS-POW2-A1-X",
        same_sign & x_pow2 & lby & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-LS-POW2-A1-Y",
        same_sign & y_pow2 & lbx & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx, gx), pos_zero)
    end

    # Larger addend is a power of two (adjacent case 2).
    checker("SELTZO-TwoSum-LS-POW2-A2-X",
        same_sign & x_pow2 & (~lby) & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-LS-POW2-A2-Y",
        same_sign & y_pow2 & (~lbx) & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, gx), pos_zero)
    end

    # Larger addend has trailing zeros (general case).
    checker("SELTZO-TwoSum-LS-T0-G-X",
        same_sign & (~lbx) & (~tbx) & (~x_pow2) & (~tby) &
        (ex > ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LS-T0-G-Y",
        same_sign & (~lby) & (~tby) & (~y_pow2) & (~tbx) &
        (ey > ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gy), pos_zero)
    end

    # Larger addend has trailing zeros (adjacent case 1).
    checker("SELTZO-TwoSum-LS-T0-A1-X",
        same_sign & (~lbx) & (~tbx) & (~x_pow2) & lby & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LS-T0-A1-Y",
        same_sign & (~lby) & (~tby) & (~y_pow2) & lbx & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx, gy), pos_zero)
    end

    # Larger addend has trailing zeros (adjacent case 2).
    checker("SELTZO-TwoSum-LS-T0-A2-X",
        same_sign & (~lbx) & (~tbx) & (~x_pow2) & (~lby) & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LS-T0-A2-Y",
        same_sign & (~lby) & (~tby) & (~y_pow2) & (~lbx) & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, gy), pos_zero)
    end

    # Larger addend has trailing ones (general case).
    checker("SELTZO-TwoSum-LS-T1-G-X",
        same_sign & (~lbx) & tbx & (~tby) &
        (ex > ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LS-T1-G-Y",
        same_sign & (~lby) & tby & (~tbx) &
        (ey > ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, gy), pos_zero)
    end

    # Larger addend has trailing ones (adjacent case 1).
    checker("SELTZO-TwoSum-LS-T1-A1-X",
        same_sign & (~lbx) & tbx & lby & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LS-T1-A1-Y",
        same_sign & (~lby) & tby & lbx & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx, gy), pos_zero)
    end

    # Larger addend has trailing ones (adjacent case 2).
    checker("SELTZO-TwoSum-LS-T1-A2-X",
        same_sign & (~lbx) & tbx & (~lby) & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LS-T1-A2-Y",
        same_sign & (~lby) & tby & (~lbx) & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, gy), pos_zero)
    end

    # Larger addend is an all-ones number (general case).
    checker("SELTZO-TwoSum-LD-ALL1-G-X",
        diff_sign & x_all1 & (~tby) &
        (ex > ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-LD-ALL1-G-Y",
        diff_sign & y_all1 & (~tbx) &
        (ey > ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, gx), pos_zero)
    end

    # Larger addend is an all-ones number (adjacent case 1).
    checker("SELTZO-TwoSum-LD-ALL1-A1-X",
        diff_sign & x_all1 & lby & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-LD-ALL1-A1-Y",
        diff_sign & y_all1 & lbx & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx, gx), pos_zero)
    end

    # Larger addend is an all-ones number (adjacent case 2).
    checker("SELTZO-TwoSum-LD-ALL1-A2-X",
        diff_sign & x_all1 & (~lby) & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, gy), pos_zero)
    end
    checker("SELTZO-TwoSum-LD-ALL1-A2-Y",
        diff_sign & y_all1 & (~lbx) & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, gx), pos_zero)
    end

    # Larger addend has trailing zeros (general case).
    checker("SELTZO-TwoSum-LD-T0-G-X",
        diff_sign & lbx & (~tbx) & (~tby) &
        (ex > ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LD-T0-G-Y",
        diff_sign & lby & (~tby) & (~tbx) &
        (ey > ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, gy), pos_zero)
    end

    # Larger addend has trailing zeros (adjacent case 1).
    checker("SELTZO-TwoSum-LD-T0-A1-X",
        diff_sign & lbx & (~tbx) & lby & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fy, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LD-T0-A1-Y",
        diff_sign & lby & (~tby) & lbx & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fx, gy), pos_zero)
    end

    # Larger addend has trailing zeros (adjacent case 2).
    checker("SELTZO-TwoSum-LD-T0-A2-X",
        diff_sign & lbx & (~tbx) & (~lby) & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LD-T0-A2-Y",
        diff_sign & lby & (~tby) & (~lbx) & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, gy), pos_zero)
    end

    # Larger addend has trailing ones (general case).
    checker("SELTZO-TwoSum-LD-T1-G-X",
        diff_sign & lbx & tbx & (~x_all1) & (~tby) &
        (ex > ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LD-T1-G-Y",
        diff_sign & lby & tby & (~y_all1) & (~tbx) &
        (ey > ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, gy), pos_zero)
    end

    # Larger addend has trailing ones (adjacent case 1).
    checker("SELTZO-TwoSum-LD-T1-A1-X",
        diff_sign & lbx & tbx & (~x_all1) & lby & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LD-T1-A1-Y",
        diff_sign & lby & tby & (~y_all1) & lbx & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx, gy), pos_zero)
    end

    # Larger addend has trailing ones (adjacent case 2).
    checker("SELTZO-TwoSum-LD-T1-A2-X",
        diff_sign & lbx & tbx & (~x_all1) & (~lby) & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-LD-T1-A2-Y",
        diff_sign & lby & tby & (~y_all1) & (~lbx) & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, gy), pos_zero)
    end

end
