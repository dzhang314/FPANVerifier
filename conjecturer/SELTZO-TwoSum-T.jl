function check_seltzo_two_sum_lemmas_t!(
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

    # Lemmas in family T apply to situations where the smaller addend
    # fits entirely inside the trailing bits of the larger addend.

    #=

    # Larger addend has leading zeros (general case).
    checker("SELTZO-TwoSum-TS-L0-G-X",
        same_sign & (~lbx) & (~tbx) & (cx != POW2) & (~tby) &
        (ex > ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-TS-L0-G-Y",
        same_sign & (~lby) & (~tby) & (cy != POW2) & (~tbx) &
        (ey > ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex, gy), pos_zero)
    end

    # Larger addend has leading zeros (adjacent case 1).
    checker("SELTZO-TwoSum-TS-L0-A1-X",
        same_sign & (~lbx) & (~tbx) & (cx != POW2) & lby & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fy, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-TS-L0-A1-Y",
        same_sign & (~lby) & (~tby) & (cy != POW2) & lbx & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fx, gy), pos_zero)
    end

    # Larger addend has leading zeros (adjacent case 2).
    checker("SELTZO-TwoSum-TS-L0-A2-X",
        same_sign & (~lbx) & (~tbx) & (cx != POW2) & (~lby) & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey - 1, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-TS-L0-A2-Y",
        same_sign & (~lby) & (~tby) & (cy != POW2) & (~lbx) & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex - 1, gy), pos_zero)
    end

    # Larger addend has leading ones (general case).
    checker("SELTZO-TwoSum-TS-L1-G-X",
        same_sign & (~lbx) & tbx & (~tby) &
        (ex > ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-TS-L1-G-Y",
        same_sign & (~lby) & tby & (~tbx) &
        (ey > ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex, gy), pos_zero)
    end

    # Larger addend has leading ones (adjacent case 1).
    checker("SELTZO-TwoSum-TS-L1-A1-X",
        same_sign & (~lbx) & tbx & lby & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, fy, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-TS-L1-A1-Y",
        same_sign & (~lby) & tby & lbx & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, fx, gy), pos_zero)
    end

    # Larger addend has leading ones (adjacent case 2).
    checker("SELTZO-TwoSum-TS-L1-A2-X",
        same_sign & (~lbx) & tbx & (~lby) & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey - 1, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-TS-L1-A2-Y",
        same_sign & (~lby) & tby & (~lbx) & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex - 1, gy), pos_zero)
    end

    # Larger addend has leading zeros (general case).
    checker("SELTZO-TwoSum-TD-L0-G-X",
        diff_sign & lbx & (~tbx) & (~tby) &
        (ex > ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-TD-L0-G-Y",
        diff_sign & lby & (~tby) & (~tbx) &
        (ey > ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex, gy), pos_zero)
    end

    # Larger addend has leading zeros (adjacent case 1).
    checker("SELTZO-TwoSum-TD-L0-A1-X",
        diff_sign & lbx & (~tbx) & lby & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, fy, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-TD-L0-A1-Y",
        diff_sign & lby & (~tby) & lbx & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, fx, gy), pos_zero)
    end

    # Larger addend has leading zeros (adjacent case 2).
    checker("SELTZO-TwoSum-TD-L0-A2-X",
        diff_sign & lbx & (~tbx) & (~lby) & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 0, ex, ey - 1, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-TD-L0-A2-Y",
        diff_sign & lby & (~tby) & (~lbx) & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 0, ey, ex - 1, gy), pos_zero)
    end

    # Larger addend has leading ones (general case).
    checker("SELTZO-TwoSum-TD-L1-G-X",
        diff_sign & lbx & tbx & (cx != ALL1) & (~tby) &
        (ex > ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 1, ex, ey, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-TD-L1-G-Y",
        diff_sign & lby & tby & (cy != ALL1) & (~tbx) &
        (ey > ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 1, ey, ex, gy), pos_zero)
    end

    # Larger addend has leading ones (adjacent case 1).
    checker("SELTZO-TwoSum-TD-L1-A1-X",
        diff_sign & lbx & tbx & (cx != ALL1) & lby & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, fy, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-TD-L1-A1-Y",
        diff_sign & lby & tby & (cy != ALL1) & lbx & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, fx, gy), pos_zero)
    end

    # Larger addend has leading ones (adjacent case 2).
    checker("SELTZO-TwoSum-TD-L1-A2-X",
        diff_sign & lbx & tbx & (cx != ALL1) & (~lby) & (~tby) &
        (ex == ey + 1) & (gy > fx + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 0, 1, ex, ey - 1, gx), pos_zero)
    end
    checker("SELTZO-TwoSum-TD-L1-A2-Y",
        diff_sign & lby & tby & (cy != ALL1) & (~lbx) & (~tbx) &
        (ey == ex + 1) & (gx > fy + 1)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 0, 1, ey, ex - 1, gy), pos_zero)
    end

    =#

end
