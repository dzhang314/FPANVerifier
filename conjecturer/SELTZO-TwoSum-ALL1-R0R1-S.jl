function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
    ::Val{R0R1},
    ::Val{SAME_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ALL1-R0R1-S1-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex > fy + (p + 1)) & (ex < ey + (p - 2)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ex + 1, ey, ey),
            SELTZORange(~sy, 1, 0, ex - p, fy, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-S1-Y",
        (CLASS_X == R0R1) & (CLASS_Y == ALL1) &
        (ey > fx + (p + 1)) & (ey < ex + (p - 2)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 0, ey + 1, ex, ex),
            SELTZORange(~sy, 1, 0, ey - p, fx, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-S2-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex < fy + (p - 1)) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ex + 1, ey, fy + 1),
            SELTZORange(sy, 1, 0, ex - p, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-S2-Y",
        (CLASS_X == R0R1) & (CLASS_Y == ALL1) &
        (ey < fx + (p - 1)) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 0, 1, ey + 1, ex, fx + 1),
            SELTZORange(sy, 1, 0, ey - p, ex - p, ex - (p - 1)))
    end

end
