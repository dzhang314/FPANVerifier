function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{ALL1},
    ::Val{R0R1},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-ALL1-R0R1-D1-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex > fy + p) & (ex < ey + (p - 1)) & (ey < fy + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, ey),
            SELTZORange(sy, 1, 0, fy, ey - p, ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-D1-Y",
        (CLASS_X == R0R1) & (CLASS_Y == ALL1) &
        (ey > fx + p) & (ey < ex + (p - 1)) & (ex < fx + (p - 1))
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 1, ey, ex, ex),
            SELTZORange(~sy, 1, 0, fx, ex - p, ex - (p - 1)))
    end

    checker("SELTZO-TwoSum-ALL1-R0R1-D2-X",
        (CLASS_X == ALL1) & (CLASS_Y == R0R1) &
        (ex < fy + p) & (ex > ey + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 1, ex, ey, fy + 1),
            SELTZORange(~sy, 0, 0, ey - (p - 1), ey - (p + p - 1), ey - (p - 1)))
    end
    checker("SELTZO-TwoSum-ALL1-R0R1-D2-Y",
        (CLASS_X == R0R1) & (CLASS_Y == ALL1) &
        (ey < fx + p) & (ey > ex + 1)
    ) do lemma
        add_case!(lemma,
            SELTZORange(~sx, 1, 1, ey, ex, fx + 1),
            SELTZORange(sy, 0, 0, ex - (p - 1), ex - (p + p - 1), ex - (p - 1)))
    end

end
