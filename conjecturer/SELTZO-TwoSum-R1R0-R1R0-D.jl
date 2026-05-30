function check_seltzo_two_sum_lemmas!(
    checker::LemmaChecker,
    ::Val{R1R0},
    ::Val{R1R0},
    ::Val{DIFF_SIGN},
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    sx, lbx, tbx, ex, fx, gx = unpack(x, T)
    sy, lby, tby, ey, fy, gy = unpack(y, T)

    checker("SELTZO-TwoSum-R1R0-R1R0-D1-X",
        (CLASS_X == R1R0) & (CLASS_Y == R1R0) &
        (ex < fy + p) & (fx < ey) & (ex > ey + 2) & (fx > fy)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, ey + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D1-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R1R0) &
        (ey < fx + p) & (fy < ex) & (ey > ex + 2) & (fy > fx)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, ex + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D2-X",
        (CLASS_X == R1R0) & (CLASS_Y == R1R0) &
        (ex < fy + p) & (fx + 1 > ey) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sx, 1, 0, ex, fx + 1, fy + 1), pos_zero)
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D2-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R1R0) &
        (ey < fx + p) & (fy + 1 > ex) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma, SELTZORange(sy, 1, 0, ey, fy + 1, fx + 1), pos_zero)
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D3-X",
        (CLASS_X == R1R0) & (CLASS_Y == R1R0) &
        (ex > fy + p) & (fx < ey) & (ex > ey + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, ey + 1, fx + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D3-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R1R0) &
        (ey > fx + p) & (fy < ex) & (ey > ex + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, ex + 1, fy + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

    checker("SELTZO-TwoSum-R1R0-R1R0-D4-X",
        (CLASS_X == R1R0) & (CLASS_Y == R1R0) &
        (ex > fy + p) & (fx > ey) & (ex < ey + p) & (ex > fx + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sx, 1, 0, ex, fx + 1, ey + 1),
            SELTZORange(~sy, 0, 0, fy + 1, fy - (p - 1), fy + 1))
    end
    checker("SELTZO-TwoSum-R1R0-R1R0-D4-Y",
        (CLASS_Y == R1R0) & (CLASS_X == R1R0) &
        (ey > fx + p) & (fy > ex) & (ey < ex + p) & (ey > fy + 2)
    ) do lemma
        add_case!(lemma,
            SELTZORange(sy, 1, 0, ey, fy + 1, ex + 1),
            SELTZORange(~sx, 0, 0, fx + 1, fx - (p - 1), fx + 1))
    end

end
