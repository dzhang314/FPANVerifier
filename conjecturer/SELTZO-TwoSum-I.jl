function check_seltzo_two_sum_lemmas_i!(
    checker::LemmaChecker,
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    p = precision(T)
    ex = unsafe_exponent(x)
    ey = unsafe_exponent(y)
    tbx = mantissa_trailing_bit(x)
    tby = mantissa_trailing_bit(y)
    same_sign = (signbit(x) == signbit(y))
    x_pow2 = (CLASS_X == POW2)
    y_pow2 = (CLASS_Y == POW2)

    checker("SELTZO-TwoSum-I-X",
        (ex > ey + (p + 1)) |
        ((ex == ey + (p + 1)) & (y_pow2 | same_sign | !x_pow2)) |
        ((ex == ey + p) & y_pow2 & (same_sign | !x_pow2) & (~tbx))
    ) do lemma
        add_case!(lemma, x, y)
    end
    checker("SELTZO-TwoSum-I-Y",
        (ey > ex + (p + 1)) |
        ((ey == ex + (p + 1)) & (x_pow2 | same_sign | !y_pow2)) |
        ((ey == ex + p) & x_pow2 & (same_sign | !y_pow2) & (~tby))
    ) do lemma
        add_case!(lemma, y, x)
    end

end
