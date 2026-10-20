function check_seltzo_two_sum_lemmas_z!(
    checker::LemmaChecker,
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T}

    pos_zero = SELTZOAbstraction(zero(T))
    neg_zero = SELTZOAbstraction(-zero(T))
    sx = signbit(x)
    sy = signbit(y)
    x_zero = (x == pos_zero) | (x == neg_zero)
    y_zero = (y == pos_zero) | (y == neg_zero)

    checker("SELTZO-TwoSum-Z1-P", x_zero & y_zero & !(sx & sy)) do lemma
        add_case!(lemma, pos_zero, pos_zero)
    end
    checker("SELTZO-TwoSum-Z1-N", x_zero & y_zero & sx & sy) do lemma
        add_case!(lemma, neg_zero, pos_zero)
    end

    checker("SELTZO-TwoSum-Z2-X", y_zero & !x_zero) do lemma
        add_case!(lemma, x, pos_zero)
    end
    checker("SELTZO-TwoSum-Z2-Y", x_zero & !y_zero) do lemma
        add_case!(lemma, y, pos_zero)
    end

end
