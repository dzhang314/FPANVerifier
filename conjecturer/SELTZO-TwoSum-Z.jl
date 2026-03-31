function check_seltzo_two_sum_lemmas_z!(
    checker::LemmaChecker,
    x::SELTZOAbstraction,
    y::SELTZOAbstraction,
    ::Type{T},
) where {T<:AbstractFloat}

    pos_zero = SELTZOAbstraction(+zero(T))
    neg_zero = SELTZOAbstraction(-zero(T))
    x_zero = (x == pos_zero) | (x == neg_zero)
    y_zero = (y == pos_zero) | (y == neg_zero)

    checker("SELTZO-TwoSum-Z1-PP", (x == pos_zero) & (y == pos_zero)) do lemma
        add_case!(lemma, pos_zero, pos_zero)
    end
    checker("SELTZO-TwoSum-Z1-PN", (x == pos_zero) & (y == neg_zero)) do lemma
        add_case!(lemma, pos_zero, pos_zero)
    end
    checker("SELTZO-TwoSum-Z1-NP", (x == neg_zero) & (y == pos_zero)) do lemma
        add_case!(lemma, pos_zero, pos_zero)
    end
    checker("SELTZO-TwoSum-Z1-NN", (x == neg_zero) & (y == neg_zero)) do lemma
        add_case!(lemma, neg_zero, pos_zero)
    end

    checker("SELTZO-TwoSum-Z2-X", y_zero & !x_zero) do lemma
        add_case!(lemma, x, pos_zero)
    end
    checker("SELTZO-TwoSum-Z2-Y", x_zero & !y_zero) do lemma
        add_case!(lemma, y, pos_zero)
    end

end
