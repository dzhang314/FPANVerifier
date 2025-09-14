module LemmaTranslation


function translate_sign_expr(expr::Symbol)
    @assert (expr == :sx) || (expr == :sy)
    return string(expr)
end


function translate_sign_expr(expr::Expr)
    @assert expr.head == :call
    @assert expr.args[1] == :(~)
    @assert length(expr.args) == 2
    return "(" * translate_sign_expr(expr.args[2]) * ",)"
end


function translate_bit_expr(expr::Int)
    if iszero(expr)
        return "0"
    elseif isone(expr)
        return "1"
    else
        @assert false
    end
end


function translate_int_expr(expr::Int)
    if expr == 1
        return "one"
    elseif expr == 2
        return "two"
    elseif expr == 3
        return "three"
    else
        @assert false
    end
end


function translate_int_expr(expr::Symbol)
    @assert expr in Symbol[:ex, :fx, :gx, :ey, :fy, :gy, :p]
    return string(expr)
end


function translate_int_expr(expr::Expr)
    @assert expr.head == :call
    if expr.args[1] == :(+)
        @assert length(expr.args) == 3
        lhs = expr.args[2]
        rhs = expr.args[3]
        if rhs isa Expr
            return translate_int_expr(lhs) * " + (" * translate_int_expr(rhs) * ")"
        else
            return translate_int_expr(lhs) * " + " * translate_int_expr(rhs)
        end
    elseif expr.args[1] == :(-)
        @assert length(expr.args) == 3
        lhs = expr.args[2]
        rhs = expr.args[3]
        if rhs isa Expr
            return translate_int_expr(lhs) * " - (" * translate_int_expr(rhs) * ")"
        else
            return translate_int_expr(lhs) * " - " * translate_int_expr(rhs)
        end
    else
        @assert false
    end
end


function translate_range_expr(expr::Symbol)
    @assert expr in Symbol[:ex, :fx, :gx, :ey, :fy, :gy]
    return string(expr)
end


function translate_range_expr(expr::Expr)
    if expr.head == :call && expr.args[1] == :(:)
        @assert length(expr.args) == 3
        start = expr.args[2]
        stop = expr.args[3]
        return ("(" * translate_int_expr(start) *
                ", " * translate_int_expr(stop) * ")")
    else
        return translate_int_expr(expr)
    end
end


function translate_hypothesis(expr::Symbol)
    @assert expr in Symbol[:same_sign, :diff_sign, :lbx, :tbx, :lby, :tby]
    return string(expr)
end


function extract_hypotheses!(result::AbstractVector, expr::Symbol)
    push!(result, expr)
    return result
end


function extract_hypotheses!(result::AbstractVector, expr::Expr)
    if (expr.head == :call) && (expr.args[1] == :&)
        for i = 2:length(expr.args)
            extract_hypotheses!(result, expr.args[i])
        end
    else
        push!(result, expr)
    end
    return result
end


function translate_hypothesis(expr::Expr)
    if (expr.head == :call) && (expr.args[1] == :(==))
        @assert length(expr.args) == 3
        lhs = expr.args[2]
        rhs = expr.args[3]
        if lhs == :cx
            return "x_" * lowercase(string(rhs))
        elseif lhs == :cy
            return "y_" * lowercase(string(rhs))
        else
            return translate_int_expr(lhs) * " == " * translate_int_expr(rhs)
        end
    elseif (expr.head == :call) && (expr.args[1] == :(<))
        @assert length(expr.args) == 3
        lhs = expr.args[2]
        rhs = expr.args[3]
        return translate_int_expr(lhs) * " < " * translate_int_expr(rhs)
    elseif (expr.head == :call) && (expr.args[1] == (:>))
        @assert length(expr.args) == 3
        lhs = expr.args[2]
        rhs = expr.args[3]
        return translate_int_expr(lhs) * " > " * translate_int_expr(rhs)
    elseif (expr.head == :call) && (expr.args[1] == :(~))
        @assert length(expr.args) == 2
        @assert expr.args[2] isa Symbol
        @assert expr.args[2] in Symbol[:lbx, :tbx, :lby, :tby]
        return "~" * string(expr.args[2])
    elseif (expr.head == :call) && (expr.args[1] == :(!=))
        @assert length(expr.args) == 3
        lhs = expr.args[2]
        @assert lhs in Symbol[:cx, :cy]
        rhs = expr.args[3]
        @assert rhs in Symbol[:POW2, :ALL1]
        return "~" * string(lhs)[2:end] * "_" * lowercase(string(rhs))
    else
        println(expr)
        @assert false
    end
end


function translate_seltzo_range(expr::Expr)
    @assert expr.head == :call
    @assert expr.args[1] == :SELTZORange
    @assert length(expr.args) == 7
    translated_args = [
        translate_sign_expr(expr.args[2]),
        translate_bit_expr(expr.args[3]),
        translate_bit_expr(expr.args[4]),
        translate_range_expr(expr.args[5]),
        translate_range_expr(expr.args[6]),
        translate_range_expr(expr.args[7]),
    ]
    return "(" * join(translated_args, ", ") * ")"
end


function translate_case(s_range::Expr, e_range::Expr)
    @assert s_range.head == :call && s_range.args[1] == :SELTZORange
    @assert e_range.head == :call && e_range.args[1] == :SELTZORange
    return ("seltzo_case(" * translate_seltzo_range(s_range) *
            ", " * translate_seltzo_range(e_range) * ")")
end


function translate_case(s_range::Expr, e_range::Symbol)
    @assert s_range.head == :call && s_range.args[1] == :SELTZORange
    @assert e_range == :pos_zero
    return ("seltzo_case_zero(" * translate_seltzo_range(s_range) * ")")
end


function translate_lemma(lemma::Expr)

    @assert lemma.head == :do
    @assert length(lemma.args) == 2
    checker_call, lemma_body = lemma.args

    @assert checker_call isa Expr
    @assert checker_call.head == :call
    @assert length(checker_call.args) == 3

    @assert checker_call.args[1] == :checker

    lemma_name = checker_call.args[2]
    @assert lemma_name isa String

    lemma_hypotheses = Union{Expr,Symbol}[]
    extract_hypotheses!(lemma_hypotheses, checker_call.args[3])

    @assert lemma_body isa Expr
    @assert lemma_body.head == :(->)
    @assert length(lemma_body.args) == 2
    @assert lemma_body.args[1] == :((lemma,))
    lemma_body = lemma_body.args[2]

    lemma_cases = Tuple{Union{Expr,Symbol},Union{Expr,Symbol}}[]
    if lemma_body.head == :block
        for expr in lemma_body.args
            if isa(expr, Expr) && expr.head == :call
                @assert expr.args[1] == :add_case!
                @assert expr.args[2] == :lemma
                @assert length(expr.args) == 4
                push!(lemma_cases, (expr.args[3], expr.args[4]))
            end
        end
    elseif isa(lemma_body, Expr) && lemma_body.head == :call
        @assert lemma_body.args[1] == :add_case!
        @assert lemma_body.args[2] == :lemma
        @assert length(lemma_body.args) == 4
        push!(lemma_cases, (lemma_body.args[3], lemma_body.args[4]))
    else
        @assert false
    end

    result = IOBuffer()
    println(result, "result[\"", lemma_name, "\"] = z3.Implies(")
    println(result, "    z3.And(",
        join(translate_hypothesis.(lemma_hypotheses), ", "), "),")
    if length(lemma_cases) == 1
        println(result, "    ", translate_case(lemma_cases[1]...), ",")
    elseif length(lemma_cases) > 1
        println(result, "    z3.Or(")
        for (i, c) in enumerate(lemma_cases)
            if i < length(lemma_cases)
                println(result, "        ", translate_case(c...), ",")
            else
                println(result, "        ", translate_case(c...))
            end
        end
        println(result, "    ),")
    else
        @assert false
    end
    print(result, ")")

    return lemma_name => String(take!(result))
end


function translate_lemmas(lemma_code::String)
    expressions = Meta.parseall(lemma_code)
    @assert (expressions isa Expr) && (expressions.head == :toplevel)
    result = Pair{String,String}[]
    for expr in expressions.args
        if (expr isa Expr) && (expr.head == :do)
            push!(result, translate_lemma(expr))
        end
    end
    return result
end


end # module LemmaTranslation
