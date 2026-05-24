module LemmaTranslation


const SELTZO_CLASSES = Symbol[
    :ZERO, :POW2, :ALL1,
    :R0R1, :R1R0,
    :ONE0, :ONE1,
    :TWO0, :TWO1, :MM01, :MM10,
    :G00, :G01, :G10, :G11,
]


function translate_class_hypothesis(lhs::Symbol, rhs::Symbol)
    @assert (lhs == :CLASS_X) || (lhs == :CLASS_Y)
    @assert rhs in SELTZO_CLASSES
    return (lhs == :CLASS_X ? "x_" : "y_") * lowercase(string(rhs))
end


function translate_sign_expr(expr::Symbol)
    @assert (expr == :sx) || (expr == :sy)
    return string(expr)
end


function translate_sign_expr(expr::Expr)
    @assert expr.head == :call
    @assert length(expr.args) == 2
    @assert expr.args[1] == :(~)
    return "~" * translate_sign_expr(expr.args[2])
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


const HYPOTHESIS_SYMBOLS = Symbol[
    :same_sign, :diff_sign, :lbx, :tbx, :lby, :tby,
    :x_pow2, :y_pow2, :x_all1, :y_all1,
]


function translate_hypothesis(expr::Symbol)
    @assert expr in HYPOTHESIS_SYMBOLS
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
        return (lhs == :CLASS_X) || (lhs == :CLASS_Y) ?
               translate_class_hypothesis(lhs, rhs) :
               translate_int_expr(lhs) * " == " * translate_int_expr(rhs)
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
        @assert expr.args[2] in HYPOTHESIS_SYMBOLS
        return "~" * string(expr.args[2])
    elseif (expr.head == :call) && (expr.args[1] == :(!=))
        @assert length(expr.args) == 3
        return "~" * translate_class_hypothesis(expr.args[2], expr.args[3])
    else
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


function translate_tuple(items::AbstractVector{<:AbstractString})
    if isempty(items)
        return "()"
    elseif isone(length(items))
        return "(" * only(items) * ",)"
    else
        return "(" * join(items, ", ") * ")"
    end
end


function translate_output(symbol::Symbol)
    @assert symbol == :pos_zero
    return "0"
end


function translate_output(expr::Expr)
    @assert expr.head == :call && expr.args[1] == :SELTZORange
    return translate_seltzo_range(expr)
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
    @assert !isempty(lemma_cases)
    zero_error = all(e == :pos_zero for (_, e) in lemma_cases)
    println(result, "result[\"", lemma_name,
        zero_error ? "\"] = seltzo_lemma_zero_error(" : "\"] = seltzo_lemma(")
    println(result, "    ",
        translate_tuple(translate_hypothesis.(lemma_hypotheses)), ",")
    for (s_range, e_range) in lemma_cases
        println(result, "    ", translate_output(s_range), ",")
        if !zero_error
            println(result, "    ", translate_output(e_range), ",")
        end
    end
    print(result, ")")

    return String(take!(result))
end


function is_lemma(expr::Expr)
    if (expr.head != :do) || (length(expr.args) != 2)
        return false
    end
    checker_call = expr.args[1]
    return (checker_call isa Expr) &&
           (checker_call.head == :call) &&
           (length(checker_call.args) == 3) &&
           (checker_call.args[1] == :checker)
end


extract_lemmas!(result::AbstractVector{<:AbstractString}, ::Any) = result


function extract_lemmas!(result::AbstractVector{<:AbstractString}, expr::Expr)
    if is_lemma(expr)
        push!(result, translate_lemma(expr))
    else
        for arg in expr.args
            extract_lemmas!(result, arg)
        end
    end
    return result
end


function main(args::AbstractVector{<:AbstractString}=ARGS)
    for path in args
        lemmas = extract_lemmas!(String[], Meta.parseall(read(path, String)))
        for lemma in lemmas
            println(lemma)
        end
    end
    return 0
end


end # module LemmaTranslation


if abspath(PROGRAM_FILE) == @__FILE__
    exit(LemmaTranslation.main())
end
