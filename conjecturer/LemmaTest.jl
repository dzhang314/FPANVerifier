using Base.Threads
using BFloat16s: BFloat16
using CRC32c: crc32c
using JLD2

push!(LOAD_PATH, @__DIR__)
using FloatAbstractions


function test_seltzo_two_sum_lemmas(
    two_sum_abstractions::Vector{TwoSumAbstraction{SELTZOAbstraction}},
    ::Type{T},
) where {T<:AbstractFloat}

    ± = false:true
    p = precision(T)
    pos_zero = SELTZOAbstraction(+zero(T))
    neg_zero = SELTZOAbstraction(-zero(T))
    abstract_inputs = enumerate_abstractions(SELTZOAbstraction, T)
    lemma_counts = Dict{String,Int}()

    locks = SpinLock[SpinLock() for _ = 1:nthreads()]
    buffers = Vector{Tuple{SELTZOAbstraction,SELTZOAbstraction}}[
        Tuple{SELTZOAbstraction,SELTZOAbstraction}[] for _ = 1:nthreads()]
    num_successes = Atomic{Int}(0)

    @threads :dynamic for x in abstract_inputs
        for y in abstract_inputs

            sx, lbx, lby, ex, fx, gx = unpack(x, T)
            sy, tbx, tby, ey, fy, gy = unpack(y, T)
            if abs(ex - ey) > (p + 1)
                continue
            end

            x_zero = (x == pos_zero) | (x == neg_zero)
            y_zero = (y == pos_zero) | (y == neg_zero)
            if x_zero | y_zero
                continue
            end

            checker = LemmaChecker(two_sum_abstractions, x, y, T, lemma_counts)

            #! format: off
            try
                success = checker() do lemma
                    add_case!(lemma, (false, false, false, ex, fx-1:fx, gy+1:fy-1), pos_zero)
                    add_case!(lemma, (false, false, false, ex, fx-1:fx, fy+1), pos_zero)
                end
                if success
                    tid = threadid()
                    lock(locks[tid]) do
                        push!(buffers[tid], (x, y))
                    end
                    val = atomic_add!(num_successes, 1) + 1
                    if val % 1000 == 0
                        println(val)
                    end
                end
            catch e
                if !(e isa DomainError)
                    rethrow()
                end
            end
            #! format: on

        end
    end

    save_object("$T.jld2", sort!(reduce(vcat, buffers)))
    println("$T: $(num_successes[])")

    return nothing
end


function main(
    file_name::String,
    expected_count::Int,
    expected_crc::UInt32,
    ::Type{T},
) where {T<:AbstractFloat}

    @assert isfile(file_name)
    @assert filesize(file_name) ===
            expected_count * sizeof(TwoSumAbstraction{SELTZOAbstraction})
    @assert open(crc32c, file_name) === expected_crc
    two_sum_abstractions =
        Vector{TwoSumAbstraction{SELTZOAbstraction}}(undef, expected_count)
    read!(file_name, two_sum_abstractions)
    test_seltzo_two_sum_lemmas(two_sum_abstractions, T)
    println("Successfully checked all SELTZO-TwoSum-$T lemmas.")
    flush(stdout)

    return nothing
end


if abspath(PROGRAM_FILE) == @__FILE__
    main("SELTZO-TwoSum-Float16.bin", 319_985_950, 0xCC55FA4F, Float16)
    main("SELTZO-TwoSum-BFloat16.bin", 1_172_449_766, 0xCB0D263C, BFloat16)
end
