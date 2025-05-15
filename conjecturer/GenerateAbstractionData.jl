using BFloat16s
using CRC32c

push!(LOAD_PATH, @__DIR__)
using FloatAbstractions


function generate_abstraction_data(
    ::Type{A},
    op::Symbol,
    ::Type{T},
    expected_count::Int,
    expected_crc::UInt32,
) where {A<:FloatAbstraction,T<:AbstractFloat}

    abstraction_name = string(A)
    @assert endswith(abstraction_name, "Abstraction")
    abstraction_name = abstraction_name[begin:end-length("Abstraction")]

    file_name = "$abstraction_name-$op-$T.bin"
    if !isfile(file_name)
        println("Generating $file_name...")
        flush(stdout)
        if op === :TwoSum
            open(file_name, "w") do io
                write(io, two_sum_abstractions(A, T))
            end
        elseif op === :TwoProd
            open(file_name, "w") do io
                write(io, two_prod_abstractions(A, T))
            end
        else
            error("Unknown operation: $op (expected :TwoSum or :TwoProd)")
        end
    end

    println("Verifying $file_name...")
    flush(stdout)
    @assert isfile(file_name)
    file_size = filesize(file_name)
    if op === :TwoSum
        @assert file_size === expected_count * sizeof(TwoSumAbstraction{A})
    elseif op === :TwoProd
        @assert file_size === expected_count * sizeof(TwoProdAbstraction{A})
    else
        error("Unknown operation: $op (expected :TwoSum or :TwoProd)")
    end
    @assert open(crc32c, file_name) === expected_crc

    println("Successfully verified $file_name.")
    flush(stdout)
    return nothing

end


if abspath(PROGRAM_FILE) == @__FILE__

    generate_abstraction_data(SEAbstraction, :TwoSum, Float16,
        38_638, 0x18557287)
    generate_abstraction_data(SEAbstraction, :TwoSum, BFloat16,
        548_026, 0xB20B9481)
    generate_abstraction_data(SEAbstraction, :TwoProd, Float16,
        62_524, 0x194E7F4D)
    # generate_abstraction_data(SEAbstraction, :TwoProd, BFloat16, ?, ?)

    generate_abstraction_data(SETZAbstraction, :TwoSum, Float16,
        3_833_700, 0x66E6D552)
    generate_abstraction_data(SETZAbstraction, :TwoSum, BFloat16,
        26_618_866, 0x1DB442CF)
    generate_abstraction_data(SETZAbstraction, :TwoProd, Float16,
        11_454_024, 0x8182FE97)
    # generate_abstraction_data(SETZAbstraction, :TwoProd, BFloat16, ?, ?)

    generate_abstraction_data(SELTZOAbstraction, :TwoSum, Float16,
        319_985_950, 0xCC55FA4F)
    generate_abstraction_data(SELTZOAbstraction, :TwoSum, BFloat16,
        1_172_449_766, 0xCB0D263C)
    generate_abstraction_data(SELTZOAbstraction, :TwoProd, Float16,
        1_273_864_440, 0x00AD2611)
    # generate_abstraction_data(SELTZOAbstraction, :TwoProd, BFloat16, ?, ?)

end
