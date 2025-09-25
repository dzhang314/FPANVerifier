using BFloat16s: BFloat16
using CRC32c: crc32c
using Printf: @printf

push!(LOAD_PATH, @__DIR__)
using FloatAbstractions


function FloatAbstractions.two_prod(x::BFloat16, y::BFloat16)
    p64 = Float64(x) * Float64(y)
    p16 = BFloat16(p64)
    e64 = p64 - Float64(p16)
    e16 = BFloat16(e64)
    return (p16, e16)
end


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

    filename = "$abstraction_name-$op-$T.bin"
    if !isfile(filename)
        println("Generating $filename...")
        flush(stdout)
        if op === :TwoSum
            enumerate_abstractions(TwoSumAbstraction{A}, T, filename, 64)
        elseif op === :TwoProd
            enumerate_abstractions(TwoProdAbstraction{A}, T, filename, 64)
        else
            error("Unknown operation: $op (expected :TwoSum or :TwoProd)")
        end
    end

    println("Verifying $filename...")
    flush(stdout)

    if !isfile(filename)
        println("ERROR: $filename not found.")
        flush(stdout)
        return nothing
    end

    actual_size = filesize(filename)
    if op === :TwoSum
        expected_size = expected_count * sizeof(TwoSumAbstraction{A})
        if actual_size !== expected_size
            println("ERROR: Size of $filename is incorrect.")
            println("Expected size: $expected_size bytes")
            println("Actual size: $actual_size bytes")
            flush(stdout)
        end
    elseif op === :TwoProd
        expected_size = expected_count * sizeof(TwoProdAbstraction{A})
        if actual_size !== expected_size
            println("ERROR: Size of $filename is incorrect.")
            println("Expected size: $expected_size bytes")
            println("Actual size: $actual_size bytes")
            flush(stdout)
        end
    else
        error("Unknown operation: $op (expected :TwoSum or :TwoProd)")
    end

    actual_crc = open(crc32c, filename)
    if actual_crc === expected_crc
        println("Successfully verified $filename.")
        flush(stdout)
    else
        println("ERROR: Contents of $filename are incorrect.")
        @printf("Expected CRC: 0x%08X\n", expected_crc)
        @printf("Actual CRC: 0x%08X\n", actual_crc)
        flush(stdout)
    end

    return nothing
end


if abspath(PROGRAM_FILE) == @__FILE__

    generate_abstraction_data(SEAbstraction, :TwoSum, Float16,
        38_638, 0x18557287)
    generate_abstraction_data(SEAbstraction, :TwoSum, BFloat16,
        548_026, 0xB20B9481)
    generate_abstraction_data(SEAbstraction, :TwoProd, Float16,
        62_524, 0x194E7F4D)
    generate_abstraction_data(SEAbstraction, :TwoProd, BFloat16,
        6_053_588, 0x89B01463)

    generate_abstraction_data(SETZAbstraction, :TwoSum, Float16,
        3_833_700, 0x66E6D552)
    generate_abstraction_data(SETZAbstraction, :TwoSum, BFloat16,
        26_618_866, 0x1DB442CF)
    generate_abstraction_data(SETZAbstraction, :TwoProd, Float16,
        11_454_024, 0x8182FE97)
    generate_abstraction_data(SETZAbstraction, :TwoProd, BFloat16,
        313_420_440, 0x897409CD)

    generate_abstraction_data(SELTZOAbstraction, :TwoSum, Float16,
        319_985_950, 0xCC55FA4F)
    generate_abstraction_data(SELTZOAbstraction, :TwoSum, BFloat16,
        1_172_449_766, 0xCB0D263C)
    generate_abstraction_data(SELTZOAbstraction, :TwoProd, Float16,
        1_273_864_440, 0x00AD2611)
    generate_abstraction_data(SELTZOAbstraction, :TwoProd, BFloat16,
        3_125_792_780, 0x6D14D426)

end
