using Base.Threads: @threads
using BFloat16s: BFloat16, NaNB16
using CRC32c: crc32c
using Printf: @printf

push!(LOAD_PATH, @__DIR__)
using FloatAbstractions


# Julia 1.12+ flushes subnormal BFloat16s to zero by default. This code
# restores correct IEEE semantics, which is necessary for our analysis.
@inline function _bf16_no_ftz(x::Float32)
    h = reinterpret(UInt32, x)
    h += 0x7fff + ((h >> 16) & one(h))
    result = reinterpret(BFloat16, (h >> 16) % UInt16)
    return ifelse(isnan(x), NaNB16, result)
end

@inline _bf16_no_ftz(x::Float64) = _bf16_no_ftz(Float32(x))

@inline _sub_no_ftz(x::BFloat16, y::BFloat16) =
    _bf16_no_ftz(Float32(x) - Float32(y))

@inline _add_no_ftz(x::BFloat16, y::BFloat16) =
    _bf16_no_ftz(Float32(x) + Float32(y))

@inline function FloatAbstractions.two_sum(x::BFloat16, y::BFloat16)
    s = _add_no_ftz(x, y)
    x_prime = _sub_no_ftz(s, y)
    y_prime = _sub_no_ftz(s, x_prime)
    x_err = _sub_no_ftz(x, x_prime)
    y_err = _sub_no_ftz(y, y_prime)
    e = _add_no_ftz(x_err, y_err)
    return (s, e)
end

# BFloat16 to Float64 conversion is broken on Julia 1.11 due to an LLVM 16 bug.
@static if v"16" <= Base.libllvm_version < v"17"
    @noinline _fp64(x::BFloat16) = Float64(Float32(x))
else
    @inline _fp64(x::BFloat16) = Float64(x)
end

@inline function FloatAbstractions.two_prod(x::BFloat16, y::BFloat16)
    p64 = _fp64(x) * _fp64(y)
    p16 = _bf16_no_ftz(p64)
    e64 = p64 - _fp64(p16)
    e16 = _bf16_no_ftz(e64)
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


function generate_seltzo_data(
    op::Symbol,
    ::Type{T},
    expected_count::Dict{Tuple{SELTZOClass,SELTZOClass},Int},
    expected_crc::Dict{Tuple{SELTZOClass,SELTZOClass},UInt32},
) where {T<:AbstractFloat}

    class_pairs = [
        (cx, cy)
        for cx in instances(SELTZOClass)
        for cy in instances(SELTZOClass)]

    @threads for (cx, cy) in class_pairs

        filename = "SELTZO-$op-$T-$cx-$cy.bin"
        if !isfile(filename)
            println("Generating $filename...")
            flush(stdout)
            if op === :TwoSum
                open(filename, "w") do io
                    write(io, enumerate_abstractions(
                        TwoSumAbstraction{SELTZOAbstraction}, T, cx, cy))
                end
            elseif op === :TwoProd
                open(filename, "w") do io
                    write(io, enumerate_abstractions(
                        TwoProdAbstraction{SELTZOAbstraction}, T, cx, cy))
                end
            else
                error("Unknown operation: $op (expected :TwoSum or :TwoProd)")
            end
        end

        println("Verifying $filename...")
        flush(stdout)

        if !isfile(filename)
            println("ERROR: $filename not found.")
            flush(stdout)
            continue
        end

        actual_size = filesize(filename)
        if op === :TwoSum
            expected_size = expected_count[(cx, cy)] * sizeof(
                TwoSumAbstraction{SELTZOAbstraction})
            if actual_size !== expected_size
                println("ERROR: Size of $filename is incorrect.")
                println("Expected size: $expected_size bytes")
                println("Actual size: $actual_size bytes")
                flush(stdout)
            end
        elseif op === :TwoProd
            expected_size = expected_count[(cx, cy)] * sizeof(
                TwoProdAbstraction{SELTZOAbstraction})
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
        if actual_crc === expected_crc[(cx, cy)]
            println("Successfully verified $filename.")
            flush(stdout)
        else
            println("ERROR: Contents of $filename are incorrect.")
            @printf("Expected CRC: 0x%08X\n", expected_crc[(cx, cy)])
            @printf("Actual CRC: 0x%08X\n", actual_crc)
            flush(stdout)
        end

    end

    return nothing
end


const SELTZO_TWO_SUM_F16_COUNT = Dict{Tuple{SELTZOClass,SELTZOClass},Int}(
    (ZERO, ZERO) => 4, (ZERO, POW2) => 120, (ZERO, ALL1) => 120,
    (ZERO, R0R1) => 1080, (ZERO, R1R0) => 1080, (ZERO, ONE0) => 960,
    (ZERO, ONE1) => 960, (ZERO, TWO0) => 840, (ZERO, TWO1) => 840,
    (ZERO, MM01) => 840, (ZERO, MM10) => 840, (ZERO, G00) => 2520,
    (ZERO, G01) => 2520, (ZERO, G10) => 2520, (ZERO, G11) => 2520,
    (POW2, ZERO) => 120, (POW2, POW2) => 3598, (POW2, ALL1) => 3002,
    (POW2, R0R1) => 28920, (POW2, R1R0) => 30864, (POW2, ONE0) => 25184,
    (POW2, ONE1) => 27512, (POW2, TWO0) => 22190, (POW2, TWO1) => 24066,
    (POW2, MM01) => 23898, (POW2, MM10) => 22778, (POW2, G00) => 189214,
    (POW2, G01) => 183600, (POW2, G10) => 196522, (POW2, G11) => 187968,
    (ALL1, ZERO) => 120, (ALL1, POW2) => 3002, (ALL1, ALL1) => 2894,
    (ALL1, R0R1) => 25514, (ALL1, R1R0) => 26430, (ALL1, ONE0) => 22866,
    (ALL1, ONE1) => 23592, (ALL1, TWO0) => 20036, (ALL1, TWO1) => 20622,
    (ALL1, MM01) => 20524, (ALL1, MM10) => 19994, (ALL1, G00) => 175932,
    (ALL1, G01) => 171324, (ALL1, G10) => 179824, (ALL1, G11) => 175958,
    (R0R1, ZERO) => 1080, (R0R1, POW2) => 28920, (R0R1, ALL1) => 25530,
    (R0R1, R0R1) => 236698, (R0R1, R1R0) => 248284, (R0R1, ONE0) => 209744,
    (R0R1, ONE1) => 222584, (R0R1, TWO0) => 184360, (R0R1, TWO1) => 194836,
    (R0R1, MM01) => 191946, (R0R1, MM10) => 186462, (R0R1, G00) => 1650354,
    (R0R1, G01) => 1603012, (R0R1, G10) => 1699104, (R0R1, G11) => 1639006,
    (R1R0, ZERO) => 1080, (R1R0, POW2) => 30864, (R1R0, ALL1) => 26448,
    (R1R0, R0R1) => 248284, (R1R0, R1R0) => 264114, (R1R0, ONE0) => 217908,
    (R1R0, ONE1) => 236320, (R1R0, TWO0) => 191870, (R1R0, TWO1) => 206650,
    (R1R0, MM01) => 204274, (R1R0, MM10) => 195506, (R1R0, G00) => 1790482,
    (R1R0, G01) => 1723294, (R1R0, G10) => 1851800, (R1R0, G11) => 1777952,
    (ONE0, ZERO) => 960, (ONE0, POW2) => 25184, (ONE0, ALL1) => 22880,
    (ONE0, R0R1) => 209744, (ONE0, R1R0) => 217908, (ONE0, ONE0) => 187552,
    (ONE0, ONE1) => 194584, (ONE0, TWO0) => 164594, (ONE0, TWO1) => 170330,
    (ONE0, MM01) => 169028, (ONE0, MM10) => 164918, (ONE0, G00) => 1515080,
    (ONE0, G01) => 1478844, (ONE0, G10) => 1575626, (ONE0, G11) => 1541240,
    (ONE1, ZERO) => 960, (ONE1, POW2) => 27512, (ONE1, ALL1) => 23592,
    (ONE1, R0R1) => 222584, (ONE1, R1R0) => 236320, (ONE1, ONE0) => 194584,
    (ONE1, ONE1) => 211900, (ONE1, TWO0) => 171508, (ONE1, TWO1) => 185162,
    (ONE1, MM01) => 183060, (ONE1, MM10) => 175266, (ONE1, G00) => 1543740,
    (ONE1, G01) => 1483242, (ONE1, G10) => 1588472, (ONE1, G11) => 1516096,
    (TWO0, ZERO) => 840, (TWO0, POW2) => 22190, (TWO0, ALL1) => 20048,
    (TWO0, R0R1) => 184360, (TWO0, R1R0) => 191870, (TWO0, ONE0) => 164594,
    (TWO0, ONE1) => 171508, (TWO0, TWO0) => 144906, (TWO0, TWO1) => 150092,
    (TWO0, MM01) => 148568, (TWO0, MM10) => 145086, (TWO0, G00) => 1370130,
    (TWO0, G01) => 1333436, (TWO0, G10) => 1420724, (TWO0, G11) => 1389954,
    (TWO1, ZERO) => 840, (TWO1, POW2) => 24066, (TWO1, ALL1) => 20636,
    (TWO1, R0R1) => 194836, (TWO1, R1R0) => 206650, (TWO1, ONE0) => 170330,
    (TWO1, ONE1) => 185162, (TWO1, TWO0) => 150092, (TWO1, TWO1) => 161978,
    (TWO1, MM01) => 160036, (TWO1, MM10) => 153370, (TWO1, G00) => 1408642,
    (TWO1, G01) => 1345132, (TWO1, G10) => 1442722, (TWO1, G11) => 1366012,
    (MM01, ZERO) => 840, (MM01, POW2) => 23898, (MM01, ALL1) => 20524,
    (MM01, R0R1) => 191946, (MM01, R1R0) => 204274, (MM01, ONE0) => 169028,
    (MM01, ONE1) => 183060, (MM01, TWO0) => 148568, (MM01, TWO1) => 160036,
    (MM01, MM01) => 158086, (MM01, MM10) => 151348, (MM01, G00) => 1449938,
    (MM01, G01) => 1379840, (MM01, G10) => 1494336, (MM01, G11) => 1423572,
    (MM10, ZERO) => 840, (MM10, POW2) => 22778, (MM10, ALL1) => 20006,
    (MM10, R0R1) => 186462, (MM10, R1R0) => 195506, (MM10, ONE0) => 164918,
    (MM10, ONE1) => 175266, (MM10, TWO0) => 145086, (MM10, TWO1) => 153370,
    (MM10, MM01) => 151348, (MM10, MM10) => 147002, (MM10, G00) => 1343632,
    (MM10, G01) => 1304688, (MM10, G10) => 1379058, (MM10, G11) => 1327960,
    (G00, ZERO) => 2520, (G00, POW2) => 189214, (G00, ALL1) => 176044,
    (G00, R0R1) => 1650354, (G00, R1R0) => 1790482, (G00, ONE0) => 1515080,
    (G00, ONE1) => 1543740, (G00, TWO0) => 1370130, (G00, TWO1) => 1408642,
    (G00, MM01) => 1449938, (G00, MM10) => 1343632, (G00, G00) => 12948362,
    (G00, G01) => 12680768, (G00, G10) => 13248914, (G00, G11) => 12835284,
    (G01, ZERO) => 2520, (G01, POW2) => 183600, (G01, ALL1) => 171354,
    (G01, R0R1) => 1603012, (G01, R1R0) => 1723294, (G01, ONE0) => 1478844,
    (G01, ONE1) => 1483242, (G01, TWO0) => 1333436, (G01, TWO1) => 1345132,
    (G01, MM01) => 1379840, (G01, MM10) => 1304688, (G01, G00) => 12680768,
    (G01, G01) => 12391310, (G01, G10) => 13033710, (G01, G11) => 12622398,
    (G10, ZERO) => 2520, (G10, POW2) => 196522, (G10, ALL1) => 179936,
    (G10, R0R1) => 1699104, (G10, R1R0) => 1851800, (G10, ONE0) => 1575626,
    (G10, ONE1) => 1588472, (G10, TWO0) => 1420724, (G10, TWO1) => 1442722,
    (G10, MM01) => 1494336, (G10, MM10) => 1379058, (G10, G00) => 13248914,
    (G10, G01) => 13033710, (G10, G10) => 13756850, (G10, G11) => 13481136,
    (G11, ZERO) => 2520, (G11, POW2) => 187968, (G11, ALL1) => 175988,
    (G11, R0R1) => 1639006, (G11, R1R0) => 1777952, (G11, ONE0) => 1541240,
    (G11, ONE1) => 1516096, (G11, TWO0) => 1389954, (G11, TWO1) => 1366012,
    (G11, MM01) => 1423572, (G11, MM10) => 1327960, (G11, G00) => 12835284,
    (G11, G01) => 12622398, (G11, G10) => 13481136, (G11, G11) => 13164090,
)


const SELTZO_TWO_SUM_F16_CRC = Dict{Tuple{SELTZOClass,SELTZOClass},UInt32}(
    (ZERO, ZERO) => 0x488B0E21, (ZERO, POW2) => 0x0E376E38, (ZERO, ALL1) => 0xCFE5C64A,
    (ZERO, R0R1) => 0x181FBCA3, (ZERO, R1R0) => 0x31912C3D, (ZERO, ONE0) => 0xFA51E0B4,
    (ZERO, ONE1) => 0x7F17598C, (ZERO, TWO0) => 0x22FE8C71, (ZERO, TWO1) => 0xF9997F08,
    (ZERO, MM01) => 0x6BDC22A6, (ZERO, MM10) => 0xB0BBD1DF, (ZERO, G00) => 0xF9EE83B6,
    (ZERO, G01) => 0x50BC18E5, (ZERO, G10) => 0xAEA7C3E1, (ZERO, G11) => 0x07F558B2,
    (POW2, ZERO) => 0xE4E81CB5, (POW2, POW2) => 0x3874A8BC, (POW2, ALL1) => 0xC71DBA95,
    (POW2, R0R1) => 0xC68C9424, (POW2, R1R0) => 0x524C5D83, (POW2, ONE0) => 0x6A4BEBFC,
    (POW2, ONE1) => 0xACECD3E4, (POW2, TWO0) => 0x13A6D73C, (POW2, TWO1) => 0x6BBA6FF6,
    (POW2, MM01) => 0x211CCC1A, (POW2, MM10) => 0x41E57787, (POW2, G00) => 0x78E4D294,
    (POW2, G01) => 0x73C8F3D9, (POW2, G10) => 0xECB272CA, (POW2, G11) => 0xE2561BC8,
    (ALL1, ZERO) => 0x703A87D0, (ALL1, POW2) => 0x3CD7CED5, (ALL1, ALL1) => 0x97B9AB6C,
    (ALL1, R0R1) => 0x61B42DCB, (ALL1, R1R0) => 0xD9989AD8, (ALL1, ONE0) => 0x3B4BC896,
    (ALL1, ONE1) => 0x43242126, (ALL1, TWO0) => 0x78B61E8D, (ALL1, TWO1) => 0x3CCBED99,
    (ALL1, MM01) => 0xD727CB42, (ALL1, MM10) => 0xAEC57FA4, (ALL1, G00) => 0x7FF6E009,
    (ALL1, G01) => 0x61076EA8, (ALL1, G10) => 0xBEABF592, (ALL1, G11) => 0x6054D116,
    (R0R1, ZERO) => 0x43906D41, (R0R1, POW2) => 0xB633B93A, (R0R1, ALL1) => 0x481959A8,
    (R0R1, R0R1) => 0xAEC94493, (R0R1, R1R0) => 0x11633378, (R0R1, ONE0) => 0x4FF0D580,
    (R0R1, ONE1) => 0x6BED5380, (R0R1, TWO0) => 0xFE80EE6B, (R0R1, TWO1) => 0xC842FF29,
    (R0R1, MM01) => 0xFD60DC56, (R0R1, MM10) => 0x6F634A55, (R0R1, G00) => 0xF52094EF,
    (R0R1, G01) => 0x08D25B1F, (R0R1, G10) => 0x32F6F62F, (R0R1, G11) => 0x50557ABB,
    (R1R0, ZERO) => 0x4F49C3E1, (R1R0, POW2) => 0x92B4847A, (R1R0, ALL1) => 0x3C61BDE9,
    (R1R0, R0R1) => 0xE819B883, (R1R0, R1R0) => 0xF6A9B655, (R1R0, ONE0) => 0x1C372501,
    (R1R0, ONE1) => 0xDE6BADA5, (R1R0, TWO0) => 0x87981B6F, (R1R0, TWO1) => 0xFD389F3B,
    (R1R0, MM01) => 0x2243A1F7, (R1R0, MM10) => 0xE305E70D, (R1R0, G00) => 0x78C3075F,
    (R1R0, G01) => 0xEB80FAFF, (R1R0, G10) => 0xB2C875AA, (R1R0, G11) => 0xE9085F23,
    (ONE0, ZERO) => 0x341D9E9A, (ONE0, POW2) => 0x99430FCE, (ONE0, ALL1) => 0xF227A6F8,
    (ONE0, R0R1) => 0xE997AD2E, (ONE0, R1R0) => 0x1C0800F5, (ONE0, ONE0) => 0x3679AFB6,
    (ONE0, ONE1) => 0x7202DBE9, (ONE0, TWO0) => 0x1D4028D4, (ONE0, TWO1) => 0x90849604,
    (ONE0, MM01) => 0x228F5ED7, (ONE0, MM10) => 0xFEDF33BB, (ONE0, G00) => 0xC0EEEEB2,
    (ONE0, G01) => 0xD7C063DE, (ONE0, G10) => 0xAA2EDAC1, (ONE0, G11) => 0x50A3E935,
    (ONE1, ZERO) => 0xDF5004C6, (ONE1, POW2) => 0x8267DD7F, (ONE1, ALL1) => 0x1563818F,
    (ONE1, R0R1) => 0xCEAECFF6, (ONE1, R1R0) => 0xA38F9A80, (ONE1, ONE0) => 0xE4393536,
    (ONE1, ONE1) => 0xF11C4986, (ONE1, TWO0) => 0x96B742DA, (ONE1, TWO1) => 0x0F3E88DC,
    (ONE1, MM01) => 0x78B8F200, (ONE1, MM10) => 0x5495F882, (ONE1, G00) => 0x407EFC0C,
    (ONE1, G01) => 0x25605C6D, (ONE1, G10) => 0x4C59469E, (ONE1, G11) => 0xA5D64BBA,
    (TWO0, ZERO) => 0x6F59769B, (TWO0, POW2) => 0xAADB4204, (TWO0, ALL1) => 0xCBBDB031,
    (TWO0, R0R1) => 0xAD979239, (TWO0, R1R0) => 0xEECD98BA, (TWO0, ONE0) => 0xF2989320,
    (TWO0, ONE1) => 0x05D94755, (TWO0, TWO0) => 0x33F5AB69, (TWO0, TWO1) => 0x71056230,
    (TWO0, MM01) => 0x45523548, (TWO0, MM10) => 0x9FD21BB7, (TWO0, G00) => 0x7C28F011,
    (TWO0, G01) => 0x1253CCB3, (TWO0, G10) => 0x5855B1D7, (TWO0, G11) => 0xFCB5BC0D,
    (TWO1, ZERO) => 0x8DF9A149, (TWO1, POW2) => 0xCCB3F5DA, (TWO1, ALL1) => 0x5194F2EB,
    (TWO1, R0R1) => 0xD39156D4, (TWO1, R1R0) => 0x7D3BDC76, (TWO1, ONE0) => 0x99EFA4C2,
    (TWO1, ONE1) => 0xA47AA16D, (TWO1, TWO0) => 0xAC5A7F9A, (TWO1, TWO1) => 0xC1CAD615,
    (TWO1, MM01) => 0xA0B7FF22, (TWO1, MM10) => 0xA22DE8A5, (TWO1, G00) => 0x8EF24D75,
    (TWO1, G01) => 0x564650B2, (TWO1, G10) => 0x9C3334B8, (TWO1, G11) => 0xB743C20C,
    (MM01, ZERO) => 0xCD9D167A, (MM01, POW2) => 0xC323546F, (MM01, ALL1) => 0xC25ABF01,
    (MM01, R0R1) => 0x8ED83060, (MM01, R1R0) => 0xC9B5EEB8, (MM01, ONE0) => 0x665183A5,
    (MM01, ONE1) => 0x65A6045F, (MM01, TWO0) => 0xFD359D55, (MM01, TWO1) => 0x0711944B,
    (MM01, MM01) => 0xD79135FA, (MM01, MM10) => 0xC02BA7C1, (MM01, G00) => 0xAD4C6807,
    (MM01, G01) => 0xE7058DBA, (MM01, G10) => 0xD142C6A1, (MM01, G11) => 0x17D339E6,
    (MM10, ZERO) => 0x2F3DC1A8, (MM10, POW2) => 0x99CEA90A, (MM10, ALL1) => 0xE59586A8,
    (MM10, R0R1) => 0x1BF76119, (MM10, R1R0) => 0x97B7169F, (MM10, ONE0) => 0xF22FC415,
    (MM10, ONE1) => 0x24A43D66, (MM10, TWO0) => 0x8C1E3058, (MM10, TWO1) => 0xB5028CB1,
    (MM10, MM01) => 0xEEC67850, (MM10, MM10) => 0x92489C0A, (MM10, G00) => 0xF8FF123F,
    (MM10, G01) => 0x0508ACDC, (MM10, G10) => 0xB2F50CB4, (MM10, G11) => 0xA30F8BA6,
    (G00, ZERO) => 0x9E0EB07A, (G00, POW2) => 0xC2B633A2, (G00, ALL1) => 0x733121BB,
    (G00, R0R1) => 0x5DEC9051, (G00, R1R0) => 0x5E2E6ED0, (G00, ONE0) => 0x0F056E26,
    (G00, ONE1) => 0x03155F30, (G00, TWO0) => 0x9FBB345C, (G00, TWO1) => 0x56C88033,
    (G00, MM01) => 0xE0A066B3, (G00, MM10) => 0xEFA24276, (G00, G00) => 0xF511CCBA,
    (G00, G01) => 0x8B9E5988, (G00, G10) => 0xB1367297, (G00, G11) => 0x908A8367,
    (G01, ZERO) => 0x0328D1B4, (G01, POW2) => 0x2FCD4D1F, (G01, ALL1) => 0xFC38C694,
    (G01, R0R1) => 0x87380674, (G01, R1R0) => 0x8FE28D7D, (G01, ONE0) => 0x9514DC64,
    (G01, ONE1) => 0xA36000FF, (G01, TWO0) => 0x1F672C44, (G01, TWO1) => 0x82C40E23,
    (G01, MM01) => 0xC5FAD61D, (G01, MM10) => 0x9D69BC3A, (G01, G00) => 0xF896AC7B,
    (G01, G01) => 0x82917C57, (G01, G10) => 0x7E8AD9D3, (G01, G11) => 0x0731C7A3,
    (G10, ZERO) => 0xA1AE0517, (G10, POW2) => 0x2FF28857, (G10, ALL1) => 0x1BA2E99A,
    (G10, R0R1) => 0x33D88FD3, (G10, R1R0) => 0x49B17154, (G10, ONE0) => 0xAA415C3C,
    (G10, ONE1) => 0x33C1D304, (G10, TWO0) => 0xAFBB25EB, (G10, TWO1) => 0x943B43A3,
    (G10, MM01) => 0xDDD9FC1B, (G10, MM10) => 0x6CC30C8E, (G10, G00) => 0xE3B58F2E,
    (G10, G01) => 0xBE74713D, (G10, G10) => 0xF056D21A, (G10, G11) => 0x42BF9610,
    (G11, ZERO) => 0x3C8864D9, (G11, POW2) => 0x68DA90C1, (G11, ALL1) => 0x15B2B500,
    (G11, R0R1) => 0x704C13C0, (G11, R1R0) => 0x7C2339E0, (G11, ONE0) => 0xDE83C120,
    (G11, ONE1) => 0x098D7940, (G11, TWO0) => 0xB708783F, (G11, TWO1) => 0xD4327879,
    (G11, MM01) => 0x00146C8D, (G11, MM10) => 0xAF2DA49B, (G11, G00) => 0x4ED0BAFB,
    (G11, G01) => 0x963D9374, (G11, G10) => 0x06737381, (G11, G11) => 0xD9089177,
)


const SELTZO_TWO_SUM_BF16_COUNT = Dict{Tuple{SELTZOClass,SELTZOClass},Int}(
    (ZERO, ZERO) => 4, (ZERO, POW2) => 1016, (ZERO, ALL1) => 1016,
    (ZERO, R0R1) => 6096, (ZERO, R1R0) => 6096, (ZERO, ONE0) => 5080,
    (ZERO, ONE1) => 5080, (ZERO, TWO0) => 4064, (ZERO, TWO1) => 4064,
    (ZERO, MM01) => 4064, (ZERO, MM10) => 4064, (ZERO, G00) => 6096,
    (ZERO, G01) => 6096, (ZERO, G10) => 6096, (ZERO, G11) => 6096,
    (POW2, ZERO) => 1016, (POW2, POW2) => 258062, (POW2, ALL1) => 257748,
    (POW2, R0R1) => 1547162, (POW2, R1R0) => 1547828, (POW2, ONE0) => 1289140,
    (POW2, ONE1) => 1289880, (POW2, TWO0) => 1031364, (POW2, TWO1) => 1031892,
    (POW2, MM01) => 1031832, (POW2, MM10) => 1031540, (POW2, G00) => 1696856,
    (POW2, G01) => 1698936, (POW2, G10) => 1708532, (POW2, G11) => 1710276,
    (ALL1, ZERO) => 1016, (ALL1, POW2) => 257748, (ALL1, ALL1) => 257694,
    (ALL1, R0R1) => 1545990, (ALL1, R1R0) => 1546294, (ALL1, ONE0) => 1288372,
    (ALL1, ONE1) => 1288620, (ALL1, TWO0) => 1030706, (ALL1, TWO1) => 1030880,
    (ALL1, MM01) => 1030848, (ALL1, MM10) => 1030714, (ALL1, G00) => 1701132,
    (ALL1, G01) => 1700622, (ALL1, G10) => 1708836, (ALL1, G11) => 1708394,
    (R0R1, ZERO) => 6096, (R0R1, POW2) => 1547162, (R0R1, ALL1) => 1546000,
    (R0R1, R0R1) => 9278136, (R0R1, R1R0) => 9280298, (R0R1, ONE0) => 7731384,
    (R0R1, ONE1) => 7734020, (R0R1, TWO0) => 6185298, (R0R1, TWO1) => 6187190,
    (R0R1, MM01) => 6186486, (R0R1, MM10) => 6185944, (R0R1, G00) => 10260346,
    (R0R1, G01) => 10248536, (R0R1, G10) => 10317344, (R0R1, G11) => 10310734,
    (R1R0, ZERO) => 6096, (R1R0, POW2) => 1547828, (R1R0, ALL1) => 1546306,
    (R1R0, R0R1) => 9280298, (R1R0, R1R0) => 9283704, (R1R0, ONE0) => 7732980,
    (R1R0, ONE1) => 7736790, (R1R0, TWO0) => 6186646, (R1R0, TWO1) => 6189328,
    (R1R0, MM01) => 6188736, (R1R0, MM10) => 6187388, (R1R0, G00) => 10294648,
    (R1R0, G01) => 10301624, (R1R0, G10) => 10358458, (R1R0, G11) => 10358970,
    (ONE0, ZERO) => 5080, (ONE0, POW2) => 1289140, (ONE0, ALL1) => 1288380,
    (ONE0, R0R1) => 7731384, (ONE0, R1R0) => 7732980, (ONE0, ONE0) => 6443022,
    (ONE0, ONE1) => 6444356, (ONE0, TWO0) => 5154476, (ONE0, TWO1) => 5155482,
    (ONE0, MM01) => 5155194, (ONE0, MM10) => 5154624, (ONE0, G00) => 8582950,
    (ONE0, G01) => 8591430, (ONE0, G10) => 8652740, (ONE0, G11) => 8639416,
    (ONE1, ZERO) => 5080, (ONE1, POW2) => 1289880, (ONE1, ALL1) => 1288620,
    (ONE1, R0R1) => 7734020, (ONE1, R1R0) => 7736790, (ONE1, ONE0) => 6444356,
    (ONE1, ONE1) => 6447846, (ONE1, TWO0) => 5155744, (ONE1, TWO1) => 5158134,
    (ONE1, MM01) => 5157648, (ONE1, MM10) => 5156452, (ONE1, G00) => 8545690,
    (ONE1, G01) => 8542742, (ONE1, G10) => 8596590, (ONE1, G11) => 8603348,
    (TWO0, ZERO) => 4064, (TWO0, POW2) => 1031364, (TWO0, ALL1) => 1030712,
    (TWO0, R0R1) => 6185298, (TWO0, R1R0) => 6186646, (TWO0, ONE0) => 5154476,
    (TWO0, ONE1) => 5155744, (TWO0, TWO0) => 4123796, (TWO0, TWO1) => 4124574,
    (TWO0, MM01) => 4124242, (TWO0, MM10) => 4123876, (TWO0, G00) => 6912220,
    (TWO0, G01) => 6908086, (TWO0, G10) => 6946452, (TWO0, G11) => 6940618,
    (TWO1, ZERO) => 4064, (TWO1, POW2) => 1031892, (TWO1, ALL1) => 1030888,
    (TWO1, R0R1) => 6187190, (TWO1, R1R0) => 6189328, (TWO1, ONE0) => 5155482,
    (TWO1, ONE1) => 5158134, (TWO1, TWO0) => 4124574, (TWO1, TWO1) => 4126464,
    (TWO1, MM01) => 4126024, (TWO1, MM10) => 4125134, (TWO1, G00) => 6890414,
    (TWO1, G01) => 6876678, (TWO1, G10) => 6928904, (TWO1, G11) => 6916014,
    (MM01, ZERO) => 4064, (MM01, POW2) => 1031832, (MM01, ALL1) => 1030848,
    (MM01, R0R1) => 6186486, (MM01, R1R0) => 6188736, (MM01, ONE0) => 5155194,
    (MM01, ONE1) => 5157648, (MM01, TWO0) => 4124242, (MM01, TWO1) => 4126024,
    (MM01, MM01) => 4125588, (MM01, MM10) => 4124746, (MM01, G00) => 6921576,
    (MM01, G01) => 6905684, (MM01, G10) => 6950740, (MM01, G11) => 6935288,
    (MM10, ZERO) => 4064, (MM10, POW2) => 1031540, (MM10, ALL1) => 1030720,
    (MM10, R0R1) => 6185944, (MM10, R1R0) => 6187388, (MM10, ONE0) => 5154624,
    (MM10, ONE1) => 5156452, (MM10, TWO0) => 4123876, (MM10, TWO1) => 4125134,
    (MM10, MM01) => 4124746, (MM10, MM10) => 4124364, (MM10, G00) => 6890670,
    (MM10, G01) => 6878450, (MM10, G10) => 6925484, (MM10, G11) => 6920876,
    (G00, ZERO) => 6096, (G00, POW2) => 1696856, (G00, ALL1) => 1701152,
    (G00, R0R1) => 10260346, (G00, R1R0) => 10294648, (G00, ONE0) => 8582950,
    (G00, ONE1) => 8545690, (G00, TWO0) => 6912220, (G00, TWO1) => 6890414,
    (G00, MM01) => 6921576, (G00, MM10) => 6890670, (G00, G00) => 12891372,
    (G00, G01) => 12963532, (G00, G10) => 13052736, (G00, G11) => 13030748,
    (G01, ZERO) => 6096, (G01, POW2) => 1698936, (G01, ALL1) => 1700628,
    (G01, R0R1) => 10248536, (G01, R1R0) => 10301624, (G01, ONE0) => 8591430,
    (G01, ONE1) => 8542742, (G01, TWO0) => 6908086, (G01, TWO1) => 6876678,
    (G01, MM01) => 6905684, (G01, MM10) => 6878450, (G01, G00) => 12963532,
    (G01, G01) => 12912348, (G01, G10) => 13109418, (G01, G11) => 13050112,
    (G10, ZERO) => 6096, (G10, POW2) => 1708532, (G10, ALL1) => 1708856,
    (G10, R0R1) => 10317344, (G10, R1R0) => 10358458, (G10, ONE0) => 8652740,
    (G10, ONE1) => 8596590, (G10, TWO0) => 6946452, (G10, TWO1) => 6928904,
    (G10, MM01) => 6950740, (G10, MM10) => 6925484, (G10, G00) => 13052736,
    (G10, G01) => 13109418, (G10, G10) => 13157836, (G10, G11) => 13192212,
    (G11, ZERO) => 6096, (G11, POW2) => 1710276, (G11, ALL1) => 1708400,
    (G11, R0R1) => 10310734, (G11, R1R0) => 10358970, (G11, ONE0) => 8639416,
    (G11, ONE1) => 8603348, (G11, TWO0) => 6940618, (G11, TWO1) => 6916014,
    (G11, MM01) => 6935288, (G11, MM10) => 6920876, (G11, G00) => 13030748,
    (G11, G01) => 13050112, (G11, G10) => 13192212, (G11, G11) => 13109248,
)


const SELTZO_TWO_SUM_BF16_CRC = Dict{Tuple{SELTZOClass,SELTZOClass},UInt32}(
    (ZERO, ZERO) => 0x881352C7, (ZERO, POW2) => 0x3D22E451, (ZERO, ALL1) => 0xEC0A95D3,
    (ZERO, R0R1) => 0x7F3A90D6, (ZERO, R1R0) => 0x1DF763E6, (ZERO, ONE0) => 0x5682AABB,
    (ZERO, ONE1) => 0x548BA8CA, (ZERO, TWO0) => 0x59160F5E, (ZERO, TWO1) => 0xFEECB2E1,
    (ZERO, MM01) => 0x3BBF9BCB, (ZERO, MM10) => 0x9C452674, (ZERO, G00) => 0xF4210CB9,
    (ZERO, G01) => 0xD59A5DA9, (ZERO, G10) => 0xB757AE99, (ZERO, G11) => 0x96ECFF89,
    (POW2, ZERO) => 0x7C87284F, (POW2, POW2) => 0x8440A843, (POW2, ALL1) => 0x184CBBF5,
    (POW2, R0R1) => 0x290032BC, (POW2, R1R0) => 0xDB14C87D, (POW2, ONE0) => 0xCFC704EF,
    (POW2, ONE1) => 0x3E9FEC03, (POW2, TWO0) => 0x8249EDDC, (POW2, TWO1) => 0x011978C5,
    (POW2, MM01) => 0xE22D2FCD, (POW2, MM10) => 0x17871471, (POW2, G00) => 0xCAD635DC,
    (POW2, G01) => 0x21DE7CF7, (POW2, G10) => 0x8F6BDFE0, (POW2, G11) => 0xB4F78582,
    (ALL1, ZERO) => 0x708D6558, (ALL1, POW2) => 0x0AFF0A0B, (ALL1, ALL1) => 0x07EB93E4,
    (ALL1, R0R1) => 0x0E32C9F8, (ALL1, R1R0) => 0x182EC4AD, (ALL1, ONE0) => 0x3A485DF8,
    (ALL1, ONE1) => 0xBE689442, (ALL1, TWO0) => 0xB4ACA823, (ALL1, TWO1) => 0x73A78B7E,
    (ALL1, MM01) => 0xC274483D, (ALL1, MM10) => 0x91C37E73, (ALL1, G00) => 0x3CF8DD79,
    (ALL1, G01) => 0x20DFA0BE, (ALL1, G10) => 0x652DF300, (ALL1, G11) => 0xE43AD6AD,
    (R0R1, ZERO) => 0x8CC2FAFC, (R0R1, POW2) => 0x0F0D0D1A, (R0R1, ALL1) => 0x66D51709,
    (R0R1, R0R1) => 0xFB2029A2, (R0R1, R1R0) => 0x6AC54301, (R0R1, ONE0) => 0xCE213864,
    (R0R1, ONE1) => 0x2E0A339E, (R0R1, TWO0) => 0x0958D00F, (R0R1, TWO1) => 0x560A1DCC,
    (R0R1, MM01) => 0x174D6DE4, (R0R1, MM10) => 0x65C071BB, (R0R1, G00) => 0xCA6E6444,
    (R0R1, G01) => 0x42C66231, (R0R1, G10) => 0x1FFB6A19, (R0R1, G11) => 0x1F0F465C,
    (R1R0, ZERO) => 0xA3D1F876, (R1R0, POW2) => 0x5F8711E0, (R1R0, ALL1) => 0x4E4C9F1C,
    (R1R0, R0R1) => 0x6048CF03, (R1R0, R1R0) => 0xEEB0F24D, (R1R0, ONE0) => 0x5B7D3707,
    (R1R0, ONE1) => 0xB1229EC2, (R1R0, TWO0) => 0xB120E669, (R1R0, TWO1) => 0x982D61BB,
    (R1R0, MM01) => 0xCC7348B9, (R1R0, MM10) => 0xAECD768F, (R1R0, G00) => 0x228DB7CE,
    (R1R0, G01) => 0x2F8F2B89, (R1R0, G10) => 0x30A7D622, (R1R0, G11) => 0xA485C67B,
    (ONE0, ZERO) => 0xA67C62D8, (ONE0, POW2) => 0xF57D14C7, (ONE0, ALL1) => 0xF9F024AA,
    (ONE0, R0R1) => 0xA235B178, (ONE0, R1R0) => 0x588BBA0D, (ONE0, ONE0) => 0x203DD5E4,
    (ONE0, ONE1) => 0x5A98DCC4, (ONE0, TWO0) => 0x9308499F, (ONE0, TWO1) => 0x992F13AD,
    (ONE0, MM01) => 0x3CF6E6E0, (ONE0, MM10) => 0xD341D4FD, (ONE0, G00) => 0x25ED8CA5,
    (ONE0, G01) => 0xE65AAD57, (ONE0, G10) => 0x78E45D37, (ONE0, G11) => 0x289E503D,
    (ONE1, ZERO) => 0xCC354975, (ONE1, POW2) => 0x15CED992, (ONE1, ALL1) => 0xC2245DE7,
    (ONE1, R0R1) => 0xACBBA706, (ONE1, R1R0) => 0x43BAB925, (ONE1, ONE0) => 0xE96AED24,
    (ONE1, ONE1) => 0xB92EA3BB, (ONE1, TWO0) => 0xF8357141, (ONE1, TWO1) => 0x1A748766,
    (ONE1, MM01) => 0x5F7A14E3, (ONE1, MM10) => 0x4BCDAC1F, (ONE1, G00) => 0x1F4D8138,
    (ONE1, G01) => 0x187A5C10, (ONE1, G10) => 0xB736E3D0, (ONE1, G11) => 0x26A595BA,
    (TWO0, ZERO) => 0xB6E8E5E8, (TWO0, POW2) => 0xA5B5CCBF, (TWO0, ALL1) => 0x00F7A82E,
    (TWO0, R0R1) => 0x2A875455, (TWO0, R1R0) => 0x6343AEFF, (TWO0, ONE0) => 0x1C9D8E00,
    (TWO0, ONE1) => 0x13D47025, (TWO0, TWO0) => 0x4EF6CECE, (TWO0, TWO1) => 0xF53E4D3C,
    (TWO0, MM01) => 0x48EC3499, (TWO0, MM10) => 0x61CB567A, (TWO0, G00) => 0x555D702F,
    (TWO0, G01) => 0xF780E3E5, (TWO0, G10) => 0xD6113A14, (TWO0, G11) => 0xB95F2D7B,
    (TWO1, ZERO) => 0x03F21AEB, (TWO1, POW2) => 0x9A381876, (TWO1, ALL1) => 0xD4DA68E4,
    (TWO1, R0R1) => 0xDA94933F, (TWO1, R1R0) => 0xD2E64699, (TWO1, ONE0) => 0x02F8D5FC,
    (TWO1, ONE1) => 0xA71FCB50, (TWO1, TWO0) => 0x2F2FAC5B, (TWO1, TWO1) => 0x22B76758,
    (TWO1, MM01) => 0x93EFD52A, (TWO1, MM10) => 0x41AF0664, (TWO1, G00) => 0x00AA8575,
    (TWO1, G01) => 0x38F24EEB, (TWO1, G10) => 0x9AC5B708, (TWO1, G11) => 0xDC2FEADA,
    (MM01, ZERO) => 0x26BA9D46, (MM01, POW2) => 0xEAAB63F3, (MM01, ALL1) => 0x32BF3DBF,
    (MM01, R0R1) => 0x951EFEB4, (MM01, R1R0) => 0x57F4510B, (MM01, ONE0) => 0x0AF029A4,
    (MM01, ONE1) => 0x28CC2C80, (MM01, TWO0) => 0x66DA41F1, (MM01, TWO1) => 0x0FFF0278,
    (MM01, MM01) => 0x2E089AC8, (MM01, MM10) => 0x0231AAEF, (MM01, G00) => 0x65BC4DC4,
    (MM01, G01) => 0xA63AE56D, (MM01, G10) => 0xB7916011, (MM01, G11) => 0xCAA3C4C2,
    (MM10, ZERO) => 0x93A06245, (MM10, POW2) => 0xECDAE3DA, (MM10, ALL1) => 0xA94FCEAC,
    (MM10, R0R1) => 0x85421536, (MM10, R1R0) => 0x2DBEC245, (MM10, ONE0) => 0x94C410E5,
    (MM10, ONE1) => 0xD860BCAD, (MM10, TWO0) => 0x7C811B00, (MM10, TWO1) => 0x8B32FF99,
    (MM10, MM01) => 0xEA152A2E, (MM10, MM10) => 0xF11E9FD9, (MM10, G00) => 0x3EA64305,
    (MM10, G01) => 0x6ACAB491, (MM10, G10) => 0x0AE6362F, (MM10, G11) => 0x64116C4A,
    (G00, ZERO) => 0x13E09170, (G00, POW2) => 0x73E21C03, (G00, ALL1) => 0xF5E56EED,
    (G00, R0R1) => 0x648228DF, (G00, R1R0) => 0xAF5F5F85, (G00, ONE0) => 0x65561733,
    (G00, ONE1) => 0x802548CF, (G00, TWO0) => 0x07F52AC4, (G00, TWO1) => 0x45E055A0,
    (G00, MM01) => 0x20B93723, (G00, MM10) => 0xC93B9D84, (G00, G00) => 0x89D034E6,
    (G00, G01) => 0xD62AC59E, (G00, G10) => 0x5E5FA99A, (G00, G11) => 0xE3FB04CD,
    (G01, ZERO) => 0x091190F6, (G01, POW2) => 0x1D74D43A, (G01, ALL1) => 0x42404726,
    (G01, R0R1) => 0x810A1689, (G01, R1R0) => 0x5EEBE525, (G01, ONE0) => 0x944867EA,
    (G01, ONE1) => 0x7FD71B89, (G01, TWO0) => 0xA81D26D2, (G01, TWO1) => 0x5657273B,
    (G01, MM01) => 0xC4738253, (G01, MM10) => 0xECB573AC, (G01, G00) => 0xBE5223CB,
    (G01, G01) => 0x8EEF52C0, (G01, G10) => 0x1A01C563, (G01, G11) => 0xA7F1400D,
    (G10, ZERO) => 0x2602927C, (G10, POW2) => 0x0D6D83CD, (G10, ALL1) => 0x2BCF6245,
    (G10, R0R1) => 0x8C402E8F, (G10, R1R0) => 0x7B274733, (G10, ONE0) => 0x5201F7BC,
    (G10, ONE1) => 0xBD9A5F28, (G10, TWO0) => 0x6E27DAD0, (G10, TWO1) => 0xD2CD8118,
    (G10, MM01) => 0xA5BCEFB9, (G10, MM10) => 0x80998972, (G10, G00) => 0x243D8A68,
    (G10, G01) => 0x6512943D, (G10, G10) => 0x9CE3FF91, (G10, G11) => 0xE8D30231,
    (G11, ZERO) => 0x3CF393FA, (G11, POW2) => 0x6FF98086, (G11, ALL1) => 0xDE16FF61,
    (G11, R0R1) => 0x40661CC3, (G11, R1R0) => 0x073BD7D7, (G11, ONE0) => 0x2047B96F,
    (G11, ONE1) => 0x0C442147, (G11, TWO0) => 0xBD924619, (G11, TWO1) => 0x390CA1D3,
    (G11, MM01) => 0x74580EE2, (G11, MM10) => 0x75798E30, (G11, G00) => 0xC3BCE639,
    (G11, G01) => 0x17FDC9F4, (G11, G10) => 0xDD1D0AAE, (G11, G11) => 0xCB9E19DC,
)


const SELTZO_TWO_PROD_F16_COUNT = Dict{Tuple{SELTZOClass,SELTZOClass},Int}(
    (ZERO, ZERO) => 4, (ZERO, POW2) => 120, (ZERO, ALL1) => 120,
    (ZERO, R0R1) => 1080, (ZERO, R1R0) => 1080, (ZERO, ONE0) => 960,
    (ZERO, ONE1) => 960, (ZERO, TWO0) => 840, (ZERO, TWO1) => 840,
    (ZERO, MM01) => 840, (ZERO, MM10) => 840, (ZERO, G00) => 2520,
    (ZERO, G01) => 2520, (ZERO, G10) => 2520, (ZERO, G11) => 2520,
    (POW2, ZERO) => 120, (POW2, POW2) => 2740, (POW2, ALL1) => 2780,
    (POW2, R0R1) => 24516, (POW2, R1R0) => 24516, (POW2, ONE0) => 21792,
    (POW2, ONE1) => 21792, (POW2, TWO0) => 19068, (POW2, TWO1) => 19068,
    (POW2, MM01) => 19068, (POW2, MM10) => 19068, (POW2, G00) => 57204,
    (POW2, G01) => 57204, (POW2, G10) => 57204, (POW2, G11) => 57204,
    (ALL1, ZERO) => 120, (ALL1, POW2) => 2780, (ALL1, ALL1) => 1604,
    (ALL1, R0R1) => 16416, (ALL1, R1R0) => 15596, (ALL1, ONE0) => 13088,
    (ALL1, ONE1) => 14592, (ALL1, TWO0) => 11568, (ALL1, TWO1) => 12768,
    (ALL1, MM01) => 11568, (ALL1, MM10) => 12768, (ALL1, G00) => 75180,
    (ALL1, G01) => 129036, (ALL1, G10) => 174540, (ALL1, G11) => 242148,
    (R0R1, ZERO) => 1080, (R0R1, POW2) => 24516, (R0R1, ALL1) => 16416,
    (R0R1, R0R1) => 140844, (R0R1, R1R0) => 142780, (R0R1, ONE0) => 127192,
    (R0R1, ONE1) => 125712, (R0R1, TWO0) => 111748, (R0R1, TWO1) => 109252,
    (R0R1, MM01) => 109784, (R0R1, MM10) => 111000, (R0R1, G00) => 3199900,
    (R0R1, G01) => 3134484, (R0R1, G10) => 3258696, (R0R1, G11) => 3264968,
    (R1R0, ZERO) => 1080, (R1R0, POW2) => 24516, (R1R0, ALL1) => 15596,
    (R1R0, R0R1) => 142780, (R1R0, R1R0) => 179164, (R1R0, ONE0) => 127180,
    (R1R0, ONE1) => 159416, (R1R0, TWO0) => 112132, (R1R0, TWO1) => 134856,
    (R1R0, MM01) => 132056, (R1R0, MM10) => 112640, (R1R0, G00) => 3125320,
    (R1R0, G01) => 3058312, (R1R0, G10) => 2972876, (R1R0, G11) => 2815036,
    (ONE0, ZERO) => 960, (ONE0, POW2) => 21792, (ONE0, ALL1) => 13088,
    (ONE0, R0R1) => 127192, (ONE0, R1R0) => 127180, (ONE0, ONE0) => 111744,
    (ONE0, ONE1) => 113960, (ONE0, TWO0) => 98844, (ONE0, TWO1) => 99820,
    (ONE0, MM01) => 98120, (ONE0, MM10) => 100244, (ONE0, G00) => 3046968,
    (ONE0, G01) => 3032140, (ONE0, G10) => 2911228, (ONE0, G11) => 2924232,
    (ONE1, ZERO) => 960, (ONE1, POW2) => 21792, (ONE1, ALL1) => 14592,
    (ONE1, R0R1) => 125712, (ONE1, R1R0) => 159416, (ONE1, ONE0) => 113960,
    (ONE1, ONE1) => 141496, (ONE1, TWO0) => 99584, (ONE1, TWO1) => 119848,
    (ONE1, MM01) => 116888, (ONE1, MM10) => 99284, (ONE1, G00) => 2735552,
    (ONE1, G01) => 2615432, (ONE1, G10) => 2995888, (ONE1, G11) => 2905116,
    (TWO0, ZERO) => 840, (TWO0, POW2) => 19068, (TWO0, ALL1) => 11568,
    (TWO0, R0R1) => 111748, (TWO0, R1R0) => 112132, (TWO0, ONE0) => 98844,
    (TWO0, ONE1) => 99584, (TWO0, TWO0) => 87968, (TWO0, TWO1) => 87180,
    (TWO0, MM01) => 87352, (TWO0, MM10) => 86936, (TWO0, G00) => 2772016,
    (TWO0, G01) => 2787068, (TWO0, G10) => 2806988, (TWO0, G11) => 2780240,
    (TWO1, ZERO) => 840, (TWO1, POW2) => 19068, (TWO1, ALL1) => 12768,
    (TWO1, R0R1) => 109252, (TWO1, R1R0) => 134856, (TWO1, ONE0) => 99820,
    (TWO1, ONE1) => 119848, (TWO1, TWO0) => 87180, (TWO1, TWO1) => 102836,
    (TWO1, MM01) => 100112, (TWO1, MM10) => 86092, (TWO1, G00) => 2726492,
    (TWO1, G01) => 2636360, (TWO1, G10) => 2889464, (TWO1, G11) => 2826712,
    (MM01, ZERO) => 840, (MM01, POW2) => 19068, (MM01, ALL1) => 11568,
    (MM01, R0R1) => 109784, (MM01, R1R0) => 132056, (MM01, ONE0) => 98120,
    (MM01, ONE1) => 116888, (MM01, TWO0) => 87352, (MM01, TWO1) => 100112,
    (MM01, MM01) => 98296, (MM01, MM10) => 86588, (MM01, G00) => 2820756,
    (MM01, G01) => 2741352, (MM01, G10) => 2746796, (MM01, G11) => 2716924,
    (MM10, ZERO) => 840, (MM10, POW2) => 19068, (MM10, ALL1) => 12768,
    (MM10, R0R1) => 111000, (MM10, R1R0) => 112640, (MM10, ONE0) => 100244,
    (MM10, ONE1) => 99284, (MM10, TWO0) => 86936, (MM10, TWO1) => 86092,
    (MM10, MM01) => 86588, (MM10, MM10) => 85736, (MM10, G00) => 2791748,
    (MM10, G01) => 2807944, (MM10, G10) => 2833688, (MM10, G11) => 2802956,
    (G00, ZERO) => 2520, (G00, POW2) => 57204, (G00, ALL1) => 75180,
    (G00, R0R1) => 3199900, (G00, R1R0) => 3125320, (G00, ONE0) => 3046968,
    (G00, ONE1) => 2735552, (G00, TWO0) => 2772016, (G00, TWO1) => 2726492,
    (G00, MM01) => 2820756, (G00, MM10) => 2791748, (G00, G00) => 59409916,
    (G00, G01) => 67655628, (G00, G10) => 70005544, (G00, G11) => 72787924,
    (G01, ZERO) => 2520, (G01, POW2) => 57204, (G01, ALL1) => 129036,
    (G01, R0R1) => 3134484, (G01, R1R0) => 3058312, (G01, ONE0) => 3032140,
    (G01, ONE1) => 2615432, (G01, TWO0) => 2787068, (G01, TWO1) => 2636360,
    (G01, MM01) => 2741352, (G01, MM10) => 2807944, (G01, G00) => 67655628,
    (G01, G01) => 65680292, (G01, G10) => 72554796, (G01, G11) => 72564344,
    (G10, ZERO) => 2520, (G10, POW2) => 57204, (G10, ALL1) => 174540,
    (G10, R0R1) => 3258696, (G10, R1R0) => 2972876, (G10, ONE0) => 2911228,
    (G10, ONE1) => 2995888, (G10, TWO0) => 2806988, (G10, TWO1) => 2889464,
    (G10, MM01) => 2746796, (G10, MM10) => 2833688, (G10, G00) => 70005544,
    (G10, G01) => 72554796, (G10, G10) => 57386864, (G10, G11) => 62287512,
    (G11, ZERO) => 2520, (G11, POW2) => 57204, (G11, ALL1) => 242148,
    (G11, R0R1) => 3264968, (G11, R1R0) => 2815036, (G11, ONE0) => 2924232,
    (G11, ONE1) => 2905116, (G11, TWO0) => 2780240, (G11, TWO1) => 2826712,
    (G11, MM01) => 2716924, (G11, MM10) => 2802956, (G11, G00) => 72787924,
    (G11, G01) => 72564344, (G11, G10) => 62287512, (G11, G11) => 61267912,
)


const SELTZO_TWO_PROD_F16_CRC = Dict{Tuple{SELTZOClass,SELTZOClass},UInt32}(
    (ZERO, ZERO) => 0xA6984605, (ZERO, POW2) => 0x88BC945A, (ZERO, ALL1) => 0x4206C86D,
    (ZERO, R0R1) => 0x4F891150, (ZERO, R1R0) => 0x8A80C614, (ZERO, ONE0) => 0x948813D2,
    (ZERO, ONE1) => 0x45128891, (ZERO, TWO0) => 0xBB36BD41, (ZERO, TWO1) => 0x1747DD56,
    (ZERO, MM01) => 0xDF199D4C, (ZERO, MM10) => 0x7368FD5B, (ZERO, G00) => 0x9CCE7120,
    (ZERO, G01) => 0x55B84CAD, (ZERO, G10) => 0x0BCE7CCB, (ZERO, G11) => 0xC2B84146,
    (POW2, ZERO) => 0x38C6B28C, (POW2, POW2) => 0xD5F7B0E9, (POW2, ALL1) => 0x20CC4C30,
    (POW2, R0R1) => 0x184DA110, (POW2, R1R0) => 0x2864A3B6, (POW2, ONE0) => 0x522A766D,
    (POW2, ONE1) => 0xC9E186A8, (POW2, TWO0) => 0xF49823E3, (POW2, TWO1) => 0xD45BEA6F,
    (POW2, MM01) => 0x1782B6C8, (POW2, MM10) => 0x37417F44, (POW2, G00) => 0x0F31E84F,
    (POW2, G01) => 0x7787EC16, (POW2, G10) => 0xFE5DE0FD, (POW2, G11) => 0x86EBE4A4,
    (ALL1, ZERO) => 0xA77CDDAC, (ALL1, POW2) => 0x428848F6, (ALL1, ALL1) => 0x4CCB3318,
    (ALL1, R0R1) => 0xF3BA9FD5, (ALL1, R1R0) => 0xAD8095BD, (ALL1, ONE0) => 0xB0678E9F,
    (ALL1, ONE1) => 0xF6017740, (ALL1, TWO0) => 0xF6D9F389, (ALL1, TWO1) => 0x2EF8A8DB,
    (ALL1, MM01) => 0x61FC841A, (ALL1, MM10) => 0x674AF624, (ALL1, G00) => 0x8E88D293,
    (ALL1, G01) => 0x0DA81847, (ALL1, G10) => 0x3A951F67, (ALL1, G11) => 0x57ACEBE3,
    (R0R1, ZERO) => 0xADCFCAF2, (R0R1, POW2) => 0x21C57B48, (R0R1, ALL1) => 0x401A84AA,
    (R0R1, R0R1) => 0x3DF67F7D, (R0R1, R1R0) => 0xE9D93729, (R0R1, ONE0) => 0xD3D017A6,
    (R0R1, ONE1) => 0x213F5EA7, (R0R1, TWO0) => 0x650A7EA9, (R0R1, TWO1) => 0x1B35F02D,
    (R0R1, MM01) => 0xF4BC2B48, (R0R1, MM10) => 0x60B1F3FC, (R0R1, G00) => 0xF9ECC580,
    (R0R1, G01) => 0x0376D6C3, (R0R1, G10) => 0x183C1ADA, (R0R1, G11) => 0x32AD6E2F,
    (R1R0, ZERO) => 0x4D912388, (R1R0, POW2) => 0xFEA21351, (R1R0, ALL1) => 0xBF2CAC05,
    (R1R0, R0R1) => 0x80981C5B, (R1R0, R1R0) => 0x428DD893, (R1R0, ONE0) => 0x6822A9CB,
    (R1R0, ONE1) => 0x305746E7, (R1R0, TWO0) => 0x49D0C05F, (R1R0, TWO1) => 0x5CB781FF,
    (R1R0, MM01) => 0x9A7403CA, (R1R0, MM10) => 0x1592EDD7, (R1R0, G00) => 0xF822FEA9,
    (R1R0, G01) => 0x129F431C, (R1R0, G10) => 0x5B82CE11, (R1R0, G11) => 0xBA4A7A13,
    (ONE0, ZERO) => 0x3C9EA841, (ONE0, POW2) => 0xD29F169D, (ONE0, ALL1) => 0x11060132,
    (ONE0, R0R1) => 0x3C5B9211, (ONE0, R1R0) => 0x3598EEB9, (ONE0, ONE0) => 0x92D0D15C,
    (ONE0, ONE1) => 0xA58460FF, (ONE0, TWO0) => 0x5AA737C0, (ONE0, TWO1) => 0xFD17AF94,
    (ONE0, MM01) => 0xD1F9C1D6, (ONE0, MM10) => 0xBB152E80, (ONE0, G00) => 0x10113F23,
    (ONE0, G01) => 0x8A04B2C6, (ONE0, G10) => 0x03F84912, (ONE0, G11) => 0x4F0E735D,
    (ONE1, ZERO) => 0x830F1066, (ONE1, POW2) => 0x9D4E2341, (ONE1, ALL1) => 0xB33237BC,
    (ONE1, R0R1) => 0xD65CC1E7, (ONE1, R1R0) => 0xE86A8B90, (ONE1, ONE0) => 0x4D73720D,
    (ONE1, ONE1) => 0x00991091, (ONE1, TWO0) => 0xB6F279AB, (ONE1, TWO1) => 0x47D6F8CC,
    (ONE1, MM01) => 0xC8C5EFCC, (ONE1, MM10) => 0x90A7457E, (ONE1, G00) => 0xF41BCAEC,
    (ONE1, G01) => 0xA6A85287, (ONE1, G10) => 0xC4AD2615, (ONE1, G11) => 0xB5F63319,
    (TWO0, ZERO) => 0x2966AC6E, (TWO0, POW2) => 0x562A883E, (TWO0, ALL1) => 0xC22F4A08,
    (TWO0, R0R1) => 0xE55B5328, (TWO0, R1R0) => 0x37FCACCD, (TWO0, ONE0) => 0xC058AD2D,
    (TWO0, ONE1) => 0xCF8D73CB, (TWO0, TWO0) => 0x4A378B30, (TWO0, TWO1) => 0xAFF93EC1,
    (TWO0, MM01) => 0x91B85A37, (TWO0, MM10) => 0x0B850DDA, (TWO0, G00) => 0x59798A30,
    (TWO0, G01) => 0x0DEEA44B, (TWO0, G10) => 0x9845F249, (TWO0, G11) => 0x938E2BB2,
    (TWO1, ZERO) => 0xBCD0E8D2, (TWO1, POW2) => 0x75DAEA23, (TWO1, ALL1) => 0xDE7DE466,
    (TWO1, R0R1) => 0x9E0FE650, (TWO1, R1R0) => 0x5D1B922B, (TWO1, ONE0) => 0xB5FC1B02,
    (TWO1, ONE1) => 0xEE79324D, (TWO1, TWO0) => 0x68CA7C55, (TWO1, TWO1) => 0xC1CF1D4F,
    (TWO1, MM01) => 0xCC9F57F4, (TWO1, MM10) => 0x945E853E, (TWO1, G00) => 0x73AEB052,
    (TWO1, G01) => 0x8467CFC1, (TWO1, G10) => 0x4EAAEA07, (TWO1, G11) => 0x333B00C2,
    (MM01, ZERO) => 0xA6AF4255, (MM01, POW2) => 0xB4217B9A, (MM01, ALL1) => 0x9D18DDA7,
    (MM01, R0R1) => 0xAE33C076, (MM01, R1R0) => 0x2FF6ABF9, (MM01, ONE0) => 0x4D9F11AA,
    (MM01, ONE1) => 0xEC9D059F, (MM01, TWO0) => 0x11FF5F0A, (MM01, TWO1) => 0xD325D80F,
    (MM01, MM01) => 0x0E92F311, (MM01, MM10) => 0x67F38BA7, (MM01, G00) => 0x9A597A23,
    (MM01, G01) => 0xB87EEE28, (MM01, G10) => 0xDC3E467A, (MM01, G11) => 0xA403EEB0,
    (MM10, ZERO) => 0x331906E9, (MM10, POW2) => 0x97D11987, (MM10, ALL1) => 0xA0612996,
    (MM10, R0R1) => 0x10CC2145, (MM10, R1R0) => 0x1FC4C879, (MM10, ONE0) => 0x3241E84A,
    (MM10, ONE1) => 0x15BFB144, (MM10, TWO0) => 0x19BAF286, (MM10, TWO1) => 0xAA1859BB,
    (MM10, MM01) => 0xACE21AC8, (MM10, MM10) => 0xDEFAB53B, (MM10, G00) => 0x67DF52E9,
    (MM10, G01) => 0x201ED34E, (MM10, G10) => 0xD3C9A946, (MM10, G11) => 0x9752B141,
    (G00, ZERO) => 0x5DB5692D, (G00, POW2) => 0x54D2FE87, (G00, ALL1) => 0x19A00EF9,
    (G00, R0R1) => 0xEBE78141, (G00, R1R0) => 0x7C12BD8C, (G00, ONE0) => 0xE4B458B9,
    (G00, ONE1) => 0x95AB43BE, (G00, TWO0) => 0xF3950099, (G00, TWO1) => 0x379E5AEE,
    (G00, MM01) => 0xB9AA897D, (G00, MM10) => 0x64144D5E, (G00, G00) => 0x5B7D0E0F,
    (G00, G01) => 0xF1154E27, (G00, G10) => 0xF3F23C1C, (G00, G11) => 0xB5D05AD7,
    (G01, ZERO) => 0xA0B7AE3D, (G01, POW2) => 0xADD862CC, (G01, ALL1) => 0xC6BE987C,
    (G01, R0R1) => 0x53EB82A5, (G01, R1R0) => 0x95208D5D, (G01, ONE0) => 0x99D773B3,
    (G01, ONE1) => 0xB5D854A0, (G01, TWO0) => 0xE08AD6D6, (G01, TWO1) => 0xDC65C20C,
    (G01, MM01) => 0xBCB9F8FD, (G01, MM10) => 0xB2BB7F1C, (G01, G00) => 0x0640A1CF,
    (G01, G01) => 0x2D1D88DB, (G01, G10) => 0xF553E951, (G01, G11) => 0x32D00BD9,
    (G10, ZERO) => 0xA25C91FC, (G10, POW2) => 0xA32BB0E0, (G10, ALL1) => 0xA7CF5E1D,
    (G10, R0R1) => 0x1E11A4C1, (G10, R1R0) => 0xB6F37BDC, (G10, ONE0) => 0xE10F75CB,
    (G10, ONE1) => 0xAD190A71, (G10, TWO0) => 0xC73F2FA9, (G10, TWO1) => 0x29B0BD6C,
    (G10, MM01) => 0x30CCB97C, (G10, MM10) => 0x8B74A8D3, (G10, G00) => 0xA8D2E972,
    (G10, G01) => 0x54CD5832, (G10, G10) => 0x89D7641B, (G10, G11) => 0xD6A7A3C0,
    (G11, ZERO) => 0x5F5E56EC, (G11, POW2) => 0x5A212CAB, (G11, ALL1) => 0xE5DCBA91,
    (G11, R0R1) => 0xEC5BDD30, (G11, R1R0) => 0xF0B67EB6, (G11, ONE0) => 0xFA7116A7,
    (G11, ONE1) => 0x2465489C, (G11, TWO0) => 0x870C3A7E, (G11, TWO1) => 0x1A5E7E84,
    (G11, MM01) => 0x4666210B, (G11, MM10) => 0xEA26319B, (G11, G00) => 0x1F7B87A1,
    (G11, G01) => 0x908A09AD, (G11, G10) => 0xC4793FDB, (G11, G11) => 0x4A7B4506,
)


const SELTZO_TWO_PROD_BF16_COUNT = Dict{Tuple{SELTZOClass,SELTZOClass},Int}(
    (ZERO, ZERO) => 4, (ZERO, POW2) => 1016, (ZERO, ALL1) => 1016,
    (ZERO, R0R1) => 6096, (ZERO, R1R0) => 6096, (ZERO, ONE0) => 5080,
    (ZERO, ONE1) => 5080, (ZERO, TWO0) => 4064, (ZERO, TWO1) => 4064,
    (ZERO, MM01) => 4064, (ZERO, MM10) => 4064, (ZERO, G00) => 6096,
    (ZERO, G01) => 6096, (ZERO, G10) => 6096, (ZERO, G11) => 6096,
    (POW2, ZERO) => 1016, (POW2, POW2) => 222108, (POW2, ALL1) => 222136,
    (POW2, R0R1) => 1329792, (POW2, R1R0) => 1329792, (POW2, ONE0) => 1108160,
    (POW2, ONE1) => 1108160, (POW2, TWO0) => 886528, (POW2, TWO1) => 886528,
    (POW2, MM01) => 886528, (POW2, MM10) => 886528, (POW2, G00) => 1329792,
    (POW2, G01) => 1329792, (POW2, G10) => 1329792, (POW2, G11) => 1329792,
    (ALL1, ZERO) => 1016, (ALL1, POW2) => 222136, (ALL1, ALL1) => 217316,
    (ALL1, R0R1) => 1301856, (ALL1, R1R0) => 1304484, (ALL1, ONE0) => 1084400,
    (ALL1, ONE1) => 1084880, (ALL1, TWO0) => 867584, (ALL1, TWO1) => 867904,
    (ALL1, MM01) => 867584, (ALL1, MM10) => 867904, (ALL1, G00) => 2435016,
    (ALL1, G01) => 3571200, (ALL1, G10) => 3934748, (ALL1, G11) => 4319512,
    (R0R1, ZERO) => 6096, (R0R1, POW2) => 1329792, (R0R1, ALL1) => 1301856,
    (R0R1, R0R1) => 7826324, (R0R1, R1R0) => 7828788, (R0R1, ONE0) => 6513408,
    (R0R1, ONE1) => 6531800, (R0R1, TWO0) => 5211808, (R0R1, TWO1) => 5217668,
    (R0R1, MM01) => 5212284, (R0R1, MM10) => 5217376, (R0R1, G00) => 25992816,
    (R0R1, G01) => 25606916, (R0R1, G10) => 25990096, (R0R1, G11) => 25983592,
    (R1R0, ZERO) => 6096, (R1R0, POW2) => 1329792, (R1R0, ALL1) => 1304484,
    (R1R0, R0R1) => 7828788, (R1R0, R1R0) => 7884052, (R1R0, ONE0) => 6513948,
    (R1R0, ONE1) => 6579388, (R1R0, TWO0) => 5210932, (R1R0, TWO1) => 5246976,
    (R1R0, MM01) => 5236336, (R1R0, MM10) => 5214356, (R1R0, G00) => 25505860,
    (R1R0, G01) => 25995248, (R1R0, G10) => 25857148, (R1R0, G11) => 25609468,
    (ONE0, ZERO) => 5080, (ONE0, POW2) => 1108160, (ONE0, ALL1) => 1084400,
    (ONE0, R0R1) => 6513408, (ONE0, R1R0) => 6513948, (ONE0, ONE0) => 5423632,
    (ONE0, ONE1) => 5431956, (ONE0, TWO0) => 4339072, (ONE0, TWO1) => 4341452,
    (ONE0, MM01) => 4339524, (ONE0, MM10) => 4340352, (ONE0, G00) => 21648080,
    (ONE0, G01) => 21644232, (ONE0, G10) => 21646048, (ONE0, G11) => 21642992,
    (ONE1, ZERO) => 5080, (ONE1, POW2) => 1108160, (ONE1, ALL1) => 1084880,
    (ONE1, R0R1) => 6531800, (ONE1, R1R0) => 6579388, (ONE1, ONE0) => 5431956,
    (ONE1, ONE1) => 5485220, (ONE1, TWO0) => 4346100, (ONE1, TWO1) => 4377808,
    (ONE1, MM01) => 4364768, (ONE1, MM10) => 4351824, (ONE1, G00) => 21544384,
    (ONE1, G01) => 21485780, (ONE1, G10) => 21711740, (ONE1, G11) => 21674208,
    (TWO0, ZERO) => 4064, (TWO0, POW2) => 886528, (TWO0, ALL1) => 867584,
    (TWO0, R0R1) => 5211808, (TWO0, R1R0) => 5210932, (TWO0, ONE0) => 4339072,
    (TWO0, ONE1) => 4346100, (TWO0, TWO0) => 3471520, (TWO0, TWO1) => 3474468,
    (TWO0, MM01) => 3471456, (TWO0, MM10) => 3473696, (TWO0, G00) => 17320892,
    (TWO0, G01) => 17321508, (TWO0, G10) => 17323144, (TWO0, G11) => 17318492,
    (TWO1, ZERO) => 4064, (TWO1, POW2) => 886528, (TWO1, ALL1) => 867904,
    (TWO1, R0R1) => 5217668, (TWO1, R1R0) => 5246976, (TWO1, ONE0) => 4341452,
    (TWO1, ONE1) => 4377808, (TWO1, TWO0) => 3474468, (TWO1, TWO1) => 3496528,
    (TWO1, MM01) => 3487720, (TWO1, MM10) => 3480900, (TWO1, G00) => 17364468,
    (TWO1, G01) => 17341780, (TWO1, G10) => 17347608, (TWO1, G11) => 17335852,
    (MM01, ZERO) => 4064, (MM01, POW2) => 886528, (MM01, ALL1) => 867584,
    (MM01, R0R1) => 5212284, (MM01, R1R0) => 5236336, (MM01, ONE0) => 4339524,
    (MM01, ONE1) => 4364768, (MM01, TWO0) => 3471456, (MM01, TWO1) => 3487720,
    (MM01, MM01) => 3480276, (MM01, MM10) => 3475896, (MM01, G00) => 17335184,
    (MM01, G01) => 17325316, (MM01, G10) => 17333780, (MM01, G11) => 17326824,
    (MM10, ZERO) => 4064, (MM10, POW2) => 886528, (MM10, ALL1) => 867904,
    (MM10, R0R1) => 5217376, (MM10, R1R0) => 5214356, (MM10, ONE0) => 4340352,
    (MM10, ONE1) => 4351824, (MM10, TWO0) => 3473696, (MM10, TWO1) => 3480900,
    (MM10, MM01) => 3475896, (MM10, MM10) => 3477984, (MM10, G00) => 17334084,
    (MM10, G01) => 17333740, (MM10, G10) => 17329636, (MM10, G11) => 17326276,
    (G00, ZERO) => 6096, (G00, POW2) => 1329792, (G00, ALL1) => 2435016,
    (G00, R0R1) => 25992816, (G00, R1R0) => 25505860, (G00, ONE0) => 21648080,
    (G00, ONE1) => 21544384, (G00, TWO0) => 17320892, (G00, TWO1) => 17364468,
    (G00, MM01) => 17335184, (G00, MM10) => 17334084, (G00, G00) => 82620660,
    (G00, G01) => 90497672, (G00, G10) => 91510484, (G00, G11) => 91478436,
    (G01, ZERO) => 6096, (G01, POW2) => 1329792, (G01, ALL1) => 3571200,
    (G01, R0R1) => 25606916, (G01, R1R0) => 25995248, (G01, ONE0) => 21644232,
    (G01, ONE1) => 21485780, (G01, TWO0) => 17321508, (G01, TWO1) => 17341780,
    (G01, MM01) => 17325316, (G01, MM10) => 17333740, (G01, G00) => 90497672,
    (G01, G01) => 84061184, (G01, G10) => 91855736, (G01, G11) => 91837964,
    (G10, ZERO) => 6096, (G10, POW2) => 1329792, (G10, ALL1) => 3934748,
    (G10, R0R1) => 25990096, (G10, R1R0) => 25857148, (G10, ONE0) => 21646048,
    (G10, ONE1) => 21711740, (G10, TWO0) => 17323144, (G10, TWO1) => 17347608,
    (G10, MM01) => 17333780, (G10, MM10) => 17329636, (G10, G00) => 91510484,
    (G10, G01) => 91855736, (G10, G10) => 82542996, (G10, G11) => 88915988,
    (G11, ZERO) => 6096, (G11, POW2) => 1329792, (G11, ALL1) => 4319512,
    (G11, R0R1) => 25983592, (G11, R1R0) => 25609468, (G11, ONE0) => 21642992,
    (G11, ONE1) => 21674208, (G11, TWO0) => 17318492, (G11, TWO1) => 17335852,
    (G11, MM01) => 17326824, (G11, MM10) => 17326276, (G11, G00) => 91478436,
    (G11, G01) => 91837964, (G11, G10) => 88915988, (G11, G11) => 82881104,
)


const SELTZO_TWO_PROD_BF16_CRC = Dict{Tuple{SELTZOClass,SELTZOClass},UInt32}(
    (ZERO, ZERO) => 0x66001AE3, (ZERO, POW2) => 0x49C81023, (ZERO, ALL1) => 0xFF56E7B2,
    (ZERO, R0R1) => 0xBF9947E5, (ZERO, R1R0) => 0xAE066A73, (ZERO, ONE0) => 0x12DE3276,
    (ZERO, ONE1) => 0xFB6DA792, (ZERO, TWO0) => 0x78AEF2E7, (ZERO, TWO1) => 0xB316FDF7,
    (ZERO, MM01) => 0x3E390817, (ZERO, MM10) => 0xF5810707, (ZERO, G00) => 0xFDE652A2,
    (ZERO, G01) => 0x0E37647F, (ZERO, G10) => 0x1FA849E9, (ZERO, G11) => 0xEC797F34,
    (POW2, ZERO) => 0x7880C516, (POW2, POW2) => 0x11FDE8BF, (POW2, ALL1) => 0xC478F2BB,
    (POW2, R0R1) => 0xAAE52677, (POW2, R1R0) => 0xF6A391FD, (POW2, ONE0) => 0x891A1B5A,
    (POW2, ONE1) => 0xD995478A, (POW2, TWO0) => 0x8F8728C4, (POW2, TWO1) => 0x97B369A9,
    (POW2, MM01) => 0x8794E81F, (POW2, MM10) => 0x9FA0A972, (POW2, G00) => 0xCF70F9E0,
    (POW2, G01) => 0xFB4D6B66, (POW2, G10) => 0xA70BDCEC, (POW2, G11) => 0x93364E6A,
    (ALL1, ZERO) => 0x133C0E12, (ALL1, POW2) => 0x38555BA3, (ALL1, ALL1) => 0x2CAC77A1,
    (ALL1, R0R1) => 0x68124630, (ALL1, R1R0) => 0x5D948EBE, (ALL1, ONE0) => 0xDD797D75,
    (ALL1, ONE1) => 0x90E2B739, (ALL1, TWO0) => 0x1045FFEE, (ALL1, TWO1) => 0x94FF6FC7,
    (ALL1, MM01) => 0x1EFF203D, (ALL1, MM10) => 0x97C89900, (ALL1, G00) => 0x2860DC86,
    (ALL1, G01) => 0x8F3D1D09, (ALL1, G10) => 0x183A1417, (ALL1, G11) => 0x91DA5F18,
    (R0R1, ZERO) => 0xF70B1AA1, (R0R1, POW2) => 0x5F3EAB7D, (R0R1, ALL1) => 0x2B81F1D9,
    (R0R1, R0R1) => 0x8A8EDC7B, (R0R1, R1R0) => 0x980B1248, (R0R1, ONE0) => 0xE3EFDE44,
    (R0R1, ONE1) => 0x81A3D985, (R0R1, TWO0) => 0x7E432A30, (R0R1, TWO1) => 0x4FB26887,
    (R0R1, MM01) => 0x17F30C4E, (R0R1, MM10) => 0x64A85927, (R0R1, G00) => 0xD2F67DE1,
    (R0R1, G01) => 0x09D754DF, (R0R1, G10) => 0x98E28EBC, (R0R1, G11) => 0xDCAE5775,
    (R1R0, ZERO) => 0xAB4AC68D, (R1R0, POW2) => 0x2173ACB6, (R1R0, ALL1) => 0xA6A3A5E4,
    (R1R0, R0R1) => 0xB485B565, (R1R0, R1R0) => 0x9D14E286, (R1R0, ONE0) => 0xE931F2B3,
    (R1R0, ONE1) => 0x0AF4EE0D, (R1R0, TWO0) => 0xE4C980A4, (R1R0, TWO1) => 0x37A707BA,
    (R1R0, MM01) => 0x7B7FCCF1, (R1R0, MM10) => 0x3E6BAF36, (R1R0, G00) => 0xB52A865E,
    (R1R0, G01) => 0x25E167B2, (R1R0, G10) => 0x99B59626, (R1R0, G11) => 0x4FB7B283,
    (ONE0, ZERO) => 0x90EA99CB, (ONE0, POW2) => 0xF661D170, (ONE0, ALL1) => 0xE5C99A25,
    (ONE0, R0R1) => 0xF817998F, (ONE0, R1R0) => 0xEA3B23D5, (ONE0, ONE0) => 0x2865D657,
    (ONE0, ONE1) => 0x46F8E26F, (ONE0, TWO0) => 0x2CD5F542, (ONE0, TWO1) => 0x639888DA,
    (ONE0, MM01) => 0xBBA70F2F, (ONE0, MM10) => 0x063D68A5, (ONE0, G00) => 0xEA98CF24,
    (ONE0, G01) => 0xDBBD9725, (ONE0, G10) => 0x26AFBF5F, (ONE0, G11) => 0xE712126C,
    (ONE1, ZERO) => 0x111925F3, (ONE1, POW2) => 0x95603CC3, (ONE1, ALL1) => 0x02155808,
    (ONE1, R0R1) => 0xA0E384F2, (ONE1, R1R0) => 0xA27D2E9E, (ONE1, ONE0) => 0xD023073E,
    (ONE1, ONE1) => 0xB4A4DEE6, (ONE1, TWO0) => 0x9CBBCBD0, (ONE1, TWO1) => 0xB39E96E4,
    (ONE1, MM01) => 0x949F0EE1, (ONE1, MM10) => 0x7D07D2FB, (ONE1, G00) => 0x2A7CCBDF,
    (ONE1, G01) => 0xC8E01209, (ONE1, G10) => 0xB8C01F8C, (ONE1, G11) => 0x90857425,
    (TWO0, ZERO) => 0xF52EE106, (TWO0, POW2) => 0xC62EAF7E, (TWO0, ALL1) => 0x1A6B6758,
    (TWO0, R0R1) => 0x04031473, (TWO0, R1R0) => 0x3C9256F8, (TWO0, ONE0) => 0x959E54CA,
    (TWO0, ONE1) => 0xDEBFEB32, (TWO0, TWO0) => 0x9E5BA4A8, (TWO0, TWO1) => 0x7B235916,
    (TWO0, MM01) => 0x508DA3BE, (TWO0, MM10) => 0xFD2686FB, (TWO0, G00) => 0x43532120,
    (TWO0, G01) => 0x32BCC134, (TWO0, G10) => 0x90407B8A, (TWO0, G11) => 0x8E4D017F,
    (TWO1, ZERO) => 0x2C76ACAA, (TWO1, POW2) => 0x0AA07B0F, (TWO1, ALL1) => 0x98130C69,
    (TWO1, R0R1) => 0xE2C596F0, (TWO1, R1R0) => 0xCA3F67CB, (TWO1, ONE0) => 0x93BE86F4,
    (TWO1, ONE1) => 0x77C003DE, (TWO1, TWO0) => 0x2E0F79AB, (TWO1, TWO1) => 0xF1960F26,
    (TWO1, MM01) => 0x4831BF0F, (TWO1, MM10) => 0x7F7E757B, (TWO1, G00) => 0xAC3332D9,
    (TWO1, G01) => 0x0B61D6AD, (TWO1, G10) => 0xEE1313D2, (TWO1, G11) => 0x6C3A3321,
    (MM01, ZERO) => 0x4142F7CD, (MM01, POW2) => 0x7EF0CEFE, (MM01, ALL1) => 0x570453C5,
    (MM01, R0R1) => 0xF2027218, (MM01, R1R0) => 0x543BDC85, (MM01, ONE0) => 0x8BAD8238,
    (MM01, ONE1) => 0x95735836, (MM01, TWO0) => 0x878FA75F, (MM01, TWO1) => 0x0AAA3EFB,
    (MM01, MM01) => 0x5CF7D30C, (MM01, MM10) => 0xE06F624B, (MM01, G00) => 0x2BACC732,
    (MM01, G01) => 0x481CEA74, (MM01, G10) => 0x456C5741, (MM01, G11) => 0x6178F144,
    (MM10, ZERO) => 0x981ABA61, (MM10, POW2) => 0xB27E1A8F, (MM10, ALL1) => 0xF21DA9CD,
    (MM10, R0R1) => 0x079DD269, (MM10, R1R0) => 0x5F1DE397, (MM10, ONE0) => 0x27F73E17,
    (MM10, ONE1) => 0x7014D088, (MM10, TWO0) => 0xE0BCDD05, (MM10, TWO1) => 0x7DDC5F2A,
    (MM10, MM01) => 0x48521AFC, (MM10, MM10) => 0x6A017FDE, (MM10, G00) => 0xDD040D9C,
    (MM10, G01) => 0xFA1B8242, (MM10, G10) => 0xCB356C02, (MM10, G11) => 0x3EB49649,
    (G00, ZERO) => 0x99FFE637, (G00, POW2) => 0x300F578A, (G00, ALL1) => 0x82BF59F4,
    (G00, R0R1) => 0xEC910024, (G00, R1R0) => 0xAFC30D3D, (G00, ONE0) => 0x731AA8FD,
    (G00, ONE1) => 0xFE77F73A, (G00, TWO0) => 0x11F8BDCD, (G00, TWO1) => 0xBE345A1C,
    (G00, MM01) => 0x6688609A, (G00, MM10) => 0xD9DF666C, (G00, G00) => 0xBE8F9657,
    (G00, G01) => 0xDA6E24A6, (G00, G10) => 0x3849D68F, (G00, G11) => 0x870DB0EE,
    (G01, ZERO) => 0x5164807C, (G01, POW2) => 0x1A345533, (G01, ALL1) => 0xDEE2784B,
    (G01, R0R1) => 0x2A706846, (G01, R1R0) => 0xCC3D76DD, (G01, ONE0) => 0x8CBDC74D,
    (G01, ONE1) => 0x0BDD7F2D, (G01, TWO0) => 0xDEB912EA, (G01, TWO1) => 0x1C788DB0,
    (G01, MM01) => 0x25C1323B, (G01, MM10) => 0x0BBDB168, (G01, G00) => 0xA851EBF5,
    (G01, G01) => 0x9B002B10, (G01, G10) => 0xFA66DF38, (G01, G11) => 0x49BBC0C1,
    (G10, ZERO) => 0x0D255C50, (G10, POW2) => 0x647952F8, (G10, ALL1) => 0x85CC1509,
    (G10, R0R1) => 0x62246D2E, (G10, R1R0) => 0x3AF980FE, (G10, ONE0) => 0xF6395BD3,
    (G10, ONE1) => 0xE92A25B0, (G10, TWO0) => 0xCC901F57, (G10, TWO1) => 0xD818417E,
    (G10, MM01) => 0xFAA9F00F, (G10, MM10) => 0x49DA025D, (G10, G00) => 0x9A94DD2A,
    (G10, G01) => 0x5D6E3179, (G10, G10) => 0x55C75709, (G10, G11) => 0x8FAC1669,
    (G11, ZERO) => 0xC5BE3A1B, (G11, POW2) => 0x4E425041, (G11, ALL1) => 0xB73F13DF,
    (G11, R0R1) => 0x913B3517, (G11, R1R0) => 0xAA7CEBD0, (G11, ONE0) => 0xBDB23EAE,
    (G11, ONE1) => 0xE0CAE1B9, (G11, TWO0) => 0x05B8F17A, (G11, TWO1) => 0x7DA7B14F,
    (G11, MM01) => 0x05080631, (G11, MM10) => 0xAFF0EC07, (G11, G00) => 0x0BCAEED9,
    (G11, G01) => 0x074E3F13, (G11, G10) => 0x713B87E3, (G11, G11) => 0x94A2DF6D,
)


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

    # generate_abstraction_data(SELTZOAbstraction, :TwoSum, Float16,
    #     319_985_950, 0xCC55FA4F)
    # generate_abstraction_data(SELTZOAbstraction, :TwoSum, BFloat16,
    #     1_172_449_766, 0xCB0D263C)
    # generate_abstraction_data(SELTZOAbstraction, :TwoProd, Float16,
    #     1_273_864_440, 0x00AD2611)
    # generate_abstraction_data(SELTZOAbstraction, :TwoProd, BFloat16,
    #     3_125_732_804, 0x83D08863)

    generate_seltzo_data(:TwoSum, Float16,
        SELTZO_TWO_SUM_F16_COUNT, SELTZO_TWO_SUM_F16_CRC)
    generate_seltzo_data(:TwoSum, BFloat16,
        SELTZO_TWO_SUM_BF16_COUNT, SELTZO_TWO_SUM_BF16_CRC)
    generate_seltzo_data(:TwoProd, Float16,
        SELTZO_TWO_PROD_F16_COUNT, SELTZO_TWO_PROD_F16_CRC)
    generate_seltzo_data(:TwoProd, BFloat16,
        SELTZO_TWO_PROD_BF16_COUNT, SELTZO_TWO_PROD_BF16_CRC)

end
