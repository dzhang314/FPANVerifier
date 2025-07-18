using Base.Threads: @threads
using BFloat16s: BFloat16
using Quadmath: Float128
using Test: @test, @testset

push!(LOAD_PATH, @__DIR__)
using FloatAbstractions


function verify_exhaustive(::Type{T}, ::Type{U}) where {T,U}
    @threads for i = typemin(U):typemax(U)
        x = reinterpret(T, i)
        se = SEAbstraction(x)
        setz = SETZAbstraction(x)
        seltzo = SELTZOAbstraction(x)

        @assert signbit(x) === signbit(se)
        @assert signbit(x) === signbit(setz)
        @assert signbit(x) === signbit(seltzo)

        @assert unsafe_exponent(x) === unsafe_exponent(se)
        @assert unsafe_exponent(x) === unsafe_exponent(setz)
        @assert unsafe_exponent(x) === unsafe_exponent(seltzo)

        @assert mantissa_trailing_zeros(x) === mantissa_trailing_zeros(setz)

        @assert mantissa_leading_bit(x) === mantissa_leading_bit(seltzo)
        @assert mantissa_leading_bits(x) === mantissa_leading_bits(seltzo)
        @assert mantissa_leading_zeros(x) === mantissa_leading_zeros(seltzo)
        @assert mantissa_leading_ones(x) === mantissa_leading_ones(seltzo)

        @assert mantissa_trailing_bit(x) === mantissa_trailing_bit(seltzo)
        @assert mantissa_trailing_bits(x) === mantissa_trailing_bits(seltzo)
        @assert mantissa_trailing_zeros(x) === mantissa_trailing_zeros(seltzo)
        @assert mantissa_trailing_ones(x) === mantissa_trailing_ones(seltzo)

        @assert unpack(se) ===
                (unpack_bools(se)..., unpack_ints(se)...)
        @assert unpack(se, T) ===
                (unpack_bools(se, T)..., unpack_ints(se, T)...)
        @assert unpack(setz) ===
                (unpack_bools(setz)..., unpack_ints(setz)...)
        @assert unpack(setz, T) ===
                (unpack_bools(setz, T)..., unpack_ints(setz, T)...)
        @assert unpack(seltzo) ===
                (unpack_bools(seltzo)..., unpack_ints(seltzo)...)
        @assert unpack(seltzo, T) ===
                (unpack_bools(seltzo, T)..., unpack_ints(seltzo, T)...)
    end
    return true
end


@testset "FloatAbstractions (exhaustive)" begin
    @test verify_exhaustive(Float16, UInt16)
    @test verify_exhaustive(BFloat16, UInt16)
    @test verify_exhaustive(Float32, UInt32)
end


function verify_random(::Type{T}, ::Type{U}, n::Int) where {T,U}
    @threads for _ = 1:n
        x = reinterpret(T, rand(U))
        se = SEAbstraction(x)
        setz = SETZAbstraction(x)
        seltzo = SELTZOAbstraction(x)

        @assert signbit(x) === signbit(se)
        @assert signbit(x) === signbit(setz)
        @assert signbit(x) === signbit(seltzo)

        @assert unsafe_exponent(x) === unsafe_exponent(se)
        @assert unsafe_exponent(x) === unsafe_exponent(setz)
        @assert unsafe_exponent(x) === unsafe_exponent(seltzo)

        @assert mantissa_trailing_zeros(x) === mantissa_trailing_zeros(setz)

        @assert mantissa_leading_bit(x) === mantissa_leading_bit(seltzo)
        @assert mantissa_leading_bits(x) === mantissa_leading_bits(seltzo)
        @assert mantissa_leading_zeros(x) === mantissa_leading_zeros(seltzo)
        @assert mantissa_leading_ones(x) === mantissa_leading_ones(seltzo)

        @assert mantissa_trailing_bit(x) === mantissa_trailing_bit(seltzo)
        @assert mantissa_trailing_bits(x) === mantissa_trailing_bits(seltzo)
        @assert mantissa_trailing_zeros(x) === mantissa_trailing_zeros(seltzo)
        @assert mantissa_trailing_ones(x) === mantissa_trailing_ones(seltzo)

        @assert unpack(se) ===
                (unpack_bools(se)..., unpack_ints(se)...)
        @assert unpack(se, T) ===
                (unpack_bools(se, T)..., unpack_ints(se, T)...)
        @assert unpack(setz) ===
                (unpack_bools(setz)..., unpack_ints(setz)...)
        @assert unpack(setz, T) ===
                (unpack_bools(setz, T)..., unpack_ints(setz, T)...)
        @assert unpack(seltzo) ===
                (unpack_bools(seltzo)..., unpack_ints(seltzo)...)
        @assert unpack(seltzo, T) ===
                (unpack_bools(seltzo, T)..., unpack_ints(seltzo, T)...)
    end
    return true
end


@testset "FloatAbstractions (random)" begin
    @test verify_random(Float64, UInt64, 10000000000)
    @test verify_random(Float128, UInt128, 1000000000)
end
