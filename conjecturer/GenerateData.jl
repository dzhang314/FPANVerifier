using BFloat16s

@inline Base.fma(x::BFloat16, y::BFloat16, z::BFloat16) =
    BFloat16(fma(Float32(x), Float32(y), Float32(z)))

push!(LOAD_PATH, @__DIR__)
using FloatAbstractions


if !isfile("SE-TwoSum-Float16.bin")
    open("SE-TwoSum-Float16.bin", "w") do io
        write(io, two_sum_abstractions(SEAbstraction, Float16))
    end
end

if !isfile("SE-TwoProd-Float16.bin")
    open("SE-TwoProd-Float16.bin", "w") do io
        write(io, two_prod_abstractions(SEAbstraction, Float16))
    end
end

if !isfile("SE-TwoSum-BFloat16.bin")
    open("SE-TwoSum-BFloat16.bin", "w") do io
        write(io, two_sum_abstractions(SEAbstraction, BFloat16))
    end
end

if !isfile("SE-TwoProd-BFloat16.bin")
    open("SE-TwoProd-BFloat16.bin", "w") do io
        write(io, two_prod_abstractions(SEAbstraction, BFloat16))
    end
end


if !isfile("SETZ-TwoSum-Float16.bin")
    open("SETZ-TwoSum-Float16.bin", "w") do io
        write(io, two_sum_abstractions(SETZAbstraction, Float16))
    end
end

if !isfile("SETZ-TwoProd-Float16.bin")
    open("SETZ-TwoProd-Float16.bin", "w") do io
        write(io, two_prod_abstractions(SETZAbstraction, Float16))
    end
end

if !isfile("SETZ-TwoSum-BFloat16.bin")
    open("SETZ-TwoSum-BFloat16.bin", "w") do io
        write(io, two_sum_abstractions(SETZAbstraction, BFloat16))
    end
end

if !isfile("SETZ-TwoProd-BFloat16.bin")
    open("SETZ-TwoProd-BFloat16.bin", "w") do io
        write(io, two_prod_abstractions(SETZAbstraction, BFloat16))
    end
end


if !isfile("SELTZO-TwoSum-Float16.bin")
    open("SELTZO-TwoSum-Float16.bin", "w") do io
        write(io, two_sum_abstractions(SELTZOAbstraction, Float16))
    end
end

if !isfile("SELTZO-TwoProd-Float16.bin")
    open("SELTZO-TwoProd-Float16.bin", "w") do io
        write(io, two_prod_abstractions(SELTZOAbstraction, Float16))
    end
end

if !isfile("SELTZO-TwoSum-BFloat16.bin")
    open("SELTZO-TwoSum-BFloat16.bin", "w") do io
        write(io, two_sum_abstractions(SELTZOAbstraction, BFloat16))
    end
end

if !isfile("SELTZO-TwoProd-BFloat16.bin")
    open("SELTZO-TwoProd-BFloat16.bin", "w") do io
        write(io, two_prod_abstractions(SELTZOAbstraction, BFloat16))
    end
end