import z3


GLOBAL_PRECISION: z3.ArithRef = z3.Int("PRECISION")
GLOBAL_ZERO_EXPONENT: z3.ArithRef = z3.Int("ZERO_EXPONENT")


class SELTZOVariable(object):

    def __init__(
        self,
        solver: z3.Solver,
        name: str,
    ) -> None:

        self.name: str = name
        self.sign_bit: z3.BoolRef = z3.Bool(name + "_sign_bit")
        self.leading_bit: z3.BoolRef = z3.Bool(name + "_leading_bit")
        self.trailing_bit: z3.BoolRef = z3.Bool(name + "_trailing_bit")
        self.exponent: z3.ArithRef = z3.Int(name + "_exponent")
        self.num_leading_bits: z3.ArithRef = z3.Int(name + "_num_leading_bits")
        self.num_trailing_bits: z3.ArithRef = z3.Int(name + "_num_trailing_bits")

        # FPANVerifier works in an abstract floating-point domain where all
        # floating-point numbers are finite and normalized or zero. Infinities,
        # NaNs, and subnormal numbers are not explicitly modeled in the SELTZO
        # abstraction, and overflow and underflow are assumed not to occur.

        # These assumptions incur no loss of generality for the purpose of
        # analyzing floating-point accumulation networks, which are equivariant
        # to scaling of all inputs by a common power of two (i.e., a uniform
        # translation of all exponents). This means that their behavior is
        # identical on normalized and subnormal inputs, so any statement that
        # holds for normalized inputs also holds for subnormal inputs.

        # In fact, these assumptions actually make our results stronger!
        # All statements proven by FPANVerifier are true, not only in the
        # domain of concrete floating-point numbers, but also in an extended
        # domain with infinite exponent range.

        solver.add(self.exponent >= GLOBAL_ZERO_EXPONENT)
        self.is_zero: z3.BoolRef = self.exponent == GLOBAL_ZERO_EXPONENT

        solver.add(self.num_leading_bits > 0)
        solver.add(self.num_trailing_bits > 0)
        solver.add(
            z3.Implies(
                self.is_zero,
                z3.And(
                    ~self.leading_bit,
                    ~self.trailing_bit,
                    self.num_leading_bits == GLOBAL_PRECISION - 1,
                    self.num_trailing_bits == GLOBAL_PRECISION - 1,
                ),
            )
        )
        solver.add(
            z3.Implies(
                self.leading_bit == self.trailing_bit,
                z3.Or(
                    self.num_leading_bits + self.num_trailing_bits
                    <= GLOBAL_PRECISION - 2,
                    z3.And(
                        self.num_leading_bits == GLOBAL_PRECISION - 1,
                        self.num_trailing_bits == GLOBAL_PRECISION - 1,
                    ),
                ),
            )
        )
        solver.add(
            z3.Implies(
                self.leading_bit != self.trailing_bit,
                z3.Or(
                    self.num_leading_bits + self.num_trailing_bits
                    <= GLOBAL_PRECISION - 3,
                    self.num_leading_bits + self.num_trailing_bits
                    == GLOBAL_PRECISION - 1,
                ),
            )
        )

    def can_equal(self, other: "SELTZOVariable") -> z3.BoolRef:
        return z3.And(
            self.sign_bit == other.sign_bit,
            self.leading_bit == other.leading_bit,
            self.trailing_bit == other.trailing_bit,
            self.exponent == other.exponent,
            self.num_leading_bits == other.num_leading_bits,
            self.num_trailing_bits == other.num_trailing_bits,
        )

    def is_power_of_two(self) -> z3.BoolRef:
        return z3.And(
            ~self.is_zero,
            ~self.leading_bit,
            ~self.trailing_bit,
            self.num_leading_bits == GLOBAL_PRECISION - 1,
            self.num_trailing_bits == GLOBAL_PRECISION - 1,
        )

    def s_dominates(self, other: "SELTZOVariable") -> z3.BoolRef:
        return z3.Or(
            other.is_zero,
            self.exponent >= other.exponent + GLOBAL_PRECISION,
            z3.And(
                ~self.trailing_bit,
                self.exponent + self.num_trailing_bits
                >= other.exponent + GLOBAL_PRECISION,
            ),
        )

    def p_dominates(self, other: "SELTZOVariable") -> z3.BoolRef:
        return z3.Or(
            other.is_zero,
            self.exponent >= other.exponent + GLOBAL_PRECISION,
        )

    def ulp_dominates(self, other: "SELTZOVariable") -> z3.BoolRef:
        return z3.Or(
            other.is_zero,
            self.exponent > other.exponent + (GLOBAL_PRECISION - 1),
            z3.And(
                self.exponent == other.exponent + (GLOBAL_PRECISION - 1),
                other.is_power_of_two(),
            ),
        )

    def qd_dominates(self, other: "SELTZOVariable") -> z3.BoolRef:
        return z3.Or(
            other.is_zero,
            self.exponent > other.exponent + GLOBAL_PRECISION,
            z3.And(
                self.exponent == other.exponent + GLOBAL_PRECISION,
                other.is_power_of_two(),
            ),
        )

    def strongly_dominates(self, other: "SELTZOVariable") -> z3.BoolRef:
        return z3.Or(
            other.is_zero,
            self.exponent > other.exponent + (GLOBAL_PRECISION + 1),
            z3.And(
                self.exponent == other.exponent + (GLOBAL_PRECISION + 1),
                z3.Or(
                    self.sign_bit == other.sign_bit,
                    ~self.is_power_of_two(),
                    other.is_power_of_two(),
                ),
            ),
            z3.And(
                self.exponent == other.exponent + GLOBAL_PRECISION,
                other.is_power_of_two(),
                ~self.trailing_bit,
                z3.Or(
                    self.sign_bit == other.sign_bit,
                    ~self.is_power_of_two(),
                ),
            ),
        )

    def is_smaller_than(
        self,
        other: "SELTZOVariable",
        magnitude: int | z3.ArithRef,
    ) -> z3.BoolRef:
        return z3.Or(
            self.is_zero,
            self.exponent + magnitude < other.exponent,
            z3.And(
                self.exponent + magnitude == other.exponent,
                z3.Or(
                    self.is_power_of_two(),
                    z3.And(~self.leading_bit, other.leading_bit),
                    z3.And(
                        self.leading_bit,
                        other.leading_bit,
                        self.num_leading_bits < other.num_leading_bits,
                    ),
                    z3.And(
                        ~self.leading_bit,
                        ~other.leading_bit,
                        self.num_leading_bits > other.num_leading_bits,
                    ),
                ),
            ),
        )

    def can_fast_two_sum(self, other: "SELTZOVariable") -> z3.BoolRef:
        return z3.Or(
            self.is_zero,
            other.is_zero,
            self.exponent >= other.exponent,
            z3.And(
                ~self.trailing_bit,
                self.exponent + self.num_trailing_bits >= other.exponent,
            ),
        )
