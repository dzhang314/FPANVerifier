import z3
from enum import Enum, auto
from smt_utils import get_bool, get_int


FLOAT16_PRECISION: int = 11
FLOAT16_ZERO_EXPONENT: int = -15
FLOAT16_MIN_EXPONENT: int = FLOAT16_ZERO_EXPONENT + 1


GLOBAL_PRECISION: z3.ArithRef = z3.Int("PRECISION")
GLOBAL_ZERO_EXPONENT: z3.ArithRef = z3.Int("ZERO_EXPONENT")


class SELTZOClass(Enum):
    ZERO = auto()
    POW2 = auto()
    ALL1 = auto()
    R0R1 = auto()
    R1R0 = auto()
    ONE0 = auto()
    ONE1 = auto()
    TWO0 = auto()
    TWO1 = auto()
    MM01 = auto()
    MM10 = auto()
    G00 = auto()
    G01 = auto()
    G10 = auto()
    G11 = auto()


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

    def classify(self, model: z3.ModelRef) -> SELTZOClass:
        if get_bool(model, self.is_zero):
            return SELTZOClass.ZERO
        p: int = get_int(model, GLOBAL_PRECISION)
        lb: bool = get_bool(model, self.leading_bit)
        tb: bool = get_bool(model, self.trailing_bit)
        nlb: int = get_int(model, self.num_leading_bits)
        ntb: int = get_int(model, self.num_trailing_bits)
        if nlb == p - 1 and ntb == p - 1:
            if (not lb) and (not tb):
                return SELTZOClass.POW2
            if lb and tb:
                return SELTZOClass.ALL1
        elif nlb + ntb == p - 1:
            if (not lb) and tb:
                return SELTZOClass.R0R1
            if lb and (not tb):
                return SELTZOClass.R1R0
        elif nlb + ntb == p - 2:
            if lb and tb:
                return SELTZOClass.ONE0
            if (not lb) and (not tb):
                return SELTZOClass.ONE1
        elif nlb + ntb == p - 3:
            if lb and tb:
                return SELTZOClass.TWO0
            if (not lb) and (not tb):
                return SELTZOClass.TWO1
            if lb and (not tb):
                return SELTZOClass.MM01
            if (not lb) and tb:
                return SELTZOClass.MM10
        elif 1 < nlb + ntb < p - 3:
            if (not lb) and (not tb):
                return SELTZOClass.G00
            if (not lb) and tb:
                return SELTZOClass.G01
            if lb and (not tb):
                return SELTZOClass.G10
            if lb and tb:
                return SELTZOClass.G11
        assert False

    def key(self, model: z3.ModelRef, exponent_offset: int = 0) -> int:
        # For now, we only support lookup from Float16 data files.
        assert get_int(model, GLOBAL_PRECISION) == FLOAT16_PRECISION
        zero_exponent: int = get_int(model, GLOBAL_ZERO_EXPONENT)
        s: bool = get_bool(model, self.sign_bit)
        lb: bool = get_bool(model, self.leading_bit)
        tb: bool = get_bool(model, self.trailing_bit)
        e: int = get_int(model, self.exponent)
        if e == zero_exponent:
            e = FLOAT16_ZERO_EXPONENT
        else:
            assert e > zero_exponent
            e += exponent_offset
        assert -16383 <= e <= 16384
        nlb: int = get_int(model, self.num_leading_bits)
        assert 0 <= nlb <= 127
        ntb: int = get_int(model, self.num_trailing_bits)
        assert 0 <= ntb <= 127
        return (
            (int(s) << 31)
            | (int(lb) << 30)
            | (int(tb) << 29)
            | ((e + 16383) << 14)
            | (nlb << 7)
            | ntb
        )


def seltzo_keys(
    model: z3.ModelRef,
    variables: list[SELTZOVariable],
) -> list[int]:
    # For now, we only support lookup from Float16 data files.
    assert get_int(model, GLOBAL_PRECISION) == FLOAT16_PRECISION
    zero_exponent: int = get_int(model, GLOBAL_ZERO_EXPONENT)
    nonzero_exponents: list[int] = []
    for variable in variables:
        exponent: int = get_int(model, variable.exponent)
        if exponent != zero_exponent:
            assert exponent > zero_exponent
            nonzero_exponents.append(exponent)
    min_exponent: int = min(nonzero_exponents, default=0)
    return [
        variable.key(
            model,
            (FLOAT16_MIN_EXPONENT - min_exponent) + (FLOAT16_PRECISION + 1),
        )
        for variable in variables
    ]
