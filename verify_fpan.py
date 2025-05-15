#!/usr/bin/env python3

import z3

from se_lemmas import two_sum_se_lemmas
from setz_lemmas import two_sum_setz_lemmas
from seltzo_lemmas import two_sum_seltzo_lemmas
from sys import argv
from typing import Self


GLOBAL_PRECISION: z3.ArithRef = z3.Int("PRECISION")
GLOBAL_ZERO_EXPONENT: z3.ArithRef = z3.Int("ZERO_EXPONENT")
GLOBAL_MANTISSA_WIDTH: z3.ArithRef = GLOBAL_PRECISION - 1


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

        # We model a hypothetical floating-point datatype with infinite
        # exponent range, eliminating the possibility of overflow or underflow.
        # This means that all results proven in this model assume that no
        # overflow or underflow occurs when performing the actual computation.

        # We do not consider infinities or NaNs in this model, so all
        # floating-point numbers are either positive, negative, or zero.

        # When analyzing floating-point accumulation networks,
        # only relative exponent values matter, not absolute values.
        # We can set the zero point anywhere without loss of generality.
        solver.add(self.exponent >= GLOBAL_ZERO_EXPONENT)
        self.is_zero: z3.BoolRef = self.exponent == GLOBAL_ZERO_EXPONENT

        solver.add(self.num_leading_bits > 0)
        solver.add(self.num_trailing_bits > 0)
        solver.add(
            z3.Implies(
                self.is_zero,
                z3.And(
                    z3.Not(self.leading_bit),
                    z3.Not(self.trailing_bit),
                    self.num_leading_bits == GLOBAL_MANTISSA_WIDTH,
                    self.num_trailing_bits == GLOBAL_MANTISSA_WIDTH,
                ),
            )
        )
        solver.add(
            z3.Implies(
                self.leading_bit == self.trailing_bit,
                z3.Or(
                    self.num_leading_bits + self.num_trailing_bits
                    < GLOBAL_MANTISSA_WIDTH,
                    z3.And(
                        self.num_leading_bits == GLOBAL_MANTISSA_WIDTH,
                        self.num_trailing_bits == GLOBAL_MANTISSA_WIDTH,
                    ),
                ),
            )
        )
        solver.add(
            z3.Implies(
                self.leading_bit != self.trailing_bit,
                z3.Or(
                    self.num_leading_bits + self.num_trailing_bits
                    < GLOBAL_MANTISSA_WIDTH - 1,
                    self.num_leading_bits + self.num_trailing_bits
                    == GLOBAL_MANTISSA_WIDTH,
                ),
            )
        )

    def can_equal(self, other: Self) -> z3.BoolRef:
        return z3.Or(
            z3.And(self.is_zero, other.is_zero),
            z3.And(
                self.sign_bit == other.sign_bit,
                self.leading_bit == other.leading_bit,
                self.trailing_bit == other.trailing_bit,
                self.exponent == other.exponent,
                self.num_leading_bits == other.num_leading_bits,
                self.num_trailing_bits == other.num_trailing_bits,
            ),
        )

    def is_power_of_two(self) -> z3.BoolRef:
        return z3.And(
            z3.Not(self.is_zero),
            z3.Not(self.leading_bit),
            z3.Not(self.trailing_bit),
            self.num_leading_bits == GLOBAL_MANTISSA_WIDTH,
            self.num_trailing_bits == GLOBAL_MANTISSA_WIDTH,
        )

    def s_dominates(self, other: Self) -> z3.BoolRef:
        ntz: z3.ArithRef = z3.If(
            self.trailing_bit, z3.IntVal(0), self.num_trailing_bits
        )
        return z3.Or(
            other.is_zero,
            self.exponent >= other.exponent + (GLOBAL_PRECISION - ntz),
        )

    def p_dominates(self, other: Self) -> z3.BoolRef:
        return z3.Or(
            other.is_zero,
            self.exponent >= other.exponent + GLOBAL_PRECISION,
        )

    def ulp_dominates(self, other: Self) -> z3.BoolRef:
        return z3.Or(
            other.is_zero,
            self.exponent > other.exponent + (GLOBAL_PRECISION - 1),
            z3.And(
                self.exponent == other.exponent + (GLOBAL_PRECISION - 1),
                other.is_power_of_two(),
            ),
        )

    def qd_dominates(self, other: Self) -> z3.BoolRef:
        return z3.Or(
            other.is_zero,
            self.exponent > other.exponent + GLOBAL_PRECISION,
            z3.And(
                self.exponent == other.exponent + GLOBAL_PRECISION,
                other.is_power_of_two(),
            ),
        )

    def strongly_dominates(self, other: Self) -> z3.BoolRef:
        return z3.Or(
            other.is_zero,
            self.exponent > other.exponent + (GLOBAL_PRECISION + 1),
            z3.And(
                self.exponent == other.exponent + (GLOBAL_PRECISION + 1),
                z3.Or(
                    self.sign_bit == other.sign_bit,
                    z3.Not(self.is_power_of_two()),
                    other.is_power_of_two(),
                ),
            ),
            z3.And(
                self.exponent == other.exponent + GLOBAL_PRECISION,
                other.is_power_of_two(),
                z3.Not(self.trailing_bit),
                z3.Or(self.sign_bit == other.sign_bit, z3.Not(self.is_power_of_two())),
            ),
        )

    def is_smaller_than(self, other: Self, magnitude: int | z3.ArithRef) -> z3.BoolRef:
        return z3.Or(self.is_zero, self.exponent + magnitude < other.exponent)
