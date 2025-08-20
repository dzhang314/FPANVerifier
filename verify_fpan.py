#!/usr/bin/env python3

import z3

from sys import argv, stderr
from time import sleep
from typing import Self

from setz_lemmas import setz_two_sum_lemmas
from smt_utils import SMTJob, create_smt_job


Z3_ZERO: z3.ArithRef = z3.IntVal(0)
Z3_ONE: z3.ArithRef = z3.IntVal(1)
Z3_TWO: z3.ArithRef = z3.IntVal(2)
Z3_THREE: z3.ArithRef = z3.IntVal(3)
GLOBAL_PRECISION: z3.ArithRef = z3.Int("PRECISION")
GLOBAL_ZERO_EXPONENT: z3.ArithRef = z3.Int("ZERO_EXPONENT")
GLOBAL_MANTISSA_WIDTH: z3.ArithRef = GLOBAL_PRECISION - 1
INTERNAL_SEPARATOR: str = "__"


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


# TODO: Eventually, all `assert` statements should be
# replaced by informative user-facing error messages.


class VerifierContext(object):

    def __init__(self) -> None:
        self.solver: z3.Solver = z3.SolverFor("QF_LIA")
        self.variables: dict[str, list[SELTZOVariable]] = {}

    def handle_variable_command(self, arguments: list[str]) -> None:
        assert len(arguments) == 1
        name: str = arguments[0]
        assert INTERNAL_SEPARATOR not in name
        assert name not in self.variables
        self.variables[name] = [
            SELTZOVariable(self.solver, name + INTERNAL_SEPARATOR + "0")
        ]

    def handle_two_sum_command(self, arguments: list[str]) -> None:
        assert len(arguments) == 2
        name_a: str = arguments[0]
        name_b: str = arguments[1]
        assert name_a in self.variables
        assert name_b in self.variables
        list_a: list[SELTZOVariable] = self.variables[name_a]
        list_b: list[SELTZOVariable] = self.variables[name_b]
        old_a: SELTZOVariable = list_a[-1]
        old_b: SELTZOVariable = list_b[-1]
        new_a: SELTZOVariable = SELTZOVariable(
            self.solver, name_a + INTERNAL_SEPARATOR + str(len(list_a))
        )
        new_b: SELTZOVariable = SELTZOVariable(
            self.solver, name_b + INTERNAL_SEPARATOR + str(len(list_b))
        )
        list_a.append(new_a)
        list_b.append(new_b)
        lemmas: dict[str, z3.BoolRef] = setz_two_sum_lemmas(
            old_a,
            old_b,
            new_a,
            new_b,
            old_a.sign_bit,
            old_b.sign_bit,
            new_a.sign_bit,
            new_b.sign_bit,
            old_a.exponent,
            old_b.exponent,
            new_a.exponent,
            new_b.exponent,
            z3.If(old_a.trailing_bit, Z3_ZERO, old_a.num_trailing_bits),
            z3.If(old_b.trailing_bit, Z3_ZERO, old_b.num_trailing_bits),
            z3.If(new_a.trailing_bit, Z3_ZERO, new_a.num_trailing_bits),
            z3.If(new_b.trailing_bit, Z3_ZERO, new_b.num_trailing_bits),
            lambda v: v.is_zero,
            lambda v: z3.Not(v.sign_bit),
            lambda v: v.sign_bit,
            lambda v, w: v.can_equal(w),
            GLOBAL_PRECISION,
            Z3_ONE,
            Z3_TWO,
            Z3_THREE,
        )
        for claim in lemmas.values():
            self.solver.add(claim)

    def extract_logical_condition(self, arguments: list[str]) -> z3.BoolRef:
        assert len(arguments) == 3
        name_a: str = arguments[0]
        name_b: str = arguments[2]
        assert name_a in self.variables
        assert name_b in self.variables
        a: SELTZOVariable = self.variables[name_a][-1]
        b: SELTZOVariable = self.variables[name_b][-1]
        if arguments[1] == "s_dominates":
            return a.s_dominates(b)
        elif arguments[1] == "p_dominates":
            return a.p_dominates(b)
        elif arguments[1] == "ulp_dominates":
            return a.ulp_dominates(b)
        elif arguments[1] == "qd_dominates":
            return a.qd_dominates(b)
        elif arguments[1] == "strongly_dominates":
            return a.strongly_dominates(b)
        else:
            assert False

    def handle_assume_command(self, arguments: list[str]) -> None:
        self.solver.add(self.extract_logical_condition(arguments))

    def handle_prove_command(self, arguments: list[str]) -> None:
        # TODO: Sanitize claim_name to ensure it is a valid filename.
        claim_name: str = "_".join(arguments)
        job: SMTJob = create_smt_job(
            self.solver, "QF_LIA", claim_name, self.extract_logical_condition(arguments)
        )
        job.start()
        while True:
            if job.poll():
                assert job.result is not None
                assert len(job.processes) == 1
                solver_name: str = job.processes.popitem()[0]
                if job.result[1] == z3.unsat:
                    print(
                        solver_name,
                        "proved",
                        claim_name,
                        f"in {job.result[0]:.3f} seconds.",
                    )
                elif job.result[1] == z3.sat:
                    print(
                        "ERROR:",
                        solver_name,
                        "REFUTED",
                        claim_name,
                        f"in {job.result[0]:.3f} seconds.",
                    )
                else:
                    assert False
                break
            # Sleep to avoid busy waiting. Even the fastest SMT solvers
            # take a few milliseconds, so 0.1ms is a reasonable interval.
            sleep(0.0001)


def main() -> None:
    for path in argv[1:]:
        try:
            with open(path) as f:
                print(f"Processing file: {repr(path)}")
                context: VerifierContext = VerifierContext()
                for line in f:
                    parts: list[str] = []
                    for part in line.split():
                        if part.startswith("#"):
                            break
                        parts.append(part)
                    if not parts:
                        continue
                    command, *arguments = parts
                    if command == "variable":
                        context.handle_variable_command(arguments)
                    elif command == "assume":
                        context.handle_assume_command(arguments)
                    elif command == "two_sum":
                        context.handle_two_sum_command(arguments)
                    elif command == "prove":
                        context.handle_prove_command(arguments)
                    elif command == "bound":
                        # TODO: Implement bound command.
                        pass
                    else:
                        print(f"ERROR: Unknown command {repr(command)}.", file=stderr)
                        break
        except FileNotFoundError:
            print(f"ERROR: File {repr(path)} not found.", file=stderr)
        except OSError:
            print(f"ERROR: Unable to read file {repr(path)}.", file=stderr)


if __name__ == "__main__":
    main()
