#!/usr/bin/env python3

import sys
import z3

from os import cpu_count
from time import sleep
from typing import cast

from setz_lemmas import setz_two_sum_lemmas
from seltzo_lemmas import seltzo_two_sum_lemmas
from smt_utils import SMT_SOLVERS, UNSUPPORTED_LOGICS, SMTJob, create_smt_job


EXIT_NO_SOLVERS: int = 1


LIA_SOLVERS: list[str] = [
    solver for solver in SMT_SOLVERS if "QF_LIA" not in UNSUPPORTED_LOGICS[solver]
]
if not LIA_SOLVERS:
    print(
        "ERROR: No SMT solvers available on your $PATH support QF_LIA.",
        file=sys.stderr,
    )
    print("Please install at least one of the following SMT solvers:", file=sys.stderr)
    for solver, logics in UNSUPPORTED_LOGICS.items():
        if "QF_LIA" not in logics:
            print("    -", solver, file=sys.stderr)
    sys.exit(EXIT_NO_SOLVERS)
SOLVER_LEN: int = max(map(len, LIA_SOLVERS))


Z3_ZERO: z3.ArithRef = z3.IntVal(0)
Z3_ONE: z3.ArithRef = z3.IntVal(1)
Z3_TWO: z3.ArithRef = z3.IntVal(2)
Z3_THREE: z3.ArithRef = z3.IntVal(3)
GLOBAL_PRECISION: z3.ArithRef = z3.Int("PRECISION")
GLOBAL_ZERO_EXPONENT: z3.ArithRef = z3.Int("ZERO_EXPONENT")
GLOBAL_MANTISSA_WIDTH: z3.ArithRef = GLOBAL_PRECISION - 1
INTERNAL_SEPARATOR: str = "__"


def compute_job_count() -> int:
    assert LIA_SOLVERS
    num_cores: int | None = cpu_count()
    if num_cores is None:
        print(
            "WARNING: Could not determine CPU core count using os.cpu_count().",
            file=sys.stderr,
        )
        num_cores = 1
    return max(num_cores // len(LIA_SOLVERS), 1)


JOB_COUNT: int = compute_job_count()
print("Computing bounds with", JOB_COUNT, "parallel jobs.")


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
        # This means that all results proved in this model assume that no
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

    def can_equal(self, other: "SELTZOVariable") -> z3.BoolRef:
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

    def s_dominates(self, other: "SELTZOVariable") -> z3.BoolRef:
        ntz: z3.ArithRef = z3.If(
            self.trailing_bit, z3.IntVal(0), self.num_trailing_bits
        )
        return z3.Or(
            other.is_zero,
            self.exponent >= other.exponent + (GLOBAL_PRECISION - ntz),
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

    def is_smaller_than(
        self,
        other: "SELTZOVariable",
        magnitude: int | z3.ArithRef,
    ) -> z3.BoolRef:
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
        for claim in setz_two_sum_lemmas(
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
        ).values():
            self.solver.add(claim)
        for claim in seltzo_two_sum_lemmas(
            old_a,
            old_b,
            new_a,
            new_b,
            old_a.sign_bit,
            old_b.sign_bit,
            new_a.sign_bit,
            new_b.sign_bit,
            old_a.leading_bit,
            old_b.leading_bit,
            new_a.leading_bit,
            new_b.leading_bit,
            old_a.trailing_bit,
            old_b.trailing_bit,
            new_a.trailing_bit,
            new_b.trailing_bit,
            old_a.exponent,
            old_b.exponent,
            new_a.exponent,
            new_b.exponent,
            old_a.num_leading_bits,
            old_b.num_leading_bits,
            new_a.num_leading_bits,
            new_b.num_leading_bits,
            old_a.num_trailing_bits,
            old_b.num_trailing_bits,
            new_a.num_trailing_bits,
            new_b.num_trailing_bits,
            lambda v: v.is_zero,
            lambda v: z3.Not(v.sign_bit),
            lambda v: v.sign_bit,
            lambda v, w: v.can_equal(w),
            GLOBAL_PRECISION,
            Z3_ONE,
            Z3_TWO,
            Z3_THREE,
        ).values():
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
                        " ".join(arguments).ljust(29),
                        "proved by",
                        solver_name.ljust(SOLVER_LEN),
                        f"in{job.result[0]:8.3f} seconds.",
                    )
                elif job.result[1] == z3.sat:
                    print(
                        "ERROR:",
                        " ".join(arguments).ljust(29),
                        "REFUTED by",
                        solver_name.ljust(SOLVER_LEN),
                        f"in{job.result[0]:8.3f} seconds.",
                    )
                else:
                    assert False
                break
            # Sleep to avoid busy waiting. Even the fastest SMT solvers
            # take a few milliseconds, so 0.1ms is a reasonable interval.
            sleep(0.0001)

    def format_bound(self, name_a: str, name_b: str, k: int, j: int) -> str:
        if j == 0:
            return f"|{name_a}| <= u^{k} |{name_b}|"
        elif -20 <= j <= -1:
            return f"|{name_a}| <= {2**-j} u^{k} |{name_b}|"
        elif 1 <= j <= 20:
            return f"|{name_a}| <= (1/{2**j}) u^{k} |{name_b}|"
        else:
            return f"|{name_a}| <= 2^{-j} u^{k} |{name_b}|"

    def test_bound(
        self,
        name_a: str,
        name_b: str,
        k: int,
        j: int,
        verbose: bool,
    ) -> tuple[bool, str, float]:
        assert name_a in self.variables
        assert name_b in self.variables
        a: SELTZOVariable = self.variables[name_a][-1]
        b: SELTZOVariable = self.variables[name_b][-1]
        # TODO: Sanitize bound name to ensure it is a valid filename.
        bound_name: str = f"bound_{name_a}_{name_b}_{k}_{j}"
        job: SMTJob = create_smt_job(
            self.solver,
            "QF_LIA",
            bound_name,
            a.is_smaller_than(b, GLOBAL_PRECISION * k + j),
        )
        job.start()
        while True:
            if job.poll():
                assert job.result is not None
                assert len(job.processes) == 1
                solver_name: str = job.processes.popitem()[0]
                solver_time: float = job.result[0]
                if job.result[1] == z3.unsat:
                    if verbose:
                        print(
                            f"\x1b[2K  {solver_name.rjust(SOLVER_LEN)} proved ",
                            self.format_bound(name_a, name_b, k, j).ljust(29),
                            f"in{solver_time:8.3f} seconds.",
                            end="\r",
                        )
                    return (True, solver_name, solver_time)
                elif job.result[1] == z3.sat:
                    if verbose:
                        print(
                            f"\x1b[2K  {solver_name.rjust(SOLVER_LEN)} refuted",
                            self.format_bound(name_a, name_b, k, j).ljust(29),
                            f"in{solver_time:8.3f} seconds.",
                            end="\r",
                        )
                    return (False, solver_name, solver_time)
                else:
                    assert False
            # Sleep to avoid busy waiting. Even the fastest SMT solvers
            # take a few milliseconds, so 0.1ms is a reasonable interval.
            sleep(0.0001)

    def handle_bound_command(
        self,
        arguments: list[str],
        origin_k: int = 0,
        origin_j: int = -1024,
        verbose: bool = True,
    ) -> None:

        assert origin_j <= 0
        assert len(arguments) == 3
        assert arguments[1] == "/"
        name_a: str = arguments[0]
        name_b: str = arguments[2]
        assert name_a in self.variables
        assert name_b in self.variables
        print(f"Bounding |{name_a}| relative to |{name_b}|.", end="\r")

        last_passing_name: str | None = None
        last_passing_time: float | None = None

        def test_bound(k: int, j: int) -> bool:
            nonlocal last_passing_name
            nonlocal last_passing_time
            result: tuple[bool, str, float] = self.test_bound(
                name_a, name_b, k, j, verbose
            )
            if result[0]:
                last_passing_name = result[1]
                last_passing_time = result[2]
            return result[0]

        # Perform a linear scan to find passing and failing values of k.
        passing_k: int | None = None
        failing_k: int | None = None
        trial_k: int
        if test_bound(origin_k, origin_j):
            passing_k = origin_k
            while True:
                trial_k = passing_k + 1
                if test_bound(trial_k, origin_j):
                    passing_k = trial_k
                else:
                    failing_k = trial_k
                    break
        else:
            failing_k = origin_k
            while True:
                trial_k = failing_k - 1
                if test_bound(trial_k, origin_j):
                    passing_k = trial_k
                    break
                else:
                    failing_k = trial_k

        # Assert that the linear scan succeeded.
        assert passing_k is not None
        assert failing_k is not None
        assert passing_k + 1 == failing_k

        # Perform an exponential scan to find a failing value of j.
        passing_j: int = origin_j
        failing_j: int | None = None
        trial_j: int
        while passing_j < 0:
            trial_j = (passing_j + 1) // 2
            if test_bound(passing_k, trial_j):
                passing_j = trial_j
            else:
                failing_j = trial_j
                break
        if failing_j is None:
            assert passing_j == 0
            if test_bound(passing_k, 1):
                passing_j = 1
                while True:
                    trial_j = passing_j * 2
                    if test_bound(passing_k, trial_j):
                        passing_j = trial_j
                    else:
                        failing_j = trial_j
                        break
            else:
                failing_j = 1

        # Assert that the exponential scan succeeded.
        assert failing_j is not None
        assert passing_j < failing_j

        # Perform a binary search to tighten the bounds on j.
        while passing_j + 1 < failing_j:
            trial_j = (passing_j + failing_j) // 2
            if test_bound(passing_k, trial_j):
                passing_j = trial_j
            else:
                failing_j = trial_j

        # Assert that the binary search succeeded.
        assert passing_j + 1 == failing_j

        last_passing_name = cast(str, cast(object, last_passing_name))
        assert last_passing_name is not None
        last_passing_time = cast(float, cast(object, last_passing_time))
        assert last_passing_time is not None
        print(
            "\x1b[2K"
            + self.format_bound(name_a, name_b, passing_k, passing_j).ljust(29),
            f"proved by {last_passing_name.ljust(SOLVER_LEN)}",
            f"in{last_passing_time:8.3f} seconds.",
        )


def main() -> None:
    for path in sys.argv[1:]:
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
                        context.handle_bound_command(arguments)
                    else:
                        print(
                            f"ERROR: Unknown command {repr(command)}.", file=sys.stderr
                        )
                        break
        except FileNotFoundError:
            print(f"ERROR: File {repr(path)} not found.", file=sys.stderr)
        except OSError:
            print(f"ERROR: Unable to read file {repr(path)}.", file=sys.stderr)


if __name__ == "__main__":
    main()
