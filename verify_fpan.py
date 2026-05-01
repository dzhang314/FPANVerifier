#!/usr/bin/env python3

import os
import struct
import sys
import z3

from time import sleep
from typing import BinaryIO, cast
from uuid import uuid4

from se_lemmas import se_two_prod_lemmas
from setz_lemmas import setz_two_sum_lemmas
from seltzo_lemmas import seltzo_two_sum_lemmas
from seltzo_variables import (
    FLOAT16_PRECISION,
    GLOBAL_PRECISION,
    GLOBAL_ZERO_EXPONENT,
    SELTZOClass,
    SELTZOVariable,
    seltzo_keys,
)
from smt_utils import (
    SMTJob,
    get_bool,
    get_int,
    pop_flag,
    detect_smt_solvers,
    create_smt_job,
)


EXIT_NO_SOLVERS: int = 1


LIA_SOLVERS: set[str] = detect_smt_solvers("QF_LIA", EXIT_NO_SOLVERS)
SOLVER_LEN: int = max(map(len, LIA_SOLVERS))
SHOW_COUNTEREXAMPLES: bool = pop_flag("--show-counterexamples")
VERBOSE_COUNTEREXAMPLES: bool = pop_flag("--verbose-counterexamples")
CHECK_FAST_TWO_SUM: bool = pop_flag("--check-fast-two-sum")

INTERNAL_SEPARATOR: str = "__"

RECORD_FORMAT: str = "<IIII"
RECORD_SIZE: int = struct.calcsize(RECORD_FORMAT)

DATA_DIR: str = os.path.join(os.path.dirname(os.path.abspath(__file__)), "conjecturer")
DATA_PREFIX: str = "SELTZO-TwoSum-Float16-"
DATA_SUFFIX: str = ".bin"

Z3_ZERO: z3.ArithRef = z3.IntVal(0)
Z3_ONE: z3.ArithRef = z3.IntVal(1)
Z3_TWO: z3.ArithRef = z3.IntVal(2)
Z3_THREE: z3.ArithRef = z3.IntVal(3)


def load_seltzo_data_files() -> (
    dict[tuple[SELTZOClass, SELTZOClass], tuple[BinaryIO, int]]
):
    result: dict[tuple[SELTZOClass, SELTZOClass], tuple[BinaryIO, int]] = {}
    try:
        filenames = os.listdir(DATA_DIR)
    except OSError:
        print(f"Directory {repr(DATA_DIR)} not found.")
        return result

    for filename in sorted(filenames):
        if filename.startswith(DATA_PREFIX) and filename.endswith(DATA_SUFFIX):
            stem: str = filename[len(DATA_PREFIX) : -len(DATA_SUFFIX)]
            parts: list[str] = stem.split("-")
            if len(parts) != 2:
                continue
            try:
                cx: SELTZOClass = SELTZOClass[parts[0]]
                cy: SELTZOClass = SELTZOClass[parts[1]]
            except KeyError:
                continue

            path: str = os.path.join(DATA_DIR, filename)
            try:
                data_file = open(path, "rb")
            except OSError:
                print(f"Could not open file {repr(path)}.")
                continue

            data_size: int = data_file.seek(0, os.SEEK_END)
            _ = data_file.seek(0, os.SEEK_SET)
            assert data_size % RECORD_SIZE == 0
            result[(cx, cy)] = (data_file, data_size // RECORD_SIZE)

    expected_count: int = len(SELTZOClass) ** 2
    if not result:
        print(f"No files matching {repr(DATA_PREFIX + '*' + DATA_SUFFIX)} found.")
    else:
        total_records: int = sum(num_records for _, num_records in result.values())
        print(f"Successfully opened {len(result)} SELTZO-TwoSum-Float16 data files.")
        print(f"Found {total_records} SELTZO-TwoSum-Float16 records.")
        if len(result) != expected_count:
            print(
                f"WARNING: Expected {expected_count} SELTZO-TwoSum-Float16 data files.",
                file=sys.stderr,
            )

    return result


DATA_FILES: dict[tuple[SELTZOClass, SELTZOClass], tuple[BinaryIO, int]] = (
    load_seltzo_data_files()
)


# TODO: Eventually, all `assert` statements should be
# replaced by informative user-facing error messages.


def to_digit(bit: bool) -> str:
    return "1" if bit else "0"


def set_digit(digit_dict: dict[int, str], index: int, digit: str) -> None:
    assert index in digit_dict
    assert digit_dict[index] == "?" or digit_dict[index] == digit
    digit_dict[index] = digit


def extract_digits(
    model: z3.ModelRef,
    variable: SELTZOVariable,
) -> dict[int, str]:

    zero_exponent: int = get_int(model, GLOBAL_ZERO_EXPONENT)
    exponent: int = get_int(model, variable.exponent)
    assert zero_exponent <= exponent

    digit_dict: dict[int, str] = {}
    if exponent > zero_exponent:

        precision: int = get_int(model, GLOBAL_PRECISION)
        for k in range(precision):
            digit_dict[exponent - k] = "?"
        set_digit(digit_dict, exponent, "1")

        leading_bit: bool = get_bool(model, variable.leading_bit)
        num_leading_bits: int = get_int(model, variable.num_leading_bits)
        for k in range(1, num_leading_bits + 1):
            set_digit(digit_dict, exponent - k, to_digit(leading_bit))
        if num_leading_bits < precision - 1:
            set_digit(
                digit_dict,
                exponent - (num_leading_bits + 1),
                to_digit(not leading_bit),
            )

        trailing_bit: bool = get_bool(model, variable.trailing_bit)
        num_trailing_bits: int = get_int(model, variable.num_trailing_bits)
        for k in range(1, num_trailing_bits + 1):
            set_digit(digit_dict, exponent - (precision - k), to_digit(trailing_bit))
        if num_trailing_bits < precision - 1:
            set_digit(
                digit_dict,
                exponent - (precision - (num_trailing_bits + 1)),
                to_digit(not trailing_bit),
            )

    return digit_dict


def is_identity_case(
    model: z3.ModelRef,
    x: SELTZOVariable,
    y: SELTZOVariable,
    s: SELTZOVariable,
    e: SELTZOVariable,
) -> bool:
    nonzero = (not get_bool(model, x.is_zero)) and (not get_bool(model, y.is_zero))
    x_dominates_y = get_bool(model, x.strongly_dominates(y))
    y_dominates_x = get_bool(model, y.strongly_dominates(x))
    s_equals_x = get_bool(model, s.can_equal(x))
    s_equals_y = get_bool(model, s.can_equal(y))
    e_equals_x = get_bool(model, e.can_equal(x))
    e_equals_y = get_bool(model, e.can_equal(y))
    return nonzero and (
        (x_dominates_y and s_equals_x and e_equals_y)
        or (y_dominates_x and s_equals_y and e_equals_x)
    )


def show_two_sum(
    model: z3.ModelRef,
    x: SELTZOVariable,
    y: SELTZOVariable,
    s: SELTZOVariable,
    e: SELTZOVariable,
    prefix: str = "",
) -> None:
    cx: SELTZOClass = x.classify(model)
    cy: SELTZOClass = y.classify(model)
    cs: SELTZOClass = s.classify(model)
    ce: SELTZOClass = e.classify(model)
    dx: dict[int, str] = extract_digits(model, x)
    dy: dict[int, str] = extract_digits(model, y)
    ds: dict[int, str] = extract_digits(model, s)
    de: dict[int, str] = extract_digits(model, e)
    kx, ky, ks, ke = seltzo_keys(model, [x, y, s, e])
    sx: str = "-" if get_bool(model, x.sign_bit) else "+"
    sy: str = "-" if get_bool(model, y.sign_bit) else "+"
    ss: str = "-" if get_bool(model, s.sign_bit) else "+"
    se: str = "-" if get_bool(model, e.sign_bit) else "+"
    if any((dx, dy, ds, de)):  # at least one number is nonzero
        e_min: int = min(min(d) for d in (dx, dy, ds, de) if d)
        e_max: int = max(max(d) for d in (dx, dy, ds, de) if d)
        x_str: str = "".join(dx.get(e, ".") for e in range(e_max, e_min - 1, -1))
        y_str: str = "".join(dy.get(e, ".") for e in range(e_max, e_min - 1, -1))
        s_str: str = "".join(ds.get(e, ".") for e in range(e_max, e_min - 1, -1))
        e_str: str = "".join(de.get(e, ".") for e in range(e_max, e_min - 1, -1))
        print(f"{prefix}{sx}{x_str} " + f"({cx.name}, 0x{kx:08X})")
        print(f"{prefix}{sy}{y_str} " + f"({cy.name}, 0x{ky:08X})")
        print(prefix + "=" * (e_max - e_min + 2))
        print(f"{prefix}{ss}{s_str} " + f"({cs.name}, 0x{ks:08X})")
        print(f"{prefix}{se}{e_str} " + f"({ce.name}, 0x{ke:08X})")
    else:  # all numbers are zero
        print(f"{prefix}{sx}0 " + f"({cx.name}, 0x{kx:08X})")
        print(f"{prefix}{sy}0 " + f"({cy.name}, 0x{ky:08X})")
        print(prefix + "=" * 2)
        print(f"{prefix}{ss}0 " + f"({cs.name}, 0x{ks:08X})")
        print(f"{prefix}{se}0 " + f"({ce.name}, 0x{ke:08X})")


def exists_in_data_file(
    data_file: BinaryIO,
    num_records: int,
    keys: tuple[int, int, int, int],
) -> bool:
    lo: int = 0
    hi: int = num_records - 1
    while lo <= hi:
        mid: int = (lo + hi) // 2
        _ = data_file.seek(mid * RECORD_SIZE)
        data: bytes = data_file.read(RECORD_SIZE)
        record: tuple[int, int, int, int] = struct.unpack(RECORD_FORMAT, data)
        if record < keys:
            lo = mid + 1
        elif record > keys:
            hi = mid - 1
        else:
            return True
    return False


def exists_in_data(
    keys: tuple[int, int, int, int],
    cx: SELTZOClass,
    cy: SELTZOClass,
) -> bool:
    assert DATA_FILES
    if (cx, cy) not in DATA_FILES:
        return False
    return exists_in_data_file(*DATA_FILES[(cx, cy)], keys)


def format_bound(name_a: str, name_b: str, k: int, j: int) -> str:
    if j == 0:
        return f"|{name_a}| <= u^{k} |{name_b}|"
    elif -20 <= j <= -1:
        return f"|{name_a}| <= {2**-j} u^{k} |{name_b}|"
    elif 1 <= j <= 20:
        return f"|{name_a}| <= (1/{2**j}) u^{k} |{name_b}|"
    else:
        return f"|{name_a}| <= 2^{-j} u^{k} |{name_b}|"


class FPANVerifier(object):

    def __init__(self) -> None:
        self.solver: z3.Solver = z3.SolverFor("QF_LIA")
        self.solver.add(GLOBAL_PRECISION >= 8)
        self.variables: dict[str, list[SELTZOVariable]] = {}
        self.two_sum_operands: list[
            tuple[SELTZOVariable, SELTZOVariable, SELTZOVariable, SELTZOVariable]
        ] = []

    def handle_variable_command(self, arguments: list[str]) -> None:
        assert len(arguments) == 1
        name: str = arguments[0]
        assert INTERNAL_SEPARATOR not in name
        assert name not in self.variables
        self.variables[name] = [
            SELTZOVariable(self.solver, name + INTERNAL_SEPARATOR + "0")
        ]

    def add_two_sum_constraints(
        self,
        x: SELTZOVariable,
        y: SELTZOVariable,
        s: SELTZOVariable,
        e: SELTZOVariable,
    ) -> None:

        instantiated_setz_lemmas = setz_two_sum_lemmas(
            x,
            y,
            s,
            e,
            x.sign_bit,
            y.sign_bit,
            s.sign_bit,
            e.sign_bit,
            x.exponent,
            y.exponent,
            s.exponent,
            e.exponent,
            z3.If(x.trailing_bit, Z3_ZERO, x.num_trailing_bits),
            z3.If(y.trailing_bit, Z3_ZERO, y.num_trailing_bits),
            z3.If(s.trailing_bit, Z3_ZERO, s.num_trailing_bits),
            z3.If(e.trailing_bit, Z3_ZERO, e.num_trailing_bits),
            lambda v: v.is_zero,
            lambda v: ~v.sign_bit,
            lambda v: v.sign_bit,
            lambda v, w: v.can_equal(w),
            GLOBAL_PRECISION,
            Z3_ONE,
            Z3_TWO,
            Z3_THREE,
        )

        for claim in instantiated_setz_lemmas.values():
            self.solver.add(claim)

        instantiated_seltzo_lemmas: dict[str, z3.BoolRef] = seltzo_two_sum_lemmas(
            x,
            y,
            s,
            e,
            x.sign_bit,
            y.sign_bit,
            s.sign_bit,
            e.sign_bit,
            x.leading_bit,
            y.leading_bit,
            s.leading_bit,
            e.leading_bit,
            x.trailing_bit,
            y.trailing_bit,
            s.trailing_bit,
            e.trailing_bit,
            x.exponent,
            y.exponent,
            s.exponent,
            e.exponent,
            x.num_leading_bits,
            y.num_leading_bits,
            s.num_leading_bits,
            e.num_leading_bits,
            x.num_trailing_bits,
            y.num_trailing_bits,
            s.num_trailing_bits,
            e.num_trailing_bits,
            lambda v: v.is_zero,
            lambda v: ~v.sign_bit,
            lambda v: v.sign_bit,
            lambda v, w: v.can_equal(w),
            GLOBAL_PRECISION,
            Z3_ONE,
            Z3_TWO,
            Z3_THREE,
        )

        for claim in instantiated_seltzo_lemmas.values():
            self.solver.add(claim)

    def add_two_prod_constraints(
        self,
        x: SELTZOVariable,
        y: SELTZOVariable,
        p: SELTZOVariable,
        e: SELTZOVariable,
    ) -> None:
        for claim in se_two_prod_lemmas(
            x,
            y,
            p,
            e,
            x.sign_bit,
            y.sign_bit,
            p.sign_bit,
            e.sign_bit,
            x.exponent,
            y.exponent,
            p.exponent,
            e.exponent,
            lambda v: v.is_zero,
            lambda v: ~v.sign_bit,
            lambda v: v.sign_bit,
            GLOBAL_PRECISION,
            GLOBAL_ZERO_EXPONENT + 1,
            Z3_ONE,
            Z3_TWO,
        ).values():
            self.solver.add(claim)

    def show_counterexample(
        self,
        claim: z3.BoolRef,
        precision: int = FLOAT16_PRECISION,
    ) -> None:
        for level in range(5):
            self.solver.push()
            self.solver.add(~claim)
            self.solver.add(GLOBAL_PRECISION == precision)
            for var_list in self.variables.values():
                for var in var_list:
                    if level == 0:
                        self.solver.add(var.num_leading_bits == precision - 1)
                        self.solver.add(var.num_trailing_bits == precision - 1)
                    elif level < 4:
                        self.solver.add(
                            var.num_leading_bits + var.num_trailing_bits
                            >= precision - level
                        )
            if self.solver.check() == z3.sat:
                print(
                    f"Found counterexample with precision p = {precision} at level {level}."
                )
                counterexample: z3.ModelRef = self.solver.model()
                for x, y, s, e in self.two_sum_operands:
                    if not DATA_FILES:
                        print(f"\n({s.name}, {e.name}) := TwoSum({x.name}, {y.name}):")
                        show_two_sum(counterexample, x, y, s, e, prefix="  ")
                    else:
                        kx, ky, ks, ke = seltzo_keys(counterexample, [x, y, s, e])
                        cx = x.classify(counterexample)
                        cy = y.classify(counterexample)
                        is_valid: bool = is_identity_case(
                            counterexample, x, y, s, e
                        ) or exists_in_data((kx, ky, ks, ke), cx, cy)
                        if VERBOSE_COUNTEREXAMPLES or not is_valid:
                            print(
                                f"\n({s.name}, {e.name}) := TwoSum({x.name}, {y.name})",
                                "(valid):" if is_valid else "(invalid):",
                            )
                            show_two_sum(counterexample, x, y, s, e, prefix="  ")
                print()
                self.solver.pop()
                break
            else:
                self.solver.pop()
        else:
            print(
                f"WARNING: No counterexample found with precision p = {precision}.",
                file=sys.stderr,
            )

    def check(self, claim: z3.BoolRef) -> tuple[bool, str, float]:
        job: SMTJob = create_smt_job(self.solver, "QF_LIA", str(uuid4()), claim)
        job.start(LIA_SOLVERS)
        while True:
            if job.poll():
                assert job.result is not None
                assert len(job.processes) == 1
                solver_name: str = job.processes.popitem()[0]
                if job.result[1] == z3.unsat:
                    return (True, solver_name, job.result[0])
                elif job.result[1] == z3.sat:
                    return (False, solver_name, job.result[0])
                else:
                    assert False
            # Sleep to avoid busy waiting. Even the fastest SMT solvers
            # take a few milliseconds, so 0.1ms is a reasonable interval.
            sleep(0.0001)

    def handle_two_sum_command(self, arguments: list[str], line_number: int) -> None:
        assert len(arguments) == 2
        name_a: str = arguments[0]
        name_b: str = arguments[1]
        assert name_a in self.variables
        assert name_b in self.variables
        list_a: list[SELTZOVariable] = self.variables[name_a]
        list_b: list[SELTZOVariable] = self.variables[name_b]
        old_a: SELTZOVariable = list_a[-1]
        old_b: SELTZOVariable = list_b[-1]
        if CHECK_FAST_TWO_SUM:
            result, _, _ = self.check(old_a.can_fast_two_sum(old_b))
            if result:
                print(
                    "NOTE: two_sum command on line",
                    line_number,
                    "can be replaced by fast_two_sum.",
                    file=sys.stderr,
                )
        new_a: SELTZOVariable = SELTZOVariable(
            self.solver, name_a + INTERNAL_SEPARATOR + str(len(list_a))
        )
        new_b: SELTZOVariable = SELTZOVariable(
            self.solver, name_b + INTERNAL_SEPARATOR + str(len(list_b))
        )
        list_a.append(new_a)
        list_b.append(new_b)
        self.two_sum_operands.append((old_a, old_b, new_a, new_b))
        self.add_two_sum_constraints(old_a, old_b, new_a, new_b)

    def handle_fast_two_sum_command(
        self, arguments: list[str], line_number: int
    ) -> None:
        assert len(arguments) == 2
        name_a: str = arguments[0]
        name_b: str = arguments[1]
        assert name_a in self.variables
        assert name_b in self.variables
        list_a: list[SELTZOVariable] = self.variables[name_a]
        list_b: list[SELTZOVariable] = self.variables[name_b]
        old_a: SELTZOVariable = list_a[-1]
        old_b: SELTZOVariable = list_b[-1]
        result, _, _ = self.check(old_a.can_fast_two_sum(old_b))
        if not result:
            print(
                "ERROR: fast_two_sum command on line",
                line_number,
                "is invalid and should be replaced by two_sum.",
                file=sys.stderr,
            )
        new_a: SELTZOVariable = SELTZOVariable(
            self.solver, name_a + INTERNAL_SEPARATOR + str(len(list_a))
        )
        new_b: SELTZOVariable = SELTZOVariable(
            self.solver, name_b + INTERNAL_SEPARATOR + str(len(list_b))
        )
        list_a.append(new_a)
        list_b.append(new_b)
        self.two_sum_operands.append((old_a, old_b, new_a, new_b))
        self.add_two_sum_constraints(old_a, old_b, new_a, new_b)

    def handle_two_prod_command(self, arguments: list[str], line_number: int) -> None:
        assert len(arguments) == 4
        name_x: str = arguments[0]
        name_y: str = arguments[1]
        name_p: str = arguments[2]
        name_e: str = arguments[3]
        assert name_x in self.variables
        assert name_y in self.variables
        assert name_p in self.variables
        assert name_e in self.variables
        if (len(self.variables[name_p]) > 1) or (len(self.variables[name_e]) > 1):
            print(
                "WARNING: two_prod command on line",
                line_number,
                "outputs to a variable already assigned.",
                file=sys.stderr,
            )
        x: SELTZOVariable = self.variables[name_x][-1]
        y: SELTZOVariable = self.variables[name_y][-1]
        p: SELTZOVariable = self.variables[name_p][-1]
        e: SELTZOVariable = self.variables[name_e][-1]
        self.add_two_prod_constraints(x, y, p, e)

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
        claim: z3.BoolRef = self.extract_logical_condition(arguments)
        result, solver_name, solver_time = self.check(claim)
        if result:
            print(
                " ".join(arguments).ljust(30),
                "proved by",
                solver_name.ljust(SOLVER_LEN),
                f"in{solver_time:8.3f} seconds.",
            )
        else:
            print(
                "ERROR:",
                " ".join(arguments).ljust(22),
                "REFUTED by",
                solver_name.ljust(SOLVER_LEN),
                f"in{solver_time:8.3f} seconds.",
                file=sys.stderr,
            )
            if SHOW_COUNTEREXAMPLES:
                self.show_counterexample(claim)

    def handle_bound_command(
        self,
        arguments: list[str],
        origin_k: int = 0,
        origin_j: int = -64,
        verbose: bool = True,
    ) -> None:

        assert origin_j <= 0
        assert len(arguments) == 3
        assert arguments[1] == "/"
        name_a: str = arguments[0]
        name_b: str = arguments[2]
        assert name_a in self.variables
        assert name_b in self.variables
        a: SELTZOVariable = self.variables[name_a][-1]
        b: SELTZOVariable = self.variables[name_b][-1]
        print(f"Bounding |{name_a}| relative to |{name_b}|.", end="\r")

        last_passing_name: str | None = None
        last_passing_time: float | None = None

        def check_bound(k: int, j: int) -> bool:
            nonlocal last_passing_name
            nonlocal last_passing_time
            result, solver_name, solver_time = self.check(
                a.is_smaller_than(b, GLOBAL_PRECISION * k + j)
            )
            if verbose:
                if result:
                    print(
                        f"\x1b[2K  {solver_name.rjust(SOLVER_LEN)} proved ",
                        format_bound(name_a, name_b, k, j).ljust(30),
                        f"in{solver_time:8.3f} seconds.",
                        end="\r",
                    )
                else:
                    print(
                        f"\x1b[2K  {solver_name.rjust(SOLVER_LEN)} refuted",
                        format_bound(name_a, name_b, k, j).ljust(30),
                        f"in{solver_time:8.3f} seconds.",
                        end="\r",
                    )
            if result:
                last_passing_name = solver_name
                last_passing_time = solver_time
            return result

        # Perform a linear scan to find passing and failing values of k.
        passing_k: int | None = None
        failing_k: int | None = None
        trial_k: int
        if check_bound(origin_k, origin_j):
            passing_k = origin_k
            while True:
                trial_k = passing_k + 1
                if check_bound(trial_k, origin_j):
                    passing_k = trial_k
                else:
                    failing_k = trial_k
                    break
        else:
            failing_k = origin_k
            while True:
                trial_k = failing_k - 1
                if check_bound(trial_k, origin_j):
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
            if check_bound(passing_k, trial_j):
                passing_j = trial_j
            else:
                failing_j = trial_j
                break
        if failing_j is None:
            assert passing_j == 0
            if check_bound(passing_k, 1):
                passing_j = 1
                while True:
                    trial_j = passing_j * 2
                    if check_bound(passing_k, trial_j):
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
            if check_bound(passing_k, trial_j):
                passing_j = trial_j
            else:
                failing_j = trial_j

        # Assert that the binary search succeeded.
        assert passing_j + 1 == failing_j

        # Print final bound.
        last_passing_name = cast(str, cast(object, last_passing_name))
        assert last_passing_name is not None
        last_passing_time = cast(float, cast(object, last_passing_time))
        assert last_passing_time is not None
        print(
            "\x1b[2K" + format_bound(name_a, name_b, passing_k, passing_j).ljust(30),
            f"proved by {last_passing_name.ljust(SOLVER_LEN)}",
            f"in{last_passing_time:8.3f} seconds.",
        )
        if SHOW_COUNTEREXAMPLES:
            self.show_counterexample(
                a.is_smaller_than(b, GLOBAL_PRECISION * passing_k + failing_j)
            )


def main() -> None:
    for path in sys.argv[1:]:
        try:
            with open(path) as f:
                print(f"Processing file {repr(path)}.")
                verifier: FPANVerifier = FPANVerifier()
                line_number: int = 0
                for line in f.readlines():
                    line_number += 1
                    if "#" in line:
                        line = line[: line.index("#")]
                    parts: list[str] = line.split()
                    if not parts:
                        continue
                    command, *arguments = parts
                    if command == "variable":
                        verifier.handle_variable_command(arguments)
                    elif command == "assume":
                        verifier.handle_assume_command(arguments)
                    elif command == "two_sum":
                        verifier.handle_two_sum_command(arguments, line_number)
                    elif command == "fast_two_sum":
                        verifier.handle_fast_two_sum_command(arguments, line_number)
                    elif command == "two_prod":
                        verifier.handle_two_prod_command(arguments, line_number)
                    elif command == "prove":
                        verifier.handle_prove_command(arguments)
                    elif command == "bound":
                        verifier.handle_bound_command(arguments)
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
