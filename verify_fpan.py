#!/usr/bin/env python3

import os
import struct
import sys
import z3

from time import sleep
from typing import Callable, cast

from setz_lemmas import setz_two_sum_lemmas
from seltzo_lemmas import seltzo_two_sum_lemmas
from smt_utils import SMTJob, detect_smt_solvers, create_smt_job, pop_flag


EXIT_NO_SOLVERS: int = 1


LIA_SOLVERS: set[str] = detect_smt_solvers("QF_LIA", EXIT_NO_SOLVERS)
SOLVER_LEN: int = max(map(len, LIA_SOLVERS))
SHOW_COUNTEREXAMPLES: bool = pop_flag("--show-counterexamples")
VERBOSE_COUNTEREXAMPLES: bool = pop_flag("--verbose-counterexamples")
CHECK_FAST_TWO_SUM: bool = pop_flag("--check-fast-two-sum")
INTERNAL_SEPARATOR: str = "__"
FLOAT16_PRECISION: int = 11
FLOAT16_ZERO_EXPONENT: int = -15
FLOAT16_MIN_EXPONENT: int = FLOAT16_ZERO_EXPONENT + 1
Z3_ZERO: z3.ArithRef = z3.IntVal(0)
Z3_ONE: z3.ArithRef = z3.IntVal(1)
Z3_TWO: z3.ArithRef = z3.IntVal(2)
Z3_THREE: z3.ArithRef = z3.IntVal(3)
GLOBAL_PRECISION: z3.ArithRef = z3.Int("PRECISION")
GLOBAL_ZERO_EXPONENT: z3.ArithRef = z3.Int("ZERO_EXPONENT")


def try_open(path: str):
    try:
        return open(path, "rb")
    except:
        return None


DATA_PATH: str = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "conjecturer",
    "SELTZO-TwoSum-Float16.bin",
)
DATA_FILE = try_open(DATA_PATH)
if DATA_FILE is None:
    print(f"File {repr(DATA_PATH)} not found.")
else:
    print(f"Successfully opened {repr(DATA_PATH)}.")
    DATA_SIZE: int = DATA_FILE.seek(0, os.SEEK_END)
    _ = DATA_FILE.seek(0, os.SEEK_SET)
    RECORD_FORMAT: str = "<IIII"
    RECORD_SIZE: int = struct.calcsize(RECORD_FORMAT)
    assert DATA_SIZE % RECORD_SIZE == 0
    NUM_RECORDS: int = DATA_SIZE // RECORD_SIZE
    print(f"Found {NUM_RECORDS} SELTZO-TwoSum records.")


class SELTZOVariable(object):

    def __init__(
        self,
        solver: z3.Solver,
        name: str,
    ) -> None:

        self.name: str = name

        self.sign_bit: z3.BoolRef = z3.Bool(
            name + INTERNAL_SEPARATOR + "sign_bit",
        )
        self.leading_bit: z3.BoolRef = z3.Bool(
            name + INTERNAL_SEPARATOR + "leading_bit",
        )
        self.trailing_bit: z3.BoolRef = z3.Bool(
            name + INTERNAL_SEPARATOR + "trailing_bit",
        )
        self.exponent: z3.ArithRef = z3.Int(
            name + INTERNAL_SEPARATOR + "exponent",
        )
        self.num_leading_bits: z3.ArithRef = z3.Int(
            name + INTERNAL_SEPARATOR + "num_leading_bits",
        )
        self.num_trailing_bits: z3.ArithRef = z3.Int(
            name + INTERNAL_SEPARATOR + "num_trailing_bits",
        )

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


# TODO: Eventually, all `assert` statements should be
# replaced by informative user-facing error messages.


def to_bool(expr: z3.BoolRef) -> bool:
    if z3.is_true(expr):
        return True
    elif z3.is_false(expr):
        return False
    assert False


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

    zero_exponent: int = model[GLOBAL_ZERO_EXPONENT].as_long()
    exponent: int = model[variable.exponent].as_long()
    assert zero_exponent <= exponent

    digit_dict: dict[int, str] = {}
    if exponent > zero_exponent:

        precision: int = model[GLOBAL_PRECISION].as_long()
        for k in range(precision):
            digit_dict[exponent - k] = "?"
        set_digit(digit_dict, exponent, "1")

        leading_bit: bool = to_bool(model[variable.leading_bit])
        num_leading_bits: int = model[variable.num_leading_bits].as_long()
        for k in range(1, num_leading_bits + 1):
            set_digit(digit_dict, exponent - k, to_digit(leading_bit))
        if num_leading_bits < precision - 1:
            set_digit(
                digit_dict,
                exponent - (num_leading_bits + 1),
                to_digit(not leading_bit),
            )

        trailing_bit: bool = to_bool(model[variable.trailing_bit])
        num_trailing_bits: int = model[variable.num_trailing_bits].as_long()
        for k in range(1, num_trailing_bits + 1):
            set_digit(digit_dict, exponent - (precision - k), to_digit(trailing_bit))
        if num_trailing_bits < precision - 1:
            set_digit(
                digit_dict,
                exponent - (precision - (num_trailing_bits + 1)),
                to_digit(not trailing_bit),
            )

    return digit_dict


def seltzo_key(
    model: z3.ModelRef,
    variable: SELTZOVariable,
    exponent_offset: int,
) -> int:
    # For now, we only support lookup from Float16 data files.
    assert model[GLOBAL_PRECISION].as_long() == FLOAT16_PRECISION
    zero_exponent: int = model[GLOBAL_ZERO_EXPONENT].as_long()
    s: bool = to_bool(model[variable.sign_bit])
    lb: bool = to_bool(model[variable.leading_bit])
    tb: bool = to_bool(model[variable.trailing_bit])
    e: int = model[variable.exponent].as_long()
    if e == zero_exponent:
        e = FLOAT16_ZERO_EXPONENT
    else:
        assert e > zero_exponent
        e += exponent_offset
    assert -16383 <= e <= 16384
    nlb: int = model[variable.num_leading_bits].as_long()
    assert 0 <= nlb <= 127
    ntb: int = model[variable.num_trailing_bits].as_long()
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
    assert model[GLOBAL_PRECISION].as_long() == FLOAT16_PRECISION
    zero_exponent: int = model[GLOBAL_ZERO_EXPONENT].as_long()
    nonzero_exponents: list[int] = []
    for variable in variables:
        exponent: int = model[variable.exponent].as_long()
        if exponent != zero_exponent:
            assert exponent > zero_exponent
            nonzero_exponents.append(exponent)
    min_exponent: int = min(nonzero_exponents, default=0)
    return [
        seltzo_key(
            model,
            variable,
            (FLOAT16_MIN_EXPONENT - min_exponent) + (FLOAT16_PRECISION + 1),
        )
        for variable in variables
    ]


def show_two_sum(
    model: z3.ModelRef,
    x: SELTZOVariable,
    y: SELTZOVariable,
    s: SELTZOVariable,
    e: SELTZOVariable,
    prefix: str = "",
) -> None:
    x_sign: str = "-" if to_bool(model[x.sign_bit]) else "+"
    y_sign: str = "-" if to_bool(model[y.sign_bit]) else "+"
    s_sign: str = "-" if to_bool(model[s.sign_bit]) else "+"
    e_sign: str = "-" if to_bool(model[e.sign_bit]) else "+"
    x_digits: dict[int, str] = extract_digits(model, x)
    y_digits: dict[int, str] = extract_digits(model, y)
    s_digits: dict[int, str] = extract_digits(model, s)
    e_digits: dict[int, str] = extract_digits(model, e)
    keys: set[int] = set()
    keys.update(x_digits.keys())
    keys.update(y_digits.keys())
    keys.update(s_digits.keys())
    keys.update(e_digits.keys())
    x_seltzo, y_seltzo, s_seltzo, e_seltzo = seltzo_keys(model, [x, y, s, e])
    if keys:  # at least one number is nonzero
        max_key: int = max(keys)
        min_key: int = min(keys)
        key_range: Callable[[], range] = lambda: range(max_key, min_key - 1, -1)
        x_str: str = "".join(x_digits.get(k, ".") for k in key_range())
        y_str: str = "".join(y_digits.get(k, ".") for k in key_range())
        s_str: str = "".join(s_digits.get(k, ".") for k in key_range())
        e_str: str = "".join(e_digits.get(k, ".") for k in key_range())
        print(f"{prefix}{x_sign}{x_str} (0x{x_seltzo:08X})")
        print(f"{prefix}{y_sign}{y_str} (0x{y_seltzo:08X})")
        print(prefix + "=" * (max_key - min_key + 2))
        print(f"{prefix}{s_sign}{s_str} (0x{s_seltzo:08X})")
        print(f"{prefix}{e_sign}{e_str} (0x{e_seltzo:08X})")
    else:  # all numbers are zero
        print(f"{prefix}{x_sign}0 (0x{x_seltzo:08X})")
        print(f"{prefix}{y_sign}0 (0x{y_seltzo:08X})")
        print(prefix + "=" * 2)
        print(f"{prefix}{s_sign}0 (0x{s_seltzo:08X})")
        print(f"{prefix}{e_sign}0 (0x{e_seltzo:08X})")


def exists_in_data(key_x: int, key_y: int, key_s: int, key_e: int) -> bool:
    assert DATA_FILE is not None
    target: tuple[int, int, int, int] = (key_x, key_y, key_s, key_e)
    lo: int = 0
    hi: int = NUM_RECORDS - 1
    while lo <= hi:
        mid: int = (lo + hi) // 2
        _ = DATA_FILE.seek(mid * RECORD_SIZE)
        data: bytes = DATA_FILE.read(RECORD_SIZE)
        record: tuple[int, int, int, int] = struct.unpack(RECORD_FORMAT, data)
        if record < target:
            lo = mid + 1
        elif record > target:
            hi = mid - 1
        else:
            return True
    return False


def format_bound(name_a: str, name_b: str, k: int, j: int) -> str:
    if j == 0:
        return f"|{name_a}| <= u^{k} |{name_b}|"
    elif -20 <= j <= -1:
        return f"|{name_a}| <= {2**-j} u^{k} |{name_b}|"
    elif 1 <= j <= 20:
        return f"|{name_a}| <= (1/{2**j}) u^{k} |{name_b}|"
    else:
        return f"|{name_a}| <= 2^{-j} u^{k} |{name_b}|"


class VerifierContext(object):

    def __init__(self) -> None:
        self.solver: z3.Solver = z3.SolverFor("QF_LIA")
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
        for claim in setz_two_sum_lemmas(
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
        ).values():
            self.solver.add(claim)

        for claim in seltzo_two_sum_lemmas(
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
        ).values():
            self.solver.add(claim)

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
            # TODO: Sanitize claim name to ensure it is a valid filename.
            claim_name: str = f"fast_two_sum_{old_a.name}_{old_b.name}"
            job: SMTJob = create_smt_job(
                self.solver, "QF_LIA", claim_name, old_a.can_fast_two_sum(old_b)
            )
            job.start(LIA_SOLVERS)
            while True:
                if job.poll():
                    assert job.result is not None
                    if job.result[1] == z3.unsat:
                        print(
                            "NOTE: two_sum command on line",
                            line_number,
                            "can be replaced by fast_two_sum.",
                        )
                    break
                sleep(0.0001)

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

        # TODO: Sanitize claim name to ensure it is a valid filename.
        claim_name: str = f"fast_two_sum_{old_a.name}_{old_b.name}"
        job: SMTJob = create_smt_job(
            self.solver, "QF_LIA", claim_name, old_a.can_fast_two_sum(old_b)
        )
        job.start(LIA_SOLVERS)
        while True:
            if job.poll():
                assert job.result is not None
                if job.result[1] == z3.sat:
                    print(
                        "ERROR: fast_two_sum command on line",
                        line_number,
                        "is invalid and should be replaced by two_sum.",
                    )
                break
            sleep(0.0001)

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

    def show_counterexample(
        self,
        claim: z3.BoolRef,
        precision: int = FLOAT16_PRECISION,
    ) -> None:
        self.solver.push()
        self.solver.add(GLOBAL_PRECISION == precision)
        self.solver.add(~claim)
        if self.solver.check() == z3.sat:
            counterexample: z3.ModelRef = self.solver.model()
            for x, y, s, e in self.two_sum_operands:
                if DATA_FILE is None:
                    print(f"\n({s.name}, {e.name}) := TwoSum({x.name}, {y.name}):")
                    show_two_sum(counterexample, x, y, s, e, prefix="  ")
                else:
                    keys: list[int] = seltzo_keys(counterexample, [x, y, s, e])
                    is_valid: bool = exists_in_data(*keys)
                    if VERBOSE_COUNTEREXAMPLES or not is_valid:
                        print(
                            f"\n({s.name}, {e.name}) := TwoSum({x.name}, {y.name})",
                            "(valid):" if is_valid else "(invalid):",
                        )
                        show_two_sum(counterexample, x, y, s, e, prefix="  ")
            print()
        else:
            print(f"WARNING: No counterexample found with precision p = {precision}.")
        self.solver.pop()

    def handle_prove_command(self, arguments: list[str]) -> None:
        claim: z3.BoolRef = self.extract_logical_condition(arguments)
        # TODO: Sanitize claim_name to ensure it is a valid filename.
        claim_name: str = "_".join(arguments)
        job: SMTJob = create_smt_job(self.solver, "QF_LIA", claim_name, claim)
        job.start(LIA_SOLVERS)
        while True:
            if job.poll():
                assert job.result is not None
                assert len(job.processes) == 1
                solver_name: str = job.processes.popitem()[0]
                if job.result[1] == z3.unsat:
                    print(
                        " ".join(arguments).ljust(30),
                        "proved by",
                        solver_name.ljust(SOLVER_LEN),
                        f"in{job.result[0]:8.3f} seconds.",
                    )
                elif job.result[1] == z3.sat:
                    print(
                        "ERROR:",
                        " ".join(arguments).ljust(22),
                        "REFUTED by",
                        solver_name.ljust(SOLVER_LEN),
                        f"in{job.result[0]:8.3f} seconds.",
                    )
                    if SHOW_COUNTEREXAMPLES:
                        self.show_counterexample(claim)
                else:
                    assert False
                break
            sleep(0.0001)

    def test_bound(
        self,
        name_a: str,
        name_b: str,
        a: SELTZOVariable,
        b: SELTZOVariable,
        k: int,
        j: int,
        verbose: bool,
    ) -> tuple[bool, str, float]:
        # TODO: Sanitize bound name to ensure it is a valid filename.
        bound_name: str = f"bound_{name_a}_{name_b}_{k}_{j}"
        job: SMTJob = create_smt_job(
            self.solver,
            "QF_LIA",
            bound_name,
            a.is_smaller_than(b, GLOBAL_PRECISION * k + j),
        )
        job.start(LIA_SOLVERS)
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
                            format_bound(name_a, name_b, k, j).ljust(30),
                            f"in{solver_time:8.3f} seconds.",
                            end="\r",
                        )
                    return (True, solver_name, solver_time)
                elif job.result[1] == z3.sat:
                    if verbose:
                        print(
                            f"\x1b[2K  {solver_name.rjust(SOLVER_LEN)} refuted",
                            format_bound(name_a, name_b, k, j).ljust(30),
                            f"in{solver_time:8.3f} seconds.",
                            end="\r",
                        )
                    return (False, solver_name, solver_time)
                else:
                    assert False
            sleep(0.0001)

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

        def local_test_bound(k: int, j: int) -> bool:
            nonlocal last_passing_name
            nonlocal last_passing_time
            result: tuple[bool, str, float] = self.test_bound(
                name_a, name_b, a, b, k, j, verbose
            )
            if result[0]:
                last_passing_name = result[1]
                last_passing_time = result[2]
            return result[0]

        # Perform a linear scan to find passing and failing values of k.
        passing_k: int | None = None
        failing_k: int | None = None
        trial_k: int
        if local_test_bound(origin_k, origin_j):
            passing_k = origin_k
            while True:
                trial_k = passing_k + 1
                if local_test_bound(trial_k, origin_j):
                    passing_k = trial_k
                else:
                    failing_k = trial_k
                    break
        else:
            failing_k = origin_k
            while True:
                trial_k = failing_k - 1
                if local_test_bound(trial_k, origin_j):
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
            if local_test_bound(passing_k, trial_j):
                passing_j = trial_j
            else:
                failing_j = trial_j
                break
        if failing_j is None:
            assert passing_j == 0
            if local_test_bound(passing_k, 1):
                passing_j = 1
                while True:
                    trial_j = passing_j * 2
                    if local_test_bound(passing_k, trial_j):
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
            if local_test_bound(passing_k, trial_j):
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
                context: VerifierContext = VerifierContext()
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
                        context.handle_variable_command(arguments)
                    elif command == "assume":
                        context.handle_assume_command(arguments)
                    elif command == "two_sum":
                        context.handle_two_sum_command(arguments, line_number)
                    elif command == "fast_two_sum":
                        context.handle_fast_two_sum_command(arguments, line_number)
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
