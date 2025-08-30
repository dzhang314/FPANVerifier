#!/usr/bin/env python3

import os
import sys
import z3

from operator import eq
from subprocess import run
from time import sleep

from se_lemmas import se_two_sum_lemmas
from setz_lemmas import setz_two_sum_lemmas
from seltzo_lemmas import seltzo_two_sum_lemmas
from smt_utils import (
    SMTJob,
    detect_smt_solvers,
    compute_job_count,
    create_smt_job,
    count_leading_zeros,
    count_leading_ones,
    count_trailing_zeros,
    count_trailing_ones,
)


EXIT_NO_SOLVERS: int = 1
EXIT_BITWUZLA_COUNTEREXAMPLE: int = 2
EXIT_CVC5_COUNTEREXAMPLE: int = 3
EXIT_Z3_COUNTEREXAMPLE: int = 4
EXIT_OTHER_COUNTEREXAMPLE: int = 5


BVFP_SOLVERS: set[str] = detect_smt_solvers("QF_BVFP", EXIT_NO_SOLVERS)
JOB_COUNT: int = compute_job_count(BVFP_SOLVERS, EXIT_NO_SOLVERS)
print("Verifying lemmas with", JOB_COUNT, "parallel jobs.")


SOLVER_LEN: int = max(map(len, BVFP_SOLVERS))
ONE: z3.BitVecNumRef = z3.BitVecVal(1, 1)
RNE: z3.FPRMRef = z3.RoundNearestTiesToEven()


def create_two_sum_jobs(
    exponent_width: int,
    promoted_exponent_width: int,
    precision: int,
    model: str,
    *,
    prefix: str = "",
    suffix: str = "",
) -> list[SMTJob]:

    mantissa_width: int = precision - 1
    exponent_padding: z3.BitVecNumRef = z3.BitVecVal(
        0, promoted_exponent_width - exponent_width
    )
    exponent_bias: z3.BitVecNumRef = z3.BitVecVal(
        2 ** (exponent_width - 1) - 1,  # pyright: ignore[reportAny]
        promoted_exponent_width,
    )

    x_sign_bit: z3.BitVecRef = z3.BitVec("x_sign_bit", 1)
    x_exponent: z3.BitVecRef = z3.BitVec("x_exponent", exponent_width)
    x_mantissa: z3.BitVecRef = z3.BitVec("x_mantissa", mantissa_width)
    x: z3.FPRef = z3.fpFP(x_sign_bit, x_exponent, x_mantissa)

    y_sign_bit: z3.BitVecRef = z3.BitVec("y_sign_bit", 1)
    y_exponent: z3.BitVecRef = z3.BitVec("y_exponent", exponent_width)
    y_mantissa: z3.BitVecRef = z3.BitVec("y_mantissa", mantissa_width)
    y: z3.FPRef = z3.fpFP(y_sign_bit, y_exponent, y_mantissa)

    s_sign_bit: z3.BitVecRef = z3.BitVec("s_sign_bit", 1)
    s_exponent: z3.BitVecRef = z3.BitVec("s_exponent", exponent_width)
    s_mantissa: z3.BitVecRef = z3.BitVec("s_mantissa", mantissa_width)
    s: z3.FPRef = z3.fpFP(s_sign_bit, s_exponent, s_mantissa)

    e_sign_bit: z3.BitVecRef = z3.BitVec("e_sign_bit", 1)
    e_exponent: z3.BitVecRef = z3.BitVec("e_exponent", exponent_width)
    e_mantissa: z3.BitVecRef = z3.BitVec("e_mantissa", mantissa_width)
    e: z3.FPRef = z3.fpFP(e_sign_bit, e_exponent, e_mantissa)

    solver: z3.Solver = z3.SolverFor("QF_BVFP")

    solver.add(~z3.fpIsInf(x))
    solver.add(~z3.fpIsNaN(x))
    solver.add(~z3.fpIsSubnormal(x))

    solver.add(~z3.fpIsInf(y))
    solver.add(~z3.fpIsNaN(y))
    solver.add(~z3.fpIsSubnormal(y))

    solver.add(~z3.fpIsInf(s))
    solver.add(~z3.fpIsNaN(s))
    solver.add(~z3.fpIsSubnormal(s))

    solver.add(~z3.fpIsInf(e))
    solver.add(~z3.fpIsNaN(e))
    solver.add(~z3.fpIsSubnormal(e))

    solver.add(s == z3.fpAdd(RNE, x, y))
    x_prime: z3.FPRef = z3.fpSub(RNE, s, y)
    y_prime: z3.FPRef = z3.fpSub(RNE, s, x_prime)
    x_err: z3.FPRef = z3.fpSub(RNE, x, x_prime)
    y_err: z3.FPRef = z3.fpSub(RNE, y, y_prime)
    solver.add(e == z3.fpAdd(RNE, x_err, y_err))

    max_idx: int = mantissa_width - 1
    x_leading_bit: z3.BoolRef = z3.Extract(max_idx, max_idx, x_mantissa) == ONE
    y_leading_bit: z3.BoolRef = z3.Extract(max_idx, max_idx, y_mantissa) == ONE
    s_leading_bit: z3.BoolRef = z3.Extract(max_idx, max_idx, s_mantissa) == ONE
    e_leading_bit: z3.BoolRef = z3.Extract(max_idx, max_idx, e_mantissa) == ONE

    x_trailing_bit: z3.BoolRef = z3.Extract(0, 0, x_mantissa) == ONE
    y_trailing_bit: z3.BoolRef = z3.Extract(0, 0, y_mantissa) == ONE
    s_trailing_bit: z3.BoolRef = z3.Extract(0, 0, s_mantissa) == ONE
    e_trailing_bit: z3.BoolRef = z3.Extract(0, 0, e_mantissa) == ONE

    lemmas: dict[str, z3.BoolRef]
    if model == "SE":
        lemmas = se_two_sum_lemmas(
            x,
            y,
            s,
            e,
            x_sign_bit,
            y_sign_bit,
            s_sign_bit,
            e_sign_bit,
            z3.Concat(exponent_padding, x_exponent) - exponent_bias,
            z3.Concat(exponent_padding, y_exponent) - exponent_bias,
            z3.Concat(exponent_padding, s_exponent) - exponent_bias,
            z3.Concat(exponent_padding, e_exponent) - exponent_bias,
            z3.fpIsZero,
            z3.fpIsPositive,
            z3.fpIsNegative,
            eq,
            z3.BitVecVal(precision, promoted_exponent_width),
            z3.BitVecVal(1, promoted_exponent_width),
            z3.BitVecVal(2, promoted_exponent_width),
        )
    elif model == "SETZ":
        lemmas = setz_two_sum_lemmas(
            x,
            y,
            s,
            e,
            x_sign_bit,
            y_sign_bit,
            s_sign_bit,
            e_sign_bit,
            z3.Concat(exponent_padding, x_exponent) - exponent_bias,
            z3.Concat(exponent_padding, y_exponent) - exponent_bias,
            z3.Concat(exponent_padding, s_exponent) - exponent_bias,
            z3.Concat(exponent_padding, e_exponent) - exponent_bias,
            count_trailing_zeros(x_mantissa, promoted_exponent_width),
            count_trailing_zeros(y_mantissa, promoted_exponent_width),
            count_trailing_zeros(s_mantissa, promoted_exponent_width),
            count_trailing_zeros(e_mantissa, promoted_exponent_width),
            z3.fpIsZero,
            z3.fpIsPositive,
            z3.fpIsNegative,
            eq,
            z3.BitVecVal(precision, promoted_exponent_width),
            z3.BitVecVal(1, promoted_exponent_width),
            z3.BitVecVal(2, promoted_exponent_width),
            z3.BitVecVal(3, promoted_exponent_width),
        )
    elif model == "SELTZO":
        lemmas = seltzo_two_sum_lemmas(
            x,
            y,
            s,
            e,
            x_sign_bit,
            y_sign_bit,
            s_sign_bit,
            e_sign_bit,
            x_leading_bit,
            y_leading_bit,
            s_leading_bit,
            e_leading_bit,
            x_trailing_bit,
            y_trailing_bit,
            s_trailing_bit,
            e_trailing_bit,
            z3.Concat(exponent_padding, x_exponent) - exponent_bias,
            z3.Concat(exponent_padding, y_exponent) - exponent_bias,
            z3.Concat(exponent_padding, s_exponent) - exponent_bias,
            z3.Concat(exponent_padding, e_exponent) - exponent_bias,
            z3.If(
                x_leading_bit,
                count_leading_ones(x_mantissa, promoted_exponent_width),
                count_leading_zeros(x_mantissa, promoted_exponent_width),
            ),
            z3.If(
                y_leading_bit,
                count_leading_ones(y_mantissa, promoted_exponent_width),
                count_leading_zeros(y_mantissa, promoted_exponent_width),
            ),
            z3.If(
                s_leading_bit,
                count_leading_ones(s_mantissa, promoted_exponent_width),
                count_leading_zeros(s_mantissa, promoted_exponent_width),
            ),
            z3.If(
                e_leading_bit,
                count_leading_ones(e_mantissa, promoted_exponent_width),
                count_leading_zeros(e_mantissa, promoted_exponent_width),
            ),
            z3.If(
                x_trailing_bit,
                count_trailing_ones(x_mantissa, promoted_exponent_width),
                count_trailing_zeros(x_mantissa, promoted_exponent_width),
            ),
            z3.If(
                y_trailing_bit,
                count_trailing_ones(y_mantissa, promoted_exponent_width),
                count_trailing_zeros(y_mantissa, promoted_exponent_width),
            ),
            z3.If(
                s_trailing_bit,
                count_trailing_ones(s_mantissa, promoted_exponent_width),
                count_trailing_zeros(s_mantissa, promoted_exponent_width),
            ),
            z3.If(
                e_trailing_bit,
                count_trailing_ones(e_mantissa, promoted_exponent_width),
                count_trailing_zeros(e_mantissa, promoted_exponent_width),
            ),
            z3.fpIsZero,
            z3.fpIsPositive,
            z3.fpIsNegative,
            eq,
            z3.BitVecVal(precision, promoted_exponent_width),
            z3.BitVecVal(1, promoted_exponent_width),
            z3.BitVecVal(2, promoted_exponent_width),
            z3.BitVecVal(3, promoted_exponent_width),
        )
    else:
        raise ValueError(f"Unknown floating-point model: {repr(model)}")

    return [
        create_smt_job(solver, "QF_BVFP", prefix + name + suffix, lemma)
        for name, lemma in lemmas.items()
    ]


def main() -> None:

    remaining_jobs: list[SMTJob] = []

    print("Constructing f16 lemmas...")
    remaining_jobs += create_two_sum_jobs(5, 8, 11, "SE", suffix="-F16")
    remaining_jobs += create_two_sum_jobs(5, 8, 11, "SETZ", suffix="-F16")
    remaining_jobs += create_two_sum_jobs(5, 8, 11, "SELTZO", suffix="-F16")

    if "--verify-bf16" in sys.argv:
        print("Constructing bf16 lemmas...")
        remaining_jobs += create_two_sum_jobs(8, 12, 8, "SE", suffix="-BF16")
        remaining_jobs += create_two_sum_jobs(8, 12, 8, "SETZ", suffix="-BF16")
        remaining_jobs += create_two_sum_jobs(8, 12, 8, "SELTZO", suffix="-BF16")

    if "--verify-f32" in sys.argv:
        print("Constructing f32 lemmas...")
        remaining_jobs += create_two_sum_jobs(8, 12, 24, "SE", suffix="-F32")
        remaining_jobs += create_two_sum_jobs(8, 12, 24, "SETZ", suffix="-F32")
        remaining_jobs += create_two_sum_jobs(8, 12, 24, "SELTZO", suffix="-F32")

    if "--verify-f64" in sys.argv:
        print("Constructing f64 lemmas...")
        remaining_jobs += create_two_sum_jobs(11, 16, 53, "SE", suffix="-F64")
        remaining_jobs += create_two_sum_jobs(11, 16, 53, "SETZ", suffix="-F64")
        remaining_jobs += create_two_sum_jobs(11, 16, 53, "SELTZO", suffix="-F64")

    if "--verify-f128" in sys.argv:
        print("Constructing f128 lemmas...")
        remaining_jobs += create_two_sum_jobs(15, 20, 113, "SE", suffix="-F128")
        remaining_jobs += create_two_sum_jobs(15, 20, 113, "SETZ", suffix="-F128")
        remaining_jobs += create_two_sum_jobs(15, 20, 113, "SELTZO", suffix="-F128")

    if "--verify-f256" in sys.argv:
        print("Constructing f256 lemmas...")
        remaining_jobs += create_two_sum_jobs(19, 24, 237, "SE", suffix="-F256")
        remaining_jobs += create_two_sum_jobs(19, 24, 237, "SETZ", suffix="-F256")
        remaining_jobs += create_two_sum_jobs(19, 24, 237, "SELTZO", suffix="-F256")

    running_jobs: list[SMTJob] = []
    filename_len: int = max(len(job.filename) for job in remaining_jobs)

    prefix: str = ""
    for i, arg in enumerate(sys.argv):
        if arg == "--prefix":
            prefix = sys.argv[i + 1]
        elif arg.startswith("--prefix="):
            prefix = arg[len("--prefix=") :]
    if prefix:
        print(f'Verifying only lemmas that begin with "{prefix}".')

    while running_jobs or remaining_jobs:

        # Start new jobs until all job slots are filled.
        while remaining_jobs and (len(running_jobs) < JOB_COUNT):
            next_job: SMTJob = remaining_jobs.pop(0)
            if os.path.basename(next_job.filename).startswith(prefix):
                next_job.start(BVFP_SOLVERS)
                running_jobs.append(next_job)

        # Check status of all running jobs.
        finished_jobs: list[SMTJob] = []
        for job in running_jobs:
            if job.poll():
                assert job.result is not None
                finished_jobs.append(job)

                # Print results of finished jobs.
                assert len(job.processes) == 1
                solver_name: str = job.processes.popitem()[0]

                if job.result[1] == z3.unsat:
                    print(
                        solver_name.rjust(SOLVER_LEN),
                        "proved",
                        job.filename.ljust(filename_len),
                        f"in{job.result[0]:8.3f} seconds.",
                    )
                elif job.result[1] == z3.sat:
                    print(
                        solver_name.rjust(SOLVER_LEN),
                        "refuted",
                        job.filename.ljust(filename_len),
                        f"in{job.result[0]:8.3f} seconds.",
                    )
                    print("Counterexample:")
                    with open(job.filename, "a") as f:
                        _ = f.write("(get-model)\n")
                    if solver_name == "bitwuzla":
                        _ = run(["bitwuzla", "--produce-models", job.filename])
                        sys.exit(EXIT_BITWUZLA_COUNTEREXAMPLE)
                    elif solver_name == "cvc5":
                        _ = run(["cvc5", "--fp-exp", "--produce-models", job.filename])
                        sys.exit(EXIT_CVC5_COUNTEREXAMPLE)
                    elif solver_name == "z3":
                        _ = run(["z3", job.filename])
                        sys.exit(EXIT_Z3_COUNTEREXAMPLE)
                    else:
                        sys.exit(EXIT_OTHER_COUNTEREXAMPLE)
                else:
                    assert False

        # Vacate slots of finished jobs.
        for job in finished_jobs:
            running_jobs.remove(job)

        # Sleep to avoid busy waiting. Even the fastest SMT solvers
        # take a few milliseconds, so 0.1ms is a reasonable interval.
        sleep(0.0001)


if __name__ == "__main__":
    main()
