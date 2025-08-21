import os
import subprocess
import z3

from random import shuffle
from sys import argv
from time import perf_counter_ns
from typing import TypeVar


def count_leading_zeros(b: z3.BitVecRef, result_width: int) -> z3.BitVecRef:
    result: z3.BitVecRef = z3.BitVecVal(0, result_width)
    for i in range(1, b.size() + 1):
        substr: z3.BitVecRef = z3.Extract(b.size() - 1, b.size() - i, b)
        zeros: z3.BitVecRef = z3.BitVecVal(0, i)
        result = z3.If(substr == zeros, z3.BitVecVal(i, result_width), result)
    return result


def count_leading_ones(b: z3.BitVecRef, result_width: int) -> z3.BitVecRef:
    result: z3.BitVecRef = z3.BitVecVal(0, result_width)
    for i in range(1, b.size() + 1):
        substr: z3.BitVecRef = z3.Extract(b.size() - 1, b.size() - i, b)
        ones: z3.BitVecRef = z3.BitVecVal(2**i - 1, i)  # pyright: ignore[reportAny]
        result = z3.If(substr == ones, z3.BitVecVal(i, result_width), result)
    return result


def count_trailing_zeros(b: z3.BitVecRef, result_width: int) -> z3.BitVecRef:
    result: z3.BitVecRef = z3.BitVecVal(0, result_width)
    for i in range(1, b.size() + 1):
        substr: z3.BitVecRef = z3.Extract(i - 1, 0, b)
        zeros: z3.BitVecRef = z3.BitVecVal(0, i)
        result = z3.If(substr == zeros, z3.BitVecVal(i, result_width), result)
    return result


def count_trailing_ones(b: z3.BitVecRef, result_width: int) -> z3.BitVecRef:
    result: z3.BitVecRef = z3.BitVecVal(0, result_width)
    for i in range(1, b.size() + 1):
        substr: z3.BitVecRef = z3.Extract(i - 1, 0, b)
        ones: z3.BitVecRef = z3.BitVecVal(2**i - 1, i)  # pyright: ignore[reportAny]
        result = z3.If(substr == ones, z3.BitVecVal(i, result_width), result)
    return result


BoolVar = TypeVar("BoolVar", z3.BoolRef, z3.BitVecRef)
IntVar = TypeVar("IntVar", z3.ArithRef, z3.BitVecRef)
FloatVar = TypeVar("FloatVar")


# This wrapper is a workaround for Pyright's inability
# to propagate type variables through overload sets.
def z3_If(a: z3.BoolRef, b: IntVar, c: IntVar) -> IntVar:
    return z3.If(  # pyright: ignore[reportCallIssue, reportUnknownVariableType]
        a, b, c  # pyright: ignore[reportArgumentType]
    )


def pop_flag(flag: str) -> bool:
    assert flag != "--"
    indices: list[int] = []
    for i, arg in enumerate(argv):
        if arg == "--":
            break
        elif arg == flag:
            indices.append(i)
    if indices:
        for index in reversed(indices):
            _ = argv.pop(index)
        return True
    return False


def detect_smt_solvers() -> set[str]:

    result: set[str] = set[str]()

    # if not pop_flag("--no-alt-ergo"):
    #     try:
    #         alt_ergo_version: str = subprocess.check_output(
    #             ["alt-ergo", "--version"], text=True
    #         )
    #         print("Found Alt-Ergo:", alt_ergo_version.strip())
    #         result.add("alt-ergo")
    #     except OSError:
    #         print("Alt-Ergo not available.")

    if not pop_flag("--no-bitwuzla"):
        try:
            bitwuzla_version: str = subprocess.check_output(
                ["bitwuzla", "--version"], text=True
            )
            print("Found Bitwuzla:", bitwuzla_version.strip())
            result.add("bitwuzla")
        except OSError:
            print("Bitwuzla not available.")

    if not pop_flag("--no-cvc5"):
        try:
            cvc5_version: str = subprocess.check_output(
                ["cvc5", "--version"], text=True
            )
            print("Found CVC5:", cvc5_version.splitlines()[0].strip())
            result.add("cvc5")
        except OSError:
            print("CVC5 not available.")

    if not pop_flag("--no-mathsat"):
        try:
            mathsat_version: str = subprocess.check_output(
                ["mathsat", "-version"], text=True
            )
            print("Found MathSAT:", mathsat_version.strip())
            result.add("mathsat")
        except OSError:
            print("MathSAT not available.")

    if not pop_flag("--no-opensmt"):
        try:
            opensmt_version: str = subprocess.check_output(
                ["opensmt", "--version"], text=True, stderr=subprocess.STDOUT
            )
            print("Found OpenSMT:", opensmt_version.strip())
            result.add("opensmt")
        except OSError:
            print("OpenSMT not available.")

    # if not pop_flag("--no-princess"):
    #     try:
    #         princess_version: str = subprocess.check_output(
    #             ["princess", "+version"], text=True
    #         )
    #         print("Found Princess:", princess_version.strip())
    #         result.add("princess")
    #     except OSError:
    #         print("Princess not available.")

    if not pop_flag("--no-smtinterpol"):
        try:
            smtinterpol_version: str = subprocess.check_output(
                ["smtinterpol", "-version"], text=True, stderr=subprocess.STDOUT
            )
            print("Found SMTInterpol:", smtinterpol_version.strip())
            result.add("smtinterpol")
        except OSError:
            print("SMTInterpol not available.")

    # if not pop_flag("--no-smtrat"):
    #     try:
    #         # SMT-RAT returns a nonzero exit code, so check_output fails.
    #         proc: subprocess.CompletedProcess[str] = subprocess.run(
    #             ["smtrat", "--version"], capture_output=True, text=True
    #         )
    #         print("Found SMT-RAT:", proc.stdout.splitlines()[0].strip())
    #         result.add("smtrat")
    #     except OSError:
    #         print("SMT-RAT not available.")

    # if not pop_flag("--no-stp"):
    #     try:
    #         stp_version: str = subprocess.check_output(
    #             ["stp", "--version"], text=True
    #         )
    #         print("Found STP:", stp_version.splitlines()[0].strip())
    #         result.add("stp")
    #     except OSError:
    #         print("STP not available.")

    if not pop_flag("--no-yices"):
        try:
            yices_version: str = subprocess.check_output(
                ["yices-smt2", "--version"], text=True
            )
            print("Found Yices:", yices_version.splitlines()[0].strip())
            result.add("yices-smt2")
        except OSError:
            print("Yices not available.")

    if not pop_flag("--no-z3"):
        try:
            z3_version: str = subprocess.check_output(["z3", "--version"], text=True)
            print("Found Z3:", z3_version.strip())
            result.add("z3")
        except OSError:
            print("Z3 not available.")

    return result


SMT_SOLVERS: set[str] = detect_smt_solvers()
UNSUPPORTED_LOGICS: dict[str, set[str]] = {
    # "alt-ergo": {"QF_BVFP"},
    "bitwuzla": {"QF_LIA"},
    "cvc5": set(),
    "mathsat": set(),
    "opensmt": {"QF_BVFP"},
    # "princess": {"QF_BVFP"},
    "smtinterpol": {"QF_BVFP"},
    # "smtrat": {"QF_BVFP"},
    # "stp": {"QF_BVFP", "QF_LIA"},
    "yices-smt2": {"QF_BVFP"},
    "z3": set(),
}


class SMTJob(object):

    def __init__(self, filename: str, logic: str) -> None:
        assert os.path.isfile(filename)
        self.filename: str = filename
        self.logic: str = logic
        self.processes: dict[str, tuple[int, subprocess.Popen[str]]] = {}
        self.result: tuple[float, z3.CheckSatResult] | None = None

    def start(self) -> None:
        assert not self.processes
        assert self.result is None
        solvers: list[str] = []
        for solver in SMT_SOLVERS:
            if self.logic not in UNSUPPORTED_LOGICS[solver]:
                solvers.append(solver)
        # Launch solvers in random order to prevent launch order bias.
        shuffle(solvers)
        for solver in solvers:
            command: list[str] = [solver]
            if solver == "cvc5" and self.logic == "QF_BVFP":
                command.append("--fp-exp")
            if solver == "princess":
                command.append("+quiet")
            if solver == "smtinterpol":
                command.append("-q")
                command.append("-no-success")
            command.append(self.filename)
            self.processes[solver] = (
                perf_counter_ns(),
                subprocess.Popen(
                    command,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                ),
            )

    def poll(self) -> bool:
        assert self.processes

        if self.result is not None:
            return True

        finished_solver: str | None = None
        for smt_solver, (start, process) in self.processes.items():
            if process.poll() is not None:

                # Measure elapsed time.
                stop: int = perf_counter_ns()
                elapsed: float = (stop - start) / 1.0e9

                # Verify successful termination.
                stdout, stderr = process.communicate()
                if process.returncode != 0:
                    raise RuntimeError(
                        f"{smt_solver} exited with code {process.returncode} on file "
                        + repr(self.filename)
                        + ":\n"
                        + stdout
                        + "\n"
                        + stderr
                    )

                # Parse SMT solver output.
                if stdout == "unsat\n":
                    assert not stderr
                    self.result = (elapsed, z3.unsat)
                elif stdout == "sat\n":
                    assert not stderr
                    self.result = (elapsed, z3.sat)
                elif stdout == "unknown\n":
                    assert not stderr
                    self.result = (elapsed, z3.unknown)
                else:
                    raise RuntimeError(
                        f"Unexpected output from {smt_solver} on file "
                        + repr(self.filename)
                        + ":\n"
                        + stdout
                        + "\n"
                        + stderr
                    )

                finished_solver = smt_solver
                break

        # If an SMT solver has terminated, kill all other solvers.
        if finished_solver is not None:
            for other_solver in self.processes.keys() - {finished_solver}:
                self.processes[other_solver][1].kill()
                del self.processes[other_solver]

        return self.result is not None


def create_smt_job(
    solver: z3.Solver, logic: str, name: str, claim: z3.BoolRef
) -> SMTJob:

    # Obtain current solver state and claim in SMT-LIB 2 format.
    solver.push()
    solver.add(z3.Not(claim))
    contents: str = f"(set-logic {logic})\n" + solver.to_smt2()
    solver.pop()

    # Write SMT-LIB 2 file in tmp subdirectory.
    os.makedirs("tmp", exist_ok=True)
    filename: str = os.path.join("tmp", name + ".smt2")
    with open(filename, "w") as f:
        _ = f.write(contents)

    return SMTJob(filename, logic)
