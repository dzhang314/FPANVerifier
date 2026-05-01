#!/usr/bin/env python3

import sys
import z3

from setz_lemmas import setz_two_sum_lemmas
from seltzo_lemmas import seltzo_two_sum_lemmas
from seltzo_variables import SELTZOVariable, GLOBAL_PRECISION


Z3_ZERO: z3.ArithRef = z3.IntVal(0)
Z3_ONE: z3.ArithRef = z3.IntVal(1)
Z3_TWO: z3.ArithRef = z3.IntVal(2)
Z3_THREE: z3.ArithRef = z3.IntVal(3)


def check_equivalence(
    solver: z3.Solver,
    lemma_name: str,
    primal_lemma: z3.BoolRef,
    dual_lemma: z3.BoolRef,
) -> None:

    assert z3.is_implies(primal_lemma)
    assert z3.is_implies(dual_lemma)
    assert primal_lemma.num_args() == 2
    assert dual_lemma.num_args() == 2
    primal_hypothesis: z3.BoolRef = primal_lemma.arg(0)
    primal_conclusion: z3.BoolRef = primal_lemma.arg(1)
    dual_hypothesis: z3.BoolRef = dual_lemma.arg(0)
    dual_conclusion: z3.BoolRef = dual_lemma.arg(1)

    solver.push()
    solver.add(primal_hypothesis != dual_hypothesis)
    if solver.check() != z3.unsat:
        print(
            f"ERROR: Hypothesis of {lemma_name} is distinct from its mirror dual.",
            file=sys.stderr,
        )
    solver.pop()

    solver.push()
    solver.add(primal_conclusion != dual_conclusion)
    if solver.check() != z3.unsat:
        print(
            f"ERROR: Conclusion of {lemma_name} is distinct from its mirror dual.",
            file=sys.stderr,
        )
    solver.pop()


def main_setz() -> None:

    solver: z3.Solver = z3.SolverFor("QF_LIA")
    x: SELTZOVariable = SELTZOVariable(solver, "x")
    y: SELTZOVariable = SELTZOVariable(solver, "y")
    s: SELTZOVariable = SELTZOVariable(solver, "s")
    e: SELTZOVariable = SELTZOVariable(solver, "e")

    primal_setz_lemmas: dict[str, z3.BoolRef] = setz_two_sum_lemmas(
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

    dual_setz_lemmas: dict[str, z3.BoolRef] = setz_two_sum_lemmas(
        y,
        x,
        s,
        e,
        y.sign_bit,
        x.sign_bit,
        s.sign_bit,
        e.sign_bit,
        y.exponent,
        x.exponent,
        s.exponent,
        e.exponent,
        z3.If(y.trailing_bit, Z3_ZERO, y.num_trailing_bits),
        z3.If(x.trailing_bit, Z3_ZERO, x.num_trailing_bits),
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

    setz_lemma_names: set[str] = set(primal_setz_lemmas.keys())
    special_setz_lemma_names: set[str] = {
        "SETZ-TwoSum-Z1-PP",
        "SETZ-TwoSum-Z1-PN",
        "SETZ-TwoSum-Z1-NP",
        "SETZ-TwoSum-Z1-NN",
        "SETZ-TwoSum-FS2",
        "SETZ-TwoSum-FS3",
        "SETZ-TwoSum-FD2",
    }

    print("Checking SETZ lemma mirror duality...")
    mirror_name: str
    for name in setz_lemma_names:
        if name.endswith("-X"):
            mirror_name = name[:-2] + "-Y"
            if mirror_name in setz_lemma_names:
                check_equivalence(
                    solver,
                    name,
                    primal_setz_lemmas[name],
                    dual_setz_lemmas[mirror_name],
                )
            else:
                print(f"ERROR: Lemma {name} has no mirror dual.", file=sys.stderr)
        elif name.endswith("-Y"):
            mirror_name = name[:-2] + "-X"
            if mirror_name in setz_lemma_names:
                check_equivalence(
                    solver,
                    name,
                    primal_setz_lemmas[name],
                    dual_setz_lemmas[mirror_name],
                )
            else:
                print(f"ERROR: Lemma {name} has no mirror dual.", file=sys.stderr)
        else:
            if name not in special_setz_lemma_names:
                print(
                    f"WARNING: Lemma {name} has no recognized suffix.", file=sys.stderr
                )

    print("Checking SETZ lemma hypothesis satisfiability...")
    for name in setz_lemma_names:
        lemma: z3.BoolRef = primal_setz_lemmas[name]
        assert z3.is_implies(lemma)
        assert lemma.num_args() == 2
        hypothesis: z3.BoolRef = lemma.arg(0)
        solver.push()
        solver.add(GLOBAL_PRECISION <= 9)
        solver.add(hypothesis)
        if solver.check() != z3.sat:
            print(f"ERROR: Lemma {name} has unsatisfiable hypotheses.", file=sys.stderr)
        solver.pop()

    print("Checking SETZ lemma hypothesis disjointness...")
    for name_a in setz_lemma_names:
        for name_b in setz_lemma_names:
            if name_a != name_b:
                lemma_a: z3.BoolRef = primal_setz_lemmas[name_a]
                lemma_b: z3.BoolRef = primal_setz_lemmas[name_b]
                assert z3.is_implies(lemma_a)
                assert z3.is_implies(lemma_b)
                assert lemma_a.num_args() == 2
                assert lemma_b.num_args() == 2
                hypothesis_a: z3.BoolRef = lemma_a.arg(0)
                hypothesis_b: z3.BoolRef = lemma_b.arg(0)
                solver.push()
                solver.add(GLOBAL_PRECISION >= 4)
                solver.add(hypothesis_a)
                solver.add(hypothesis_b)
                if solver.check() != z3.unsat:
                    print(
                        f"WARNING: Lemmas {name_a} and {name_b} have overlapping hypotheses.",
                        file=sys.stderr,
                    )
                solver.pop()


def main_seltzo() -> None:

    solver: z3.Solver = z3.SolverFor("QF_LIA")
    x: SELTZOVariable = SELTZOVariable(solver, "x")
    y: SELTZOVariable = SELTZOVariable(solver, "y")
    s: SELTZOVariable = SELTZOVariable(solver, "s")
    e: SELTZOVariable = SELTZOVariable(solver, "e")

    primal_seltzo_lemmas: dict[str, z3.BoolRef] = seltzo_two_sum_lemmas(
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

    dual_seltzo_lemmas: dict[str, z3.BoolRef] = seltzo_two_sum_lemmas(
        y,
        x,
        s,
        e,
        y.sign_bit,
        x.sign_bit,
        s.sign_bit,
        e.sign_bit,
        y.leading_bit,
        x.leading_bit,
        s.leading_bit,
        e.leading_bit,
        y.trailing_bit,
        x.trailing_bit,
        s.trailing_bit,
        e.trailing_bit,
        y.exponent,
        x.exponent,
        s.exponent,
        e.exponent,
        y.num_leading_bits,
        x.num_leading_bits,
        s.num_leading_bits,
        e.num_leading_bits,
        y.num_trailing_bits,
        x.num_trailing_bits,
        s.num_trailing_bits,
        e.num_trailing_bits,
        lambda v: v.is_zero,
        lambda v: ~v.sign_bit,
        lambda v: v.sign_bit,
        lambda v, w: v.can_equal(w),
        GLOBAL_PRECISION,
        z3.IntVal(1),
        z3.IntVal(2),
        z3.IntVal(3),
    )

    if primal_seltzo_lemmas.keys() != dual_seltzo_lemmas.keys():
        print(
            "ERROR: seltzo_two_sum_lemmas returns inconsistent lemma names.",
            file=sys.stderr,
        )

    precise_seltzo_lemma_names: set[str] = set(
        lemma_name
        for lemma_name in primal_seltzo_lemmas.keys()
        if not lemma_name.startswith("SELTZO-TwoSum-P0")
        and not lemma_name.startswith("SELTZO-TwoSum-T0")
    )

    print("Checking SELTZO lemma mirror duality...")
    mirror_name: str
    for name in precise_seltzo_lemma_names:
        if name.endswith("-X"):
            mirror_name = name[:-2] + "-Y"
            if mirror_name in precise_seltzo_lemma_names:
                check_equivalence(
                    solver,
                    name,
                    primal_seltzo_lemmas[name],
                    dual_seltzo_lemmas[mirror_name],
                )
            else:
                print(f"ERROR: Lemma {name} has no mirror dual.", file=sys.stderr)
        elif name.endswith("-Y"):
            mirror_name = name[:-2] + "-X"
            if mirror_name in precise_seltzo_lemma_names:
                check_equivalence(
                    solver,
                    name,
                    primal_seltzo_lemmas[name],
                    dual_seltzo_lemmas[mirror_name],
                )
            else:
                print(f"ERROR: Lemma {name} has no mirror dual.", file=sys.stderr)
        else:
            if not (name.endswith("-SE") or name.endswith("-DE")):
                print(
                    f"WARNING: Lemma {name} has no recognized suffix.", file=sys.stderr
                )

    print("Checking SELTZO lemma hypothesis satisfiability...")
    for name in precise_seltzo_lemma_names:
        lemma: z3.BoolRef = primal_seltzo_lemmas[name]
        assert z3.is_implies(lemma)
        assert lemma.num_args() == 2
        hypothesis: z3.BoolRef = lemma.arg(0)
        solver.push()
        solver.add(GLOBAL_PRECISION <= 9)
        solver.add(hypothesis)
        if solver.check() != z3.sat:
            print(f"ERROR: Lemma {name} has unsatisfiable hypotheses.", file=sys.stderr)
        solver.pop()

    print("Checking SELTZO lemma hypothesis disjointness...")
    for name_a in precise_seltzo_lemma_names:
        for name_b in precise_seltzo_lemma_names:
            if name_a != name_b:
                lemma_a: z3.BoolRef = primal_seltzo_lemmas[name_a]
                lemma_b: z3.BoolRef = primal_seltzo_lemmas[name_b]
                assert z3.is_implies(lemma_a)
                assert z3.is_implies(lemma_b)
                assert lemma_a.num_args() == 2
                assert lemma_b.num_args() == 2
                hypothesis_a: z3.BoolRef = lemma_a.arg(0)
                hypothesis_b: z3.BoolRef = lemma_b.arg(0)
                solver.push()
                solver.add(GLOBAL_PRECISION >= 4)
                solver.add(hypothesis_a)
                solver.add(hypothesis_b)
                if solver.check() != z3.unsat:
                    print(
                        f"WARNING: Lemmas {name_a} and {name_b} have overlapping hypotheses.",
                        file=sys.stderr,
                    )
                solver.pop()


if __name__ == "__main__":
    main_setz()
    main_seltzo()
