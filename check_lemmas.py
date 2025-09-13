#!/usr/bin/env python3

import sys
import z3

from seltzo_lemmas import seltzo_two_sum_lemmas
from seltzo_variables import SELTZOVariable, GLOBAL_PRECISION


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
    primal_hypothesis = primal_lemma.arg(0)
    primal_conclusion = primal_lemma.arg(1)
    dual_hypothesis = dual_lemma.arg(0)
    dual_conclusion = dual_lemma.arg(1)

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


def main() -> None:

    solver = z3.SolverFor("QF_LIA")
    x = SELTZOVariable(solver, "x")
    y = SELTZOVariable(solver, "y")
    s = SELTZOVariable(solver, "s")
    e = SELTZOVariable(solver, "e")

    lemmas = seltzo_two_sum_lemmas(
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
        z3.IntVal(1),
        z3.IntVal(2),
        z3.IntVal(3),
    )

    mirror_lemmas = seltzo_two_sum_lemmas(
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

    if lemmas.keys() != mirror_lemmas.keys():
        print(
            "ERROR: seltzo_two_sum_lemmas returns inconsistent lemma names.",
            file=sys.stderr,
        )

    precise_lemma_names = set(
        lemma_name
        for lemma_name in lemmas.keys()
        if not lemma_name.startswith("SELTZO-TwoSum-P0")
        and not lemma_name.startswith("SELTZO-TwoSum-T0")
    )

    print("Checking lemma mirror duality...")
    for name in precise_lemma_names:
        if name.endswith("-X"):
            mirror_name = name[:-2] + "-Y"
            if mirror_name in precise_lemma_names:
                check_equivalence(
                    solver, name, lemmas[name], mirror_lemmas[mirror_name]
                )
            else:
                print(f"ERROR: Lemma {name} has no mirror dual.", file=sys.stderr)
        elif name.endswith("-Y"):
            mirror_name = name[:-2] + "-X"
            if mirror_name in precise_lemma_names:
                check_equivalence(
                    solver, name, lemmas[name], mirror_lemmas[mirror_name]
                )
            else:
                print(f"ERROR: Lemma {name} has no mirror dual.", file=sys.stderr)
        else:
            if not (name.endswith("-SE") or name.endswith("-DE")):
                print(
                    f"WARNING: Lemma {name} has no recognized suffix.", file=sys.stderr
                )

    print("Checking lemma hypothesis satisfiability...")
    for name in precise_lemma_names:
        lemma = lemmas[name]
        assert z3.is_implies(lemma)
        assert lemma.num_args() == 2
        hypothesis = lemma.arg(0)
        solver.push()
        solver.add(GLOBAL_PRECISION <= 9)
        solver.add(hypothesis)
        if solver.check() != z3.sat:
            print(f"ERROR: Lemma {name} has unsatisfiable hypotheses.", file=sys.stderr)
        solver.pop()

    print("Checking lemma hypothesis disjointness...")
    for name_a in precise_lemma_names:
        for name_b in precise_lemma_names:
            if name_a != name_b:
                lemma_a = lemmas[name_a]
                lemma_b = lemmas[name_b]
                assert z3.is_implies(lemma_a)
                assert z3.is_implies(lemma_b)
                assert lemma_a.num_args() == 2
                assert lemma_b.num_args() == 2
                hypothesis_a = lemma_a.arg(0)
                hypothesis_b = lemma_b.arg(0)
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
    main()
