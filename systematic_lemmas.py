import z3
from smt_utils import BoolVar, IntVar
from typing import Literal, TypeAlias


SELTZOValue: TypeAlias = tuple[BoolVar, int, int, IntVar, IntVar, IntVar] | Literal[0]


def seltzo_two_sum_systematic_lemmas(
    sx: BoolVar,
    sy: BoolVar,
    ss: BoolVar,
    se: BoolVar,
    lbx: z3.BoolRef,
    lby: z3.BoolRef,
    lbs: z3.BoolRef,
    lbe: z3.BoolRef,
    tbx: z3.BoolRef,
    tby: z3.BoolRef,
    tbs: z3.BoolRef,
    tbe: z3.BoolRef,
    ex: IntVar,
    ey: IntVar,
    es: IntVar,
    ee: IntVar,
    fx: IntVar,
    fy: IntVar,
    fs: IntVar,
    fe: IntVar,
    gx: IntVar,
    gy: IntVar,
    gs: IntVar,
    ge: IntVar,
    same_sign: z3.BoolRef,
    diff_sign: z3.BoolRef,
    xy_nonzero: z3.BoolRef,
    x_pow2: z3.BoolRef,
    y_pow2: z3.BoolRef,
    x_all1: z3.BoolRef,
    y_all1: z3.BoolRef,
    x_r0r1: z3.BoolRef,
    y_r0r1: z3.BoolRef,
    x_r1r0: z3.BoolRef,
    y_r1r0: z3.BoolRef,
    s_pos_zero: z3.BoolRef,
    e_pos_zero: z3.BoolRef,
    p: IntVar,
    one: IntVar,
    two: IntVar,
    three: IntVar,
) -> dict[str, z3.BoolRef]:

    implicit_hypothesis: z3.BoolRef = xy_nonzero
    result: dict[str, z3.BoolRef] = {}

    def seltzo_output(
        value: SELTZOValue[BoolVar, IntVar],
        s: BoolVar,
        lb: z3.BoolRef,
        tb: z3.BoolRef,
        e: IntVar,
        f: IntVar,
        g: IntVar,
        is_pos_zero: z3.BoolRef,
    ) -> z3.BoolRef:
        if not value:
            return is_pos_zero
        s_val, lb_val, tb_val, e_val, f_val, g_val = value
        return z3.And(
            s == s_val,
            lb if lb_val else ~lb,
            tb if tb_val else ~tb,
            e == e_val,
            f == f_val,
            g == g_val,
        )

    def seltzo_lemma(
        hypotheses: tuple[z3.BoolRef, ...],
        *outputs: SELTZOValue[BoolVar, IntVar],
    ) -> z3.BoolRef:
        assert outputs and len(outputs) % 2 == 0
        cases: list[z3.BoolRef] = []
        for i in range(0, len(outputs), 2):
            s = seltzo_output(outputs[i], ss, lbs, tbs, es, fs, gs, s_pos_zero)
            e = seltzo_output(outputs[i + 1], se, lbe, tbe, ee, fe, ge, e_pos_zero)
            cases.append(z3.And(s, e))
        return z3.Implies(
            z3.And(implicit_hypothesis, *hypotheses),
            cases[0] if len(cases) == 1 else z3.Or(*cases),
        )

    def seltzo_lemma_zero_error(
        hypotheses: tuple[z3.BoolRef, ...],
        *outputs: SELTZOValue[BoolVar, IntVar],
    ) -> z3.BoolRef:
        assert outputs
        cases: list[z3.BoolRef] = []
        for output in outputs:
            s = seltzo_output(output, ss, lbs, tbs, es, fs, gs, s_pos_zero)
            cases.append(z3.And(s, e_pos_zero))
        return z3.Implies(
            z3.And(implicit_hypothesis, *hypotheses),
            cases[0] if len(cases) == 1 else z3.Or(*cases),
        )

    # ALL CODE BELOW THIS LINE IS MACHINE-GENERATED.
    # DO NOT EDIT THESE LEMMA STATEMENTS DIRECTLY!

    # conjecturer/SELTZO-TwoSum-ALL1-ALL1-D.jl
    implicit_hypothesis = z3.And(xy_nonzero, x_all1, y_all1, diff_sign)
    result["SELTZO-TwoSum-ALL1-ALL1-DE"] = seltzo_lemma_zero_error(
        (ex == ey,),
        0,
    )
    result["SELTZO-TwoSum-ALL1-ALL1-DA1-X"] = seltzo_lemma_zero_error(
        (ex == ey + one,),
        (sx, 1, 1, ex - one, fx - one, gx - one),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-DA1-Y"] = seltzo_lemma_zero_error(
        (ey == ex + one,),
        (sy, 1, 1, ey - one, fy - one, gy - one),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-DA2-X"] = seltzo_lemma(
        (ex == ey + two,),
        (sx, 0, 1, ex, ey, ey + one),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-DA2-Y"] = seltzo_lemma(
        (ey == ex + two,),
        (sy, 0, 1, ey, ex, ex + one),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-DG-X"] = seltzo_lemma(
        (ex > ey + two, ex < ey + p),
        (sx, 1, 1, ex, ey + one, ey + one),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-DG-Y"] = seltzo_lemma(
        (ey > ex + two, ey < ex + p),
        (sy, 1, 1, ey, ex + one, ex + one),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-DB-X"] = seltzo_lemma(
        (ex == ey + p,),
        (sx, 1, 0, ex, ey + one, ey + two),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-DB-Y"] = seltzo_lemma(
        (ey == ex + p,),
        (sy, 1, 0, ey, ex + one, ex + two),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )

    # conjecturer/SELTZO-TwoSum-ALL1-ALL1-S.jl
    implicit_hypothesis = z3.And(xy_nonzero, x_all1, y_all1, same_sign)
    result["SELTZO-TwoSum-ALL1-ALL1-SE"] = seltzo_lemma_zero_error(
        (ex == ey,),
        (sx, 1, 1, ex + one, fx + one, gx + one),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-SA-X"] = seltzo_lemma(
        (ex == ey + one,),
        (sx, 0, 1, ex + one, ey, ey + one),
        (sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-SA-Y"] = seltzo_lemma(
        (ey == ex + one,),
        (sy, 0, 1, ey + one, ex, ex + one),
        (sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-SG-X"] = seltzo_lemma(
        (ex > ey + one, ex < ey + (p - one)),
        (sx, 0, 1, ex + one, ey, ey + one),
        (sy, 1, 0, fx, fy, fy + one),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-SG-Y"] = seltzo_lemma(
        (ey > ex + one, ey < ex + (p - one)),
        (sy, 0, 1, ey + one, ex, ex + one),
        (sx, 1, 0, fy, fx, fx + one),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-SB1-X"] = seltzo_lemma(
        (ex == ey + (p - one),),
        (sx, 0, 0, ex + one, fx + one, gx + one),
        (sy, 1, 0, fx, fy, fy + one),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-SB1-Y"] = seltzo_lemma(
        (ey == ex + (p - one),),
        (sy, 0, 0, ey + one, fy + one, gy + one),
        (sx, 1, 0, fy, fx, fx + one),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-SB2-X"] = seltzo_lemma(
        (ex == ey + p,),
        (sx, 0, 0, ex + one, fx + one, gx + one),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-SB2-Y"] = seltzo_lemma(
        (ey == ex + p,),
        (sy, 0, 0, ey + one, fy + one, gy + one),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )

    # conjecturer/SELTZO-TwoSum-ALL1-POW2-D.jl
    implicit_hypothesis = z3.And(xy_nonzero, diff_sign)
    result["SELTZO-TwoSum-ALL1-POW2-DE-X"] = seltzo_lemma_zero_error(
        (x_all1, y_pow2, ex == ey),
        (sx, 1, 0, ex - one, fx, fx + one),
    )
    result["SELTZO-TwoSum-ALL1-POW2-DE-Y"] = seltzo_lemma_zero_error(
        (y_all1, x_pow2, ey == ex),
        (sy, 1, 0, ey - one, fy, fy + one),
    )
    result["SELTZO-TwoSum-ALL1-POW2-DB1-X"] = seltzo_lemma_zero_error(
        (x_all1, y_pow2, ex == ey + (p - one)),
        (sx, 1, 0, ex, ey, ey + one),
    )
    result["SELTZO-TwoSum-ALL1-POW2-DB1-Y"] = seltzo_lemma_zero_error(
        (y_all1, x_pow2, ey == ex + (p - one)),
        (sy, 1, 0, ey, ex, ex + one),
    )
    result["SELTZO-TwoSum-ALL1-POW2-DB2-X"] = seltzo_lemma(
        (x_all1, y_pow2, ex == ey + p),
        (sx, 1, 0, ex, ey + one, ey + two),
        (~sy, 0, 0, fx, fx - p, fx),
    )
    result["SELTZO-TwoSum-ALL1-POW2-DB2-Y"] = seltzo_lemma(
        (y_all1, x_pow2, ey == ex + p),
        (sy, 1, 0, ey, ex + one, ex + two),
        (~sx, 0, 0, fy, fy - p, fy),
    )

    # conjecturer/SELTZO-TwoSum-ALL1-POW2-S.jl
    implicit_hypothesis = z3.And(xy_nonzero, same_sign)
    result["SELTZO-TwoSum-ALL1-POW2-SE-X"] = seltzo_lemma(
        (x_all1, y_pow2, ex == ey),
        (sx, 1, 0, ex + one, ey - one, ey),
        (~sy, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-ALL1-POW2-SE-Y"] = seltzo_lemma(
        (y_all1, x_pow2, ey == ex),
        (sy, 1, 0, ey + one, ex - one, ex),
        (~sx, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-ALL1-POW2-SG-X"] = seltzo_lemma(
        (x_all1, y_pow2, ex > ey, ex < ey + (p - two)),
        (sx, 0, 0, ex + one, ey, ey),
        (~sy, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-ALL1-POW2-SG-Y"] = seltzo_lemma(
        (y_all1, x_pow2, ey > ex, ey < ex + (p - two)),
        (sy, 0, 0, ey + one, ex, ex),
        (~sx, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-ALL1-POW2-SB1-X"] = seltzo_lemma(
        (x_all1, y_pow2, ex == ey + (p - two)),
        (sx, 0, 0, ex + one, ey - one, ex + one),
        (sy, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-ALL1-POW2-SB1-Y"] = seltzo_lemma(
        (y_all1, x_pow2, ey == ex + (p - two)),
        (sy, 0, 0, ey + one, ex - one, ey + one),
        (sx, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-ALL1-POW2-SB2-X"] = seltzo_lemma_zero_error(
        (x_all1, y_pow2, ex == ey + (p - one)),
        (sx, 0, 0, ex + one, fx + one, gx + one),
    )
    result["SELTZO-TwoSum-ALL1-POW2-SB2-Y"] = seltzo_lemma_zero_error(
        (y_all1, x_pow2, ey == ex + (p - one)),
        (sy, 0, 0, ey + one, fy + one, gy + one),
    )
    result["SELTZO-TwoSum-ALL1-POW2-SB3-X"] = seltzo_lemma(
        (x_all1, y_pow2, ex == ey + p),
        (sx, 0, 0, ex + one, fx + one, gx + one),
        (~sy, 0, 0, fx, fx - p, fx),
    )
    result["SELTZO-TwoSum-ALL1-POW2-SB3-Y"] = seltzo_lemma(
        (y_all1, x_pow2, ey == ex + p),
        (sy, 0, 0, ey + one, fy + one, gy + one),
        (~sx, 0, 0, fy, fy - p, fy),
    )

    # conjecturer/SELTZO-TwoSum-ALL1-R0R1-D.jl
    implicit_hypothesis = z3.And(xy_nonzero, diff_sign)
    result["SELTZO-TwoSum-ALL1-R0R1-DE0-X"] = seltzo_lemma_zero_error(
        (x_all1, y_r0r1, ex == ey, ey > fy + two),
        (sx, 1, 0, ex - one, fy, fy + one),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-DE0-Y"] = seltzo_lemma_zero_error(
        (y_all1, x_r0r1, ey == ex, ex > fx + two),
        (sy, 1, 0, ey - one, fx, fx + one),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-DE1-X"] = seltzo_lemma_zero_error(
        (x_all1, y_r0r1, ex == ey, ey == fy + two),
        (sx, 0, 0, ex - one, ex - (p + one), ex - one),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-DE1-Y"] = seltzo_lemma_zero_error(
        (y_all1, x_r0r1, ey == ex, ex == fx + two),
        (sy, 0, 0, ey - one, ey - (p + one), ey - one),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D1-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex > fy + p, ex < ey + (p - one), ey < fy + (p - one)),
        (sx, 1, 1, ex, ey, ey),
        (sy, 1, 0, fy, ey - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D1-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey > fx + p, ey < ex + (p - one), ex < fx + (p - one)),
        (sy, 1, 1, ey, ex, ex),
        (sx, 1, 0, fx, ex - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D1A-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == ey + (p - one), ey < fy + (p - one)),
        (sx, 1, 0, ex, ey, ey + one),
        (sy, 1, 0, fy, ey - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D1A-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == ex + (p - one), ex < fx + (p - one)),
        (sy, 1, 0, ey, ex, ex + one),
        (sx, 1, 0, fx, ex - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D1B-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex > fy + p, ex < ey + (p - one), ey == fy + (p - one)),
        (sx, 1, 1, ex, ey, ey),
        (sy, 0, 0, fy, fy - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D1B-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey > fx + p, ey < ex + (p - one), ex == fx + (p - one)),
        (sy, 1, 1, ey, ex, ex),
        (sx, 0, 0, fx, fx - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D1AB-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == ey + (p - one), ey == fy + (p - one)),
        (sx, 1, 0, ex, ey, ey + one),
        (sy, 0, 0, fy, fy - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D1AB-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == ex + (p - one), ex == fx + (p - one)),
        (sy, 1, 0, ey, ex, ex + one),
        (sx, 0, 0, fx, fx - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D2-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex < fy + p, ex > ey + one),
        (sx, 1, 1, ex, ey, fy + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D2-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey < fx + p, ey > ex + one),
        (sy, 1, 1, ey, ex, fx + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D2A0-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == fy + p, ex > ey + one, ey > fy + two),
        (sx, 1, 0, ex, ey, fy + two),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D2A0-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == fx + p, ey > ex + one, ex > fx + two),
        (sy, 1, 0, ey, ex, fx + two),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D2A1-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == fy + p, ey == fy + two),
        (sx, 1, 0, ex, ey, fy + three),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D2A1-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == fx + p, ex == fx + two),
        (sy, 1, 0, ey, ex, fx + three),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D2B-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex < fy + p, ex == ey + one),
        (sx, 0, 0, ex, ey - one, fy + one),
        (sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D2B-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey < fx + p, ey == ex + one),
        (sy, 0, 0, ey, ex - one, fx + one),
        (sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D2AB-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == fy + p, ex == ey + one),
        (sx, 0, 0, ex, ey - one, fy + two),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-D2AB-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == fx + p, ey == ex + one),
        (sy, 0, 0, ey, ex - one, fx + two),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-DB0-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == ey + p, ey > fy + two, ey < fy + (p - one)),
        (sx, 1, 0, ex, ey + one, ey + two),
        (~sy, 1, 0, ey - one, fy, ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-DB0-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == ex + p, ex > fx + two, ex < fx + (p - one)),
        (sy, 1, 0, ey, ex + one, ex + two),
        (~sx, 1, 0, ex - one, fx, ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-DB1-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == ey + p, ey == fy + two),
        (sx, 1, 0, ex, ey + one, ey + two),
        (~sy, 0, 0, ey - one, ey - (p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-DB1-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == ex + p, ex == fx + two),
        (sy, 1, 0, ey, ex + one, ex + two),
        (~sx, 0, 0, ex - one, ex - (p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-DB2-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == ey + p, ey == fy + (p - one)),
        (sx, 1, 0, ex, ey + one, ey + two),
        (~sy, 1, 0, ey - one, fy - one, ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-DB2-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == ex + p, ex == fx + (p - one)),
        (sy, 1, 0, ey, ex + one, ex + two),
        (~sx, 1, 0, ex - one, fx - one, ex - (p - one)),
    )

    # conjecturer/SELTZO-TwoSum-ALL1-R0R1-S.jl
    implicit_hypothesis = z3.And(xy_nonzero, same_sign)
    result["SELTZO-TwoSum-ALL1-R0R1-SE0-X"] = seltzo_lemma_zero_error(
        (x_all1, y_r0r1, ex == ey, ex < fy + (p - one)),
        (sx, 1, 1, ex + one, ex - one, fy + one),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-SE0-Y"] = seltzo_lemma_zero_error(
        (y_all1, x_r0r1, ey == ex, ey < fx + (p - one)),
        (sy, 1, 1, ey + one, ey - one, fx + one),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-SE1-X"] = seltzo_lemma_zero_error(
        (x_all1, y_r0r1, ex == ey, ex == fy + (p - one)),
        (sx, 1, 0, ex + one, ex - one, ex),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-SE1-Y"] = seltzo_lemma_zero_error(
        (y_all1, x_r0r1, ey == ex, ey == fx + (p - one)),
        (sy, 1, 0, ey + one, ey - one, ey),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S1-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex > fy + (p + one), ex < ey + (p - two), ey < fy + (p - one)),
        (sx, 0, 0, ex + one, ey, ey),
        (~sy, 1, 0, ex - p, fy, ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S1-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey > fx + (p + one), ey < ex + (p - two), ex < fx + (p - one)),
        (sy, 0, 0, ey + one, ex, ex),
        (~sx, 1, 0, ey - p, fx, ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S1A-X"] = seltzo_lemma(
        (
            x_all1,
            y_r0r1,
            ex == fy + (p + one),
            ex < ey + (p - two),
            ey < fy + (p - one),
        ),
        (sx, 0, 0, ex + one, ey, ey),
        (~sy, 0, 0, ex - p, ey - (p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S1A-Y"] = seltzo_lemma(
        (
            y_all1,
            x_r0r1,
            ey == fx + (p + one),
            ey < ex + (p - two),
            ex < fx + (p - one),
        ),
        (sy, 0, 0, ey + one, ex, ex),
        (~sx, 0, 0, ey - p, ex - (p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S1B-X"] = seltzo_lemma(
        (
            x_all1,
            y_r0r1,
            ex > fy + (p + one),
            ex == ey + (p - two),
            ey < fy + (p - one),
        ),
        (sx, 0, 1, ex + one, ey, ey + one),
        (~sy, 1, 0, ex - p, fy, ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S1B-Y"] = seltzo_lemma(
        (
            y_all1,
            x_r0r1,
            ey > fx + (p + one),
            ey == ex + (p - two),
            ex < fx + (p - one),
        ),
        (sy, 0, 1, ey + one, ex, ex + one),
        (~sx, 1, 0, ey - p, fx, ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S1C-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex > ey + one, ex < ey + (p - two), ey == fy + (p - one)),
        (sx, 0, 0, ex + one, ey, ey),
        (~sy, 1, 0, ex - p, fy - one, ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S1C-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey > ex + one, ey < ex + (p - two), ex == fx + (p - one)),
        (sy, 0, 0, ey + one, ex, ex),
        (~sx, 1, 0, ey - p, fx - one, ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S1AB-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == fy + (p + one), ex == ey + (p - two)),
        (sx, 0, 1, ex + one, ey, ey + one),
        (~sy, 0, 0, ex - p, ey - (p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S1AB-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == fx + (p + one), ey == ex + (p - two)),
        (sy, 0, 1, ey + one, ex, ex + one),
        (~sx, 0, 0, ey - p, ex - (p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S1BC-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == ey + (p - two), ey == fy + (p - one)),
        (sx, 0, 1, ex + one, ey, ey + one),
        (~sy, 1, 0, ex - p, fy - one, ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S1BC-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == ex + (p - two), ex == fx + (p - one)),
        (sy, 0, 1, ey + one, ex, ex + one),
        (~sx, 1, 0, ey - p, fx - one, ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S2-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex < fy + (p - one), ex > ey + one),
        (sx, 0, 1, ex + one, ey, fy + one),
        (sy, 1, 0, ex - p, ey - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S2-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey < fx + (p - one), ey > ex + one),
        (sy, 0, 1, ey + one, ex, fx + one),
        (sx, 1, 0, ey - p, ex - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S2A-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == fy + (p - one), ex > ey + one),
        (sx, 0, 0, ex + one, ey, ey),
        (sy, 1, 0, ex - p, ey - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S2A-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == fx + (p - one), ey > ex + one),
        (sy, 0, 0, ey + one, ex, ex),
        (sx, 1, 0, ey - p, ex - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S2B0-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == fy + p, ex > ey + one, ey > fy + two),
        (sx, 0, 0, ex + one, ey, ey),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S2B0-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == fx + p, ey > ex + one, ex > fx + two),
        (sy, 0, 0, ey + one, ex, ex),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S2B1-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == fy + p, ey == fy + two),
        (sx, 0, 1, ex + one, ey, ey + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S2B1-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == fx + p, ex == fx + two),
        (sy, 0, 1, ey + one, ex, ex + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S2C-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex < fy + (p - one), ex == ey + one),
        (sx, 0, 1, ex + one, ey, fy + one),
        (sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S2C-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey < fx + (p - one), ey == ex + one),
        (sy, 0, 1, ey + one, ex, fx + one),
        (sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S2AC-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == fy + (p - one), ex == ey + one),
        (sx, 0, 0, ex + one, ey, ey),
        (sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S2AC-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == fx + (p - one), ey == ex + one),
        (sy, 0, 0, ey + one, ex, ex),
        (sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S2BC-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == fy + p, ex == ey + one),
        (sx, 0, 0, ex + one, ey, ey),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-S2BC-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == fx + p, ey == ex + one),
        (sy, 0, 0, ey + one, ex, ex),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-SB10-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == ey + (p - one), ey < fy + (p - one)),
        (sx, 0, 0, ex + one, ey, ex + one),
        (sy, 1, 0, fy, ey - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-SB10-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == ex + (p - one), ex < fx + (p - one)),
        (sy, 0, 0, ey + one, ex, ey + one),
        (sx, 1, 0, fx, ex - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-SB11-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == ey + (p - one), ey == fy + (p - one)),
        (sx, 0, 0, ex + one, ey, ex + one),
        (sy, 0, 0, fy, fy - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-SB11-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == ex + (p - one), ex == fx + (p - one)),
        (sy, 0, 0, ey + one, ex, ey + one),
        (sx, 0, 0, fx, fx - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-SB20-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == ey + p, ey > fy + two, ey < fy + (p - one)),
        (sx, 0, 0, ex + one, ey + one, ex + one),
        (~sy, 1, 0, ey - one, fy, ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-SB20-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == ex + p, ex > fx + two, ex < fx + (p - one)),
        (sy, 0, 0, ey + one, ex + one, ey + one),
        (~sx, 1, 0, ex - one, fx, ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-SB21-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == ey + p, ey == fy + two),
        (sx, 0, 0, ex + one, ey + one, ex + one),
        (~sy, 0, 0, ey - one, ey - (p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-SB21-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == ex + p, ex == fx + two),
        (sy, 0, 0, ey + one, ex + one, ey + one),
        (~sx, 0, 0, ex - one, ex - (p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-SB22-X"] = seltzo_lemma(
        (x_all1, y_r0r1, ex == ey + p, ey == fy + (p - one)),
        (sx, 0, 0, ex + one, ey + one, ex + one),
        (~sy, 1, 0, ey - one, fy - one, ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R0R1-SB22-Y"] = seltzo_lemma(
        (y_all1, x_r0r1, ey == ex + p, ex == fx + (p - one)),
        (sy, 0, 0, ey + one, ex + one, ey + one),
        (~sx, 1, 0, ex - one, fx - one, ex - (p - one)),
    )

    # conjecturer/SELTZO-TwoSum-ALL1-R1R0-D.jl
    implicit_hypothesis = z3.And(xy_nonzero, diff_sign)
    result["SELTZO-TwoSum-ALL1-R1R0-DE0-X"] = seltzo_lemma_zero_error(
        (x_all1, y_r1r0, ex == ey, ey < fy + (p - one)),
        (sx, 1, 0, fy, ex - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-DE0-Y"] = seltzo_lemma_zero_error(
        (y_all1, x_r1r0, ey == ex, ex < fx + (p - one)),
        (sy, 1, 0, fx, ey - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-DE1-X"] = seltzo_lemma_zero_error(
        (x_all1, y_r1r0, ex == ey, ey == fy + (p - one)),
        (sx, 0, 0, fy, fy - p, fy),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-DE1-Y"] = seltzo_lemma_zero_error(
        (y_all1, x_r1r0, ey == ex, ex == fx + (p - one)),
        (sy, 0, 0, fx, fx - p, fx),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-D1-X"] = seltzo_lemma(
        (x_all1, y_r1r0, ex > fy + (p + one), ex < ey + p),
        (sx, 1, 1, ex, ey + one, ey + one),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-D1-Y"] = seltzo_lemma(
        (y_all1, x_r1r0, ey > fx + (p + one), ey < ex + p),
        (sy, 1, 1, ey, ex + one, ex + one),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-D1A-X"] = seltzo_lemma(
        (x_all1, y_r1r0, ex == fy + (p + one)),
        (sx, 1, 0, ex, ey, ey + one),
        (sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-D1A-Y"] = seltzo_lemma(
        (y_all1, x_r1r0, ey == fx + (p + one)),
        (sy, 1, 0, ey, ex, ex + one),
        (sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-D1B0-X"] = seltzo_lemma_zero_error(
        (x_all1, y_r1r0, ex == fy + p, ey < fy + (p - one)),
        (sx, 1, 0, ex, ey, ey + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-D1B0-Y"] = seltzo_lemma_zero_error(
        (y_all1, x_r1r0, ey == fx + p, ex < fx + (p - one)),
        (sy, 1, 0, ey, ex, ex + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-D1B1-X"] = seltzo_lemma_zero_error(
        (x_all1, y_r1r0, ex == fy + p, ey == fy + (p - one)),
        (sx, 0, 0, ex, ex - p, ex),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-D1B1-Y"] = seltzo_lemma_zero_error(
        (y_all1, x_r1r0, ey == fx + p, ex == fx + (p - one)),
        (sy, 0, 0, ey, ey - p, ey),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-DB-X"] = seltzo_lemma(
        (x_all1, y_r1r0, ex == ey + p),
        (sx, 1, 0, ex, ey + one, ey + two),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-DB-Y"] = seltzo_lemma(
        (y_all1, x_r1r0, ey == ex + p),
        (sy, 1, 0, ey, ex + one, ex + two),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )

    # conjecturer/SELTZO-TwoSum-ALL1-R1R0-S.jl
    implicit_hypothesis = z3.And(xy_nonzero, same_sign)
    result["SELTZO-TwoSum-ALL1-R1R0-SE0-X"] = seltzo_lemma(
        (x_all1, y_r1r0, ex == ey, ex < fy + (p - one)),
        (sx, 1, 0, ex + one, fy, fy + one),
        (~sy, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-SE0-Y"] = seltzo_lemma(
        (y_all1, x_r1r0, ey == ex, ey < fx + (p - one)),
        (sy, 1, 0, ey + one, fx, fx + one),
        (~sx, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-SE1-X"] = seltzo_lemma(
        (x_all1, y_r1r0, ex == ey, ex == fy + (p - one)),
        (sx, 1, 0, ex + one, fy + one, fy + two),
        (sy, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-SE1-Y"] = seltzo_lemma(
        (y_all1, x_r1r0, ey == ex, ey == fx + (p - one)),
        (sy, 1, 0, ey + one, fx + one, fx + two),
        (sx, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-S1-X"] = seltzo_lemma(
        (x_all1, y_r1r0, ex > fy + (p + one), ex < ey + (p - one)),
        (sx, 0, 1, ex + one, ey, ey + one),
        (sy, 1, 0, ex - p, fy, fy + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-S1-Y"] = seltzo_lemma(
        (y_all1, x_r1r0, ey > fx + (p + one), ey < ex + (p - one)),
        (sy, 0, 1, ey + one, ex, ex + one),
        (sx, 1, 0, ey - p, fx, fx + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-S1A-X"] = seltzo_lemma(
        (x_all1, y_r1r0, ex == fy + (p + one), ex < ey + (p - one)),
        (sx, 0, 1, ex + one, ey, ey + one),
        (sy, 0, 0, ex - p, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-S1A-Y"] = seltzo_lemma(
        (y_all1, x_r1r0, ey == fx + (p + one), ey < ex + (p - one)),
        (sy, 0, 1, ey + one, ex, ex + one),
        (sx, 0, 0, ey - p, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-S1B-X"] = seltzo_lemma_zero_error(
        (x_all1, y_r1r0, ex == fy + p),
        (sx, 0, 1, ex + one, ey, ey + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-S1B-Y"] = seltzo_lemma_zero_error(
        (y_all1, x_r1r0, ey == fx + p),
        (sy, 0, 1, ey + one, ex, ex + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-S2-X"] = seltzo_lemma(
        (x_all1, y_r1r0, ex < fy + (p - one), ex > ey),
        (sx, 0, 0, ex + one, ey, fy + one),
        (~sy, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-S2-Y"] = seltzo_lemma(
        (y_all1, x_r1r0, ey < fx + (p - one), ey > ex),
        (sy, 0, 0, ey + one, ex, fx + one),
        (~sx, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-S2A-X"] = seltzo_lemma(
        (x_all1, y_r1r0, ex == fy + (p - one), ex > ey),
        (sx, 0, 0, ex + one, ey, fy + two),
        (sy, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-S2A-Y"] = seltzo_lemma(
        (y_all1, x_r1r0, ey == fx + (p - one), ey > ex),
        (sy, 0, 0, ey + one, ex, fx + two),
        (sx, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-SB10-X"] = seltzo_lemma(
        (x_all1, y_r1r0, ex == ey + (p - one), ey > fy + two),
        (sx, 0, 0, ex + one, ey, ex + one),
        (sy, 1, 0, ex - p, fy, fy + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-SB10-Y"] = seltzo_lemma(
        (y_all1, x_r1r0, ey == ex + (p - one), ex > fx + two),
        (sy, 0, 0, ey + one, ex, ey + one),
        (sx, 1, 0, ey - p, fx, fx + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-SB11-X"] = seltzo_lemma(
        (x_all1, y_r1r0, ex == ey + (p - one), ey == fy + two),
        (sx, 0, 0, ex + one, ey, ex + one),
        (sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-SB11-Y"] = seltzo_lemma(
        (y_all1, x_r1r0, ey == ex + (p - one), ex == fx + two),
        (sy, 0, 0, ey + one, ex, ey + one),
        (sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-SB2-X"] = seltzo_lemma(
        (x_all1, y_r1r0, ex == ey + p),
        (sx, 0, 0, ex + one, ey + one, ex + one),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-SB2-Y"] = seltzo_lemma(
        (y_all1, x_r1r0, ey == ex + p),
        (sy, 0, 0, ey + one, ex + one, ey + one),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )

    # conjecturer/SELTZO-TwoSum-L.jl
    implicit_hypothesis = xy_nonzero
    result["SELTZO-TwoSum-LS-POW2-G-X"] = seltzo_lemma_zero_error(
        (same_sign, x_pow2, ~tby, ex > ey + one, gy > fx + one),
        (sx, 0, 0, ex, ey, gy),
    )
    result["SELTZO-TwoSum-LS-POW2-G-Y"] = seltzo_lemma_zero_error(
        (same_sign, y_pow2, ~tbx, ey > ex + one, gx > fy + one),
        (sy, 0, 0, ey, ex, gx),
    )
    result["SELTZO-TwoSum-LS-POW2-A0-X"] = seltzo_lemma_zero_error(
        (same_sign, x_pow2, ~lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 1, 0, ex, ey - one, gy),
    )
    result["SELTZO-TwoSum-LS-POW2-A0-Y"] = seltzo_lemma_zero_error(
        (same_sign, y_pow2, ~lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 1, 0, ey, ex - one, gx),
    )
    result["SELTZO-TwoSum-LS-POW2-A1-X"] = seltzo_lemma_zero_error(
        (same_sign, x_pow2, lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 1, 0, ex, fy, gy),
    )
    result["SELTZO-TwoSum-LS-POW2-A1-Y"] = seltzo_lemma_zero_error(
        (same_sign, y_pow2, lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 1, 0, ey, fx, gx),
    )
    result["SELTZO-TwoSum-LS-T0-G-X"] = seltzo_lemma_zero_error(
        (same_sign, ~lbx, ~tbx, ~x_pow2, ~tby, ex > ey + one, gy > fx + one),
        (sx, 0, 0, ex, ey, gx),
    )
    result["SELTZO-TwoSum-LS-T0-G-Y"] = seltzo_lemma_zero_error(
        (same_sign, ~lby, ~tby, ~y_pow2, ~tbx, ey > ex + one, gx > fy + one),
        (sy, 0, 0, ey, ex, gy),
    )
    result["SELTZO-TwoSum-LS-T0-A0-X"] = seltzo_lemma_zero_error(
        (same_sign, ~lbx, ~tbx, ~x_pow2, ~lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 1, 0, ex, ey - one, gx),
    )
    result["SELTZO-TwoSum-LS-T0-A0-Y"] = seltzo_lemma_zero_error(
        (same_sign, ~lby, ~tby, ~y_pow2, ~lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 1, 0, ey, ex - one, gy),
    )
    result["SELTZO-TwoSum-LS-T0-A1-X"] = seltzo_lemma_zero_error(
        (same_sign, ~lbx, ~tbx, ~x_pow2, lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 1, 0, ex, fy, gx),
    )
    result["SELTZO-TwoSum-LS-T0-A1-Y"] = seltzo_lemma_zero_error(
        (same_sign, ~lby, ~tby, ~y_pow2, lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 1, 0, ey, fx, gy),
    )
    result["SELTZO-TwoSum-LS-T1-G-X"] = seltzo_lemma_zero_error(
        (same_sign, ~lbx, tbx, ~tby, ex > ey + one, gy > fx + one),
        (sx, 0, 1, ex, ey, gx),
    )
    result["SELTZO-TwoSum-LS-T1-G-Y"] = seltzo_lemma_zero_error(
        (same_sign, ~lby, tby, ~tbx, ey > ex + one, gx > fy + one),
        (sy, 0, 1, ey, ex, gy),
    )
    result["SELTZO-TwoSum-LS-T1-A0-X"] = seltzo_lemma_zero_error(
        (same_sign, ~lbx, tbx, ~lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 1, 1, ex, ey - one, gx),
    )
    result["SELTZO-TwoSum-LS-T1-A0-Y"] = seltzo_lemma_zero_error(
        (same_sign, ~lby, tby, ~lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 1, 1, ey, ex - one, gy),
    )
    result["SELTZO-TwoSum-LS-T1-A1-X"] = seltzo_lemma_zero_error(
        (same_sign, ~lbx, tbx, lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 1, 1, ex, fy, gx),
    )
    result["SELTZO-TwoSum-LS-T1-A1-Y"] = seltzo_lemma_zero_error(
        (same_sign, ~lby, tby, lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 1, 1, ey, fx, gy),
    )
    result["SELTZO-TwoSum-LD-ALL1-G-X"] = seltzo_lemma_zero_error(
        (diff_sign, x_all1, ~tby, ex > ey + one, gy > fx + one),
        (sx, 1, 1, ex, ey, gy),
    )
    result["SELTZO-TwoSum-LD-ALL1-G-Y"] = seltzo_lemma_zero_error(
        (diff_sign, y_all1, ~tbx, ey > ex + one, gx > fy + one),
        (sy, 1, 1, ey, ex, gx),
    )
    result["SELTZO-TwoSum-LD-ALL1-A0-X"] = seltzo_lemma_zero_error(
        (diff_sign, x_all1, ~lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 0, 1, ex, ey - one, gy),
    )
    result["SELTZO-TwoSum-LD-ALL1-A0-Y"] = seltzo_lemma_zero_error(
        (diff_sign, y_all1, ~lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 0, 1, ey, ex - one, gx),
    )
    result["SELTZO-TwoSum-LD-ALL1-A1-X"] = seltzo_lemma_zero_error(
        (diff_sign, x_all1, lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 0, 1, ex, fy, gy),
    )
    result["SELTZO-TwoSum-LD-ALL1-A1-Y"] = seltzo_lemma_zero_error(
        (diff_sign, y_all1, lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 0, 1, ey, fx, gx),
    )
    result["SELTZO-TwoSum-LD-T0-G-X"] = seltzo_lemma_zero_error(
        (diff_sign, lbx, ~tbx, ~tby, ex > ey + one, gy > fx + one),
        (sx, 1, 0, ex, ey, gx),
    )
    result["SELTZO-TwoSum-LD-T0-G-Y"] = seltzo_lemma_zero_error(
        (diff_sign, lby, ~tby, ~tbx, ey > ex + one, gx > fy + one),
        (sy, 1, 0, ey, ex, gy),
    )
    result["SELTZO-TwoSum-LD-T0-A0-X"] = seltzo_lemma_zero_error(
        (diff_sign, lbx, ~tbx, ~lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 0, 0, ex, ey - one, gx),
    )
    result["SELTZO-TwoSum-LD-T0-A0-Y"] = seltzo_lemma_zero_error(
        (diff_sign, lby, ~tby, ~lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 0, 0, ey, ex - one, gy),
    )
    result["SELTZO-TwoSum-LD-T0-A1-X"] = seltzo_lemma_zero_error(
        (diff_sign, lbx, ~tbx, lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 0, 0, ex, fy, gx),
    )
    result["SELTZO-TwoSum-LD-T0-A1-Y"] = seltzo_lemma_zero_error(
        (diff_sign, lby, ~tby, lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 0, 0, ey, fx, gy),
    )
    result["SELTZO-TwoSum-LD-T1-G-X"] = seltzo_lemma_zero_error(
        (diff_sign, lbx, tbx, ~x_all1, ~tby, ex > ey + one, gy > fx + one),
        (sx, 1, 1, ex, ey, gx),
    )
    result["SELTZO-TwoSum-LD-T1-G-Y"] = seltzo_lemma_zero_error(
        (diff_sign, lby, tby, ~y_all1, ~tbx, ey > ex + one, gx > fy + one),
        (sy, 1, 1, ey, ex, gy),
    )
    result["SELTZO-TwoSum-LD-T1-A0-X"] = seltzo_lemma_zero_error(
        (diff_sign, lbx, tbx, ~x_all1, ~lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 0, 1, ex, ey - one, gx),
    )
    result["SELTZO-TwoSum-LD-T1-A0-Y"] = seltzo_lemma_zero_error(
        (diff_sign, lby, tby, ~y_all1, ~lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 0, 1, ey, ex - one, gy),
    )
    result["SELTZO-TwoSum-LD-T1-A1-X"] = seltzo_lemma_zero_error(
        (diff_sign, lbx, tbx, ~x_all1, lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 0, 1, ex, fy, gx),
    )
    result["SELTZO-TwoSum-LD-T1-A1-Y"] = seltzo_lemma_zero_error(
        (diff_sign, lby, tby, ~y_all1, lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 0, 1, ey, fx, gy),
    )

    # conjecturer/SELTZO-TwoSum-POW2-ALL1-D.jl
    implicit_hypothesis = z3.And(xy_nonzero, diff_sign)
    result["SELTZO-TwoSum-POW2-ALL1-DA1-X"] = seltzo_lemma_zero_error(
        (x_pow2, y_all1, ex == ey + one),
        (sx, 0, 0, fx, fx - p, fx),
    )
    result["SELTZO-TwoSum-POW2-ALL1-DA1-Y"] = seltzo_lemma_zero_error(
        (y_pow2, x_all1, ey == ex + one),
        (sy, 0, 0, fy, fy - p, fy),
    )
    result["SELTZO-TwoSum-POW2-ALL1-DA2-X"] = seltzo_lemma(
        (x_pow2, y_all1, ex == ey + two),
        (sx, 0, 0, ex - one, fx - one, gx - one),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-POW2-ALL1-DA2-Y"] = seltzo_lemma(
        (y_pow2, x_all1, ey == ex + two),
        (sy, 0, 0, ey - one, fy - one, gy - one),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-POW2-ALL1-DG-X"] = seltzo_lemma(
        (x_pow2, y_all1, ex > ey + two, ex < ey + (p + one)),
        (sx, 1, 0, ex - one, ey, ey + one),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-POW2-ALL1-DG-Y"] = seltzo_lemma(
        (y_pow2, x_all1, ey > ex + two, ey < ex + (p + one)),
        (sy, 1, 0, ey - one, ex, ex + one),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-POW2-ALL1-DB-X"] = seltzo_lemma(
        (x_pow2, y_all1, ex == ey + (p + one)),
        (sx, 1, 1, ex - one, ey, ex - one),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-POW2-ALL1-DB-Y"] = seltzo_lemma(
        (y_pow2, x_all1, ey == ex + (p + one)),
        (sy, 1, 1, ey - one, ex, ey - one),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )

    # conjecturer/SELTZO-TwoSum-POW2-ALL1-S.jl
    implicit_hypothesis = z3.And(xy_nonzero, same_sign)
    result["SELTZO-TwoSum-POW2-ALL1-SA1-X"] = seltzo_lemma(
        (x_pow2, y_all1, ex == ey + one),
        (sx, 0, 0, ex + one, fx + one, gx + one),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-POW2-ALL1-SA1-Y"] = seltzo_lemma(
        (y_pow2, x_all1, ey == ex + one),
        (sy, 0, 0, ey + one, fy + one, gy + one),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-POW2-ALL1-SA2-X"] = seltzo_lemma(
        (x_pow2, y_all1, ex == ey + two),
        (sx, 1, 0, ex, ey, ey + one),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-POW2-ALL1-SA2-Y"] = seltzo_lemma(
        (y_pow2, x_all1, ey == ex + two),
        (sy, 1, 0, ey, ex, ex + one),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-POW2-ALL1-SG-X"] = seltzo_lemma(
        (x_pow2, y_all1, ex > ey + two, ex < ey + p),
        (sx, 0, 0, ex, ey + one, ey + one),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-POW2-ALL1-SG-Y"] = seltzo_lemma(
        (y_pow2, x_all1, ey > ex + two, ey < ex + p),
        (sy, 0, 0, ey, ex + one, ex + one),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-POW2-ALL1-SB-X"] = seltzo_lemma(
        (x_pow2, y_all1, ex == ey + p),
        (sx, 0, 1, ex, ey + one, ey + two),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-POW2-ALL1-SB-Y"] = seltzo_lemma(
        (y_pow2, x_all1, ey == ex + p),
        (sy, 0, 1, ey, ex + one, ex + two),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )

    # conjecturer/SELTZO-TwoSum-POW2-POW2-D.jl
    implicit_hypothesis = z3.And(xy_nonzero, x_pow2, y_pow2, diff_sign)
    result["SELTZO-TwoSum-POW2-POW2-DE"] = seltzo_lemma_zero_error(
        (ex == ey,),
        0,
    )
    result["SELTZO-TwoSum-POW2-POW2-DA-X"] = seltzo_lemma_zero_error(
        (ex == ey + one,),
        (sx, 0, 0, ex - one, fx - one, gx - one),
    )
    result["SELTZO-TwoSum-POW2-POW2-DA-Y"] = seltzo_lemma_zero_error(
        (ey == ex + one,),
        (sy, 0, 0, ey - one, fy - one, gy - one),
    )
    result["SELTZO-TwoSum-POW2-POW2-DG-X"] = seltzo_lemma_zero_error(
        (ex > ey + one, ex < ey + p),
        (sx, 1, 0, ex - one, ey - one, ey),
    )
    result["SELTZO-TwoSum-POW2-POW2-DG-Y"] = seltzo_lemma_zero_error(
        (ey > ex + one, ey < ex + p),
        (sy, 1, 0, ey - one, ex - one, ex),
    )
    result["SELTZO-TwoSum-POW2-POW2-DB-X"] = seltzo_lemma_zero_error(
        (ex == ey + p,),
        (sx, 1, 1, ex - one, fx - one, gx - one),
    )
    result["SELTZO-TwoSum-POW2-POW2-DB-Y"] = seltzo_lemma_zero_error(
        (ey == ex + p,),
        (sy, 1, 1, ey - one, fy - one, gy - one),
    )

    # conjecturer/SELTZO-TwoSum-POW2-POW2-S.jl
    implicit_hypothesis = z3.And(xy_nonzero, x_pow2, y_pow2, same_sign)
    result["SELTZO-TwoSum-POW2-POW2-SE"] = seltzo_lemma_zero_error(
        (ex == ey,),
        (sx, 0, 0, ex + one, fx + one, gx + one),
    )
    result["SELTZO-TwoSum-POW2-POW2-SB-X"] = seltzo_lemma_zero_error(
        (ex == ey + (p - one),),
        (sx, 0, 1, ex, ey, ey + one),
    )
    result["SELTZO-TwoSum-POW2-POW2-SB-Y"] = seltzo_lemma_zero_error(
        (ey == ex + (p - one),),
        (sy, 0, 1, ey, ex, ex + one),
    )

    # conjecturer/SELTZO-TwoSum-POW2-R0R1-D.jl
    implicit_hypothesis = z3.And(xy_nonzero, diff_sign)
    result["SELTZO-TwoSum-POW2-R0R1-DA0-X"] = seltzo_lemma_zero_error(
        (x_pow2, y_r0r1, ex == ey + one, ey > fy + two, ey < fy + (p - one)),
        (sx, 1, 0, ey - one, fy, ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-DA0-Y"] = seltzo_lemma_zero_error(
        (y_pow2, x_r0r1, ey == ex + one, ex > fx + two, ex < fx + (p - one)),
        (sy, 1, 0, ex - one, fx, ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-DA1-X"] = seltzo_lemma_zero_error(
        (x_pow2, y_r0r1, ex == ey + one, ey == fy + two),
        (sx, 0, 0, ey - one, ey - (p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-DA1-Y"] = seltzo_lemma_zero_error(
        (y_pow2, x_r0r1, ey == ex + one, ex == fx + two),
        (sy, 0, 0, ex - one, ex - (p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-DA2-X"] = seltzo_lemma_zero_error(
        (x_pow2, y_r0r1, ex == ey + one, ey == fy + (p - one)),
        (sx, 1, 0, ey - one, fy - one, ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-DA2-Y"] = seltzo_lemma_zero_error(
        (y_pow2, x_r0r1, ey == ex + one, ex == fx + (p - one)),
        (sy, 1, 0, ex - one, fx - one, ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D1-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex > fy + (p + one), ex < ey + p, ey < fy + (p - one)),
        (sx, 1, 0, ex - one, ey - one, ey),
        (sy, 1, 0, fy, ey - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D1-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey > fx + (p + one), ey < ex + p, ex < fx + (p - one)),
        (sy, 1, 0, ey - one, ex - one, ex),
        (sx, 1, 0, fx, ex - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D1A-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex > fy + p, ex < ey + p, ey == fy + (p - one)),
        (sx, 1, 0, ex - one, ey - one, ey),
        (sy, 0, 0, fy, fy - p, fy),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D1A-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey > fx + p, ey < ex + p, ex == fx + (p - one)),
        (sy, 1, 0, ey - one, ex - one, ex),
        (sx, 0, 0, fx, fx - p, fx),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D2-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex < fy + (p + one), ex > ey + two),
        (sx, 1, 0, ex - one, ey, fy + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D2-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey < fx + (p + one), ey > ex + two),
        (sy, 1, 0, ey - one, ex, fx + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D2A-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex == fy + (p + one), ex > ey + two),
        (sx, 1, 1, ex - one, ey, ey),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D2A-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey == fx + (p + one), ey > ex + two),
        (sy, 1, 1, ey - one, ex, ex),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D2B-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex < fy + (p + one), ex == ey + two),
        (sx, 0, 0, ex - one, ey - one, fy + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D2B-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey < fx + (p + one), ey == ex + two),
        (sy, 0, 0, ey - one, ex - one, fx + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-DB10-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex == ey + p, ey < fy + (p - one)),
        (sx, 1, 1, ex - one, ey - one, ex - one),
        (sy, 1, 0, fy, ey - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-DB10-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey == ex + p, ex < fx + (p - one)),
        (sy, 1, 1, ey - one, ex - one, ey - one),
        (sx, 1, 0, fx, ex - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-DB11-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex == ey + p, ey == fy + (p - one)),
        (sx, 1, 1, ex - one, ey - one, ex - one),
        (sy, 0, 0, fy, fy - p, fy),
    )
    result["SELTZO-TwoSum-POW2-R0R1-DB11-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey == ex + p, ex == fx + (p - one)),
        (sy, 1, 1, ey - one, ex - one, ey - one),
        (sx, 0, 0, fx, fx - p, fx),
    )
    result["SELTZO-TwoSum-POW2-R0R1-DB20-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex == ey + (p + one), ey > fy + two, ey < fy + (p - one)),
        (sx, 1, 1, ex - one, ey, ex - one),
        (~sy, 1, 0, ey - one, fy, ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-DB20-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey == ex + (p + one), ex > fx + two, ex < fx + (p - one)),
        (sy, 1, 1, ey - one, ex, ey - one),
        (~sx, 1, 0, ex - one, fx, ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-DB21-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex == ey + (p + one), ey == fy + two),
        (sx, 1, 1, ex - one, ey, ex - one),
        (~sy, 0, 0, ey - one, ey - (p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-DB21-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey == ex + (p + one), ex == fx + two),
        (sy, 1, 1, ey - one, ex, ey - one),
        (~sx, 0, 0, ex - one, ex - (p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-DB22-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex == ey + (p + one), ey == fy + (p - one)),
        (sx, 1, 1, ex - one, ey, ex - one),
        (~sy, 1, 0, ey - one, fy - one, ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-DB22-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey == ex + (p + one), ex == fx + (p - one)),
        (sy, 1, 1, ey - one, ex, ey - one),
        (~sx, 1, 0, ex - one, fx - one, ex - (p - one)),
    )

    # conjecturer/SELTZO-TwoSum-POW2-R0R1-S.jl
    implicit_hypothesis = z3.And(xy_nonzero, same_sign)
    result["SELTZO-TwoSum-POW2-R0R1-SA0-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex == ey + one, ey > fy + two, ey < fy + (p - one)),
        (sx, 1, 0, ex, ey - one, fy + one),
        (~sy, 0, 0, ex - p, ex - (p + p), ex - p),
    )
    result["SELTZO-TwoSum-POW2-R0R1-SA0-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey == ex + one, ex > fx + two, ex < fx + (p - one)),
        (sy, 1, 0, ey, ex - one, fx + one),
        (~sx, 0, 0, ey - p, ey - (p + p), ey - p),
    )
    result["SELTZO-TwoSum-POW2-R0R1-SA1-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex == ey + one, ey == fy + two),
        (sx, 1, 0, ex, ey - two, fy + one),
        (~sy, 0, 0, ex - p, ex - (p + p), ex - p),
    )
    result["SELTZO-TwoSum-POW2-R0R1-SA1-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey == ex + one, ex == fx + two),
        (sy, 1, 0, ey, ex - two, fx + one),
        (~sx, 0, 0, ey - p, ey - (p + p), ey - p),
    )
    result["SELTZO-TwoSum-POW2-R0R1-SA2-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex == ey + one, ey == fy + (p - one)),
        (sx, 1, 0, ex, ey - one, ey),
        (sy, 0, 0, ex - p, ex - (p + p), ex - p),
    )
    result["SELTZO-TwoSum-POW2-R0R1-SA2-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey == ex + one, ex == fx + (p - one)),
        (sy, 1, 0, ey, ex - one, ex),
        (sx, 0, 0, ey - p, ey - (p + p), ey - p),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S1-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex > fy + p, ex < ey + (p - one), ey < fy + (p - one)),
        (sx, 0, 0, ex, ey, ey),
        (sy, 1, 0, fy, ey - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S1-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey > fx + p, ey < ex + (p - one), ex < fx + (p - one)),
        (sy, 0, 0, ey, ex, ex),
        (sx, 1, 0, fx, ex - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S1A-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex > ey + one, ex < ey + (p - one), ey == fy + (p - one)),
        (sx, 0, 0, ex, ey, ey),
        (sy, 0, 0, fy, fy - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S1A-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey > ex + one, ey < ex + (p - one), ex == fx + (p - one)),
        (sy, 0, 0, ey, ex, ex),
        (sx, 0, 0, fx, fx - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S2-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex < fy + p, ex > ey + one),
        (sx, 0, 0, ex, ey, fy + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S2-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey < fx + p, ey > ex + one),
        (sy, 0, 0, ey, ex, fx + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S2A0-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex == fy + p, ex > ey + one, ey > fy + two),
        (sx, 0, 1, ex, ey, fy + two),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S2A0-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey == fx + p, ey > ex + one, ex > fx + two),
        (sy, 0, 1, ey, ex, fx + two),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S2A1-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex == fy + p, ey == fy + two),
        (sx, 0, 1, ex, ey, fy + three),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S2A1-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey == fx + p, ex == fx + two),
        (sy, 0, 1, ey, ex, fx + three),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-SB10-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex == ey + (p - one), ey < fy + (p - one)),
        (sx, 0, 1, ex, ey, ey + one),
        (sy, 1, 0, fy, ey - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-SB10-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey == ex + (p - one), ex < fx + (p - one)),
        (sy, 0, 1, ey, ex, ex + one),
        (sx, 1, 0, fx, ex - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-SB11-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex == ey + (p - one), ey == fy + (p - one)),
        (sx, 0, 1, ex, ey, ey + one),
        (sy, 0, 0, fy, fy - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-SB11-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey == ex + (p - one), ex == fx + (p - one)),
        (sy, 0, 1, ey, ex, ex + one),
        (sx, 0, 0, fx, fx - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-SB20-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex == ey + p, ey > fy + two, ey < fy + (p - one)),
        (sx, 0, 1, ex, ey + one, ey + two),
        (~sy, 1, 0, ey - one, fy, ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-SB20-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey == ex + p, ex > fx + two, ex < fx + (p - one)),
        (sy, 0, 1, ey, ex + one, ex + two),
        (~sx, 1, 0, ex - one, fx, ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-SB21-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex == ey + p, ey == fy + two),
        (sx, 0, 1, ex, ey + one, ey + two),
        (~sy, 0, 0, ey - one, ey - (p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-SB21-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey == ex + p, ex == fx + two),
        (sy, 0, 1, ey, ex + one, ex + two),
        (~sx, 0, 0, ex - one, ex - (p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-SB22-X"] = seltzo_lemma(
        (x_pow2, y_r0r1, ex == ey + p, ey == fy + (p - one)),
        (sx, 0, 1, ex, ey + one, ey + two),
        (~sy, 1, 0, ey - one, fy - one, ey - (p - one)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-SB22-Y"] = seltzo_lemma(
        (y_pow2, x_r0r1, ey == ex + p, ex == fx + (p - one)),
        (sy, 0, 1, ey, ex + one, ex + two),
        (~sx, 1, 0, ex - one, fx - one, ex - (p - one)),
    )

    # conjecturer/SELTZO-TwoSum-POW2-R1R0-D.jl
    implicit_hypothesis = z3.And(xy_nonzero, diff_sign)
    result["SELTZO-TwoSum-POW2-R1R0-DA1-X"] = seltzo_lemma_zero_error(
        (x_pow2, y_r1r0, ex == ey + one),
        (sx, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-DA1-Y"] = seltzo_lemma_zero_error(
        (y_pow2, x_r1r0, ey == ex + one),
        (sy, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-DA20-X"] = seltzo_lemma_zero_error(
        (x_pow2, y_r1r0, ex == ey + two, ex < fy + (p + one)),
        (sx, 0, 0, ex - one, fy + one, fy + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-DA20-Y"] = seltzo_lemma_zero_error(
        (y_pow2, x_r1r0, ey == ex + two, ey < fx + (p + one)),
        (sy, 0, 0, ey - one, fx + one, fx + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-DA21-X"] = seltzo_lemma_zero_error(
        (x_pow2, y_r1r0, ex == ey + two, ex == fy + (p + one)),
        (sx, 0, 1, ex - one, fy + one, fy + two),
    )
    result["SELTZO-TwoSum-POW2-R1R0-DA21-Y"] = seltzo_lemma_zero_error(
        (y_pow2, x_r1r0, ey == ex + two, ey == fx + (p + one)),
        (sy, 0, 1, ey - one, fx + one, fx + two),
    )
    result["SELTZO-TwoSum-POW2-R1R0-D1-X"] = seltzo_lemma(
        (x_pow2, y_r1r0, ex > fy + (p + one), ex < ey + (p + one)),
        (sx, 1, 0, ex - one, ey, ey + one),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-D1-Y"] = seltzo_lemma(
        (y_pow2, x_r1r0, ey > fx + (p + one), ey < ex + (p + one)),
        (sy, 1, 0, ey - one, ex, ex + one),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-D2-X"] = seltzo_lemma_zero_error(
        (x_pow2, y_r1r0, ex < fy + (p + one), ex > ey + two),
        (sx, 1, 0, ex - one, ey, fy + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-D2-Y"] = seltzo_lemma_zero_error(
        (y_pow2, x_r1r0, ey < fx + (p + one), ey > ex + two),
        (sy, 1, 0, ey - one, ex, fx + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-D2A-X"] = seltzo_lemma_zero_error(
        (x_pow2, y_r1r0, ex == fy + (p + one), ex > ey + two),
        (sx, 1, 1, ex - one, ey, fy + two),
    )
    result["SELTZO-TwoSum-POW2-R1R0-D2A-Y"] = seltzo_lemma_zero_error(
        (y_pow2, x_r1r0, ey == fx + (p + one), ey > ex + two),
        (sy, 1, 1, ey - one, ex, fx + two),
    )
    result["SELTZO-TwoSum-POW2-R1R0-DB-X"] = seltzo_lemma(
        (x_pow2, y_r1r0, ex == ey + (p + one)),
        (sx, 1, 1, ex - one, ey, ey + p),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-DB-Y"] = seltzo_lemma(
        (y_pow2, x_r1r0, ey == ex + (p + one)),
        (sy, 1, 1, ey - one, ex, ex + p),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )

    # conjecturer/SELTZO-TwoSum-POW2-R1R0-S.jl
    implicit_hypothesis = z3.And(xy_nonzero, same_sign)
    result["SELTZO-TwoSum-POW2-R1R0-S1-X"] = seltzo_lemma(
        (x_pow2, y_r1r0, ex > fy + p, ex > ey + two, ex < ey + p),
        (sx, 0, 0, ex, ey + one, ey + one),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-S1-Y"] = seltzo_lemma(
        (y_pow2, x_r1r0, ey > fx + p, ey > ex + two, ey < ex + p),
        (sy, 0, 0, ey, ex + one, ex + one),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-S1A0-X"] = seltzo_lemma_zero_error(
        (x_pow2, y_r1r0, ex == fy + p, ex > ey + one),
        (sx, 0, 1, ex, ey, ey + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-S1A0-Y"] = seltzo_lemma_zero_error(
        (y_pow2, x_r1r0, ey == fx + p, ey > ex + one),
        (sy, 0, 1, ey, ex, ex + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-S1A1-X"] = seltzo_lemma_zero_error(
        (x_pow2, y_r1r0, ex == fy + p, ex == ey + one),
        (sx, 1, 1, ex, fy, ey + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-S1A1-Y"] = seltzo_lemma_zero_error(
        (y_pow2, x_r1r0, ey == fx + p, ey == ex + one),
        (sy, 1, 1, ey, fx, ex + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-S1B-X"] = seltzo_lemma(
        (x_pow2, y_r1r0, ex == fy + (p + one), ex == ey + two),
        (sx, 1, 0, ex, ey, ey + one),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-S1B-Y"] = seltzo_lemma(
        (y_pow2, x_r1r0, ey == fx + (p + one), ey == ex + two),
        (sy, 1, 0, ey, ex, ex + one),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-SB-X"] = seltzo_lemma(
        (x_pow2, y_r1r0, ex == ey + p),
        (sx, 0, 1, ex, ey + one, ey + two),
        (~sy, 0, 0, fy + one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-POW2-R1R0-SB-Y"] = seltzo_lemma(
        (y_pow2, x_r1r0, ey == ex + p),
        (sy, 0, 1, ey, ex + one, ex + two),
        (~sx, 0, 0, fx + one, fx - (p - one), fx + one),
    )

    # conjecturer/SELTZO-TwoSum-R0R1-ALL1-D.jl
    implicit_hypothesis = z3.And(xy_nonzero, diff_sign)
    result["SELTZO-TwoSum-R0R1-ALL1-DA1-X"] = seltzo_lemma_zero_error(
        (x_r0r1, y_all1, ex == ey + one),
        (sx, 1, 0, fx, ex - (p + one), ex - p),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-DA1-Y"] = seltzo_lemma_zero_error(
        (y_r0r1, x_all1, ey == ex + one),
        (sy, 1, 0, fy, ey - (p + one), ey - p),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-DA2-X"] = seltzo_lemma(
        (x_r0r1, y_all1, ex == ey + two, ex > fx + two),
        (sx, 0, 0, ex - one, fx, ex - (p - one)),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-DA2-Y"] = seltzo_lemma(
        (y_r0r1, x_all1, ey == ex + two, ey > fy + two),
        (sy, 0, 0, ey - one, fy, ey - (p - one)),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-D1-X"] = seltzo_lemma(
        (x_r0r1, y_all1, fx > ey + one, ex < ey + p),
        (sx, 0, 1, ex, fx, ey + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-D1-Y"] = seltzo_lemma(
        (y_r0r1, x_all1, fy > ex + one, ey < ex + p),
        (sy, 0, 1, ey, fy, ex + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-D1A-X"] = seltzo_lemma(
        (x_r0r1, y_all1, fx == ey + one, ex < ey + p),
        (sx, 0, 1, ex, fx - one, ey + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-D1A-Y"] = seltzo_lemma(
        (y_r0r1, x_all1, fy == ex + one, ey < ex + p),
        (sy, 0, 1, ey, fy - one, ex + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-D1B-X"] = seltzo_lemma(
        (x_r0r1, y_all1, fx > ey + one, ex == ey + p),
        (sx, 0, 0, ex, fx, ey + two),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-D1B-Y"] = seltzo_lemma(
        (y_r0r1, x_all1, fy > ex + one, ey == ex + p),
        (sy, 0, 0, ey, fy, ex + two),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-D1AB-X"] = seltzo_lemma(
        (x_r0r1, y_all1, fx == ey + one, ex == ey + p),
        (sx, 0, 0, ex, ex - p, ex),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-D1AB-Y"] = seltzo_lemma(
        (y_r0r1, x_all1, fy == ex + one, ey == ex + p),
        (sy, 0, 0, ey, ey - p, ey),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-D2-X"] = seltzo_lemma(
        (x_r0r1, y_all1, fx < ey, ex > ey + two),
        (sx, 1, 0, ex - one, ey, ex - (p - one)),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-D2-Y"] = seltzo_lemma(
        (y_r0r1, x_all1, fy < ex, ey > ex + two),
        (sy, 1, 0, ey - one, ex, ey - (p - one)),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-D2A-X"] = seltzo_lemma(
        (x_r0r1, y_all1, fx == ey),
        (sx, 1, 0, ex - one, ex - p, ex - (p - one)),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-D2A-Y"] = seltzo_lemma(
        (y_r0r1, x_all1, fy == ex),
        (sy, 1, 0, ey - one, ey - p, ey - (p - one)),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )

    # conjecturer/SELTZO-TwoSum-R0R1-ALL1-S.jl
    implicit_hypothesis = z3.And(xy_nonzero, same_sign)
    result["SELTZO-TwoSum-R0R1-ALL1-SA10-X"] = seltzo_lemma(
        (x_r0r1, y_all1, ex == ey + one, ex < fx + (p - one)),
        (sx, 0, 1, ex + one, fx, fx + one),
        (sy, 0, 0, ex - p, ex - (p + p), ex - p),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-SA10-Y"] = seltzo_lemma(
        (y_r0r1, x_all1, ey == ex + one, ey < fy + (p - one)),
        (sy, 0, 1, ey + one, fy, fy + one),
        (sx, 0, 0, ey - p, ey - (p + p), ey - p),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-SA11-X"] = seltzo_lemma(
        (x_r0r1, y_all1, ex == ey + one, ex == fx + (p - one)),
        (sx, 0, 0, ex + one, fx, fx + p),
        (sy, 0, 0, ex - p, ex - (p + p), ex - p),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-SA11-Y"] = seltzo_lemma(
        (y_r0r1, x_all1, ey == ex + one, ey == fy + (p - one)),
        (sy, 0, 0, ey + one, fy, fy + p),
        (sx, 0, 0, ey - p, ey - (p + p), ey - p),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-SA20-X"] = seltzo_lemma(
        (x_r0r1, y_all1, ex == ey + two, ex > fx + two),
        (sx, 1, 1, ex, ey, fx + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-SA20-Y"] = seltzo_lemma(
        (y_r0r1, x_all1, ey == ex + two, ey > fy + two),
        (sy, 1, 1, ey, ex, fy + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-SA21-X"] = seltzo_lemma(
        (x_r0r1, y_all1, ex == ey + two, ex == fx + two),
        (sx, 1, 1, ex, ex - p, ex),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-SA21-Y"] = seltzo_lemma(
        (y_r0r1, x_all1, ey == ex + two, ey == fy + two),
        (sy, 1, 1, ey, ey - p, ey),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-S1-X"] = seltzo_lemma(
        (x_r0r1, y_all1, fx > ey, ex < ey + p, ex > fx + two),
        (sx, 0, 1, ex, fx + one, ey + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-S1-Y"] = seltzo_lemma(
        (y_r0r1, x_all1, fy > ex, ey < ex + p, ey > fy + two),
        (sy, 0, 1, ey, fy + one, ex + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-S1A-X"] = seltzo_lemma(
        (x_r0r1, y_all1, ex == ey + p, ex > fx + two),
        (sx, 0, 0, ex, fx + one, fx + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-S1A-Y"] = seltzo_lemma(
        (y_r0r1, x_all1, ey == ex + p, ey > fy + two),
        (sy, 0, 0, ey, fy + one, fy + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-S1B-X"] = seltzo_lemma(
        (x_r0r1, y_all1, fx > ey, ex < ey + p, ex == fx + two),
        (sx, 1, 1, ex, fx, ey + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-S1B-Y"] = seltzo_lemma(
        (y_r0r1, x_all1, fy > ex, ey < ex + p, ey == fy + two),
        (sy, 1, 1, ey, fy, ex + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-S1AB-X"] = seltzo_lemma(
        (x_r0r1, y_all1, ex == ey + p, ex == fx + two),
        (sx, 1, 0, ex, fx, fx + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-S1AB-Y"] = seltzo_lemma(
        (y_r0r1, x_all1, ey == ex + p, ey == fy + two),
        (sy, 1, 0, ey, fy, fy + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-S2-X"] = seltzo_lemma(
        (x_r0r1, y_all1, fx < ey, ex > ey + two),
        (sx, 0, 1, ex, ey + one, fx + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-S2-Y"] = seltzo_lemma(
        (y_r0r1, x_all1, fy < ex, ey > ex + two),
        (sy, 0, 1, ey, ex + one, fy + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-S2A-X"] = seltzo_lemma(
        (x_r0r1, y_all1, fx == ey, ex > ey + two),
        (sx, 0, 1, ex, ey + one, fx + two),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-ALL1-S2A-Y"] = seltzo_lemma(
        (y_r0r1, x_all1, fy == ex, ey > ex + two),
        (sy, 0, 1, ey, ex + one, fy + two),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )

    # conjecturer/SELTZO-TwoSum-R0R1-POW2-D.jl
    implicit_hypothesis = z3.And(xy_nonzero, diff_sign)
    result["SELTZO-TwoSum-R0R1-POW2-DE0-X"] = seltzo_lemma_zero_error(
        (x_r0r1, y_pow2, ex == ey, ex < fx + (p - one)),
        (sx, 1, 0, fx, ex - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-POW2-DE0-Y"] = seltzo_lemma_zero_error(
        (y_r0r1, x_pow2, ey == ex, ey < fy + (p - one)),
        (sy, 1, 0, fy, ey - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-POW2-DE1-X"] = seltzo_lemma_zero_error(
        (x_r0r1, y_pow2, ex == ey, ex == fx + (p - one)),
        (sx, 0, 0, fx, fx - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-POW2-DE1-Y"] = seltzo_lemma_zero_error(
        (y_r0r1, x_pow2, ey == ex, ey == fy + (p - one)),
        (sy, 0, 0, fy, fy - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-POW2-D1-X"] = seltzo_lemma_zero_error(
        (x_r0r1, y_pow2, fx + one < ey, ex > ey + one),
        (sx, 1, 0, ex - one, ey - one, ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-POW2-D1-Y"] = seltzo_lemma_zero_error(
        (y_r0r1, x_pow2, fy + one < ex, ey > ex + one),
        (sy, 1, 0, ey - one, ex - one, ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-POW2-D1A-X"] = seltzo_lemma_zero_error(
        (x_r0r1, y_pow2, fx + one == ey),
        (sx, 1, 0, ex - one, ex - p, ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-POW2-D1A-Y"] = seltzo_lemma_zero_error(
        (y_r0r1, x_pow2, fy + one == ex),
        (sy, 1, 0, ey - one, ey - p, ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-POW2-D1B0-X"] = seltzo_lemma_zero_error(
        (x_r0r1, y_pow2, fx == ey, ex < fx + (p - one)),
        (sx, 0, 1, ex, ey - one, ey),
    )
    result["SELTZO-TwoSum-R0R1-POW2-D1B0-Y"] = seltzo_lemma_zero_error(
        (y_r0r1, x_pow2, fy == ex, ey < fy + (p - one)),
        (sy, 0, 1, ey, ex - one, ex),
    )
    result["SELTZO-TwoSum-R0R1-POW2-D1B1-X"] = seltzo_lemma_zero_error(
        (x_r0r1, y_pow2, fx == ey, ex == fx + (p - one)),
        (sx, 0, 0, ex, ey - one, ex),
    )
    result["SELTZO-TwoSum-R0R1-POW2-D1B1-Y"] = seltzo_lemma_zero_error(
        (y_r0r1, x_pow2, fy == ex, ey == fy + (p - one)),
        (sy, 0, 0, ey, ex - one, ey),
    )
    result["SELTZO-TwoSum-R0R1-POW2-D1C-X"] = seltzo_lemma_zero_error(
        (x_r0r1, y_pow2, fx + one < ey, ex == ey + one),
        (sx, 0, 0, ex - one, fx, ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-POW2-D1C-Y"] = seltzo_lemma_zero_error(
        (y_r0r1, x_pow2, fy + one < ex, ey == ex + one),
        (sy, 0, 0, ey - one, fy, ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-POW2-DB1-X"] = seltzo_lemma_zero_error(
        (x_r0r1, y_pow2, ex == ey + (p - one), ex < fx + (p - one)),
        (sx, 0, 0, ex, fx, ey + one),
    )
    result["SELTZO-TwoSum-R0R1-POW2-DB1-Y"] = seltzo_lemma_zero_error(
        (y_r0r1, x_pow2, ey == ex + (p - one), ey < fy + (p - one)),
        (sy, 0, 0, ey, fy, ex + one),
    )
    result["SELTZO-TwoSum-R0R1-POW2-DB20-X"] = seltzo_lemma(
        (x_r0r1, y_pow2, ex == ey + p, ex < fx + (p - one)),
        (sx, 0, 0, ex, fx, ey + two),
        (~sy, 0, 0, ey, ey - p, ey),
    )
    result["SELTZO-TwoSum-R0R1-POW2-DB20-Y"] = seltzo_lemma(
        (y_r0r1, x_pow2, ey == ex + p, ey < fy + (p - one)),
        (sy, 0, 0, ey, fy, ex + two),
        (~sx, 0, 0, ex, ex - p, ex),
    )
    result["SELTZO-TwoSum-R0R1-POW2-DB21-X"] = seltzo_lemma(
        (x_r0r1, y_pow2, ex == ey + p, ex == fx + (p - one)),
        (sx, 0, 0, ex, ex - p, ex),
        (~sy, 0, 0, ey, ey - p, ey),
    )
    result["SELTZO-TwoSum-R0R1-POW2-DB21-Y"] = seltzo_lemma(
        (y_r0r1, x_pow2, ey == ex + p, ey == fy + (p - one)),
        (sy, 0, 0, ey, ey - p, ey),
        (~sx, 0, 0, ex, ex - p, ex),
    )

    # conjecturer/SELTZO-TwoSum-R0R1-POW2-S.jl
    implicit_hypothesis = z3.And(xy_nonzero, same_sign)
    result["SELTZO-TwoSum-R0R1-POW2-SE0-X"] = seltzo_lemma(
        (x_r0r1, y_pow2, ex == ey, ex < fx + (p - one)),
        (sx, 0, 0, ex + one, fx + one, fx + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-POW2-SE0-Y"] = seltzo_lemma(
        (y_r0r1, x_pow2, ey == ex, ey < fy + (p - one)),
        (sy, 0, 0, ey + one, fy + one, fy + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-POW2-SE1-X"] = seltzo_lemma(
        (x_r0r1, y_pow2, ex == ey, ex == fx + (p - one)),
        (sx, 0, 0, ex + one, fx, ex + one),
        (sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-POW2-SE1-Y"] = seltzo_lemma(
        (y_r0r1, x_pow2, ey == ex, ey == fy + (p - one)),
        (sy, 0, 0, ey + one, fy, ey + one),
        (sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R0R1-POW2-S1-X"] = seltzo_lemma_zero_error(
        (x_r0r1, y_pow2, fx + one > ey, ex < ey + (p - one), ex > fx + two),
        (sx, 0, 1, ex, fx + one, ey),
    )
    result["SELTZO-TwoSum-R0R1-POW2-S1-Y"] = seltzo_lemma_zero_error(
        (y_r0r1, x_pow2, fy + one > ex, ey < ex + (p - one), ey > fy + two),
        (sy, 0, 1, ey, fy + one, ex),
    )
    result["SELTZO-TwoSum-R0R1-POW2-S1A-X"] = seltzo_lemma_zero_error(
        (x_r0r1, y_pow2, fx + one == ey, ex > fx + two),
        (sx, 0, 1, ex, fx + one, ey + one),
    )
    result["SELTZO-TwoSum-R0R1-POW2-S1A-Y"] = seltzo_lemma_zero_error(
        (y_r0r1, x_pow2, fy + one == ex, ey > fy + two),
        (sy, 0, 1, ey, fy + one, ex + one),
    )
    result["SELTZO-TwoSum-R0R1-POW2-S1B-X"] = seltzo_lemma_zero_error(
        (x_r0r1, y_pow2, fx + one > ey, ex < ey + (p - one), ex == fx + two),
        (sx, 1, 1, ex, fx, ey),
    )
    result["SELTZO-TwoSum-R0R1-POW2-S1B-Y"] = seltzo_lemma_zero_error(
        (y_r0r1, x_pow2, fy + one > ex, ey < ex + (p - one), ey == fy + two),
        (sy, 1, 1, ey, fy, ex),
    )
    result["SELTZO-TwoSum-R0R1-POW2-S1AB-X"] = seltzo_lemma_zero_error(
        (x_r0r1, y_pow2, fx + one == ey, ex == fx + two),
        (sx, 1, 1, ex, ex - p, ex),
    )
    result["SELTZO-TwoSum-R0R1-POW2-S1AB-Y"] = seltzo_lemma_zero_error(
        (y_r0r1, x_pow2, fy + one == ex, ey == fy + two),
        (sy, 1, 1, ey, ey - p, ey),
    )
    result["SELTZO-TwoSum-R0R1-POW2-SB10-X"] = seltzo_lemma_zero_error(
        (x_r0r1, y_pow2, ex == ey + (p - one), ex > fx + two),
        (sx, 0, 0, ex, fx + one, fx + one),
    )
    result["SELTZO-TwoSum-R0R1-POW2-SB10-Y"] = seltzo_lemma_zero_error(
        (y_r0r1, x_pow2, ey == ex + (p - one), ey > fy + two),
        (sy, 0, 0, ey, fy + one, fy + one),
    )
    result["SELTZO-TwoSum-R0R1-POW2-SB11-X"] = seltzo_lemma_zero_error(
        (x_r0r1, y_pow2, ex == ey + (p - one), ex == fx + two),
        (sx, 1, 0, ex, fx, fx + one),
    )
    result["SELTZO-TwoSum-R0R1-POW2-SB11-Y"] = seltzo_lemma_zero_error(
        (y_r0r1, x_pow2, ey == ex + (p - one), ey == fy + two),
        (sy, 1, 0, ey, fy, fy + one),
    )
    result["SELTZO-TwoSum-R0R1-POW2-SB20-X"] = seltzo_lemma(
        (x_r0r1, y_pow2, ex == ey + p, ex > fx + two),
        (sx, 0, 0, ex, fx + one, fx + one),
        (~sy, 0, 0, ey, ey - p, ey),
    )
    result["SELTZO-TwoSum-R0R1-POW2-SB20-Y"] = seltzo_lemma(
        (y_r0r1, x_pow2, ey == ex + p, ey > fy + two),
        (sy, 0, 0, ey, fy + one, fy + one),
        (~sx, 0, 0, ex, ex - p, ex),
    )
    result["SELTZO-TwoSum-R0R1-POW2-SB21-X"] = seltzo_lemma(
        (x_r0r1, y_pow2, ex == ey + p, ex == fx + two),
        (sx, 1, 0, ex, fx, fx + one),
        (~sy, 0, 0, ey, ey - p, ey),
    )
    result["SELTZO-TwoSum-R0R1-POW2-SB21-Y"] = seltzo_lemma(
        (y_r0r1, x_pow2, ey == ex + p, ey == fy + two),
        (sy, 1, 0, ey, fy, fy + one),
        (~sx, 0, 0, ex, ex - p, ex),
    )

    # conjecturer/SELTZO-TwoSum-R1R0-ALL1-D.jl
    implicit_hypothesis = z3.And(xy_nonzero, diff_sign)
    result["SELTZO-TwoSum-R1R0-ALL1-DA10-X"] = seltzo_lemma_zero_error(
        (x_r1r0, y_all1, ex == ey + one, ex > fx + two),
        (sx, 1, 1, ey, fx, ey - (p - two)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-DA10-Y"] = seltzo_lemma_zero_error(
        (y_r1r0, x_all1, ey == ex + one, ey > fy + two),
        (sy, 1, 1, ex, fy, ex - (p - two)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-DA11-X"] = seltzo_lemma_zero_error(
        (x_r1r0, y_all1, ex == ey + one, ex == fx + two),
        (sx, 0, 1, ey, ey - (p - one), ey - (p - two)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-DA11-Y"] = seltzo_lemma_zero_error(
        (y_r1r0, x_all1, ey == ex + one, ey == fy + two),
        (sy, 0, 1, ex, ex - (p - one), ex - (p - two)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-DA20-X"] = seltzo_lemma(
        (x_r1r0, y_all1, ex == ey + two, ex > fx + two),
        (sx, 0, 0, ex, ey, fx + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-DA20-Y"] = seltzo_lemma(
        (y_r1r0, x_all1, ey == ex + two, ey > fy + two),
        (sy, 0, 0, ey, ex, fy + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-DA21-X"] = seltzo_lemma(
        (x_r1r0, y_all1, ex == ey + two, ex == fx + two),
        (sx, 0, 0, ex, ex - p, ex),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-DA21-Y"] = seltzo_lemma(
        (y_r1r0, x_all1, ey == ex + two, ey == fy + two),
        (sy, 0, 0, ey, ey - p, ey),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-D1-X"] = seltzo_lemma(
        (x_r1r0, y_all1, fx > ey, ex < ey + p, ex > fx + two),
        (sx, 1, 0, ex, fx + one, ey + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-D1-Y"] = seltzo_lemma(
        (y_r1r0, x_all1, fy > ex, ey < ex + p, ey > fy + two),
        (sy, 1, 0, ey, fy + one, ex + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-D1A-X"] = seltzo_lemma(
        (x_r1r0, y_all1, fx > ey, ex < ey + p, ex == fx + two),
        (sx, 0, 0, ex, fx, ey + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-D1A-Y"] = seltzo_lemma(
        (y_r1r0, x_all1, fy > ex, ey < ex + p, ey == fy + two),
        (sy, 0, 0, ey, fy, ex + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-D2-X"] = seltzo_lemma(
        (x_r1r0, y_all1, fx < ey, ex > ey + two),
        (sx, 1, 0, ex, ey + one, fx + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-D2-Y"] = seltzo_lemma(
        (y_r1r0, x_all1, fy < ex, ey > ex + two),
        (sy, 1, 0, ey, ex + one, fy + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-D2A-X"] = seltzo_lemma(
        (x_r1r0, y_all1, fx == ey, ex > ey + two),
        (sx, 1, 0, ex, ey + one, fx + two),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-D2A-Y"] = seltzo_lemma(
        (y_r1r0, x_all1, fy == ex, ey > ex + two),
        (sy, 1, 0, ey, ex + one, fy + two),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-DB0-X"] = seltzo_lemma(
        (x_r1r0, y_all1, ex == ey + p, ex > fx + two),
        (sx, 1, 1, ex, fx + one, fx + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-DB0-Y"] = seltzo_lemma(
        (y_r1r0, x_all1, ey == ex + p, ey > fy + two),
        (sy, 1, 1, ey, fy + one, fy + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-DB1-X"] = seltzo_lemma(
        (x_r1r0, y_all1, ex == ey + p, ex == fx + two),
        (sx, 0, 1, ex, fx, fx + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-DB1-Y"] = seltzo_lemma(
        (y_r1r0, x_all1, ey == ex + p, ey == fy + two),
        (sy, 0, 1, ey, fy, fy + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )

    # conjecturer/SELTZO-TwoSum-R1R0-ALL1-S.jl
    implicit_hypothesis = z3.And(xy_nonzero, same_sign)
    result["SELTZO-TwoSum-R1R0-ALL1-S1-X"] = seltzo_lemma(
        (x_r1r0, y_all1, fx > ey + one, ex < ey + p),
        (sx, 1, 0, ex, fx, ey + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-S1-Y"] = seltzo_lemma(
        (y_r1r0, x_all1, fy > ex + one, ey < ex + p),
        (sy, 1, 0, ey, fy, ex + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-S1A-X"] = seltzo_lemma(
        (x_r1r0, y_all1, fx == ey + one, ex < ey + p),
        (sx, 1, 0, ex, fx - one, ey + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-S1A-Y"] = seltzo_lemma(
        (y_r1r0, x_all1, fy == ex + one, ey < ex + p),
        (sy, 1, 0, ey, fy - one, ex + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-S1B-X"] = seltzo_lemma(
        (x_r1r0, y_all1, fx > ey + one, ex == ey + p),
        (sx, 1, 1, ex, fx, ey + two),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-S1B-Y"] = seltzo_lemma(
        (y_r1r0, x_all1, fy > ex + one, ey == ex + p),
        (sy, 1, 1, ey, fy, ex + two),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-S1AB-X"] = seltzo_lemma(
        (x_r1r0, y_all1, fx == ey + one, ex == ey + p),
        (sx, 1, 1, ex, fx - one, ex),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-S1AB-Y"] = seltzo_lemma(
        (y_r1r0, x_all1, fy == ex + one, ey == ex + p),
        (sy, 1, 1, ey, fy - one, ey),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-S2-X"] = seltzo_lemma(
        (x_r1r0, y_all1, fx < ey, ex > ey, ex < fx + (p - one)),
        (sx, 0, 0, ex + one, ey, fx + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-S2-Y"] = seltzo_lemma(
        (y_r1r0, x_all1, fy < ex, ey > ex, ey < fy + (p - one)),
        (sy, 0, 0, ey + one, ex, fy + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-S2A-X"] = seltzo_lemma(
        (x_r1r0, y_all1, fx == ey),
        (sx, 0, 0, ex + one, ex - (p - one), ex + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-S2A-Y"] = seltzo_lemma(
        (y_r1r0, x_all1, fy == ex),
        (sy, 0, 0, ey + one, ey - (p - one), ey + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-S2B-X"] = seltzo_lemma(
        (x_r1r0, y_all1, fx < ey, ex > ey, ex == fx + (p - one)),
        (sx, 0, 1, ex + one, ey, ey + one),
        (~sy, 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-S2B-Y"] = seltzo_lemma(
        (y_r1r0, x_all1, fy < ex, ey > ex, ey == fy + (p - one)),
        (sy, 0, 1, ey + one, ex, ex + one),
        (~sx, 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
    )

    # conjecturer/SELTZO-TwoSum-R1R0-POW2-D.jl
    implicit_hypothesis = z3.And(xy_nonzero, diff_sign)
    result["SELTZO-TwoSum-R1R0-POW2-DE0-X"] = seltzo_lemma_zero_error(
        (x_r1r0, y_pow2, ex == ey, ex > fx + two),
        (sx, 1, 0, ex - one, fx, fx + one),
    )
    result["SELTZO-TwoSum-R1R0-POW2-DE0-Y"] = seltzo_lemma_zero_error(
        (y_r1r0, x_pow2, ey == ex, ey > fy + two),
        (sy, 1, 0, ey - one, fy, fy + one),
    )
    result["SELTZO-TwoSum-R1R0-POW2-DE1-X"] = seltzo_lemma_zero_error(
        (x_r1r0, y_pow2, ex == ey, ex == fx + two),
        (sx, 0, 0, ex - one, fx - (p - one), fx + one),
    )
    result["SELTZO-TwoSum-R1R0-POW2-DE1-Y"] = seltzo_lemma_zero_error(
        (y_r1r0, x_pow2, ey == ex, ey == fy + two),
        (sy, 0, 0, ey - one, fy - (p - one), fy + one),
    )
    result["SELTZO-TwoSum-R1R0-POW2-D1-X"] = seltzo_lemma_zero_error(
        (x_r1r0, y_pow2, fx + one > ey, ex < ey + (p - one), ex > fx + two),
        (sx, 1, 0, ex, fx + one, ey),
    )
    result["SELTZO-TwoSum-R1R0-POW2-D1-Y"] = seltzo_lemma_zero_error(
        (y_r1r0, x_pow2, fy + one > ex, ey < ex + (p - one), ey > fy + two),
        (sy, 1, 0, ey, fy + one, ex),
    )
    result["SELTZO-TwoSum-R1R0-POW2-D1A-X"] = seltzo_lemma_zero_error(
        (x_r1r0, y_pow2, fx + one == ey, ex > fx + two),
        (sx, 1, 0, ex, fx + one, ey + one),
    )
    result["SELTZO-TwoSum-R1R0-POW2-D1A-Y"] = seltzo_lemma_zero_error(
        (y_r1r0, x_pow2, fy + one == ex, ey > fy + two),
        (sy, 1, 0, ey, fy + one, ex + one),
    )
    result["SELTZO-TwoSum-R1R0-POW2-D1B-X"] = seltzo_lemma_zero_error(
        (x_r1r0, y_pow2, ex == ey + (p - one), ex > fx + two),
        (sx, 1, 1, ex, fx + one, fx + one),
    )
    result["SELTZO-TwoSum-R1R0-POW2-D1B-Y"] = seltzo_lemma_zero_error(
        (y_r1r0, x_pow2, ey == ex + (p - one), ey > fy + two),
        (sy, 1, 1, ey, fy + one, fy + one),
    )
    result["SELTZO-TwoSum-R1R0-POW2-D1C-X"] = seltzo_lemma_zero_error(
        (x_r1r0, y_pow2, fx + one > ey, ex < ey + (p - one), ex == fx + two),
        (sx, 0, 0, ex, fx, ey),
    )
    result["SELTZO-TwoSum-R1R0-POW2-D1C-Y"] = seltzo_lemma_zero_error(
        (y_r1r0, x_pow2, fy + one > ex, ey < ex + (p - one), ey == fy + two),
        (sy, 0, 0, ey, fy, ex),
    )
    result["SELTZO-TwoSum-R1R0-POW2-D1AC-X"] = seltzo_lemma_zero_error(
        (x_r1r0, y_pow2, fx + one == ey, ex == fx + two),
        (sx, 0, 0, ex, ex - p, ex),
    )
    result["SELTZO-TwoSum-R1R0-POW2-D1AC-Y"] = seltzo_lemma_zero_error(
        (y_r1r0, x_pow2, fy + one == ex, ey == fy + two),
        (sy, 0, 0, ey, ey - p, ey),
    )
    result["SELTZO-TwoSum-R1R0-POW2-D1BC-X"] = seltzo_lemma_zero_error(
        (x_r1r0, y_pow2, ex == ey + (p - one), ex == fx + two),
        (sx, 0, 1, ex, fx, fx + one),
    )
    result["SELTZO-TwoSum-R1R0-POW2-D1BC-Y"] = seltzo_lemma_zero_error(
        (y_r1r0, x_pow2, ey == ex + (p - one), ey == fy + two),
        (sy, 0, 1, ey, fy, fy + one),
    )

    # conjecturer/SELTZO-TwoSum-R1R0-POW2-S.jl
    implicit_hypothesis = z3.And(xy_nonzero, same_sign)
    result["SELTZO-TwoSum-R1R0-POW2-S1-X"] = seltzo_lemma_zero_error(
        (x_r1r0, y_pow2, fx + one < ey, ex + one > ey, ex < fx + (p - one)),
        (sx, 0, 0, ex + one, ey - one, fx + one),
    )
    result["SELTZO-TwoSum-R1R0-POW2-S1-Y"] = seltzo_lemma_zero_error(
        (y_r1r0, x_pow2, fy + one < ex, ey + one > ex, ey < fy + (p - one)),
        (sy, 0, 0, ey + one, ex - one, fy + one),
    )
    result["SELTZO-TwoSum-R1R0-POW2-S1A-X"] = seltzo_lemma_zero_error(
        (x_r1r0, y_pow2, fx + one == ey),
        (sx, 0, 0, ex + one, ex - (p - one), ex + one),
    )
    result["SELTZO-TwoSum-R1R0-POW2-S1A-Y"] = seltzo_lemma_zero_error(
        (y_r1r0, x_pow2, fy + one == ex),
        (sy, 0, 0, ey + one, ey - (p - one), ey + one),
    )
    result["SELTZO-TwoSum-R1R0-POW2-S1B0-X"] = seltzo_lemma_zero_error(
        (x_r1r0, y_pow2, fx == ey, ex < fx + (p - one)),
        (sx, 1, 0, ex, ey - one, fx),
    )
    result["SELTZO-TwoSum-R1R0-POW2-S1B0-Y"] = seltzo_lemma_zero_error(
        (y_r1r0, x_pow2, fy == ex, ey < fy + (p - one)),
        (sy, 1, 0, ey, ex - one, fy),
    )
    result["SELTZO-TwoSum-R1R0-POW2-S1B1-X"] = seltzo_lemma_zero_error(
        (x_r1r0, y_pow2, fx == ey, ex == fx + (p - one)),
        (sx, 1, 1, ex, ey - one, ex),
    )
    result["SELTZO-TwoSum-R1R0-POW2-S1B1-Y"] = seltzo_lemma_zero_error(
        (y_r1r0, x_pow2, fy == ex, ey == fy + (p - one)),
        (sy, 1, 1, ey, ex - one, ey),
    )
    result["SELTZO-TwoSum-R1R0-POW2-S1C-X"] = seltzo_lemma_zero_error(
        (x_r1r0, y_pow2, fx + one < ey, ex + one > ey, ex == fx + (p - one)),
        (sx, 0, 1, ex + one, ey - one, ey),
    )
    result["SELTZO-TwoSum-R1R0-POW2-S1C-Y"] = seltzo_lemma_zero_error(
        (y_r1r0, x_pow2, fy + one < ex, ey + one > ex, ey == fy + (p - one)),
        (sy, 0, 1, ey + one, ex - one, ex),
    )
    result["SELTZO-TwoSum-R1R0-POW2-SB-X"] = seltzo_lemma_zero_error(
        (x_r1r0, y_pow2, ex == ey + (p - one), fx > ey),
        (sx, 1, 1, ex, fx, ey + one),
    )
    result["SELTZO-TwoSum-R1R0-POW2-SB-Y"] = seltzo_lemma_zero_error(
        (y_r1r0, x_pow2, ey == ex + (p - one), fy > ex),
        (sy, 1, 1, ey, fy, ex + one),
    )

    # conjecturer/SELTZO-TwoSum-T.jl
    implicit_hypothesis = xy_nonzero
    result["SELTZO-TwoSum-TS-L0-G-X"] = seltzo_lemma_zero_error(
        (same_sign, ~lbx, ~tbx, ~x_pow2, ~tby, gx > ey, gy + (p - one) > ex),
        (sx, 0, 0, ex, fx, gy),
    )
    result["SELTZO-TwoSum-TS-L0-G-Y"] = seltzo_lemma_zero_error(
        (same_sign, ~lby, ~tby, ~y_pow2, ~tbx, gy > ex, gx + (p - one) > ey),
        (sy, 0, 0, ey, fy, gx),
    )
    result["SELTZO-TwoSum-TS-L1-G-X"] = seltzo_lemma_zero_error(
        (same_sign, lbx, ~tbx, ~tby, fx > ey, gx > ey, gy + (p - one) > ex),
        (sx, 1, 0, ex, fx, gy),
    )
    result["SELTZO-TwoSum-TS-L1-G-Y"] = seltzo_lemma_zero_error(
        (same_sign, lby, ~tby, ~tbx, fy > ex, gy > ex, gx + (p - one) > ey),
        (sy, 1, 0, ey, fy, gx),
    )
    result["SELTZO-TwoSum-TD-L0-G-X"] = seltzo_lemma_zero_error(
        (diff_sign, ~lbx, tbx, ~tby, fx > ey, gx > ey, gy + (p - one) > ex),
        (sx, 0, 1, ex, fx, gy),
    )
    result["SELTZO-TwoSum-TD-L0-G-Y"] = seltzo_lemma_zero_error(
        (diff_sign, ~lby, tby, ~tbx, fy > ex, gy > ex, gx + (p - one) > ey),
        (sy, 0, 1, ey, fy, gx),
    )
    result["SELTZO-TwoSum-TD-L1-G-X"] = seltzo_lemma_zero_error(
        (diff_sign, lbx, tbx, ~x_all1, ~tby, gx > ey, gy + (p - one) > ex),
        (sx, 1, 1, ex, fx, gy),
    )
    result["SELTZO-TwoSum-TD-L1-G-Y"] = seltzo_lemma_zero_error(
        (diff_sign, lby, tby, ~y_all1, ~tbx, gy > ex, gx + (p - one) > ey),
        (sy, 1, 1, ey, fy, gx),
    )

    return result
