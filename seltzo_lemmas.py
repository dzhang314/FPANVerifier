# pyright: reportUnusedParameter=false, reportUnusedVariable=false
import z3
from smt_utils import BoolVar, IntVar, FloatVar, z3_If
from typing import Callable


def seltzo_two_sum_lemmas(
    x: FloatVar,
    y: FloatVar,
    s: FloatVar,
    e: FloatVar,
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
    nlbx: IntVar,
    nlby: IntVar,
    nlbs: IntVar,
    nlbe: IntVar,
    ntbx: IntVar,
    ntby: IntVar,
    ntbs: IntVar,
    ntbe: IntVar,
    is_zero: Callable[[FloatVar], z3.BoolRef],
    is_positive: Callable[[FloatVar], z3.BoolRef],
    is_negative: Callable[[FloatVar], z3.BoolRef],
    is_equal: Callable[[FloatVar, FloatVar], z3.BoolRef],
    p: IntVar,
    one: IntVar,
    two: IntVar,
    three: IntVar,
) -> dict[str, z3.BoolRef]:

    result: dict[str, z3.BoolRef] = {}

    same_sign: z3.BoolRef = sx == sy
    diff_sign: z3.BoolRef = sx != sy

    x_zero: z3.BoolRef = is_zero(x)
    y_zero: z3.BoolRef = is_zero(y)
    s_zero: z3.BoolRef = is_zero(s)
    e_zero: z3.BoolRef = is_zero(e)

    xy_nonzero: z3.BoolRef = z3.And(~x_zero, ~y_zero)
    s_pos_zero: z3.BoolRef = z3.And(is_positive(s), s_zero)
    e_pos_zero: z3.BoolRef = z3.And(is_positive(e), e_zero)

    fx: IntVar = ex - (nlbx + one)
    fy: IntVar = ey - (nlby + one)

    f0x: IntVar = ex - z3_If(lbx, nlbx + one, one)
    f0y: IntVar = ey - z3_If(lby, nlby + one, one)

    f1x: IntVar = ex - z3_If(lbx, one, nlbx + one)
    f1y: IntVar = ey - z3_If(lby, one, nlby + one)

    gx: IntVar = ex - (p - (ntbx + one))
    gy: IntVar = ey - (p - (ntby + one))

    g0x: IntVar = ex - (p - z3_If(tbx, ntbx + one, one))
    g0y: IntVar = ey - (p - z3_If(tby, ntby + one, one))

    g1x: IntVar = ex - (p - z3_If(tbx, one, ntbx + one))
    g1y: IntVar = ey - (p - z3_If(tby, one, ntby + one))

    x_pow2: z3.BoolRef = z3.And(~x_zero, ~lbx, ~tbx, nlbx == p - one, ntbx == p - one)
    y_pow2: z3.BoolRef = z3.And(~y_zero, ~lby, ~tby, nlby == p - one, ntby == p - one)

    x_all1: z3.BoolRef = z3.And(lbx, tbx, nlbx == p - one, ntbx == p - one)
    y_all1: z3.BoolRef = z3.And(lby, tby, nlby == p - one, ntby == p - one)

    x_r0r1: z3.BoolRef = z3.And(~lbx, tbx, nlbx + ntbx == p - one)
    y_r0r1: z3.BoolRef = z3.And(~lby, tby, nlby + ntby == p - one)

    x_r1r0: z3.BoolRef = z3.And(lbx, ~tbx, nlbx + ntbx == p - one)
    y_r1r0: z3.BoolRef = z3.And(lby, ~tby, nlby + ntby == p - one)

    x_one0: z3.BoolRef = z3.And(lbx, tbx, nlbx + ntbx == p - two)
    y_one0: z3.BoolRef = z3.And(lby, tby, nlby + ntby == p - two)

    x_one1: z3.BoolRef = z3.And(~lbx, ~tbx, nlbx + ntbx == p - two)
    y_one1: z3.BoolRef = z3.And(~lby, ~tby, nlby + ntby == p - two)

    x_two0: z3.BoolRef = z3.And(lbx, tbx, nlbx + ntbx == p - three)
    y_two0: z3.BoolRef = z3.And(lby, tby, nlby + ntby == p - three)

    x_two1: z3.BoolRef = z3.And(~lbx, ~tbx, nlbx + ntbx == p - three)
    y_two1: z3.BoolRef = z3.And(~lby, ~tby, nlby + ntby == p - three)

    x_mm01: z3.BoolRef = z3.And(lbx, ~tbx, nlbx + ntbx == p - three)
    y_mm01: z3.BoolRef = z3.And(lby, ~tby, nlby + ntby == p - three)

    x_mm10: z3.BoolRef = z3.And(~lbx, tbx, nlbx + ntbx == p - three)
    y_mm10: z3.BoolRef = z3.And(~lby, tby, nlby + ntby == p - three)

    x_g00: z3.BoolRef = z3.And(~lbx, ~tbx, nlbx + ntbx < p - three)
    y_g00: z3.BoolRef = z3.And(~lby, ~tby, nlby + ntby < p - three)

    x_g01: z3.BoolRef = z3.And(~lbx, tbx, nlbx + ntbx < p - three)
    y_g01: z3.BoolRef = z3.And(~lby, tby, nlby + ntby < p - three)

    x_g10: z3.BoolRef = z3.And(lbx, ~tbx, nlbx + ntbx < p - three)
    y_g10: z3.BoolRef = z3.And(lby, ~tby, nlby + ntby < p - three)

    x_g11: z3.BoolRef = z3.And(lbx, tbx, nlbx + ntbx < p - three)
    y_g11: z3.BoolRef = z3.And(lby, tby, nlby + ntby < p - three)

    def seltzo_case_helper(
        clauses: list[z3.BoolRef],
        variables: tuple[BoolVar, z3.BoolRef, z3.BoolRef, IntVar, IntVar, IntVar],
        values: tuple[
            tuple[BoolVar] | BoolVar | None,
            int | None,
            int | None,
            tuple[IntVar, IntVar] | IntVar | None,
            tuple[IntVar, IntVar] | IntVar | None,
            tuple[IntVar, IntVar] | IntVar | None,
        ],
    ) -> None:
        s_var, lb_var, tb_var, e_var, nlb_var, ntb_var = variables
        s_val, lb_val, tb_val, e_val, f_val, g_val = values
        assert s_var is not s_val
        assert lb_var is not lb_val
        assert tb_var is not tb_val
        assert e_var is not e_val
        if isinstance(s_val, tuple):
            clauses.append(s_var != s_val[0])
        elif s_val is not None:
            clauses.append(s_var == s_val)
        if lb_val is not None:
            assert lb_val == 0 or lb_val == 1
            clauses.append(lb_var if lb_val else ~lb_var)
        if tb_val is not None:
            assert tb_val == 0 or tb_val == 1
            clauses.append(tb_var if tb_val else ~tb_var)
        if e_val is not None and not isinstance(e_val, tuple):
            e_val = (e_val, e_val)
        if f_val is not None and not isinstance(f_val, tuple):
            f_val = (f_val, f_val)
        if g_val is not None and not isinstance(g_val, tuple):
            g_val = (g_val, g_val)
        if e_val is not None:
            clauses.append(e_var >= e_val[0])
            clauses.append(e_var <= e_val[1])
        if e_val is not None and f_val is not None:
            clauses.append(nlb_var >= e_val[0] - f_val[1] - one)
            clauses.append(nlb_var <= e_val[1] - f_val[0] - one)
        if e_val is not None and g_val is not None:
            clauses.append(ntb_var >= (p - one) - (e_val[1] - g_val[0]))
            clauses.append(ntb_var <= (p - one) - (e_val[0] - g_val[1]))
        return None

    def seltzo_case_zero(
        s_values: tuple[
            tuple[BoolVar] | BoolVar | None,
            int | None,
            int | None,
            tuple[IntVar, IntVar] | IntVar | None,
            tuple[IntVar, IntVar] | IntVar | None,
            tuple[IntVar, IntVar] | IntVar | None,
        ],
    ) -> z3.BoolRef:
        clauses: list[z3.BoolRef] = []
        seltzo_case_helper(clauses, (ss, lbs, tbs, es, nlbs, ntbs), s_values)
        clauses.append(e_pos_zero)
        return z3.And(*clauses)

    def seltzo_case(
        s_values: tuple[
            tuple[BoolVar] | BoolVar | None,
            int | None,
            int | None,
            IntVar | None,
            IntVar | None,
            IntVar | None,
        ],
        e_values: tuple[
            tuple[BoolVar] | BoolVar | None,
            int | None,
            int | None,
            IntVar | None,
            IntVar | None,
            IntVar | None,
        ],
    ) -> z3.BoolRef:
        clauses: list[z3.BoolRef] = []
        seltzo_case_helper(clauses, (ss, lbs, tbs, es, nlbs, ntbs), s_values)
        seltzo_case_helper(clauses, (se, lbe, tbe, ee, nlbe, ntbe), e_values)
        return z3.And(*clauses)

    ############################################################################

    result["SELTZO-TwoSum-FS-POW2-G-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, x_pow2, ~tby, ex > ey + one, gy > fx + one),
        seltzo_case_zero((sx, 0, 0, ex, ey, gy)),
    )
    result["SELTZO-TwoSum-FS-POW2-G-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, y_pow2, ~tbx, ey > ex + one, gx > fy + one),
        seltzo_case_zero((sy, 0, 0, ey, ex, gx)),
    )

    result["SELTZO-TwoSum-FS-POW2-A1-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, x_pow2, ~tby, ex == ey + one, lby, gy > fx + one),
        seltzo_case_zero((sx, 1, 0, ex, fy, gy)),
    )
    result["SELTZO-TwoSum-FS-POW2-A1-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, y_pow2, ~tbx, ey == ex + one, lbx, gx > fy + one),
        seltzo_case_zero((sy, 1, 0, ey, fx, gx)),
    )

    result["SELTZO-TwoSum-FS-POW2-A2-X"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, x_pow2, ~tby, ex == ey + one, ~lby, gy > fx + one
        ),
        seltzo_case_zero((sx, 1, 0, ex, ey - one, gy)),
    )
    result["SELTZO-TwoSum-FS-POW2-A2-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, y_pow2, ~tbx, ey == ex + one, ~lbx, gx > fy + one
        ),
        seltzo_case_zero((sy, 1, 0, ey, ex - one, gx)),
    )

    result["SELTZO-TwoSum-FS-POW2-B1-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_pow2,
            ~tby,
            ex > ey + one,
            gy == fx + one,
            z3.Or(y_pow2, y_one1, y_mm01),
        ),
        seltzo_case_zero((sx, 0, 1, ex, ey, gy + one)),
    )
    result["SELTZO-TwoSum-FS-POW2-B1-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_pow2,
            ~tbx,
            ey > ex + one,
            gx == fy + one,
            z3.Or(x_pow2, x_one1, x_mm01),
        ),
        seltzo_case_zero((sy, 0, 1, ey, ex, gx + one)),
    )

    result["SELTZO-TwoSum-FS-POW2-B2-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, ~tby, ex > ey + one, gy == fx + one, y_two1),
        seltzo_case_zero((sx, 0, 1, ex, ey, gy + two)),
    )
    result["SELTZO-TwoSum-FS-POW2-B2-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, ~tbx, ey > ex + one, gx == fy + one, x_two1),
        seltzo_case_zero((sy, 0, 1, ey, ex, gx + two)),
    )

    result["SELTZO-TwoSum-FS-POW2-B3-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, ~tby, ex > ey + one, gy == fx + one, y_r1r0),
        seltzo_case_zero((sx, 0, 1, ex, ey, ey + one)),
    )
    result["SELTZO-TwoSum-FS-POW2-B3-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, ~tbx, ey > ex + one, gx == fy + one, x_r1r0),
        seltzo_case_zero((sy, 0, 1, ey, ex, ex + one)),
    )

    result["SELTZO-TwoSum-FS-POW2-B4-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, ~tby, ex > ey + one, gy == fx + one, y_g00),
        z3.Or(
            seltzo_case_zero((sx, 0, 1, ex, ey, (gy + one, fy - one))),
            seltzo_case_zero((sx, 0, 1, ex, ey, fy + one)),
        ),
    )
    result["SELTZO-TwoSum-FS-POW2-B4-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, ~tbx, ey > ex + one, gx == fy + one, x_g00),
        z3.Or(
            seltzo_case_zero((sy, 0, 1, ey, ex, (gx + one, fx - one))),
            seltzo_case_zero((sy, 0, 1, ey, ex, fx + one)),
        ),
    )

    result["SELTZO-TwoSum-FS-POW2-B5-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, ~tby, ex > ey + one, gy == fx + one, y_g10),
        seltzo_case_zero((sx, 0, 1, ex, ey, (gy + one, fy))),
    )
    result["SELTZO-TwoSum-FS-POW2-B5-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, ~tbx, ey > ex + one, gx == fy + one, x_g10),
        seltzo_case_zero((sy, 0, 1, ey, ex, (gx + one, fx))),
    )

    result["SELTZO-TwoSum-FS-POW2-AB1-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, ~tby, ex == ey + one, gy == fx + one, y_r1r0),
        seltzo_case_zero((sx, 1, 1, ex, ex - p, ex)),
    )
    result["SELTZO-TwoSum-FS-POW2-AB1-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, ~tbx, ey == ex + one, gx == fy + one, x_r1r0),
        seltzo_case_zero((sy, 1, 1, ey, ey - p, ey)),
    )

    result["SELTZO-TwoSum-FS-POW2-AB2-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, ~tby, ex == ey + one, gy == fx + one, y_one1),
        seltzo_case_zero((sx, 1, 1, ex, ey - one, gy + one)),
    )
    result["SELTZO-TwoSum-FS-POW2-AB2-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, ~tbx, ey == ex + one, gx == fy + one, x_one1),
        seltzo_case_zero((sy, 1, 1, ey, ex - one, gx + one)),
    )

    result["SELTZO-TwoSum-FS-POW2-AB3-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, ~tby, ex == ey + one, gy == fx + one, y_two1),
        seltzo_case_zero((sx, 1, 1, ex, ey - one, gy + two)),
    )
    result["SELTZO-TwoSum-FS-POW2-AB3-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, ~tbx, ey == ex + one, gx == fy + one, x_two1),
        seltzo_case_zero((sy, 1, 1, ey, ex - one, gx + two)),
    )

    result["SELTZO-TwoSum-FS-POW2-AB4-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, ~tby, ex == ey + one, gy == fx + one, y_mm01),
        seltzo_case_zero((sx, 1, 1, ex, fy, gy + one)),
    )
    result["SELTZO-TwoSum-FS-POW2-AB4-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, ~tbx, ey == ex + one, gx == fy + one, x_mm01),
        seltzo_case_zero((sy, 1, 1, ey, fx, gx + one)),
    )

    result["SELTZO-TwoSum-FS-POW2-AB5-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, ~tby, ex == ey + one, gy == fx + one, y_g00),
        z3.Or(
            seltzo_case_zero((sx, 1, 1, ex, ey - one, (gy + one, fy - one))),
            seltzo_case_zero((sx, 1, 1, ex, ey - one, fy + one)),
        ),
    )
    result["SELTZO-TwoSum-FS-POW2-AB5-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, ~tbx, ey == ex + one, gx == fy + one, x_g00),
        z3.Or(
            seltzo_case_zero((sy, 1, 1, ey, ex - one, (gx + one, fx - one))),
            seltzo_case_zero((sy, 1, 1, ey, ex - one, fx + one)),
        ),
    )

    result["SELTZO-TwoSum-FS-POW2-AB6-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, ~tby, ex == ey + one, gy == fx + one, y_g10),
        seltzo_case_zero((sx, 1, 1, ex, fy, (gy + one, fy))),
    )
    result["SELTZO-TwoSum-FS-POW2-AB6-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, ~tbx, ey == ex + one, gx == fy + one, x_g10),
        seltzo_case_zero((sy, 1, 1, ey, fx, (gx + one, fx))),
    )

    ############################################################################

    result["SELTZO-TwoSum-FD-ALL1-G-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, x_all1, ~tby, ex > ey + one, gy > fx + one),
        seltzo_case_zero((sx, 1, 1, ex, ey, gy)),
    )
    result["SELTZO-TwoSum-FD-ALL1-G-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, y_all1, ~tbx, ey > ex + one, gx > fy + one),
        seltzo_case_zero((sy, 1, 1, ey, ex, gx)),
    )

    ############################################################################

    result["SELTZO-TwoSum-FS-T0-G-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ~lbx,
            ~tby,
            ~tbx,
            ~x_pow2,
            ex > ey + one,
            gy > fx + one,
        ),
        seltzo_case_zero((sx, 0, 0, ex, ey, gx)),
    )
    result["SELTZO-TwoSum-FS-T0-G-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ~lby,
            ~tbx,
            ~tby,
            ~y_pow2,
            ey > ex + one,
            gx > fy + one,
        ),
        seltzo_case_zero((sy, 0, 0, ey, ex, gy)),
    )

    result["SELTZO-TwoSum-FS-T0-A1-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ~lbx,
            ~tby,
            ~tbx,
            ~x_pow2,
            ex == ey + one,
            lby,
            gy > fx + one,
        ),
        seltzo_case_zero((sx, 1, 0, ex, fy, gx)),
    )
    result["SELTZO-TwoSum-FS-T0-A1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ~lby,
            ~tbx,
            ~tby,
            ~y_pow2,
            ey == ex + one,
            lbx,
            gx > fy + one,
        ),
        seltzo_case_zero((sy, 1, 0, ey, fx, gy)),
    )

    result["SELTZO-TwoSum-FS-T0-A2-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ~lbx,
            ~tby,
            ~tbx,
            ~x_pow2,
            ex == ey + one,
            ~lby,
            gy > fx + one,
        ),
        seltzo_case_zero((sx, 1, 0, ex, ey - one, gx)),
    )
    result["SELTZO-TwoSum-FS-T0-A2-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ~lby,
            ~tbx,
            ~tby,
            ~y_pow2,
            ey == ex + one,
            ~lbx,
            gx > fy + one,
        ),
        seltzo_case_zero((sy, 1, 0, ey, ex - one, gy)),
    )

    result["SELTZO-TwoSum-FS-T1-G-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ~lbx, ~tby, tbx, ex > ey + one, gy > fx + one),
        seltzo_case_zero((sx, 0, 1, ex, ey, gx)),
    )
    result["SELTZO-TwoSum-FS-T1-G-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ~lby, ~tbx, tby, ey > ex + one, gx > fy + one),
        seltzo_case_zero((sy, 0, 1, ey, ex, gy)),
    )

    result["SELTZO-TwoSum-FS-T1-A1-X"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ~lbx, ~tby, tbx, ex == ey + one, lby, gy > fx + one
        ),
        seltzo_case_zero((sx, 1, 1, ex, fy, gx)),
    )
    result["SELTZO-TwoSum-FS-T1-A1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ~lby, ~tbx, tby, ey == ex + one, lbx, gx > fy + one
        ),
        seltzo_case_zero((sy, 1, 1, ey, fx, gy)),
    )

    result["SELTZO-TwoSum-FS-T1-A2-X"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ~lbx, ~tby, tbx, ex == ey + one, ~lby, gy > fx + one
        ),
        seltzo_case_zero((sx, 1, 1, ex, ey - one, gx)),
    )
    result["SELTZO-TwoSum-FS-T1-A2-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ~lby, ~tbx, tby, ey == ex + one, ~lbx, gx > fy + one
        ),
        seltzo_case_zero((sy, 1, 1, ey, ex - one, gy)),
    )

    ############################################################################

    # Sum of two powers of two (equal exponent case).
    result["SELTZO-TwoSum-POW2-POW2-SE"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_pow2, ex == ey),
        seltzo_case_zero((sx, 0, 0, ex + one, fx + one, gx + one)),
    )

    # Remaining POW2-POW2-S lemmas have been subsumed by F lemmas.

    ############################################################################

    # Difference of two powers of two (equal exponent case).
    result["SELTZO-TwoSum-POW2-POW2-DE"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_pow2, ex == ey),
        z3.And(s_pos_zero, e_pos_zero),
    )

    # Difference of two powers of two (adjacent case).
    result["SELTZO-TwoSum-POW2-POW2-DA-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_pow2, ex == ey + one),
        seltzo_case_zero((sx, 0, 0, ex - one, fx - one, gx - one)),
    )
    result["SELTZO-TwoSum-POW2-POW2-DA-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_pow2, ey == ex + one),
        seltzo_case_zero((sy, 0, 0, ey - one, fy - one, gy - one)),
    )

    # Difference of two powers of two (general case).
    result["SELTZO-TwoSum-POW2-POW2-DG-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_pow2, ex > ey + one, ex < ey + p),
        seltzo_case_zero((sx, 1, 0, ex - one, ey - one, ey)),
    )
    result["SELTZO-TwoSum-POW2-POW2-DG-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_pow2, ey > ex + one, ey < ex + p),
        seltzo_case_zero((sy, 1, 0, ey - one, ex - one, ex)),
    )

    # Difference of two powers of two (boundary case).
    result["SELTZO-TwoSum-POW2-POW2-DB-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_pow2, ex == ey + p),
        seltzo_case_zero((sx, 1, 1, ex - one, fx - one, gx - one)),
    )
    result["SELTZO-TwoSum-POW2-POW2-DB-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_pow2, ey == ex + p),
        seltzo_case_zero((sy, 1, 1, ey - one, fy - one, gy - one)),
    )

    ############################################################################

    result["SELTZO-TwoSum-ALL1-ALL1-SE"] = z3.Implies(
        z3.And(same_sign, x_all1, y_all1, ex == ey),
        seltzo_case_zero((sx, 1, 1, ex + one, fx + one, gx + one)),
    )

    result["SELTZO-TwoSum-ALL1-ALL1-SA-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_all1, ex == ey + one),
        seltzo_case(
            (sx, 0, 1, ex + one, ey, ey + one),
            (sy, 0, 0, fx, fx - p, fy + one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-SA-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_all1, ey == ex + one),
        seltzo_case(
            (sy, 0, 1, ey + one, ex, ex + one),
            (sx, 0, 0, fy, fy - p, fx + one),
        ),
    )

    result["SELTZO-TwoSum-ALL1-ALL1-SG-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_all1, ex > ey + one, ex < ey + (p - one)),
        seltzo_case(
            (sx, 0, 1, ex + one, ey, ey + one),
            (sy, 1, 0, fx, fy, fy + one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-SG-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_all1, ey > ex + one, ey < ex + (p - one)),
        seltzo_case(
            (sy, 0, 1, ey + one, ex, ex + one),
            (sx, 1, 0, fy, fx, fx + one),
        ),
    )

    result["SELTZO-TwoSum-ALL1-ALL1-SB1-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_all1, ex == ey + (p - one)),
        seltzo_case(
            (sx, 0, 0, ex + one, fx + one, gx + one),
            (sy, 1, 0, fx, fy, fy + one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-SB1-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_all1, ey == ex + (p - one)),
        seltzo_case(
            (sy, 0, 0, ey + one, fy + one, gy + one),
            (sx, 1, 0, fy, fx, fx + one),
        ),
    )

    result["SELTZO-TwoSum-ALL1-ALL1-SB2-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_all1, ex == ey + p),
        seltzo_case(
            (sx, 0, 0, ex + one, fx + one, gx + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-SB2-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_all1, ey == ex + p),
        seltzo_case(
            (sy, 0, 0, ey + one, fy + one, gy + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    ############################################################################

    result["SELTZO-TwoSum-ALL1-ALL1-DE"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_all1, ex == ey),
        z3.And(s_pos_zero, e_pos_zero),
    )

    result["SELTZO-TwoSum-ALL1-ALL1-DA1-X"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_all1, ex == ey + one),
        seltzo_case_zero((sx, 1, 1, ex - one, fx - one, gx - one)),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-DA1-Y"] = z3.Implies(
        z3.And(diff_sign, y_all1, x_all1, ey == ex + one),
        seltzo_case_zero((sy, 1, 1, ey - one, fy - one, gy - one)),
    )

    result["SELTZO-TwoSum-ALL1-ALL1-DA2-X"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_all1, ex == ey + two),
        seltzo_case(
            (sx, 0, 1, ey + two, ey, ey + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-DA2-Y"] = z3.Implies(
        z3.And(diff_sign, y_all1, x_all1, ey == ex + two),
        seltzo_case(
            (sy, 0, 1, ex + two, ex, ex + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-ALL1-ALL1-DG-X"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_all1, ex > ey + two, ex < ey + p),
        seltzo_case(
            (sx, 1, 1, ex, ey + one, ey + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-DG-Y"] = z3.Implies(
        z3.And(diff_sign, y_all1, x_all1, ey > ex + two, ey < ex + p),
        seltzo_case(
            (sy, 1, 1, ey, ex + one, ex + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-ALL1-ALL1-DB-X"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_all1, ex == ey + p),
        seltzo_case(
            (sx, 1, 0, ex, ey + one, ey + two),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-ALL1-DB-Y"] = z3.Implies(
        z3.And(diff_sign, y_all1, x_all1, ey == ex + p),
        seltzo_case(
            (sy, 1, 0, ey, ex + one, ex + two),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    ############################################################################

    result["SELTZO-TwoSum-POW2-ALL1-SE"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_all1, ex == ey),
        seltzo_case(
            (sx, 1, 0, ex + one, ey - one, ey),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-ALL1-SA1-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_all1, ex == ey + one),
        seltzo_case(
            (sx, 0, 0, ex + one, fx + one, gx + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-POW2-ALL1-SA1-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_all1, ey == ex + one),
        seltzo_case(
            (sy, 0, 0, ey + one, fy + one, gy + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-ALL1-SA2-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_all1, ex == ey + two),
        seltzo_case(
            (sx, 1, 0, ex, ey, ey + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-POW2-ALL1-SA2-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_all1, ey == ex + two),
        seltzo_case(
            (sy, 1, 0, ey, ex, ex + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-ALL1-SG-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_all1, ex > ey + two, ex < ey + p),
        seltzo_case(
            (sx, 0, 0, ex, ey + one, ey + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-POW2-ALL1-SG-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_all1, ey > ex + two, ey < ex + p),
        seltzo_case(
            (sy, 0, 0, ey, ex + one, ex + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-ALL1-SB-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_all1, ex == ey + p),
        seltzo_case(
            (sx, 0, 1, ex, ey + one, ey + two),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-POW2-ALL1-SB-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_all1, ey == ex + p),
        seltzo_case(
            (sy, 0, 1, ey, ex + one, ex + two),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    ############################################################################

    result["SELTZO-TwoSum-POW2-ALL1-DE"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_all1, ex == ey),
        seltzo_case_zero(((sx,), 1, 0, ex - one, fx, fx + one)),
    )

    result["SELTZO-TwoSum-POW2-ALL1-DA1-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_all1, ex == ey + one),
        seltzo_case_zero((sx, 0, 0, fx, fx - p, fx)),
    )
    result["SELTZO-TwoSum-POW2-ALL1-DA1-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_all1, ey == ex + one),
        seltzo_case_zero((sy, 0, 0, fy, fy - p, fy)),
    )

    result["SELTZO-TwoSum-POW2-ALL1-DA2-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_all1, ex == ey + two),
        seltzo_case(
            (sx, 0, 0, ex - one, fx - one, gx - one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-POW2-ALL1-DA2-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_all1, ey == ex + two),
        seltzo_case(
            (sy, 0, 0, ey - one, fy - one, gy - one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-ALL1-DG-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_all1, ex > ey + two, ex < ey + (p + one)),
        seltzo_case(
            (sx, 1, 0, ex - one, ey, ey + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-POW2-ALL1-DG-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_all1, ey > ex + two, ey < ex + (p + one)),
        seltzo_case(
            (sy, 1, 0, ey - one, ex, ex + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-ALL1-DB-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_all1, ex == ey + (p + one)),
        seltzo_case(
            (sx, 1, 1, ex - one, ey, ex - one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-POW2-ALL1-DB-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_all1, ey == ex + (p + one)),
        seltzo_case(
            (sy, 1, 1, ey - one, ex, ey - one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    ############################################################################

    result["SELTZO-TwoSum-ALL1-POW2-SE"] = z3.Implies(
        z3.And(same_sign, x_all1, y_pow2, ex == ey),
        seltzo_case(
            (sx, 1, 0, ex + one, ey - one, ey),
            ((sy,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-ALL1-POW2-SG-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_pow2, ex > ey, ex < ey + (p - two)),
        seltzo_case(
            (sx, 0, 0, ex + one, ey, ey),
            ((sy,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-POW2-SG-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_pow2, ey > ex, ey < ex + (p - two)),
        seltzo_case(
            (sy, 0, 0, ey + one, ex, ex),
            ((sx,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )

    result["SELTZO-TwoSum-ALL1-POw2-SB1-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_pow2, ex == ey + (p - two)),
        seltzo_case(
            (sx, 0, 0, ex + one, ey - one, ex + one),
            (sy, 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-POW2-SB1-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_pow2, ey == ex + (p - two)),
        seltzo_case(
            (sy, 0, 0, ey + one, ex - one, ey + one),
            (sx, 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )

    result["SELTZO-TwoSum-ALL1-POW2-SB2-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_pow2, ex == ey + (p - one)),
        seltzo_case_zero((sx, 0, 0, ex + one, fx + one, gx + one)),
    )
    result["SELTZO-TwoSum-ALL1-POW2-SB2-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_pow2, ey == ex + (p - one)),
        seltzo_case_zero((sy, 0, 0, ey + one, fy + one, gy + one)),
    )

    result["SELTZO-TwoSum-ALL1-POW2-SB3-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_pow2, ex == ey + p),
        seltzo_case(
            (sx, 0, 0, ex + one, fx + one, gx + one),
            ((sy,), 0, 0, fx, fx - p, fx),
        ),
    )
    result["SELTZO-TwoSum-ALL1-POW2-SB3-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_pow2, ey == ex + p),
        seltzo_case(
            (sy, 0, 0, ey + one, fy + one, gy + one),
            ((sx,), 0, 0, fy, fy - p, fy),
        ),
    )

    ############################################################################

    result["SELTZO-TwoSum-ALL1-POW2-DE"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_pow2, ex == ey),
        seltzo_case_zero((sx, 1, 0, ex - one, fx, fx + one)),
    )

    result["SELTZO-TwoSum-ALL1-POW2-DA-X"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_pow2, ex == ey + one),
        seltzo_case_zero((sx, 0, 1, ex, ey - one, ey)),
    )
    result["SELTZO-TwoSum-ALL1-POW2-DA-Y"] = z3.Implies(
        z3.And(diff_sign, y_all1, x_pow2, ey == ex + one),
        seltzo_case_zero((sy, 0, 1, ey, ex - one, ex)),
    )

    result["SELTZO-TwoSum-ALL1-POW2-DB1-X"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_pow2, ex == ey + (p - one)),
        seltzo_case_zero((sx, 1, 0, ex, ey, ey + one)),
    )
    result["SELTZO-TwoSum-ALL1-POW2-DB1-Y"] = z3.Implies(
        z3.And(diff_sign, y_all1, x_pow2, ey == ex + (p - one)),
        seltzo_case_zero((sy, 1, 0, ey, ex, ex + one)),
    )

    result["SELTZO-TwoSum-ALL1-POW2-DB2-X"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_pow2, ex == ey + p),
        seltzo_case(
            (sx, 1, 0, ex, ey + one, ey + two),
            ((sy,), 0, 0, ey, ey - p, ey),
        ),
    )
    result["SELTZO-TwoSum-ALL1-POW2-DB2-Y"] = z3.Implies(
        z3.And(diff_sign, y_all1, x_pow2, ey == ex + p),
        seltzo_case(
            (sy, 1, 0, ey, ex + one, ex + two),
            ((sx,), 0, 0, ex, ex - p, ex),
        ),
    )

    ############################################################################

    result["SELTZO-TwoSum-R1R0-ONE1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_one1, ex > fy + (p - one), ey > fx + one),
        seltzo_case((sx, 1, 0, ex, ey, gx), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-R1R0-ONE1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_one1, ey > fx + (p - one), ex > fy + one),
        seltzo_case((sy, 1, 0, ey, ex, gy), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-R1R0-ALL1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_all1, ex > ey + two, ey + one > gx),
        seltzo_case(
            (sx, 1, 0, ex, ey + one, gx),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_all1, ey > ex + two, ex + one > gy),
        seltzo_case(
            (sy, 1, 0, ey, ex + one, gy),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-R0R1-POW2-S1-X"] = z3.Implies(
        z3.And(same_sign, x_r0r1, y_pow2, ex == ey + one, ex == fx + two),
        seltzo_case_zero((sx, 1, 1, ex, ex - p, ex)),
    )
    result["SELTZO-TwoSum-R0R1-POW2-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_r0r1, x_pow2, ey == ex + one, ey == fy + two),
        seltzo_case_zero((sy, 1, 1, ey, ey - p, ey)),
    )

    result["SELTZO-TwoSum-ONE0-POW2-S1-X"] = z3.Implies(
        z3.And(same_sign, x_one0, y_pow2, fx == ey),
        seltzo_case_zero((sx, 1, 1, ex, ex - p, ex)),
    )
    result["SELTZO-TwoSum-ONE0-POW2-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_one0, x_pow2, fy == ex),
        seltzo_case_zero((sy, 1, 1, ey, ey - p, ey)),
    )

    result["SELTZO-TwoSum-R0R1-R1R0-S1-X"] = z3.Implies(
        z3.And(
            same_sign, x_r0r1, y_r1r0, ex == ey + two, ey == fx + one, fx == fy + one
        ),
        seltzo_case_zero((sx, 1, 1, ex, fx + one, gx - one)),
    )
    result["SELTZO-TwoSum-R0R1-R1R0-S1-Y"] = z3.Implies(
        z3.And(
            same_sign, y_r0r1, x_r1r0, ey == ex + two, ex == fy + one, fy == fx + one
        ),
        seltzo_case_zero((sy, 1, 1, ey, fy + one, gy - one)),
    )

    result["SELTZO-TwoSum-R1R0-R1R0-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_r1r0, ex > ey + one, fx < fy),
        seltzo_case_zero((sx, 1, 0, ex, ey, gx)),
    )
    result["SELTZO-TwoSum-R1R0-R1R0-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_r1r0, ey > ex + one, fy < fx),
        seltzo_case_zero((sy, 1, 0, ey, ex, gy)),
    )

    result["SELTZO-TwoSum-ONE1-R1R0-D1-X"] = z3.Implies(
        z3.And(
            diff_sign, x_one1, y_r1r0, ex == ey + (p - two), fx == ey, ey == fy + three
        ),
        seltzo_case_zero((sx, 1, 1, ex - one, fx - one, fx - one)),
    )
    result["SELTZO-TwoSum-ONE1-R1R0-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign, y_one1, x_r1r0, ey == ex + (p - two), fy == ex, ex == fx + three
        ),
        seltzo_case_zero((sy, 1, 1, ey - one, fy - one, fy - one)),
    )

    result["SELTZO-TwoSum-POW2-R1R0-S1-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_r1r0, ex == ey + p),
        seltzo_case((sx, 0, 1, ex, ey + one, ey + two), ((sy,), 0, 0, gy, gy - p, gy)),
    )
    result["SELTZO-TwoSum-POW2-R1R0-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_r1r0, ey == ex + p),
        seltzo_case((sy, 0, 1, ey, ex + one, ex + two), ((sx,), 0, 0, gx, gx - p, gx)),
    )

    result["SELTZO-TwoSum-R0R1-R1R0-S2-X"] = z3.Implies(
        z3.And(same_sign, x_r0r1, y_r1r0, ex > ey + one, fx == fy),
        seltzo_case_zero((sx, 0, 1, ex, ey, ey + one)),
    )
    result["SELTZO-TwoSum-R0R1-R1R0-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_r0r1, x_r1r0, ey > ex + one, fy == fx),
        seltzo_case_zero((sy, 0, 1, ey, ex, ex + one)),
    )

    result["SELTZO-TwoSum-POW2-ONE1-S1-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_one1, ex == ey + p),
        seltzo_case(
            (sx, 0, 1, ex, ey + one, ey + two),
            ((sy,), 1, 0, ey - one, fy - one, fy),
        ),
    )
    result["SELTZO-TwoSum-POW2-ONE1-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_one1, ey == ex + p),
        seltzo_case(
            (sy, 0, 1, ey, ex + one, ex + two),
            ((sx,), 1, 0, ex - one, fx - one, fx),
        ),
    )

    result["SELTZO-TwoSum-ALL1-R1R0-S1-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_r1r0, ex > ey, ex < fy + (p - one)),
        seltzo_case(
            (sx, 0, 0, ex + one, ey, gy),
            ((sy,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_r1r0, ey > ex, ey < fx + (p - one)),
        seltzo_case(
            (sy, 0, 0, ey + one, ex, gx),
            ((sx,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-ONE1-S2-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_one1, ex == ey + (p - one)),
        seltzo_case(
            (sx, 0, 1, ex, ey, ey + one),
            (sy, 0, 0, fy, fy - p, fy),
        ),
    )
    result["SELTZO-TwoSum-POW2-ONE1-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_one1, ey == ex + (p - one)),
        seltzo_case(
            (sy, 0, 1, ey, ex, ex + one),
            (sx, 0, 0, fx, fx - p, fx),
        ),
    )

    result["SELTZO-TwoSum-ALL1-R1R0-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_r1r0, ex == ey + (p - one), ey > fy + two),
        seltzo_case(
            (sx, 1, 1, ex, ey + one, ey + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_all1, x_r1r0, ey == ex + (p - one), ex > fx + two),
        seltzo_case(
            (sy, 1, 1, ey, ex + one, ex + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-R1R0-S2-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_r1r0, ex > ey + two, ex < ey + p, ex > fy + p),
        seltzo_case(
            (sx, 0, 0, ex, ey + one, ey + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-POW2-R1R0-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_r1r0, ey > ex + two, ey < ex + p, ey > fx + p),
        seltzo_case(
            (sy, 0, 0, ey, ex + one, ex + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-R1R0-ONE1-S1-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, y_one1, ex == ey + p, ex == fx + (p - one)),
        seltzo_case(
            (sx, 1, 1, ex, ex - p, ex),
            ((sy,), 1, 0, ey - one, fy - one, gy),
        ),
    )
    result["SELTZO-TwoSum-R1R0-ONE1-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_one1, ey == ex + p, ey == fy + (p - one)),
        seltzo_case(
            (sy, 1, 1, ey, ey - p, ey),
            ((sx,), 1, 0, ex - one, fx - one, gx),
        ),
    )

    result["SELTZO-TwoSum-ONE0-R0R1-D1-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_one0,
            y_r0r1,
            ex == ey + (p - one),
            ex < fx + (p - two),
            ey == fy + (p - one),
        ),
        seltzo_case(
            (sx, 1, 0, ex, fx, ey + one),
            (sy, 0, 0, fy, fy - p, fy),
        ),
    )
    result["SELTZO-TwoSum-ONE0-R0R1-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_one0,
            x_r0r1,
            ey == ex + (p - one),
            ey < fy + (p - two),
            ex == fx + (p - one),
        ),
        seltzo_case(
            (sy, 1, 0, ey, fy, ex + one),
            (sx, 0, 0, fx, fx - p, fx),
        ),
    )

    result["SELTZO-TwoSum-R1R0-R1R0-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_r1r0, ex == ey + p, ex > fx + two),
        seltzo_case(
            (sx, 1, 1, ex, gx, gx),
            ((sy,), 0, 0, gy, fy - (p - one), gy),
        ),
    )
    result["SELTZO-TwoSum-R1R0-R1R0-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_r1r0, ey == ex + p, ey > fy + two),
        seltzo_case(
            (sy, 1, 1, ey, gy, gy),
            ((sx,), 0, 0, gx, fx - (p - one), gx),
        ),
    )

    result["SELTZO-TwoSum-R0R1-R1R0-S3-X"] = z3.Implies(
        z3.And(same_sign, x_r0r1, y_r1r0, ex > fx + two, fx + one > ey, ex < fy + p),
        seltzo_case_zero((sx, 0, 1, ex, gx, gy)),
    )
    result["SELTZO-TwoSum-R0R1-R1R0-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_r0r1, x_r1r0, ey > fy + two, fy + one > ex, ey < fx + p),
        seltzo_case_zero((sy, 0, 1, ey, gy, gx)),
    )

    result["SELTZO-TwoSum-ONE1-R1R0-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_r1r0, ey > fx, ex > fy + (p + one)),
        seltzo_case(
            (sx, 1, 0, ex - one, ey, gx),
            ((sy,), 0, 0, gy, fy - (p - one), gy),
        ),
    )
    result["SELTZO-TwoSum-ONE1-R1R0-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_r1r0, ex > fy, ey > fx + (p + one)),
        seltzo_case(
            (sy, 1, 0, ey - one, ex, gy),
            ((sx,), 0, 0, gx, fx - (p - one), gx),
        ),
    )

    result["SELTZO-TwoSum-R1R0-ONE1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_one1, ex == ey + p, ex > fx + two),
        seltzo_case(
            (sx, 1, 1, ex, fx + one, gx),
            ((sy,), 1, 0, ey - one, fy - one, gy),
        ),
    )
    result["SELTZO-TwoSum-R1R0-ONE1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_one1, ey == ex + p, ey > fy + two),
        seltzo_case(
            (sy, 1, 1, ey, fy + one, gy),
            ((sx,), 1, 0, ex - one, fx - one, gx),
        ),
    )

    result["SELTZO-TwoSum-ALL1-ONE1-S1-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_one1, ex == ey + (p - one)),
        seltzo_case(
            (sx, 0, 0, ex + one, ex - (p - one), ex + one),
            (sy, 0, 0, fy, fy - p, fy),
        ),
    )
    result["SELTZO-TwoSum-ALL1-ONE1-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_one1, ey == ex + (p - one)),
        seltzo_case(
            (sy, 0, 0, ey + one, ey - (p - one), ey + one),
            (sx, 0, 0, fx, fx - p, fx),
        ),
    )

    result["SELTZO-TwoSum-ONE1-ONE1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_one1, ey == fx, ex > fy + p),
        seltzo_case(
            (sx, 0, 0, ex, ex - p, ex),
            (sy, 0, 0, fy, fy - p, fy),
        ),
    )
    result["SELTZO-TwoSum-ONE1-ONE1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_one1, ex == fy, ey > fx + p),
        seltzo_case(
            (sy, 0, 0, ey, ey - p, ey),
            (sx, 0, 0, fx, fx - p, fx),
        ),
    )

    result["SELTZO-TwoSum-MM10-POW2-S1-X"] = z3.Implies(
        z3.And(same_sign, x_mm10, y_pow2, ex == ey + one, ex == fx + two),
        seltzo_case_zero((sx, 1, 1, ex, gx, gx)),
    )
    result["SELTZO-TwoSum-MM10-POW2-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_mm10, x_pow2, ey == ex + one, ey == fy + two),
        seltzo_case_zero((sy, 1, 1, ey, gy, gy)),
    )

    result["SELTZO-TwoSum-POW2-ONE0-S1-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_one0, ex > ey + one, ex < fy + (p - one)),
        seltzo_case(
            (sx, 0, 0, ex, ey, fy),
            ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-ONE0-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_one0, ey > ex + one, ey < fx + (p - one)),
        seltzo_case(
            (sy, 0, 0, ey, ex, fx),
            ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-ONE1-ALL1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_all1, ex == ey + two, ey > fx),
        seltzo_case(
            (sx, 0, 0, ex - one, fx, fx),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-ONE1-ALL1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_all1, ey == ex + two, ex > fy),
        seltzo_case(
            (sy, 0, 0, ey - one, fy, fy),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-R0R1-D1-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_pow2,
            y_r0r1,
            ex == ey + (p + one),
            ey > fy + two,
            ey < fy + (p - one),
        ),
        seltzo_case(
            (sx, 1, 1, ex - one, ey, ex - one),
            ((sy,), 1, 0, ey - one, fy, ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_pow2,
            x_r0r1,
            ey == ex + (p + one),
            ex > fx + two,
            ex < fx + (p - one),
        ),
        seltzo_case(
            (sy, 1, 1, ey - one, ex, ey - one),
            ((sx,), 1, 0, ex - one, fx, ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-R0R1-R0R1-D1-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_r0r1,
            y_r0r1,
            ex == ey + (p - one),
            ex == fx + (p - two),
            ey < fy + (p - one),
        ),
        seltzo_case(
            (sx, 0, 0, ex, fx, fx),
            (sy, 1, 0, fy, ey - p, ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-R0R1-R0R1-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_r0r1,
            x_r0r1,
            ey == ex + (p - one),
            ey == fy + (p - two),
            ex < fx + (p - one),
        ),
        seltzo_case(
            (sy, 0, 0, ey, fy, fy),
            (sx, 1, 0, fx, ex - p, ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-R1R0-ONE1-S2-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, y_one1, ex > fy + p - two, gx == ey),
        seltzo_case(
            (sx, 0, 0, ex + one, ex - (p - one), ex + one),
            (sy, 0, 0, fy, fy - p, fy),
        ),
    )
    result["SELTZO-TwoSum-R1R0-ONE1-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_one1, ey > fx + p - two, gy == ex),
        seltzo_case(
            (sy, 0, 0, ey + one, ey - (p - one), ey + one),
            (sx, 0, 0, fx, fx - p, fx),
        ),
    )

    result["SELTZO-TwoSum-ONE1-R1R0-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_r1r0, fx == ey, ex > fy + p + one),
        seltzo_case(
            (sx, 1, 0, ex - one, fx - one, gx),
            ((sy,), 0, 0, gy, gy - p, gy),
        ),
    )
    result["SELTZO-TwoSum-ONE1-R1R0-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_r1r0, fy == ex, ey > fx + p + one),
        seltzo_case(
            (sy, 1, 0, ey - one, fy - one, gy),
            ((sx,), 0, 0, gx, gx - p, gx),
        ),
    )

    result["SELTZO-TwoSum-POW2-R0R1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_r0r1, ex == ey + (p + one), ey == fy + two),
        seltzo_case(
            (sx, 1, 1, ex - one, ey, ex - one),
            ((sy,), 0, 0, ey - one, ey - (p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_r0r1, ey == ex + (p + one), ex == fx + two),
        seltzo_case(
            (sy, 1, 1, ey - one, ex, ey - one),
            ((sx,), 0, 0, ex - one, ex - (p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-POW2-R0R1-D3-X"] = z3.Implies(
        z3.And(
            diff_sign, x_pow2, y_r0r1, ex > ey + one, ex < ey + p, ey == fy + (p - one)
        ),
        seltzo_case(
            (sx, 1, 0, ex - one, ey - one, ey),
            (sy, 0, 0, fy, fy - p, fy),
        ),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D3-Y"] = z3.Implies(
        z3.And(
            diff_sign, y_pow2, x_r0r1, ey > ex + one, ey < ex + p, ex == fx + (p - one)
        ),
        seltzo_case(
            (sy, 1, 0, ey - one, ex - one, ex),
            (sx, 0, 0, fx, fx - p, fx),
        ),
    )

    result["SELTZO-TwoSum-ALL1-TWO1-S1-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_two1, ex == ey + (p - one)),
        seltzo_case(
            (sx, 0, 0, ex + one, ey, ex + one),
            (sy, 1, 0, fy, fy - two, fy - one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-TWO1-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_two1, ey == ex + (p - one)),
        seltzo_case(
            (sy, 0, 0, ey + one, ex, ey + one),
            (sx, 1, 0, fx, fx - two, fx - one),
        ),
    )

    result["SELTZO-TwoSum-ONE1-TWO1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_two1, ex == fy + p, fx == ey),
        seltzo_case(
            (sx, 1, 0, ex - one, ex - p, ex - (p - one)),
            ((sy,), 0, 0, gy, gy - p, gy),
        ),
    )
    result["SELTZO-TwoSum-ONE1-TWO1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_two1, ey == fx + p, fy == ex),
        seltzo_case(
            (sy, 1, 0, ey - one, ey - p, ey - (p - one)),
            ((sx,), 0, 0, gx, gx - p, gx),
        ),
    )

    result["SELTZO-TwoSum-MM01-ONE1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_mm01, y_one1, ex == ey + p),
        seltzo_case(
            (sx, 1, 1, ex, fx, gx),
            ((sy,), 1, 0, ey - one, fy - one, gy),
        ),
    )
    result["SELTZO-TwoSum-MM01-ONE1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_mm01, x_one1, ey == ex + p),
        seltzo_case(
            (sy, 1, 1, ey, fy, gy),
            ((sx,), 1, 0, ex - one, fx - one, gx),
        ),
    )

    result["SELTZO-TwoSum-POW2-G01-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g01, ex == ey + (p + one), ey > fy + two),
        seltzo_case(
            (sx, 1, 1, ex - one, ey, ex - one),
            ((sy,), 1, 0, ey - one, fy, ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G01-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g01, ey == ex + (p + one), ex > fx + two),
        seltzo_case(
            (sy, 1, 1, ey - one, ex, ey - one),
            ((sx,), 1, 0, ex - one, fx, ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-POW2-ONE0-S2-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_one0, ex == ey + two, ex == fy + p),
        seltzo_case(
            (sx, 0, 1, ex, ey, ey + one),
            (sy, 0, 0, fx - one, fx - (p + one), fx - one),
        ),
    )
    result["SELTZO-TwoSum-POW2-ONE0-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_one0, ey == ex + two, ey == fx + p),
        seltzo_case(
            (sy, 0, 1, ey, ex, ex + one),
            (sx, 0, 0, fy - one, fy - (p + one), fy - one),
        ),
    )

    ############################################################################

    fs: IntVar = es - (nlbs + one)
    fe: IntVar = ee - (nlbe + one)

    f0s: IntVar = es - z3_If(lbs, nlbs + one, one)
    f0e: IntVar = ee - z3_If(lbe, nlbe + one, one)

    f1s: IntVar = es - z3_If(lbs, one, nlbs + one)
    f1e: IntVar = ee - z3_If(lbe, one, nlbe + one)

    gs: IntVar = es - (p - (ntbs + one))
    ge: IntVar = ee - (p - (ntbe + one))

    g0s: IntVar = es - (p - z3_If(tbs, ntbs + one, one))
    g0e: IntVar = ee - (p - z3_If(tbe, ntbe + one, one))

    g1s: IntVar = es - (p - z3_If(tbs, one, ntbs + one))
    g1e: IntVar = ee - (p - z3_If(tbe, one, ntbe + one))

    s_pow2: z3.BoolRef = z3.And(~s_zero, ~lbs, ~tbs, nlbs == p - one, ntbs == p - one)
    e_pow2: z3.BoolRef = z3.And(~e_zero, ~lbe, ~tbe, nlbe == p - one, ntbe == p - one)

    s_all1: z3.BoolRef = z3.And(lbs, tbs, nlbs == p - one, ntbs == p - one)
    e_all1: z3.BoolRef = z3.And(lbe, tbe, nlbe == p - one, ntbe == p - one)

    s_one0: z3.BoolRef = z3.And(lbs, tbs, nlbs + ntbs == p - two)
    e_one0: z3.BoolRef = z3.And(lbe, tbe, nlbe + ntbe == p - two)

    s_one1: z3.BoolRef = z3.And(~lbs, ~tbs, nlbs + ntbs == p - two)
    e_one1: z3.BoolRef = z3.And(~lbe, ~tbe, nlbe + ntbe == p - two)

    s_r0r1: z3.BoolRef = z3.And(~lbs, tbs, nlbs + ntbs == p - one)
    e_r0r1: z3.BoolRef = z3.And(~lbe, tbe, nlbe + ntbe == p - one)

    s_r1r0: z3.BoolRef = z3.And(lbs, ~tbs, nlbs + ntbs == p - one)
    e_r1r0: z3.BoolRef = z3.And(lbe, ~tbe, nlbe + ntbe == p - one)

    s_mm01: z3.BoolRef = z3.And(lbs, ~tbs, nlbs + ntbs == p - three)
    e_mm01: z3.BoolRef = z3.And(lbe, ~tbe, nlbe + ntbe == p - three)

    s_mm10: z3.BoolRef = z3.And(~lbs, tbs, nlbs + ntbs == p - three)
    e_mm10: z3.BoolRef = z3.And(~lbe, tbe, nlbe + ntbe == p - three)

    ############################################################# PARTIAL LEMMAS

    # Lemma P01A: Addition either preserves the exponent of the larger addend,
    # in which case the sum has at least as many leading ones as that addend,
    # or increases the exponent by one, in which case the sum must have leading
    # zeros in the exponent gap.
    result["SELTZO-TwoSum-P01A-X"] = z3.Implies(
        z3.And(same_sign, ex >= ey),
        z3.Or(
            z3.And(es == ex, f0s <= f0x),
            z3.And(es == ex + one, f1s <= ey + one),
        ),
    )
    result["SELTZO-TwoSum-P01A-Y"] = z3.Implies(
        z3.And(same_sign, ey >= ex),
        z3.Or(
            z3.And(es == ey, f0s <= f0y),
            z3.And(es == ey + one, f1s <= ex + one),
        ),
    )

    # Lemma P01B: Subtraction either preserves the exponent of the minuend,
    # in which case the difference has at least as many leading zeros as the
    # minuend, or decreases the exponent, in which case the difference must
    # have leading ones in the exponent gap.
    result["SELTZO-TwoSum-P01B-X"] = z3.Implies(
        z3.And(diff_sign, ex >= ey),
        z3.Or(
            z3.And(es == ex, f1s <= f1x),
            z3.And(es < ex, f0s <= ey),
        ),
    )
    result["SELTZO-TwoSum-P01B-Y"] = z3.Implies(
        z3.And(diff_sign, ey >= ex),
        z3.Or(
            z3.And(es == ey, f1s <= f1y),
            z3.And(es < ey, f0s <= ex),
        ),
    )

    # Lemma P02A: A zero between the exponents of the addends
    # insulates the exponent of the sum from increasing.
    result["SELTZO-TwoSum-P02A-X"] = z3.Implies(
        z3.And(same_sign, f0x > ey, xy_nonzero),
        z3.And(ss == sx, es == ex, f1s >= ey),
    )
    result["SELTZO-TwoSum-P02A-Y"] = z3.Implies(
        z3.And(same_sign, f0y > ex, xy_nonzero),
        z3.And(ss == sy, es == ey, f1s >= ex),
    )

    # Lemma P02B: A one between the exponents of the minuend and subtrahend
    # insulates the exponent of the difference from decreasing.
    result["SELTZO-TwoSum-P02B-X"] = z3.Implies(
        z3.And(diff_sign, f1x > ey, xy_nonzero, z3.Not(x_pow2)),
        z3.And(ss == sx, es == ex, f0s >= ey),
    )
    result["SELTZO-TwoSum-P02B-Y"] = z3.Implies(
        z3.And(diff_sign, f1y > ex, xy_nonzero, z3.Not(y_pow2)),
        z3.And(ss == sy, es == ey, f0s >= ex),
    )

    # Lemma P03A: Adding into leading zeros preserves the exponent.
    result["SELTZO-TwoSum-P03A-X"] = z3.Implies(
        z3.And(same_sign, ex > ey + one, ey + one > f1x),
        z3.And(ss == sx, es == ex, f1s <= ey + one),
    )
    result["SELTZO-TwoSum-P03A-Y"] = z3.Implies(
        z3.And(same_sign, ey > ex + one, ex + one > f1y),
        z3.And(ss == sy, es == ey, f1s <= ex + one),
    )

    # Lemma P03B: Subtracting from leading ones preserves the exponent.
    result["SELTZO-TwoSum-P03B-X"] = z3.Implies(
        z3.And(diff_sign, ex > ey + one, ey + one > f0x),
        z3.And(ss == sx, es == ex, f0s <= ey + one),
    )
    result["SELTZO-TwoSum-P03B-Y"] = z3.Implies(
        z3.And(diff_sign, ey > ex + one, ex + one > f0y),
        z3.And(ss == sy, es == ey, f0s <= ex + one),
    )

    # Lemma P04A: Adding into leading ones increases the exponent.
    result["SELTZO-TwoSum-P04A-X"] = z3.Implies(
        z3.And(same_sign, ex >= ey, ey > f0x, xy_nonzero),
        z3.And(ss == sx, es == ex + one, f1s <= ey),
    )
    result["SELTZO-TwoSum-P04A-Y"] = z3.Implies(
        z3.And(same_sign, ey >= ex, ex > f0y, xy_nonzero),
        z3.And(ss == sy, es == ey + one, f1s <= ex),
    )

    # Lemma P04B: Subtracting from leading zeros decreases the exponent.
    result["SELTZO-TwoSum-P04B-X"] = z3.Implies(
        z3.And(diff_sign, ex > ey + one, ey > f1x, xy_nonzero),
        z3.And(ss == sx, es == ex - one, f0s <= ey),
    )
    result["SELTZO-TwoSum-P04B-Y"] = z3.Implies(
        z3.And(diff_sign, ey > ex + one, ex > f1y, xy_nonzero),
        z3.And(ss == sy, es == ey - one, f0s <= ex),
    )

    # Lemma T01A: Adding a power of two into a leading zero bit.
    # This should eventually be replaced by complete case-by-case lemmas.
    result["SELTZO-TwoSum-T01A-X"] = z3.Implies(
        z3.And(same_sign, ex == ey + one, ~lbx, ntbx < p - two, y_pow2),
        z3.And(ss == sx, lbs, tbs == tbx, es == ex, ntbs == ntbx, e_pos_zero),
    )
    result["SELTZO-TwoSum-T01A-Y"] = z3.Implies(
        z3.And(same_sign, ey == ex + one, ~lby, ntby < p - two, x_pow2),
        z3.And(ss == sy, lbs, tbs == tby, es == ey, ntbs == ntby, e_pos_zero),
    )

    # Lemma T01B: Subtracting a power of two from a leading one bit.
    # This should eventually be replaced by complete case-by-case lemmas.
    result["SELTZO-TwoSum-T01B-X"] = z3.Implies(
        z3.And(diff_sign, ex == ey + one, lbx, ntbx < p - two, y_pow2),
        z3.And(ss == sx, ~lbs, tbs == tbx, es == ex, ntbs == ntbx, e_pos_zero),
    )
    result["SELTZO-TwoSum-T01B-Y"] = z3.Implies(
        z3.And(diff_sign, ey == ex + one, lby, ntby < p - two, x_pow2),
        z3.And(ss == sy, ~lbs, tbs == tby, es == ey, ntbs == ntby, e_pos_zero),
    )

    return result
