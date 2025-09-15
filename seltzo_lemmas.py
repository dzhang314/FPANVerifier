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
            tuple[IntVar, IntVar] | IntVar | None,
            tuple[IntVar, IntVar] | IntVar | None,
            tuple[IntVar, IntVar] | IntVar | None,
        ],
        e_values: tuple[
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
        seltzo_case_helper(clauses, (se, lbe, tbe, ee, nlbe, ntbe), e_values)
        return z3.And(*clauses)

    ############################################################# LEMMA FAMILY L

    # Lemmas in family L apply to situations where the smaller addend
    # fits entirely inside the leading bits of the larger addend.

    # Larger addend is a power of two (general case).
    result["SELTZO-TwoSum-LS-POW2-G-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, x_pow2, ~tby, ex > ey + one, gy > fx + one),
        seltzo_case_zero((sx, 0, 0, ex, ey, gy)),
    )
    result["SELTZO-TwoSum-LS-POW2-G-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, y_pow2, ~tbx, ey > ex + one, gx > fy + one),
        seltzo_case_zero((sy, 0, 0, ey, ex, gx)),
    )

    # Larger addend is a power of two (adjacent case 1).
    result["SELTZO-TwoSum-LS-POW2-A1-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, x_pow2, lby, ~tby, ex == ey + one, gy > fx + one),
        seltzo_case_zero((sx, 1, 0, ex, fy, gy)),
    )
    result["SELTZO-TwoSum-LS-POW2-A1-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, y_pow2, lbx, ~tbx, ey == ex + one, gx > fy + one),
        seltzo_case_zero((sy, 1, 0, ey, fx, gx)),
    )

    # Larger addend is a power of two (adjacent case 2).
    result["SELTZO-TwoSum-LS-POW2-A2-X"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, x_pow2, ~lby, ~tby, ex == ey + one, gy > fx + one
        ),
        seltzo_case_zero((sx, 1, 0, ex, ey - one, gy)),
    )
    result["SELTZO-TwoSum-LS-POW2-A2-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, y_pow2, ~lbx, ~tbx, ey == ex + one, gx > fy + one
        ),
        seltzo_case_zero((sy, 1, 0, ey, ex - one, gx)),
    )

    # Larger addend has trailing zeros (general case).
    result["SELTZO-TwoSum-LS-T0-G-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ~lbx,
            ~tbx,
            ~x_pow2,
            ~tby,
            ex > ey + one,
            gy > fx + one,
        ),
        seltzo_case_zero((sx, 0, 0, ex, ey, gx)),
    )
    result["SELTZO-TwoSum-LS-T0-G-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ~lby,
            ~tby,
            ~y_pow2,
            ~tbx,
            ey > ex + one,
            gx > fy + one,
        ),
        seltzo_case_zero((sy, 0, 0, ey, ex, gy)),
    )

    # Larger addend has trailing zeros (adjacent case 1).
    result["SELTZO-TwoSum-LS-T0-A1-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ~lbx,
            ~tbx,
            ~x_pow2,
            lby,
            ~tby,
            ex == ey + one,
            gy > fx + one,
        ),
        seltzo_case_zero((sx, 1, 0, ex, fy, gx)),
    )
    result["SELTZO-TwoSum-LS-T0-A1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ~lby,
            ~tby,
            ~y_pow2,
            lbx,
            ~tbx,
            ey == ex + one,
            gx > fy + one,
        ),
        seltzo_case_zero((sy, 1, 0, ey, fx, gy)),
    )

    # Larger addend has trailing zeros (adjacent case 2).
    result["SELTZO-TwoSum-LS-T0-A2-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ~lbx,
            ~tbx,
            ~x_pow2,
            ~lby,
            ~tby,
            ex == ey + one,
            gy > fx + one,
        ),
        seltzo_case_zero((sx, 1, 0, ex, ey - one, gx)),
    )
    result["SELTZO-TwoSum-LS-T0-A2-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ~lby,
            ~tby,
            ~y_pow2,
            ~lbx,
            ~tbx,
            ey == ex + one,
            gx > fy + one,
        ),
        seltzo_case_zero((sy, 1, 0, ey, ex - one, gy)),
    )

    # Larger addend has trailing ones (general case).
    result["SELTZO-TwoSum-LS-T1-G-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ~lbx, tbx, ~tby, ex > ey + one, gy > fx + one),
        seltzo_case_zero((sx, 0, 1, ex, ey, gx)),
    )
    result["SELTZO-TwoSum-LS-T1-G-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ~lby, tby, ~tbx, ey > ex + one, gx > fy + one),
        seltzo_case_zero((sy, 0, 1, ey, ex, gy)),
    )

    # Larger addend has trailing ones (adjacent case 1).
    result["SELTZO-TwoSum-LS-T1-A1-X"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ~lbx, tbx, lby, ~tby, ex == ey + one, gy > fx + one
        ),
        seltzo_case_zero((sx, 1, 1, ex, fy, gx)),
    )
    result["SELTZO-TwoSum-LS-T1-A1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ~lby, tby, lbx, ~tbx, ey == ex + one, gx > fy + one
        ),
        seltzo_case_zero((sy, 1, 1, ey, fx, gy)),
    )

    # Larger addend has trailing ones (adjacent case 2).
    result["SELTZO-TwoSum-LS-T1-A2-X"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ~lbx, tbx, ~lby, ~tby, ex == ey + one, gy > fx + one
        ),
        seltzo_case_zero((sx, 1, 1, ex, ey - one, gx)),
    )
    result["SELTZO-TwoSum-LS-T1-A2-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ~lby, tby, ~lbx, ~tbx, ey == ex + one, gx > fy + one
        ),
        seltzo_case_zero((sy, 1, 1, ey, ex - one, gy)),
    )

    # Larger addend is an all-ones number (general case).
    result["SELTZO-TwoSum-LD-ALL1-G-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, x_all1, ~tby, ex > ey + one, gy > fx + one),
        seltzo_case_zero((sx, 1, 1, ex, ey, gy)),
    )
    result["SELTZO-TwoSum-LD-ALL1-G-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, y_all1, ~tbx, ey > ex + one, gx > fy + one),
        seltzo_case_zero((sy, 1, 1, ey, ex, gx)),
    )

    # Larger addend is an all-ones number (adjacent case 1).
    result["SELTZO-TwoSum-LD-ALL1-A1-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, x_all1, lby, ~tby, ex == ey + one, gy > fx + one),
        seltzo_case_zero((sx, 0, 1, ex, fy, gy)),
    )
    result["SELTZO-TwoSum-LD-ALL1-A1-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, y_all1, lbx, ~tbx, ey == ex + one, gx > fy + one),
        seltzo_case_zero((sy, 0, 1, ey, fx, gx)),
    )

    # Larger addend is an all-ones number (adjacent case 2).
    result["SELTZO-TwoSum-LD-ALL1-A2-X"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, x_all1, ~lby, ~tby, ex == ey + one, gy > fx + one
        ),
        seltzo_case_zero((sx, 0, 1, ex, ey - one, gy)),
    )
    result["SELTZO-TwoSum-LD-ALL1-A2-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, y_all1, ~lbx, ~tbx, ey == ex + one, gx > fy + one
        ),
        seltzo_case_zero((sy, 0, 1, ey, ex - one, gx)),
    )

    # Larger addend has trailing zeros (general case).
    result["SELTZO-TwoSum-LD-T0-G-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, lbx, ~tbx, ~tby, ex > ey + one, gy > fx + one),
        seltzo_case_zero((sx, 1, 0, ex, ey, gx)),
    )
    result["SELTZO-TwoSum-LD-T0-G-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, lby, ~tby, ~tbx, ey > ex + one, gx > fy + one),
        seltzo_case_zero((sy, 1, 0, ey, ex, gy)),
    )

    # Larger addend has trailing zeros (adjacent case 1).
    result["SELTZO-TwoSum-LD-T0-A1-X"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, lbx, ~tbx, lby, ~tby, ex == ey + one, gy > fx + one
        ),
        seltzo_case_zero((sx, 0, 0, ex, fy, gx)),
    )
    result["SELTZO-TwoSum-LD-T0-A1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, lby, ~tby, lbx, ~tbx, ey == ex + one, gx > fy + one
        ),
        seltzo_case_zero((sy, 0, 0, ey, fx, gy)),
    )

    # Larger addend has trailing zeros (adjacent case 2).
    result["SELTZO-TwoSum-LD-T0-A2-X"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, lbx, ~tbx, ~lby, ~tby, ex == ey + one, gy > fx + one
        ),
        seltzo_case_zero((sx, 0, 0, ex, ey - one, gx)),
    )
    result["SELTZO-TwoSum-LD-T0-A2-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, lby, ~tby, ~lbx, ~tbx, ey == ex + one, gx > fy + one
        ),
        seltzo_case_zero((sy, 0, 0, ey, ex - one, gy)),
    )

    # Larger addend has trailing ones (general case).
    result["SELTZO-TwoSum-LD-T1-G-X"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, lbx, tbx, ~x_all1, ~tby, ex > ey + one, gy > fx + one
        ),
        seltzo_case_zero((sx, 1, 1, ex, ey, gx)),
    )
    result["SELTZO-TwoSum-LD-T1-G-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, lby, tby, ~y_all1, ~tbx, ey > ex + one, gx > fy + one
        ),
        seltzo_case_zero((sy, 1, 1, ey, ex, gy)),
    )

    # Larger addend has trailing ones (adjacent case 1).
    result["SELTZO-TwoSum-LD-T1-A1-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            diff_sign,
            lbx,
            tbx,
            ~x_all1,
            lby,
            ~tby,
            ex == ey + one,
            gy > fx + one,
        ),
        seltzo_case_zero((sx, 0, 1, ex, fy, gx)),
    )
    result["SELTZO-TwoSum-LD-T1-A1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            diff_sign,
            lby,
            tby,
            ~y_all1,
            lbx,
            ~tbx,
            ey == ex + one,
            gx > fy + one,
        ),
        seltzo_case_zero((sy, 0, 1, ey, fx, gy)),
    )

    # Larger addend has trailing ones (adjacent case 2).
    result["SELTZO-TwoSum-LD-T1-A2-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            diff_sign,
            lbx,
            tbx,
            ~x_all1,
            ~lby,
            ~tby,
            ex == ey + one,
            gy > fx + one,
        ),
        seltzo_case_zero((sx, 0, 1, ex, ey - one, gx)),
    )
    result["SELTZO-TwoSum-LD-T1-A2-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            diff_sign,
            lby,
            tby,
            ~y_all1,
            ~lbx,
            ~tbx,
            ey == ex + one,
            gx > fy + one,
        ),
        seltzo_case_zero((sy, 0, 1, ey, ex - one, gy)),
    )

    ################################################### LEMMA FAMILY POW2-POW2-S

    # Sum of two powers of two (equal exponent case).
    result["SELTZO-TwoSum-POW2-POW2-SE"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_pow2, ex == ey),
        seltzo_case_zero((sx, 0, 0, ex + one, fx + one, gx + one)),
    )

    # Sum of two powers of two (boundary case).
    result["SELTZO-TwoSum-POW2-POW2-SB-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_pow2, ex == ey + (p - one)),
        seltzo_case_zero((sx, 0, 1, ex, ey, ey + one)),
    )
    result["SELTZO-TwoSum-POW2-POW2-SB-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_pow2, ey == ex + (p - one)),
        seltzo_case_zero((sy, 0, 1, ey, ex, ex + one)),
    )

    # Remaining POW2-POW2-S lemmas have been subsumed by L lemmas.

    ################################################### LEMMA FAMILY POW2-POW2-D

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

    result["SELTZO-TwoSum-ALL1-POW2-SB1-X"] = z3.Implies(
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

    result["SELTZO-TwoSum-ONE1-R1R0-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_r1r0, fx == ey, ex == gy + p),
        seltzo_case_zero((sx, 1, 1, ex - one, ey - one, ex - (p - one))),
    )
    result["SELTZO-TwoSum-ONE1-R1R0-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_r1r0, fy == ex, ey == gx + p),
        seltzo_case_zero((sy, 1, 1, ey - one, ex - one, ey - (p - one))),
    )

    result["SELTZO-TwoSum-POW2-R1R0-S1-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_r1r0, ex == ey + p),
        seltzo_case(
            (sx, 0, 1, ex, ex - (p - one), ex - (p - two)),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-POW2-R1R0-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_r1r0, ey == ex + p),
        seltzo_case(
            (sy, 0, 1, ey, ey - (p - one), ey - (p - two)),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
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
            (sx, 0, 1, ex, ey + one, ey + two), ((sy,), 1, 0, ey - one, fy - one, fy)
        ),
    )
    result["SELTZO-TwoSum-POW2-ONE1-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_one1, ey == ex + p),
        seltzo_case(
            (sy, 0, 1, ey, ex + one, ex + two), ((sx,), 1, 0, ex - one, fx - one, fx)
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
        seltzo_case((sx, 0, 1, ex, ey, ey + one), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-POW2-ONE1-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_one1, ey == ex + (p - one)),
        seltzo_case((sy, 0, 1, ey, ex, ex + one), (sx, 0, 0, fx, fx - p, fx)),
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
        seltzo_case((sx, 1, 1, ex, ex - p, ex), ((sy,), 1, 0, ey - one, fy - one, gy)),
    )
    result["SELTZO-TwoSum-R1R0-ONE1-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_one1, ey == ex + p, ey == fy + (p - one)),
        seltzo_case((sy, 1, 1, ey, ey - p, ey), ((sx,), 1, 0, ex - one, fx - one, gx)),
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
        seltzo_case((sx, 1, 0, ex, fx, ey + one), (sy, 0, 0, fy, fy - p, fy)),
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
        seltzo_case((sy, 1, 0, ey, fy, ex + one), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-R1R0-R1R0-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_r1r0, ex == ey + p, ex > fx + two),
        seltzo_case((sx, 1, 1, ex, gx, gx), ((sy,), 0, 0, gy, fy - (p - one), gy)),
    )
    result["SELTZO-TwoSum-R1R0-R1R0-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_r1r0, ey == ex + p, ey > fy + two),
        seltzo_case((sy, 1, 1, ey, gy, gy), ((sx,), 0, 0, gx, fx - (p - one), gx)),
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
            (sx, 1, 0, ex - one, ey, gx), ((sy,), 0, 0, gy, fy - (p - one), gy)
        ),
    )
    result["SELTZO-TwoSum-ONE1-R1R0-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_r1r0, ex > fy, ey > fx + (p + one)),
        seltzo_case(
            (sy, 1, 0, ey - one, ex, gy), ((sx,), 0, 0, gx, fx - (p - one), gx)
        ),
    )

    result["SELTZO-TwoSum-R1R0-ONE1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_one1, ex == ey + p, ex > fx + two),
        seltzo_case(
            (sx, 1, 1, ex, fx + one, gx), ((sy,), 1, 0, ey - one, fy - one, gy)
        ),
    )
    result["SELTZO-TwoSum-R1R0-ONE1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_one1, ey == ex + p, ey > fy + two),
        seltzo_case(
            (sy, 1, 1, ey, fy + one, gy), ((sx,), 1, 0, ex - one, fx - one, gx)
        ),
    )

    result["SELTZO-TwoSum-ALL1-ONE1-S1-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_one1, ex == ey + (p - one)),
        seltzo_case(
            (sx, 0, 0, ex + one, ex - (p - one), ex + one), (sy, 0, 0, fy, fy - p, fy)
        ),
    )
    result["SELTZO-TwoSum-ALL1-ONE1-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_one1, ey == ex + (p - one)),
        seltzo_case(
            (sy, 0, 0, ey + one, ey - (p - one), ey + one), (sx, 0, 0, fx, fx - p, fx)
        ),
    )

    result["SELTZO-TwoSum-ONE1-ONE1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_one1, ey == fx, ex > fy + p),
        seltzo_case((sx, 0, 0, ex, ex - p, ex), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-ONE1-ONE1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_one1, ex == fy, ey > fx + p),
        seltzo_case((sy, 0, 0, ey, ey - p, ey), (sx, 0, 0, fx, fx - p, fx)),
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
        seltzo_case((sx, 0, 0, ex, fx, fx), (sy, 1, 0, fy, ey - p, ey - (p - one))),
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
        seltzo_case((sy, 0, 0, ey, fy, fy), (sx, 1, 0, fx, ex - p, ex - (p - one))),
    )

    result["SELTZO-TwoSum-R1R0-ONE1-S2-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, y_one1, ex > fy + p - two, gx == ey),
        seltzo_case(
            (sx, 0, 0, ex + one, ex - (p - one), ex + one), (sy, 0, 0, fy, fy - p, fy)
        ),
    )
    result["SELTZO-TwoSum-R1R0-ONE1-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_one1, ey > fx + p - two, gy == ex),
        seltzo_case(
            (sy, 0, 0, ey + one, ey - (p - one), ey + one), (sx, 0, 0, fx, fx - p, fx)
        ),
    )

    result["SELTZO-TwoSum-ONE1-R1R0-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_r1r0, fx == ey, ex > fy + (p + one)),
        seltzo_case((sx, 1, 0, ex - one, fx - one, gx), ((sy,), 0, 0, gy, gy - p, gy)),
    )
    result["SELTZO-TwoSum-ONE1-R1R0-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_r1r0, fy == ex, ey > fx + (p + one)),
        seltzo_case((sy, 1, 0, ey - one, fy - one, gy), ((sx,), 0, 0, gx, gx - p, gx)),
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
        seltzo_case((sx, 1, 0, ex - one, ey - one, ey), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D3-Y"] = z3.Implies(
        z3.And(
            diff_sign, y_pow2, x_r0r1, ey > ex + one, ey < ex + p, ex == fx + (p - one)
        ),
        seltzo_case((sy, 1, 0, ey - one, ex - one, ex), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-ALL1-TWO1-S1-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_two1, ex == ey + (p - one)),
        seltzo_case(
            (sx, 0, 0, ex + one, ey, ex + one), (sy, 1, 0, fy, fy - two, fy - one)
        ),
    )
    result["SELTZO-TwoSum-ALL1-TWO1-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_two1, ey == ex + (p - one)),
        seltzo_case(
            (sy, 0, 0, ey + one, ex, ey + one), (sx, 1, 0, fx, fx - two, fx - one)
        ),
    )

    result["SELTZO-TwoSum-ONE1-TWO1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_two1, ex == fy + p, fx == ey),
        seltzo_case(
            (sx, 1, 0, ex - one, ex - p, ex - (p - one)), ((sy,), 0, 0, gy, gy - p, gy)
        ),
    )
    result["SELTZO-TwoSum-ONE1-TWO1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_two1, ey == fx + p, fy == ex),
        seltzo_case(
            (sy, 1, 0, ey - one, ey - p, ey - (p - one)), ((sx,), 0, 0, gx, gx - p, gx)
        ),
    )

    result["SELTZO-TwoSum-MM01-ONE1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_mm01, y_one1, ex == ey + p),
        seltzo_case((sx, 1, 1, ex, fx, gx), ((sy,), 1, 0, ey - one, fy - one, gy)),
    )
    result["SELTZO-TwoSum-MM01-ONE1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_mm01, x_one1, ey == ex + p),
        seltzo_case((sy, 1, 1, ey, fy, gy), ((sx,), 1, 0, ex - one, fx - one, gx)),
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
            (sx, 0, 1, ex, ey, ey + one), (sy, 0, 0, fx - one, fx - (p + one), fx - one)
        ),
    )
    result["SELTZO-TwoSum-POW2-ONE0-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_one0, ey == ex + two, ey == fx + p),
        seltzo_case(
            (sy, 0, 1, ey, ex, ex + one), (sx, 0, 0, fy - one, fy - (p + one), fy - one)
        ),
    )

    result["SELTZO-TwoSum-POW2-R0R1-S1-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_r0r1, ex > ey + one, ex < fy + p),
        seltzo_case(
            (sx, 0, 0, ex, ey, gy),
            ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_r0r1, ey > ex + one, ey < fx + p),
        seltzo_case(
            (sy, 0, 0, ey, ex, gx),
            ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-R0R1-ONE1-S1-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r0r1,
            y_one1,
            ex == ey + one,
            ex == fx + (p - one),
            ey == fy + (p - three),
        ),
        seltzo_case_zero((sx, 1, 1, ex, ex - two, ex - (p - three))),
    )
    result["SELTZO-TwoSum-R0R1-ONE1-S1-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r0r1,
            x_one1,
            ey == ex + one,
            ey == fy + (p - one),
            ex == fx + (p - three),
        ),
        seltzo_case_zero((sy, 1, 1, ey, ey - two, ey - (p - three))),
    )

    result["SELTZO-TwoSum-R0R1-ONE1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_r0r1, y_one1, ex == ey + (p - one), fx == ey),
        seltzo_case((sx, 0, 0, ex, ex - p, ex), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-R0R1-ONE1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_r0r1, x_one1, ey == ex + (p - one), fy == ex),
        seltzo_case((sy, 0, 0, ey, ey - p, ey), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-R1R0-R0R1-D1-X"] = z3.Implies(
        z3.And(
            diff_sign, x_r1r0, y_r0r1, ex == ey + p, ex > gx + one, ey == fy + (p - one)
        ),
        seltzo_case((sx, 1, 1, ex, gx, gx), ((sy,), 1, 0, ey - one, fy - one, fy)),
    )
    result["SELTZO-TwoSum-R1R0-R0R1-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign, y_r1r0, x_r0r1, ey == ex + p, ey > gy + one, ex == fx + (p - one)
        ),
        seltzo_case((sy, 1, 1, ey, gy, gy), ((sx,), 1, 0, ex - one, fx - one, fx)),
    )

    result["SELTZO-TwoSum-G01-POW2-S1-X"] = z3.Implies(
        z3.And(same_sign, x_g01, y_pow2, ex == ey, ex < gx + (p - two)),
        seltzo_case(
            (sx, 0, 0, ex + one, fx, gx),
            ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-G01-POW2-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_g01, x_pow2, ey == ex, ey < gy + (p - two)),
        seltzo_case(
            (sy, 0, 0, ey + one, fy, gy),
            ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-G10-MM10-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_g10, y_mm10, ex == ey + (p - one), ey == gy + (p - three)),
        seltzo_case((sx, 1, 1, ex, fx, gx), (sy, 0, 0, gy + one, gy - one, gy - two)),
    )
    result["SELTZO-TwoSum-G10-MM10-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_g10, x_mm10, ey == ex + (p - one), ex == gx + (p - three)),
        seltzo_case((sy, 1, 1, ey, fy, gy), (sx, 0, 0, gx + one, gx - one, gx - two)),
    )

    result["SELTZO-TwoSum-MM01-R1R0-S1-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_mm01,
            y_r1r0,
            ex < ey + (p - three),
            ey == fx,
            ex > fy + (p - one),
        ),
        seltzo_case((sx, 0, 0, ex + one, gx, gx), ((sy,), 0, 0, gy, gy - p, gy)),
    )
    result["SELTZO-TwoSum-MM01-R1R0-S1-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_mm01,
            x_r1r0,
            ey < ex + (p - three),
            ex == fy,
            ey > fx + (p - one),
        ),
        seltzo_case((sy, 0, 0, ey + one, gy, gy), ((sx,), 0, 0, gx, gx - p, gx)),
    )

    result["SELTZO-TwoSum-POW2-R1R0-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_r1r0, ex == ey + (p - one), ey == fy + two),
        seltzo_case_zero((sx, 1, 1, ex - one, ey, ey)),
    )
    result["SELTZO-TwoSum-POW2-R1R0-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_r1r0, ey == ex + (p - one), ex == fx + two),
        seltzo_case_zero((sy, 1, 1, ey - one, ex, ex)),
    )

    result["SELTZO-TwoSum-R1R0-R1R0-D2-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_r1r0,
            y_r1r0,
            ex == ey + two,
            ey == fx + one,
            ey == fy + (p - one),
        ),
        seltzo_case(
            (sx, 0, 0, ex, ey, ey), ((sy,), 0, 0, fy + one, fy - (p - one), fy + one)
        ),
    )
    result["SELTZO-TwoSum-R1R0-R1R0-D2-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_r1r0,
            x_r1r0,
            ey == ex + two,
            ex == fy + one,
            ex == fx + (p - one),
        ),
        seltzo_case(
            (sy, 0, 0, ey, ex, ex), ((sx,), 0, 0, fx + one, fx - (p - one), fx + one)
        ),
    )

    result["SELTZO-TwoSum-POW2-ONE1-S3-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_one1, ex < ey + (p - one), ex > fy + (p - one)),
        seltzo_case((sx, 0, 0, ex, ey, ey), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-POW2-ONE1-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_one1, ey < ex + (p - one), ey > fx + (p - one)),
        seltzo_case((sy, 0, 0, ey, ex, ex), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-ONE1-ONE1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_one1, ey == fx + two, ex > fy + p),
        seltzo_case((sx, 1, 0, ex - one, fx + one, gx), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-ONE1-ONE1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_one1, ex == fy + two, ey > fx + p),
        seltzo_case((sy, 1, 0, ey - one, fy + one, gy), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-R1R0-MM10-D1-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_r1r0,
            y_mm10,
            ex == ey + (p - one),
            ex > fx + two,
            ey == fy + (p - three),
        ),
        seltzo_case((sx, 1, 1, ex, fx + one, gx), (sy, 0, 0, fy, fy - two, fy - two)),
    )
    result["SELTZO-TwoSum-R1R0-MM10-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_r1r0,
            x_mm10,
            ey == ex + (p - one),
            ey > fy + two,
            ex == fx + (p - three),
        ),
        seltzo_case((sy, 1, 1, ey, fy + one, gy), (sx, 0, 0, fx, fx - two, fx - two)),
    )

    result["SELTZO-TwoSum-ONE1-ONE1-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_one1, fx == ey, ex == fy + p),
        seltzo_case_zero((sx, 1, 1, ex - one, ex - (p + one), ex - one)),
    )
    result["SELTZO-TwoSum-ONE1-ONE1-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_one1, fy == ex, ey == fx + p),
        seltzo_case_zero((sy, 1, 1, ey - one, ey - (p + one), ey - one)),
    )

    result["SELTZO-TwoSum-ONE1-G10-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_g10, ex > fy + (p + one), ey > fx, fy == gy + two),
        z3.Or(
            seltzo_case((sx, 1, 0, ex - one, ey, gx), ((sy,), 1, 0, fy, gy - one, gy)),
            seltzo_case((sx, 1, 0, ex - one, ey, gx), ((sy,), 0, 0, fy, gy, gy)),
        ),
    )
    result["SELTZO-TwoSum-ONE1-G10-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_g10, ey > fx + (p + one), ex > fy, fx == gx + two),
        z3.Or(
            seltzo_case((sy, 1, 0, ey - one, ex, gy), ((sx,), 1, 0, fx, gx - one, gx)),
            seltzo_case((sy, 1, 0, ey - one, ex, gy), ((sx,), 0, 0, fx, gx, gx)),
        ),
    )

    result["SELTZO-TwoSum-POW2-R0R1-D4-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_r0r1, ex == ey + (p + one), ey == fy + (p - one)),
        seltzo_case(
            (sx, 1, 1, ex - one, ey, ex - one), ((sy,), 1, 0, ey - one, fy - one, fy)
        ),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D4-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_r0r1, ey == ex + (p + one), ex == fx + (p - one)),
        seltzo_case(
            (sy, 1, 1, ey - one, ex, ey - one), ((sx,), 1, 0, ex - one, fx - one, fx)
        ),
    )

    result["SELTZO-TwoSum-ONE1-ALL1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_all1, ey == fx),
        seltzo_case(
            (sx, 1, 0, ex - one, ey - one, ey),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-ONE1-ALL1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_all1, ex == fy),
        seltzo_case(
            (sy, 1, 0, ey - one, ex - one, ex),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-R1R0-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_r1r0, ex == ey + (p + one)),
        seltzo_case(
            (sx, 1, 1, ex - one, ey, ex - one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-POW2-R1R0-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_r1r0, ey == ex + (p + one)),
        seltzo_case(
            (sy, 1, 1, ey - one, ex, ey - one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-G10-POW2-S1-X"] = z3.Implies(
        z3.And(same_sign, x_g10, y_pow2, ex < ey + (p - one), gx > ey),
        seltzo_case_zero((sx, 1, 0, ex, fx, ey)),
    )
    result["SELTZO-TwoSum-G10-POW2-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_g10, x_pow2, ey < ex + (p - one), gy > ex),
        seltzo_case_zero((sy, 1, 0, ey, fy, ex)),
    )

    result["SELTZO-TwoSum-R1R0-ONE1-D3-X"] = z3.Implies(
        z3.And(
            diff_sign, x_r1r0, y_one1, fx + one > ey, ex > fx + two, ex < fy + (p - one)
        ),
        seltzo_case_zero((sx, 1, 0, ex, fx + one, fy)),
    )
    result["SELTZO-TwoSum-R1R0-ONE1-D3-Y"] = z3.Implies(
        z3.And(
            diff_sign, y_r1r0, x_one1, fy + one > ex, ey > fy + two, ey < fx + (p - one)
        ),
        seltzo_case_zero((sy, 1, 0, ey, fy + one, fx)),
    )

    result["SELTZO-TwoSum-R0R1-POW2-S2-X"] = z3.Implies(
        z3.And(same_sign, x_r0r1, y_pow2, ex == ey, ex == fx + (p - one)),
        seltzo_case(
            (sx, 0, 0, ex + one, ex - (p - one), ex + one),
            (sy, 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-R0R1-POW2-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_r0r1, x_pow2, ey == ex, ey == fy + (p - one)),
        seltzo_case(
            (sy, 0, 0, ey + one, ey - (p - one), ey + one),
            (sx, 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-R1R0-ONE1-S3-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, y_one1, ex == fy + (p - one), fx > ey),
        seltzo_case_zero((sx, 1, 1, ex, fx, fy + one)),
    )
    result["SELTZO-TwoSum-R1R0-ONE1-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_one1, ey == fx + (p - one), fy > ex),
        seltzo_case_zero((sy, 1, 1, ey, fy, fx + one)),
    )

    result["SELTZO-TwoSum-ONE1-POW2-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_pow2, ex == ey + (p - one)),
        seltzo_case_zero((sx, 0, 1, ex, fx - one, fx)),
    )
    result["SELTZO-TwoSum-ONE1-POW2-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_pow2, ey == ex + (p - one)),
        seltzo_case_zero((sy, 0, 1, ey, fy - one, fy)),
    )

    result["SELTZO-TwoSum-ONE0-R1R0-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_one0, y_r1r0, ex == ey + p, ex == fx + (p - two)),
        seltzo_case(
            (sx, 1, 0, ex, fx, fx + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-ONE0-R1R0-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_one0, x_r1r0, ey == ex + p, ey == fy + (p - two)),
        seltzo_case(
            (sy, 1, 0, ey, fy, fy + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-TWO1-ONE1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_two1, y_one1, ey == fx, ex > fy + (p - one)),
        seltzo_case((sx, 0, 0, ex, fx - one, gx), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-TWO1-ONE1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_two1, x_one1, ex == fy, ey > fx + (p - one)),
        seltzo_case((sy, 0, 0, ey, fy - one, gy), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-TWO1-ONE1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_two1, y_one1, ey + one == fx, ex > fy + (p - one)),
        seltzo_case((sx, 0, 0, ex, fx, gx + one), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-TWO1-ONE1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_two1, x_one1, ex + one == fy, ey > fx + (p - one)),
        seltzo_case((sy, 0, 0, ey, fy, gy + one), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-ALL1-R1R0-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_r1r0, ex == ey, ey == fy + (p - one)),
        seltzo_case_zero((sx, 0, 0, ex - (p - one), fx - (p - one), gx - (p - one))),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_all1, x_r1r0, ey == ex, ex == fx + (p - one)),
        seltzo_case_zero((sy, 0, 0, ey - (p - one), fy - (p - one), gy - (p - one))),
    )

    result["SELTZO-TwoSum-POW2-R0R1-S2-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_pow2,
            y_r0r1,
            ex == ey + p,
            ey == fx,
            ey > fy + two,
            ey < fy + (p - one),
        ),
        seltzo_case(
            (sx, 0, 1, ex, fx + one, fx + two),
            ((sy,), 1, 0, ey - one, fy, ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S2-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_pow2,
            x_r0r1,
            ey == ex + p,
            ex == fy,
            ex > fx + two,
            ex < fx + (p - one),
        ),
        seltzo_case(
            (sy, 0, 1, ey, fy + one, fy + two),
            ((sx,), 1, 0, ex - one, fx, ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-POW2-G00-S1-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g00, ex == gy + p),
        z3.Or(
            seltzo_case((sx, 0, 0, ex, ey, (gy + two, fy)), (sy, 0, 0, fx, fx - p, fx)),
            seltzo_case(
                (sx, 0, 0, ex, ey, (gy + two, fy - one)), ((sy,), 0, 0, fx, fx - p, fx)
            ),
            seltzo_case((sx, 0, 0, ex, ey, fy + one), ((sy,), 0, 0, fx, fx - p, fx)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g00, ey == gx + p),
        z3.Or(
            seltzo_case((sy, 0, 0, ey, ex, (gx + two, fx)), (sx, 0, 0, fy, fy - p, fy)),
            seltzo_case(
                (sy, 0, 0, ey, ex, (gx + two, fx - one)), ((sx,), 0, 0, fy, fy - p, fy)
            ),
            seltzo_case((sy, 0, 0, ey, ex, fx + one), ((sx,), 0, 0, fy, fy - p, fy)),
        ),
    )

    result["SELTZO-TwoSum-POW2-R0R1-S3-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_r0r1, ex == ey + p, ey == fy + (p - one)),
        seltzo_case(
            (sx, 0, 1, ex, ex - (p - one), ex - (p - two)),
            ((sy,), 1, 0, ey - one, ey - p, ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_r0r1, ey == ex + p, ex == fx + (p - one)),
        seltzo_case(
            (sy, 0, 1, ey, ey - (p - one), ey - (p - two)),
            ((sx,), 1, 0, ex - one, ex - p, ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-R0R1-POW2-S3-X"] = z3.Implies(
        z3.And(same_sign, x_r0r1, y_pow2, ex == ey, ex < fx + (p - one)),
        seltzo_case(
            (sx, 0, 0, ex + one, fx + one, gx),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-R0R1-POW2-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_r0r1, x_pow2, ey == ex, ey < fy + (p - one)),
        seltzo_case(
            (sy, 0, 0, ey + one, fy + one, gy),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-ALL1-ONE1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_one1, ex == ey, ey > fy + two),
        seltzo_case_zero((sx, 1, 0, ex - one, fy, fx + one)),
    )
    result["SELTZO-TwoSum-ALL1-ONE1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_all1, x_one1, ey == ex, ex > fx + two),
        seltzo_case_zero((sy, 1, 0, ey - one, fx, fy + one)),
    )

    result["SELTZO-TwoSum-POW2-R0R1-S4-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_r0r1, ex == ey + (p - one), ey == fy + (p - one)),
        seltzo_case((sx, 0, 1, ex, ey, ey + one), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S4-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_r0r1, ey == ex + (p - one), ex == fx + (p - one)),
        seltzo_case((sy, 0, 1, ey, ex, ex + one), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-POW2-G11-S1-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g11, ex > ey + one, ex == gy + (p - one)),
        seltzo_case(
            (sx, 0, 1, ex, ey, (gy + one, fy)),
            ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G11-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g11, ey > ex + one, ey == gx + (p - one)),
        seltzo_case(
            (sy, 0, 1, ey, ex, (gx + one, fx)),
            ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-MM10-POW2-S2-X"] = z3.Implies(
        z3.And(same_sign, x_mm10, y_pow2, ex == ey, ex == gx + (p - two)),
        seltzo_case(
            (sx, 0, 0, ex + one, fx, gx + one),
            (sy, 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-MM10-POW2-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_mm10, x_pow2, ey == ex, ey == gy + (p - two)),
        seltzo_case(
            (sy, 0, 0, ey + one, fy, gy + one),
            (sx, 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-ONE1-ONE1-D4-X"] = z3.Implies(
        z3.And(
            diff_sign, x_one1, y_one1, ex < ey + (p - one), fx > ey, ex > fy + (p - one)
        ),
        seltzo_case((sx, 0, 0, ex, fx - one, ey), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-ONE1-ONE1-D4-Y"] = z3.Implies(
        z3.And(
            diff_sign, y_one1, x_one1, ey < ex + (p - one), fy > ex, ey > fx + (p - one)
        ),
        seltzo_case((sy, 0, 0, ey, fy - one, ex), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-POW2-TWO1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_two1, ex == ey + one, ey > fy + two),
        seltzo_case_zero((sx, 1, 0, ey - one, fy, gy)),
    )
    result["SELTZO-TwoSum-POW2-TWO1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_two1, ey == ex + one, ex > fx + two),
        seltzo_case_zero((sy, 1, 0, ex - one, fx, gx)),
    )

    result["SELTZO-TwoSum-MM01-ONE1-S1-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_mm01,
            y_one1,
            ey == fx + one,
            ex > fy + (p - two),
            ex < fx + (p - three),
        ),
        seltzo_case((sx, 0, 0, ex + one, fx - one, gx), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-MM01-ONE1-S1-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_mm01,
            x_one1,
            ex == fy + one,
            ey > fx + (p - two),
            ey < fy + (p - three),
        ),
        seltzo_case((sy, 0, 0, ey + one, fy - one, gy), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-POW2-R0R1-D5-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_r0r1, ex == ey + one, ex == fy + p),
        seltzo_case_zero((sx, 1, 0, ex - two, ex - (p + one), ex - p)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D5-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_r0r1, ey == ex + one, ey == fx + p),
        seltzo_case_zero((sy, 1, 0, ey - two, ey - (p + one), ey - p)),
    )

    result["SELTZO-TwoSum-POW2-TWO1-S1-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_two1, ex < ey + (p - one), ex > fy + p),
        seltzo_case((sx, 0, 0, ex, ey, ey), (sy, 1, 0, fy, fy - two, fy - one)),
    )
    result["SELTZO-TwoSum-POW2-TWO1-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_two1, ey < ex + (p - one), ey > fx + p),
        seltzo_case((sy, 0, 0, ey, ex, ex), (sx, 1, 0, fx, fx - two, fx - one)),
    )

    result["SELTZO-TwoSum-POW2-R0R1-D6-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_r0r1, ex == ey + one, ex > fy + three, ex < fy + p),
        seltzo_case_zero((sx, 1, 0, ey - one, fy, ey - (p - one))),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D6-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_r0r1, ey == ex + one, ey > fx + three, ey < fx + p),
        seltzo_case_zero((sy, 1, 0, ex - one, fx, ex - (p - one))),
    )

    result["SELTZO-TwoSum-ALL1-R1R0-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_r1r0, ex == ey, ey < fy + (p - one)),
        seltzo_case_zero((sx, 1, 0, fy, ey - p, ey - (p - one))),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_all1, x_r1r0, ey == ex, ex < fx + (p - one)),
        seltzo_case_zero((sy, 1, 0, fx, ex - p, ex - (p - one))),
    )

    result["SELTZO-TwoSum-TWO1-R1R0-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_two1, y_r1r0, ex > fy + p, ey + one == fx),
        seltzo_case(
            (sx, 0, 0, ex, fx - one, gx),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-TWO1-R1R0-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_two1, x_r1r0, ey > fx + p, ex + one == fy),
        seltzo_case(
            (sy, 0, 0, ey, fy - one, gy),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-TWO1-R1R0-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_two1, y_r1r0, ex > fy + p, ey + two == fx),
        seltzo_case(
            (sx, 0, 0, ex, fx, gx + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-TWO1-R1R0-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_two1, x_r1r0, ey > fx + p, ex + two == fy),
        seltzo_case(
            (sy, 0, 0, ey, fy, gy + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-R1R0-R1R0-D3-X"] = z3.Implies(
        z3.And(
            diff_sign, x_r1r0, y_r1r0, ex > fy + p, ex < ey + p, fx > ey, ex > fx + two
        ),
        seltzo_case(
            (sx, 1, 0, ex, fx + one, ey + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-R1R0-R1R0-D3-Y"] = z3.Implies(
        z3.And(
            diff_sign, y_r1r0, x_r1r0, ey > fx + p, ey < ex + p, fy > ex, ey > fy + two
        ),
        seltzo_case(
            (sy, 1, 0, ey, fy + one, ex + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-R1R0-ONE1-S4-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_one1,
            ey > fx + one,
            ex < fx + (p - one),
            ex > fy + (p - two),
        ),
        seltzo_case((sx, 0, 0, ex + one, ey - one, gx), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-R1R0-ONE1-S4-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_one1,
            ex > fy + one,
            ey < fy + (p - one),
            ey > fx + (p - two),
        ),
        seltzo_case((sy, 0, 0, ey + one, ex - one, gy), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-ONE1-R0R1-D1-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_one1,
            y_r0r1,
            ex == ey,
            ex < fx + (p - two),
            ey == fy + (p - one),
        ),
        seltzo_case_zero((sx, 1, 0, fx - one, fy - one, fy)),
    )
    result["SELTZO-TwoSum-ONE1-R0R1-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_one1,
            x_r0r1,
            ey == ex,
            ey < fy + (p - two),
            ex == fx + (p - one),
        ),
        seltzo_case_zero((sy, 1, 0, fy - one, fx - one, fx)),
    )

    result["SELTZO-TwoSum-POW2-G00-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g00, ex == ey + one, ey > fy + two),
        seltzo_case_zero((sx, 1, 0, ey - one, fy, gy)),
    )
    result["SELTZO-TwoSum-POW2-G00-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g00, ey == ex + one, ex > fx + two),
        seltzo_case_zero((sy, 1, 0, ex - one, fx, gx)),
    )

    result["SELTZO-TwoSum-ONE1-G00-S1-X"] = z3.Implies(
        z3.And(same_sign, x_one1, y_g00, fx > ey, ex > fy + p, ex < ey + (p - one)),
        z3.Or(
            seltzo_case((sx, 0, 0, ex, fx, ey), (sy, 0, 0, fy, (gy, fy - two), gy)),
            seltzo_case((sx, 0, 0, ex, fx, ey), (sy, 1, 0, fy, gy - one, gy)),
            seltzo_case(
                (sx, 0, 0, ex, fx, ey), (sy, 1, 0, fy, (gy + one, fy - two), gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-ONE1-G00-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_one1, x_g00, fy > ex, ey > fx + p, ey < ex + (p - one)),
        z3.Or(
            seltzo_case((sy, 0, 0, ey, fy, ex), (sx, 0, 0, fx, (gx, fx - two), gx)),
            seltzo_case((sy, 0, 0, ey, fy, ex), (sx, 1, 0, fx, gx - one, gx)),
            seltzo_case(
                (sy, 0, 0, ey, fy, ex), (sx, 1, 0, fx, (gx + one, fx - two), gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-POW2-R0R1-S5-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_pow2,
            y_r0r1,
            ex > ey + one,
            ex < ey + (p - one),
            ey == fy + (p - one),
        ),
        seltzo_case((sx, 0, 0, ex, ey, ey), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S5-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_pow2,
            x_r0r1,
            ey > ex + one,
            ey < ex + (p - one),
            ex == fx + (p - one),
        ),
        seltzo_case((sy, 0, 0, ey, ex, ex), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-POW2-MM10-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_mm10, ex == ey + (p + one), ey > fy + two),
        seltzo_case(
            (sx, 1, 1, ex - one, ex - (p + one), ex - one),
            ((sy,), 1, 0, ey - one, fy, ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-MM10-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_mm10, ey == ex + (p + one), ex > fx + two),
        seltzo_case(
            (sy, 1, 1, ey - one, ey - (p + one), ey - one),
            ((sx,), 1, 0, ex - one, fx, ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-R1R0-R1R0-S1-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, y_r1r0, ey == fx, ex == fx + (p - one)),
        seltzo_case(
            (sx, 0, 0, ex + one, ex - (p - one), ex + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-R1R0-R1R0-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_r1r0, ex == fy, ey == fy + (p - one)),
        seltzo_case(
            (sy, 0, 0, ey + one, ey - (p - one), ey + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-ONE1-ONE1-S1-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_one1,
            y_one1,
            ex == ey + one,
            ey == fx + one,
            ex < fy + (p - one),
            ey > fy + two,
        ),
        seltzo_case_zero((sx, 1, 0, ey + one, ex - three, fy)),
    )
    result["SELTZO-TwoSum-ONE1-ONE1-S1-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_one1,
            x_one1,
            ey == ex + one,
            ex == fy + one,
            ey < fx + (p - one),
            ex > fx + two,
        ),
        seltzo_case_zero((sy, 1, 0, ex + one, ey - three, fx)),
    )

    result["SELTZO-TwoSum-POW2-MM01-S1-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_mm01, ex == fy + (p - one)),
        seltzo_case((sx, 0, 0, ex, ey, ex - (p - two)), (sy, 0, 0, fx, fx - p, fx)),
    )
    result["SELTZO-TwoSum-POW2-MM01-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_mm01, ey == fx + (p - one)),
        seltzo_case((sy, 0, 0, ey, ex, ey - (p - two)), (sx, 0, 0, fy, fy - p, fy)),
    )

    result["SELTZO-TwoSum-POW2-R1R0-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_r1r0, ex < ey + (p + one), ex > fy + (p + one)),
        seltzo_case(
            (sx, 1, 0, ex - one, ey, ey + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-POW2-R1R0-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_r1r0, ey < ex + (p + one), ey > fx + (p + one)),
        seltzo_case(
            (sy, 1, 0, ey - one, ex, ex + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-ONE1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_one1, ex == ey + one),
        seltzo_case_zero((sx, 1, 0, ey - one, fy - one, fy)),
    )
    result["SELTZO-TwoSum-POW2-ONE1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_one1, ey == ex + one),
        seltzo_case_zero((sy, 1, 0, ex - one, fx - one, fx)),
    )

    result["SELTZO-TwoSum-R1R0-R0R1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_r0r1, ex == ey, fx + one > fy, ex > fx + three),
        seltzo_case_zero((sx, 1, 0, ex - one, fx + one, ex - (p - one))),
    )
    result["SELTZO-TwoSum-R1R0-R0R1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_r0r1, ey == ex, fy + one > fx, ey > fy + three),
        seltzo_case_zero((sy, 1, 0, ey - one, fy + one, ey - (p - one))),
    )

    result["SELTZO-TwoSum-POW2-MM10-S1-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_pow2,
            y_mm10,
            ex > fy + p,
            ex < ey + (p - one),
            ey == gy + (p - three),
        ),
        seltzo_case((sx, 0, 0, ex, ey, ey), (sy, 0, 0, gy + one, gy - one, gy - two)),
    )
    result["SELTZO-TwoSum-POW2-MM10-S1-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_pow2,
            x_mm10,
            ey > fx + p,
            ey < ex + (p - one),
            ex == gx + (p - three),
        ),
        seltzo_case((sy, 0, 0, ey, ex, ex), (sx, 0, 0, gx + one, gx - one, gx - two)),
    )

    result["SELTZO-TwoSum-R1R0-R1R0-D4-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_r1r0, ex == ey + one, ex > fx + two, fx > fy + one),
        seltzo_case_zero((sx, 1, 0, ex - one, fx, gy)),
    )
    result["SELTZO-TwoSum-R1R0-R1R0-D4-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_r1r0, ey == ex + one, ey > fy + two, fy > fx + one),
        seltzo_case_zero((sy, 1, 0, ey - one, fy, gx)),
    )

    result["SELTZO-TwoSum-ALL1-ONE1-S2-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_one1, ex > ey, ex < fy + (p - two)),
        seltzo_case(
            (sx, 0, 0, ex + one, ey, fy),
            ((sy,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-ONE1-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_one1, ey > ex, ey < fx + (p - two)),
        seltzo_case(
            (sy, 0, 0, ey + one, ex, fx),
            ((sx,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-ONE1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_one1, ex > fy + p, ex < ey + p),
        seltzo_case((sx, 1, 0, ex - one, ey - one, ey), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-POW2-ONE1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_one1, ey > fx + p, ey < ex + p),
        seltzo_case((sy, 1, 0, ey - one, ex - one, ex), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-ONE0-ONE0-D1-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_one0,
            y_one0,
            ex == ey + p,
            ex < fx + (p - two),
            ey < fy + (p - two),
        ),
        seltzo_case(
            (sx, 1, 0, ex, fx, ey + two),
            ((sy,), 0, 0, fy, ey - (p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-ONE0-ONE0-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_one0,
            x_one0,
            ey == ex + p,
            ey < fy + (p - two),
            ex < fx + (p - two),
        ),
        seltzo_case(
            (sy, 1, 0, ey, fy, ex + two),
            ((sx,), 0, 0, fx, ex - (p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-G00-R1R0-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_g00, y_r1r0, fx == ey + two, ex > fy + p),
        seltzo_case(
            (sx, 0, 0, ex, (fx - one, fx), gx),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-G00-R1R0-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_g00, x_r1r0, fy == ex + two, ey > fx + p),
        seltzo_case(
            (sy, 0, 0, ey, (fy - one, fy), gy),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-R1R0-R1R0-D5-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_r1r0,
            y_r1r0,
            ex == fx + two,
            ex > fy + p,
            ex < ey + p,
            ey < fy + (p - one),
        ),
        seltzo_case(
            (sx, 0, 0, ex, fx, ey + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-R1R0-R1R0-D5-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_r1r0,
            x_r1r0,
            ey == fy + two,
            ey > fx + p,
            ey < ex + p,
            ex < fx + (p - one),
        ),
        seltzo_case(
            (sy, 0, 0, ey, fy, ex + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-R0R1-D7-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_r0r1, ex > ey + two, ex < fy + (p + one)),
        seltzo_case(
            (sx, 1, 0, ex - one, ey, gy),
            ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D7-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_r0r1, ey > ex + two, ey < fx + (p + one)),
        seltzo_case(
            (sy, 1, 0, ey - one, ex, gx),
            ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-R1R0-R0R1-S1-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_r0r1,
            ex == fy + (p - one),
            ey > fx + one,
            ex < fx + (p - two),
            ey < fy + (p - one),
        ),
        seltzo_case(
            (sx, 0, 1, ex + one, ey - one, gy + one),
            ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-R1R0-R0R1-S1-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_r0r1,
            ey == fx + (p - one),
            ex > fy + one,
            ey < fy + (p - two),
            ex < fx + (p - one),
        ),
        seltzo_case(
            (sy, 0, 1, ey + one, ex - one, gx + one),
            ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-POW2-MM10-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_mm10, ex == ey + one, ey > fy + two),
        seltzo_case_zero((sx, 1, 0, ey - one, fy, ey - (p - one))),
    )
    result["SELTZO-TwoSum-POW2-MM10-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_mm10, ey == ex + one, ex > fx + two),
        seltzo_case_zero((sy, 1, 0, ex - one, fx, ex - (p - one))),
    )

    result["SELTZO-TwoSum-R0R1-POW2-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_r0r1, y_pow2, ex == ey, ex - fx < p - one),
        seltzo_case_zero((sx, 1, 0, fx, ex - p, ex - (p - one))),
    )
    result["SELTZO-TwoSum-R0R1-POW2-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_r0r1, x_pow2, ey == ex, ey - fy < p - one),
        seltzo_case_zero((sy, 1, 0, fy, ey - p, ey - (p - one))),
    )

    result["SELTZO-TwoSum-MM10-POW2-S3-X"] = z3.Implies(
        z3.And(same_sign, x_mm10, y_pow2, ex == ey, ex - fx < p - three),
        seltzo_case(
            (sx, 0, 0, ex + one, fx, gx),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-MM10-POW2-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_mm10, x_pow2, ey == ex, ey - fy < p - three),
        seltzo_case(
            (sy, 0, 0, ey + one, fy, gy),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-ONE0-R1R0-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_one0, y_r1r0, ex == ey, fx + one < fy),
        seltzo_case_zero((sx, 1, 0, fy, fx, ex - (p - one))),
    )
    result["SELTZO-TwoSum-ONE0-R1R0-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_one0, x_r1r0, ey == ex, fy + one < fx),
        seltzo_case_zero((sy, 1, 0, fx, fy, ey - (p - one))),
    )

    result["SELTZO-TwoSum-POW2-ONE1-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_one1, ex == ey + (p + one)),
        seltzo_case(
            (sx, 1, 1, ex - one, ex - (p + one), ex - one),
            ((sy,), 1, 0, ey - one, fy - one, fy),
        ),
    )
    result["SELTZO-TwoSum-POW2-ONE1-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_one1, ey == ex + (p + one)),
        seltzo_case(
            (sy, 1, 1, ey - one, ey - (p + one), ey - one),
            ((sx,), 1, 0, ex - one, fx - one, fx),
        ),
    )

    result["SELTZO-TwoSum-ONE1-R0R1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_r0r1, fx == ey, ex < fy + (p + one)),
        seltzo_case(
            (sx, 1, 0, ex - one, fy, gy),
            ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-ONE1-R0R1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_r0r1, fy == ex, ey < fx + (p + one)),
        seltzo_case(
            (sy, 1, 0, ey - one, fx, gx),
            ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-ONE0-POW2-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_one0, y_pow2, ex == ey + (p - one), ex == fx + (p - two)),
        seltzo_case_zero((sx, 1, 0, ex, ex - (p - two), ex - (p - three))),
    )
    result["SELTZO-TwoSum-ONE0-POW2-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_one0, x_pow2, ey == ex + (p - one), ey == fy + (p - two)),
        seltzo_case_zero((sy, 1, 0, ey, ey - (p - two), ey - (p - three))),
    )

    result["SELTZO-TwoSum-R1R0-POW2-S1-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, y_pow2, ex < ey + (p - one), fx > ey),
        seltzo_case_zero((sx, 1, 0, ex, fx, ey)),
    )
    result["SELTZO-TwoSum-R1R0-POW2-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_pow2, ey < ex + (p - one), fy > ex),
        seltzo_case_zero((sy, 1, 0, ey, fy, ex)),
    )

    result["SELTZO-TwoSum-R1R0-G10-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_g10, ex == ey + two, ey == fx + one, ex == gy + p),
        z3.Or(
            seltzo_case(
                (sx, 0, 0, ex, ey, (gy + two, fy - one)), (sy, 0, 0, gy, gy - p, gy)
            ),
            seltzo_case((sx, 0, 0, ex, ey, fy + one), (sy, 0, 0, gy, gy - p, gy)),
            seltzo_case(
                (sx, 0, 0, ex, ey, (gy + two, fy)), ((sy,), 0, 0, gy, gy - p, gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-R1R0-G10-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_g10, ey == ex + two, ex == fy + one, ey == gx + p),
        z3.Or(
            seltzo_case(
                (sy, 0, 0, ey, ex, (gx + two, fx - one)), (sx, 0, 0, gx, gx - p, gx)
            ),
            seltzo_case((sy, 0, 0, ey, ex, fx + one), (sx, 0, 0, gx, gx - p, gx)),
            seltzo_case(
                (sy, 0, 0, ey, ex, (gx + two, fx)), ((sx,), 0, 0, gx, gx - p, gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-POW2-MM01-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_mm01, ex > fy + (p + one), ex < ey + (p + one)),
        seltzo_case(
            (sx, 1, 0, ex - one, ey, ey + one), ((sy,), 1, 0, fy, fy - two, fy - one)
        ),
    )
    result["SELTZO-TwoSum-POW2-MM01-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_mm01, ey > fx + (p + one), ey < ex + (p + one)),
        seltzo_case(
            (sy, 1, 0, ey - one, ex, ex + one), ((sx,), 1, 0, fx, fx - two, fx - one)
        ),
    )

    result["SELTZO-TwoSum-TWO1-TWO1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_two1, y_two1, ex == fy + (p - one), fx == ey + one),
        seltzo_case(
            (sx, 0, 0, ex, fx - one, ex - (p - two)),
            ((sy,), 0, 0, fy - one, fy - (p + one), fy - one),
        ),
    )
    result["SELTZO-TwoSum-TWO1-TWO1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_two1, x_two1, ey == fx + (p - one), fy == ex + one),
        seltzo_case(
            (sy, 0, 0, ey, fy - one, ey - (p - two)),
            ((sx,), 0, 0, fx - one, fx - (p + one), fx - one),
        ),
    )

    result["SELTZO-TwoSum-TWO1-TWO1-D2-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_two1,
            y_two1,
            ex == fy + (p - one),
            fx == ey,
            ex < fx + (p - three),
        ),
        seltzo_case(
            (sx, 0, 0, ex, fx - two, ex - (p - two)),
            ((sy,), 0, 0, fy - one, fy - (p + one), fy - one),
        ),
    )
    result["SELTZO-TwoSum-TWO1-TWO1-D2-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_two1,
            x_two1,
            ey == fx + (p - one),
            fy == ex,
            ey < fy + (p - three),
        ),
        seltzo_case(
            (sy, 0, 0, ey, fy - two, ey - (p - two)),
            ((sx,), 0, 0, fx - one, fx - (p + one), fx - one),
        ),
    )

    result["SELTZO-TwoSum-R1R0-G00-S1-X"] = z3.Implies(
        z3.And(
            same_sign, x_r1r0, y_g00, ex == gy + (p - one), gx == ey, fy == gy + two
        ),
        z3.Or(
            seltzo_case((sx, 0, 0, ex + one, fy, fy), (sy, 0, 0, gy, gy - p, gy)),
            seltzo_case(
                (sx, 0, 0, ex + one, fy + one, fy + one), ((sy,), 0, 0, gy, gy - p, gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-R1R0-G00-S1-Y"] = z3.Implies(
        z3.And(
            same_sign, y_r1r0, x_g00, ey == gx + (p - one), gy == ex, fx == gx + two
        ),
        z3.Or(
            seltzo_case((sy, 0, 0, ey + one, fx, fx), (sx, 0, 0, gx, gx - p, gx)),
            seltzo_case(
                (sy, 0, 0, ey + one, fx + one, fx + one), ((sx,), 0, 0, gx, gx - p, gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-MM01-ONE1-S2-X"] = z3.Implies(
        z3.And(
            same_sign, x_mm01, y_one1, ex == fy + (p - one), fx == ey, ey > fy + two
        ),
        seltzo_case_zero((sx, 1, 1, ex, fx - two, fy + one)),
    )
    result["SELTZO-TwoSum-MM01-ONE1-S2-Y"] = z3.Implies(
        z3.And(
            same_sign, y_mm01, x_one1, ey == fx + (p - one), fy == ex, ex > fx + two
        ),
        seltzo_case_zero((sy, 1, 1, ey, fy - two, fx + one)),
    )

    result["SELTZO-TwoSum-ONE1-POW2-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_pow2, ex < ey + (p - one), ey < fx),
        seltzo_case_zero((sx, 0, 0, ex, fx - one, ey)),
    )
    result["SELTZO-TwoSum-ONE1-POW2-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_pow2, ey < ex + (p - one), ex < fy),
        seltzo_case_zero((sy, 0, 0, ey, fy - one, ex)),
    )

    result["SELTZO-TwoSum-R1R0-POW2-D1-X"] = z3.Implies(
        z3.And(
            diff_sign, x_r1r0, y_pow2, fx + one > ey, ex < ey + (p - one), ex > fx + two
        ),
        seltzo_case_zero((sx, 1, 0, ex, gx, ey)),
    )
    result["SELTZO-TwoSum-R1R0-POW2-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign, y_r1r0, x_pow2, fy + one > ex, ey < ex + (p - one), ey > fy + two
        ),
        seltzo_case_zero((sy, 1, 0, ey, gy, ex)),
    )

    result["SELTZO-TwoSum-R1R0-ONE1-S5-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, y_one1, ex == fx + (p - one), fx == ey),
        seltzo_case((sx, 1, 1, ex, fx - one, ex), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-R1R0-ONE1-S5-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_one1, ey == fy + (p - one), fy == ex),
        seltzo_case((sy, 1, 1, ey, fy - one, ey), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-POW2-TWO1-S2-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_two1, ex == fy + (p - one)),
        seltzo_case((sx, 0, 0, ex, ey, fy + one), ((sy,), 0, 0, fx, fx - p, fx)),
    )
    result["SELTZO-TwoSum-POW2-TWO1-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_two1, ey == fx + (p - one)),
        seltzo_case((sy, 0, 0, ey, ex, fx + one), ((sx,), 0, 0, fy, fy - p, fy)),
    )

    result["SELTZO-TwoSum-POW2-G11-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g11, ex == ey + two, ey < gy + (p - two)),
        seltzo_case(
            (sx, 0, 0, ex - one, fy, gy),
            ((sy,), 0, 0, fx - one, fx - (p + one), fx - one),
        ),
    )
    result["SELTZO-TwoSum-POW2-G11-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g11, ey == ex + two, ex < gx + (p - two)),
        seltzo_case(
            (sy, 0, 0, ey - one, fx, gx),
            ((sx,), 0, 0, fy - one, fy - (p + one), fy - one),
        ),
    )

    result["SELTZO-TwoSum-POW2-TWO1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_two1, ex == fy + (p + one)),
        seltzo_case(
            (sx, 1, 1, ex - one, ey, ey),
            ((sy,), 0, 0, fy - one, fy - (p + one), fy - one),
        ),
    )
    result["SELTZO-TwoSum-POW2-TWO1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_two1, ey == fx + (p + one)),
        seltzo_case(
            (sy, 1, 1, ey - one, ex, ex),
            ((sx,), 0, 0, fx - one, fx - (p + one), fx - one),
        ),
    )

    result["SELTZO-TwoSum-POW2-TWO1-S3-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_two1, ex == fy + p, ey > fy + two),
        seltzo_case((sx, 0, 1, ex, ey, fx + two), ((sy,), 0, 0, gy, gy - p, gy)),
    )
    result["SELTZO-TwoSum-POW2-TWO1-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_two1, ey == fx + p, ex > fx + two),
        seltzo_case((sy, 0, 1, ey, ex, fy + two), ((sx,), 0, 0, gx, gx - p, gx)),
    )

    result["SELTZO-TwoSum-TWO0-R0R1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_two0, y_r0r1, ex == ey, ex > fx + two, fx > fy + two),
        seltzo_case_zero((sx, 1, 0, ex - one, fx, gy)),
    )
    result["SELTZO-TwoSum-TWO0-R0R1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_two0, x_r0r1, ey == ex, ey > fy + two, fy > fx + two),
        seltzo_case_zero((sy, 1, 0, ey - one, fy, gx)),
    )

    result["SELTZO-TwoSum-MM01-ONE1-S3-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_mm01,
            y_one1,
            ex > fy + (p - two),
            fx + one < ey,
            ex < fx + (p - three),
        ),
        seltzo_case((sx, 0, 0, ex + one, ey - one, gx), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-MM01-ONE1-S3-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_mm01,
            x_one1,
            ey > fx + (p - two),
            fy + one < ex,
            ey < fy + (p - three),
        ),
        seltzo_case((sy, 0, 0, ey + one, ex - one, gy), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-G00-R1R0-S1-X"] = z3.Implies(
        z3.And(same_sign, x_g00, y_r1r0, ex < ey + p, ey + one < gx, fy + p < ex),
        seltzo_case(
            (sx, 0, 0, ex, fx, ey + one), ((sy,), 0, 0, gy, fy - (p - one), gy)
        ),
    )
    result["SELTZO-TwoSum-G00-R1R0-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_g00, x_r1r0, ey < ex + p, ex + one < gy, fx + p < ey),
        seltzo_case(
            (sy, 0, 0, ey, fy, ex + one), ((sx,), 0, 0, gx, fx - (p - one), gx)
        ),
    )

    result["SELTZO-TwoSum-POW2-ONE1-D4-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_one1, ex > ey + two, ex < fy + p),
        seltzo_case_zero((sx, 1, 0, ex - one, ey, fy)),
    )
    result["SELTZO-TwoSum-POW2-ONE1-D4-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_one1, ey > ex + two, ey < fx + p),
        seltzo_case_zero((sy, 1, 0, ey - one, ex, fx)),
    )

    result["SELTZO-TwoSum-ONE0-ONE1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_one0, y_one1, ex == ey, fx == fy, ex > fx + three),
        seltzo_case_zero((sx, 1, 0, ex - one, fx + one, ex - (p - one))),
    )
    result["SELTZO-TwoSum-ONE0-ONE1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_one0, x_one1, ey == ex, fy == fx, ey > fy + three),
        seltzo_case_zero((sy, 1, 0, ey - one, fy + one, ey - (p - one))),
    )

    result["SELTZO-TwoSum-ONE0-ONE1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_one0, y_one1, ex == ey, ey > fy + two, fx < fy),
        seltzo_case_zero((sx, 1, 0, ex - one, fy, ex - (p - one))),
    )
    result["SELTZO-TwoSum-ONE0-ONE1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_one0, x_one1, ey == ex, ex > fx + two, fy < fx),
        seltzo_case_zero((sy, 1, 0, ey - one, fx, ey - (p - one))),
    )

    result["SELTZO-TwoSum-G10-ONE1-D1-X"] = z3.Implies(
        z3.And(
            diff_sign, x_g10, y_one1, ey == gx, fx == gx + two, fx > fy + (p - three)
        ),
        z3.Or(
            seltzo_case((sx, 1, 0, ex, fx, fx + one), (sy, 0, 0, fy, fy - p, fy)),
            seltzo_case((sx, 1, 0, ex, fx, fx - one), (sy, 0, 0, fy, fy - p, fy)),
        ),
    )
    result["SELTZO-TwoSum-G10-ONE1-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign, y_g10, x_one1, ex == gy, fy == gy + two, fy > fx + (p - three)
        ),
        z3.Or(
            seltzo_case((sy, 1, 0, ey, fy, fy + one), (sx, 0, 0, fx, fx - p, fx)),
            seltzo_case((sy, 1, 0, ey, fy, fy - one), (sx, 0, 0, fx, fx - p, fx)),
        ),
    )

    result["SELTZO-TwoSum-ONE0-ALL1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_one0, y_all1, ex == ey + p, ex == fx + (p - two)),
        seltzo_case(
            (sx, 1, 0, ex, fx, fx + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-ONE0-ALL1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_one0, x_all1, ey == ex + p, ey == fy + (p - two)),
        seltzo_case(
            (sy, 1, 0, ey, fy, fy + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-TWO0-POW2-S1-X"] = z3.Implies(
        z3.And(same_sign, x_two0, y_pow2, fx == ey),
        seltzo_case_zero((sx, 1, 1, ex, fx - one, gx)),
    )
    result["SELTZO-TwoSum-TWO0-POW2-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_two0, x_pow2, fy == ex),
        seltzo_case_zero((sy, 1, 1, ey, fy - one, gy)),
    )

    result["SELTZO-TwoSum-POW2-ONE1-D5-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_one1, ex == fy + p, ey < fy + (p - two)),
        seltzo_case_zero((sx, 1, 1, ex - one, ey, ey)),
    )
    result["SELTZO-TwoSum-POW2-ONE1-D5-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_one1, ey == fx + p, ex < fx + (p - two)),
        seltzo_case_zero((sy, 1, 1, ey - one, ex, ex)),
    )

    result["SELTZO-TwoSum-POW2-G01-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g01, ex == ey + one, ey > fy + two),
        seltzo_case_zero((sx, 1, 0, ey - one, fy, fx)),
    )
    result["SELTZO-TwoSum-POW2-G01-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g01, ey == ex + one, ex > fx + two),
        seltzo_case_zero((sy, 1, 0, ex - one, fx, fy)),
    )

    result["SELTZO-TwoSum-MM01-ONE1-S4-X"] = z3.Implies(
        z3.And(same_sign, x_mm01, y_one1, ey == fx, ey == fy + (p - two)),
        seltzo_case((sx, 1, 0, ex, gx - one, gx), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-MM01-ONE1-S4-Y"] = z3.Implies(
        z3.And(same_sign, y_mm01, x_one1, ex == fy, ex == fx + (p - two)),
        seltzo_case((sy, 1, 0, ey, gy - one, gy), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-ONE1-TWO1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_two1, ex > fy + p, ey < fx, ex < ey + (p - one)),
        seltzo_case((sx, 0, 0, ex, fx - one, ey), (sy, 1, 0, fy, gy - one, gy)),
    )
    result["SELTZO-TwoSum-ONE1-TWO1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_two1, ey > fx + p, ex < fy, ey < ex + (p - one)),
        seltzo_case((sy, 0, 0, ey, fy - one, ex), (sx, 1, 0, fx, gx - one, gx)),
    )

    result["SELTZO-TwoSum-MM01-ONE1-S5-X"] = z3.Implies(
        z3.And(same_sign, x_mm01, y_one1, ex == fy + p, ey + one < fx),
        seltzo_case((sx, 1, 0, ex, fx, ey), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-MM01-ONE1-S5-Y"] = z3.Implies(
        z3.And(same_sign, y_mm01, x_one1, ey == fx + p, ex + one < fy),
        seltzo_case((sy, 1, 0, ey, fy, ex), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-R1R0-G01-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_g01, ex == ey, ex == fx + two, fx > fy + one),
        seltzo_case_zero((sx, 1, 0, fx, fy, fx - (p - three))),
    )
    result["SELTZO-TwoSum-R1R0-G01-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_g01, ey == ex, ey == fy + two, fy > fx + one),
        seltzo_case_zero((sy, 1, 0, fy, fx, fy - (p - three))),
    )

    result["SELTZO-TwoSum-R1R0-POW2-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_pow2, ex == ey, two < ex - fx),
        seltzo_case_zero((sx, 1, 0, ex - one, fx, gx)),
    )
    result["SELTZO-TwoSum-R1R0-POW2-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_pow2, ey == ex, two < ey - fy),
        seltzo_case_zero((sy, 1, 0, ey - one, fy, gy)),
    )

    result["SELTZO-TwoSum-POW2-TWO0-D1-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_pow2,
            y_two0,
            ex < ey + (p + one),
            ex > gy + (p + two),
            ey == gy + (p - three),
        ),
        seltzo_case(
            (sx, 1, 0, ex - one, ey, ey + one), ((sy,), 1, 0, fy, gy - one, gy - two)
        ),
    )
    result["SELTZO-TwoSum-POW2-TWO0-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_pow2,
            x_two0,
            ey < ex + (p + one),
            ey > gx + (p + two),
            ex == gx + (p - three),
        ),
        seltzo_case(
            (sy, 1, 0, ey - one, ex, ex + one), ((sx,), 1, 0, fx, gx - one, gx - two)
        ),
    )

    result["SELTZO-TwoSum-R1R0-R1R0-S2-X"] = z3.Implies(
        z3.And(
            same_sign, x_r1r0, y_r1r0, ex < fx + (p - one), fx < ey, fy + (p - one) < ex
        ),
        seltzo_case(
            (sx, 0, 0, ex + one, ey, gx), ((sy,), 0, 0, gy, fy - (p - one), gy)
        ),
    )
    result["SELTZO-TwoSum-R1R0-R1R0-S2-Y"] = z3.Implies(
        z3.And(
            same_sign, y_r1r0, x_r1r0, ey < fy + (p - one), fy < ex, fx + (p - one) < ey
        ),
        seltzo_case(
            (sy, 0, 0, ey + one, ex, gy), ((sx,), 0, 0, gx, fx - (p - one), gx)
        ),
    )

    result["SELTZO-TwoSum-POW2-G10-D1-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_pow2,
            y_g10,
            ex > fy + (p + one),
            ex < ey + (p + one),
            fy == gy + two,
        ),
        z3.Or(
            seltzo_case(
                (sx, 1, 0, ex - one, ey, ey + one), ((sy,), 1, 0, fy, gy - one, gy)
            ),
            seltzo_case((sx, 1, 0, ex - one, ey, ey + one), ((sy,), 0, 0, fy, gy, gy)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G10-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_pow2,
            x_g10,
            ey > fx + (p + one),
            ey < ex + (p + one),
            fx == gx + two,
        ),
        z3.Or(
            seltzo_case(
                (sy, 1, 0, ey - one, ex, ex + one), ((sx,), 1, 0, fx, gx - one, gx)
            ),
            seltzo_case((sy, 1, 0, ey - one, ex, ex + one), ((sx,), 0, 0, fx, gx, gx)),
        ),
    )

    result["SELTZO-TwoSum-TWO1-R0R1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_two1, y_r0r1, ex == ey + (p - one), ey == fy + (p - one)),
        seltzo_case((sx, 0, 1, ex, fx, gx), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-TWO1-R0R1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_two1, x_r0r1, ey == ex + (p - one), ex == fx + (p - one)),
        seltzo_case((sy, 0, 1, ey, fy, gy), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-R1R0-R0R1-S2-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_r0r1,
            ex == ey + p,
            ex < fx + (p - one),
            ey == fy + (p - one),
        ),
        seltzo_case(
            (sx, 1, 1, ex, fx, ey + two), ((sy,), 1, 0, ey - one, fy - one, fy)
        ),
    )
    result["SELTZO-TwoSum-R1R0-R0R1-S2-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_r0r1,
            ey == ex + p,
            ey < fy + (p - one),
            ex == fx + (p - one),
        ),
        seltzo_case(
            (sy, 1, 1, ey, fy, ex + two), ((sx,), 1, 0, ex - one, fx - one, fx)
        ),
    )

    result["SELTZO-TwoSum-ONE0-POW2-S2-X"] = z3.Implies(
        z3.And(same_sign, x_one0, y_pow2, ey > fx, ex + one > ey, ex < fx + (p - two)),
        seltzo_case(
            (sx, 0, 0, ex + one, ey - one, fx),
            ((sy,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-ONE0-POW2-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_one0, x_pow2, ex > fy, ey + one > ex, ey < fy + (p - two)),
        seltzo_case(
            (sy, 0, 0, ey + one, ex - one, fy),
            ((sx,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-TWO1-POW2-S1-X"] = z3.Implies(
        z3.And(same_sign, x_two1, y_pow2, ex == ey, ex < fx + (p - three)),
        seltzo_case_zero((sx, 0, 0, gy + one, fx, gx)),
    )
    result["SELTZO-TwoSum-TWO1-POW2-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_two1, x_pow2, ey == ex, ey < fy + (p - three)),
        seltzo_case_zero((sy, 0, 0, gx + one, fy, gy)),
    )

    result["SELTZO-TwoSum-ONE0-R0R1-S1-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_one0,
            y_r0r1,
            ex > fy + (p + one),
            ex < ey + (p - two),
            ex == fx + (p - two),
            ey < fy + (p - one),
        ),
        seltzo_case(
            (sx, 0, 1, ex + one, ey - one, ey),
            ((sy,), 1, 0, ex - p, fy, ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-ONE0-R0R1-S1-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_one0,
            x_r0r1,
            ey > fx + (p + one),
            ey < ex + (p - two),
            ey == fy + (p - two),
            ex < fx + (p - one),
        ),
        seltzo_case(
            (sy, 0, 1, ey + one, ex - one, ex),
            ((sx,), 1, 0, ey - p, fx, ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-MM01-R1R0-S2-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_mm01,
            y_r1r0,
            ex > fy + (p - one),
            ey > fx,
            ex < fx + (p - three),
        ),
        seltzo_case(
            (sx, 0, 0, ex + one, ey, gx),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-MM01-R1R0-S2-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_mm01,
            x_r1r0,
            ey > fx + (p - one),
            ex > fy,
            ey < fy + (p - three),
        ),
        seltzo_case(
            (sy, 0, 0, ey + one, ex, gy),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-ALL1-TWO1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_two1, ex == ey, ey > fy + two),
        seltzo_case_zero((sx, 1, 0, ex - one, fy, fx + one)),
    )
    result["SELTZO-TwoSum-ALL1-TWO1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_all1, x_two1, ey == ex, ex > fx + two),
        seltzo_case_zero((sy, 1, 0, ey - one, fx, fy + one)),
    )

    result["SELTZO-TwoSum-POW2-G01-S1-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g01, ex == ey + p, ey > fy + two),
        seltzo_case(
            (sx, 0, 1, ex, fx + one, fx + two),
            ((sy,), 1, 0, ey - one, fy, ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G01-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g01, ey == ex + p, ex > fx + two),
        seltzo_case(
            (sy, 0, 1, ey, fy + one, fy + two),
            ((sx,), 1, 0, ex - one, fx, ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-POW2-R1R0-S3-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_r1r0, ex == ey + two, ey == fy + (p - one)),
        seltzo_case(
            (sx, 1, 0, ex, ey, ex - one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-POW2-R1R0-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_r1r0, ey == ex + two, ex == fx + (p - one)),
        seltzo_case(
            (sy, 1, 0, ey, ex, ey - one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-MM01-R0R1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_mm01, y_r0r1, ex == ey + p, ey == fy + (p - one)),
        seltzo_case((sx, 1, 1, ex, fx, gx), ((sy,), 1, 0, ey - one, fy - one, fy)),
    )
    result["SELTZO-TwoSum-MM01-R0R1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_mm01, x_r0r1, ey == ex + p, ex == fx + (p - one)),
        seltzo_case((sy, 1, 1, ey, fy, gy), ((sx,), 1, 0, ex - one, fx - one, fx)),
    )

    result["SELTZO-TwoSum-POW2-TWO1-S4-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_two1, ex == ey + p, ey > fy + two),
        seltzo_case(
            (sx, 0, 1, ex, ex - (p - one), ex - (p - two)),
            ((sy,), 1, 0, ey - one, fy, gy),
        ),
    )
    result["SELTZO-TwoSum-POW2-TWO1-S4-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_two1, ey == ex + p, ex > fx + two),
        seltzo_case(
            (sy, 0, 1, ey, ey - (p - one), ey - (p - two)),
            ((sx,), 1, 0, ex - one, fx, gx),
        ),
    )

    result["SELTZO-TwoSum-POW2-ONE0-S3-X"] = z3.Implies(
        z3.And(
            same_sign, x_pow2, y_one0, ex > ey + two, ex < ey + p, ey == fy + (p - two)
        ),
        seltzo_case(
            (sx, 0, 0, ex, ey + one, ey + one), ((sy,), 1, 0, fy, fy - two, fy - one)
        ),
    )
    result["SELTZO-TwoSum-POW2-ONE0-S3-Y"] = z3.Implies(
        z3.And(
            same_sign, y_pow2, x_one0, ey > ex + two, ey < ex + p, ex == fx + (p - two)
        ),
        seltzo_case(
            (sy, 0, 0, ey, ex + one, ex + one), ((sx,), 1, 0, fx, fx - two, fx - one)
        ),
    )

    result["SELTZO-TwoSum-POW2-R0R1-D8-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_r0r1, ex == ey + one, ey == fy + two),
        seltzo_case_zero((sx, 0, 0, gy, fx, fx)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D8-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_r0r1, ey == ex + one, ex == fx + two),
        seltzo_case_zero((sy, 0, 0, gx, fy, fy)),
    )

    result["SELTZO-TwoSum-R1R0-ONE1-D4-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_one1, fx + one == ey, ex > fy + p - one),
        seltzo_case((sx, 1, 0, ex, gx, gx + one), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-R1R0-ONE1-D4-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_one1, fy + one == ex, ey > fx + p - one),
        seltzo_case((sy, 1, 0, ey, gy, gy + one), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-ALL1-R1R0-S2-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_r1r0, ex == ey + (p - one), ey > fy + two),
        seltzo_case((sx, 0, 0, ex + one, ey, ex + one), (sy, 1, 0, fx, fy, gy)),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_r1r0, ey == ex + (p - one), ex > fx + two),
        seltzo_case((sy, 0, 0, ey + one, ex, ey + one), (sx, 1, 0, fy, fx, gx)),
    )

    result["SELTZO-TwoSum-POW2-ONE0-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_one0, ex == ey + two, ey < fy + (p - two)),
        seltzo_case(
            (sx, 0, 0, ex - one, fy, fy),
            ((sy,), 0, 0, fx - one, fx - (p + one), fx - one),
        ),
    )
    result["SELTZO-TwoSum-POW2-ONE0-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_one0, ey == ex + two, ex < fx + (p - two)),
        seltzo_case(
            (sy, 0, 0, ey - one, fx, fx),
            ((sx,), 0, 0, fy - one, fy - (p + one), fy - one),
        ),
    )

    result["SELTZO-TwoSum-POW2-MM01-S2-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_mm01, ex == ey + p),
        seltzo_case(
            (sx, 0, 1, ex, fx + one, fx + two), ((sy,), 1, 0, fy, fy - two, fy - one)
        ),
    )
    result["SELTZO-TwoSum-POW2-MM01-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_mm01, ey == ex + p),
        seltzo_case(
            (sy, 0, 1, ey, fy + one, fy + two), ((sx,), 1, 0, fx, fx - two, fx - one)
        ),
    )

    result["SELTZO-TwoSum-ONE0-ONE1-D3-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_one0,
            y_one1,
            ex == ey + (p - one),
            fx == ey + one,
            ex == fx + (p - two),
        ),
        seltzo_case((sx, 1, 0, ex, fx, fx + one), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-ONE0-ONE1-D3-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_one0,
            x_one1,
            ey == ex + (p - one),
            fy == ex + one,
            ey == fy + (p - two),
        ),
        seltzo_case((sy, 1, 0, ey, fy, fy + one), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-ALL1-TWO1-S2-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_two1, ex > ey, ex < fy + (p - three)),
        seltzo_case(
            (sx, 0, 0, ex + one, ey, gy),
            ((sy,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-TWO1-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_two1, ey > ex, ey < fx + (p - three)),
        seltzo_case(
            (sy, 0, 0, ey + one, ex, gx),
            ((sx,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )

    result["SELTZO-TwoSum-ONE1-ONE1-D5-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_one1, ex == ey + one, fx + one < fy),
        seltzo_case_zero((sx, 1, 0, ex - two, fy - one, fx)),
    )
    result["SELTZO-TwoSum-ONE1-ONE1-D5-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_one1, ey == ex + one, fy + one < fx),
        seltzo_case_zero((sy, 1, 0, ey - two, fx - one, fy)),
    )

    result["SELTZO-TwoSum-TWO1-ALL1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_two1, y_all1, ex < ey + p, fx > ey + two),
        seltzo_case(
            (sx, 0, 0, ex, fx, ey + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-TWO1-ALL1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_two1, x_all1, ey < ex + p, fy > ex + two),
        seltzo_case(
            (sy, 0, 0, ey, fy, ex + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-ONE1-MM01-S1-X"] = z3.Implies(
        z3.And(same_sign, x_one1, y_mm01, fx > ey, ex == fy + (p - one)),
        seltzo_case((sx, 0, 0, ex, fx, fy + one), (sy, 0, 0, gy, gy - p, gy)),
    )
    result["SELTZO-TwoSum-ONE1-MM01-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_one1, x_mm01, fy > ex, ey == fx + (p - one)),
        seltzo_case((sy, 0, 0, ey, fy, fx + one), (sx, 0, 0, gx, gx - p, gx)),
    )

    result["SELTZO-TwoSum-POW2-G00-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g00, ex == ey + one, ey == fy + two),
        seltzo_case_zero((sx, 0, 0, ey - one, (gy, fy - one), gy)),
    )
    result["SELTZO-TwoSum-POW2-G00-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g00, ey == ex + one, ex == fx + two),
        seltzo_case_zero((sy, 0, 0, ex - one, (gx, fx - one), gx)),
    )

    result["SELTZO-TwoSum-POW2-G10-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g10, ex == fy + (p - one), fy == gy + two),
        z3.Or(
            seltzo_case((sx, 1, 0, ex - one, ey, fy), ((sy,), 0, 0, gy, gy - p, gy)),
            seltzo_case((sx, 1, 0, ex - one, ey, fy + one), (sy, 0, 0, gy, gy - p, gy)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G10-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g10, ey == fx + (p - one), fx == gx + two),
        z3.Or(
            seltzo_case((sy, 1, 0, ey - one, ex, fx), ((sx,), 0, 0, gx, gx - p, gx)),
            seltzo_case((sy, 1, 0, ey - one, ex, fx + one), (sx, 0, 0, gx, gx - p, gx)),
        ),
    )

    result["SELTZO-TwoSum-POW2-MM01-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_mm01, ex == fy + p),
        seltzo_case((sx, 1, 0, ex - one, ey, fx + one), (sy, 0, 0, gy, gy - p, gy)),
    )
    result["SELTZO-TwoSum-POW2-MM01-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_mm01, ey == fx + p),
        seltzo_case((sy, 1, 0, ey - one, ex, fy + one), (sx, 0, 0, gx, gx - p, gx)),
    )

    result["SELTZO-TwoSum-ONE1-POW2-S1-X"] = z3.Implies(
        z3.And(same_sign, x_one1, y_pow2, ex == ey, ey < fx + (p - two)),
        seltzo_case_zero((sx, 0, 0, ex + one, fx, fx)),
    )
    result["SELTZO-TwoSum-ONE1-POW2-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_one1, x_pow2, ey == ex, ex < fy + (p - two)),
        seltzo_case_zero((sy, 0, 0, ey + one, fy, fy)),
    )

    result["SELTZO-TwoSum-POW2-TWO1-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_two1, ex < ey + p, ex > fy + (p + one)),
        seltzo_case((sx, 1, 0, ex - one, ey - one, ey), (sy, 1, 0, fy, gy - one, gy)),
    )
    result["SELTZO-TwoSum-POW2-TWO1-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_two1, ey < ex + p, ey > fx + (p + one)),
        seltzo_case((sy, 1, 0, ey - one, ex - one, ex), (sx, 1, 0, fx, gx - one, gx)),
    )

    result["SELTZO-TwoSum-ALL1-R1R0-S3-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_r1r0, ex == ey, ex < fy + (p - one)),
        seltzo_case(
            (sx, 1, 0, ex + one, fy, gy),
            ((sy,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_r1r0, ey == ex, ey < fx + (p - one)),
        seltzo_case(
            (sy, 1, 0, ey + one, fx, gx),
            ((sx,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-G01-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g01, ex == ey + one, ey == fy + two),
        seltzo_case_zero((sx, 0, 0, ey - one, (gy, fy - one), fx)),
    )
    result["SELTZO-TwoSum-POW2-G01-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g01, ey == ex + one, ex == fx + two),
        seltzo_case_zero((sy, 0, 0, ex - one, (gx, fx - one), fy)),
    )

    result["SELTZO-TwoSum-POW2-ONE0-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_one0, ex == ey + (p + one), ey < fy + (p - two)),
        seltzo_case(
            (sx, 1, 1, ex - one, ey, ex - one),
            ((sy,), 0, 0, fy, ey - (p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-ONE0-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_one0, ey == ex + (p + one), ex < fx + (p - two)),
        seltzo_case(
            (sy, 1, 1, ey - one, ex, ey - one),
            ((sx,), 0, 0, fx, ex - (p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-POW2-MM10-S2-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_mm10, ex > ey + one, ex < fy + (p - two)),
        seltzo_case(
            (sx, 0, 0, ex, ey, gy),
            ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-MM10-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_mm10, ey > ex + one, ey < fx + (p - two)),
        seltzo_case(
            (sy, 0, 0, ey, ex, gx),
            ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-ALL1-G00-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_g00, ex == ey, ey == fy + two),
        z3.Or(
            seltzo_case_zero((sx, 0, 0, ex - one, gy - one, fx + one)),
            seltzo_case_zero((sx, 0, 0, ex - one, (gy + one, fy - one), fx + one)),
        ),
    )
    result["SELTZO-TwoSum-ALL1-G00-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_all1, x_g00, ey == ex, ex == fx + two),
        z3.Or(
            seltzo_case_zero((sy, 0, 0, ey - one, gx - one, fy + one)),
            seltzo_case_zero((sy, 0, 0, ey - one, (gx + one, fx - one), fy + one)),
        ),
    )

    result["SELTZO-TwoSum-R1R0-ONE1-S6-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, y_one1, ex > ey, fx + one == fy),
        seltzo_case_zero((sx, 0, 0, ex + one, ey, ey)),
    )
    result["SELTZO-TwoSum-R1R0-ONE1-S6-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_one1, ey > ex, fy + one == fx),
        seltzo_case_zero((sy, 0, 0, ey + one, ex, ex)),
    )

    result["SELTZO-TwoSum-ONE1-G00-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_g00, fx == ey, ex == gy + p),
        seltzo_case_zero((sx, 1, 1, ex - one, fy, (gy + one, fy))),
    )
    result["SELTZO-TwoSum-ONE1-G00-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_g00, fy == ex, ey == gx + p),
        seltzo_case_zero((sy, 1, 1, ey - one, fx, (gx + one, fx))),
    )

    result["SELTZO-TwoSum-ONE1-MM01-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_mm01, fx == ey, ex == fy + (p - one)),
        seltzo_case_zero((sx, 1, 1, ex - one, fx - one, fy + one)),
    )
    result["SELTZO-TwoSum-ONE1-MM01-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_mm01, fy == ex, ey == fx + (p - one)),
        seltzo_case_zero((sy, 1, 1, ey - one, fy - one, fx + one)),
    )

    result["SELTZO-TwoSum-R1R0-ALL1-S1-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, y_all1, fx + one == ey, ex < fx + (p - one)),
        seltzo_case(
            (sx, 0, 0, ex + one, gx, gx),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_all1, fy + one == ex, ey < fy + (p - one)),
        seltzo_case(
            (sy, 0, 0, ey + one, gy, gy),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-ALL1-ONE1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_one1, ex == ey, ey == fy + two),
        seltzo_case_zero((sx, 0, 0, ex - one, fy - one, fx + one)),
    )
    result["SELTZO-TwoSum-ALL1-ONE1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_all1, x_one1, ey == ex, ex == fx + two),
        seltzo_case_zero((sy, 0, 0, ey - one, fx - one, fy + one)),
    )

    result["SELTZO-TwoSum-POW2-TWO1-D4-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_two1, ey == fy + two, ex == ey + one),
        seltzo_case_zero((sx, 0, 0, ey - one, gy, gy)),
    )
    result["SELTZO-TwoSum-POW2-TWO1-D4-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_two1, ex == fx + two, ey == ex + one),
        seltzo_case_zero((sy, 0, 0, ex - one, gx, gx)),
    )

    result["SELTZO-TwoSum-POW2-MM10-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_mm10, ex == ey + one, ey == fy + two),
        seltzo_case_zero((sx, 0, 0, ey - one, gy, fx)),
    )
    result["SELTZO-TwoSum-POW2-MM10-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_mm10, ey == ex + one, ex == fx + two),
        seltzo_case_zero((sy, 0, 0, ex - one, gx, fy)),
    )

    result["SELTZO-TwoSum-POW2-G10-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g10, ex == gy + (p + two), two < fy - gy),
        z3.Or(
            seltzo_case(
                (sx, 1, 0, ex - one, ey, (fx + one, fy - one)),
                (sy, 0, 0, gy, gy - p, gy),
            ),
            seltzo_case((sx, 1, 0, ex - one, ey, fy + one), (sy, 0, 0, gy, gy - p, gy)),
            seltzo_case(
                (sx, 1, 0, ex - one, ey, (fx + one, fy)), ((sy,), 0, 0, gy, gy - p, gy)
            ),
            seltzo_case(
                (sx, 1, 1, ex - one, ey, (fx + one, fy - one)),
                (sy, 0, 0, gy, gy - p, gy),
            ),
            seltzo_case((sx, 1, 1, ex - one, ey, fy + one), (sy, 0, 0, gy, gy - p, gy)),
            seltzo_case(
                (sx, 1, 1, ex - one, ey, (fx + one, fy - one)),
                ((sy,), 0, 0, gy, gy - p, gy),
            ),
            seltzo_case(
                (sx, 1, 1, ex - one, ey, fy + one), ((sy,), 0, 0, gy, gy - p, gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-POW2-G10-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g10, ey == gx + (p + two), two < fx - gx),
        z3.Or(
            seltzo_case(
                (sy, 1, 0, ey - one, ex, (fy + one, fx - one)),
                (sx, 0, 0, gx, gx - p, gx),
            ),
            seltzo_case((sy, 1, 0, ey - one, ex, fx + one), (sx, 0, 0, gx, gx - p, gx)),
            seltzo_case(
                (sy, 1, 0, ey - one, ex, (fy + one, fx)), ((sx,), 0, 0, gx, gx - p, gx)
            ),
            seltzo_case(
                (sy, 1, 1, ey - one, ex, (fy + one, fx - one)),
                (sx, 0, 0, gx, gx - p, gx),
            ),
            seltzo_case((sy, 1, 1, ey - one, ex, fx + one), (sx, 0, 0, gx, gx - p, gx)),
            seltzo_case(
                (sy, 1, 1, ey - one, ex, (fy + one, fx - one)),
                ((sx,), 0, 0, gx, gx - p, gx),
            ),
            seltzo_case(
                (sy, 1, 1, ey - one, ex, fx + one), ((sx,), 0, 0, gx, gx - p, gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-R1R0-G00-S2-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_g00,
            fx + one == ey,
            ex < fy + (p - three),
            ex == gy + (p - one),
        ),
        z3.Or(
            seltzo_case(
                (sx, 0, 0, ex + one, fy + one, fy + one), ((sy,), 0, 0, gy, gy - p, gy)
            ),
            seltzo_case(
                (sx, 0, 0, ex + one, fy, (gy + two, fy - one)),
                ((sy,), 0, 0, gy, gy - p, gy),
            ),
            seltzo_case(
                (sx, 0, 0, ex + one, fy, (gy + two, fy)), (sy, 0, 0, gy, gy - p, gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-R1R0-G00-S2-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_g00,
            fy + one == ex,
            ey < fx + (p - three),
            ey == gx + (p - one),
        ),
        z3.Or(
            seltzo_case(
                (sy, 0, 0, ey + one, fx + one, fx + one), ((sx,), 0, 0, gx, gx - p, gx)
            ),
            seltzo_case(
                (sy, 0, 0, ey + one, fx, (gx + two, fx - one)),
                ((sx,), 0, 0, gx, gx - p, gx),
            ),
            seltzo_case(
                (sy, 0, 0, ey + one, fx, (gx + two, fx)), (sx, 0, 0, gx, gx - p, gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-G01-POW2-D1-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_g01,
            y_pow2,
            ex == ey + one,
            ex == gx + (p - three),
            fx + one == ey,
        ),
        seltzo_case_zero((sx, 1, 0, ey, (gx, fx - one), gx - two)),
    )
    result["SELTZO-TwoSum-G01-POW2-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_g01,
            x_pow2,
            ey == ex + one,
            ey == gy + (p - three),
            fy + one == ex,
        ),
        seltzo_case_zero((sy, 1, 0, ex, (gy, fy - one), gy - two)),
    )

    result["SELTZO-TwoSum-POW2-R0R1-S6-X"] = z3.Implies(
        z3.And(
            same_sign, x_pow2, y_r0r1, ex > ey + one, ex < ey + (p - two), ex == fy + p
        ),
        seltzo_case(
            (sx, 0, 1, ex, ey, gy + one),
            ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S6-Y"] = z3.Implies(
        z3.And(
            same_sign, y_pow2, x_r0r1, ey > ex + one, ey < ex + (p - two), ey == fx + p
        ),
        seltzo_case(
            (sy, 0, 1, ey, ex, gx + one),
            ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-ALL1-G00-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_g00, ex == ey, ex > fy + two),
        seltzo_case_zero((sx, 1, 0, ex - one, fy, fx + one)),
    )
    result["SELTZO-TwoSum-ALL1-G00-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_all1, x_g00, ey == ex, ey > fx + two),
        seltzo_case_zero((sy, 1, 0, ey - one, fx, fy + one)),
    )

    result["SELTZO-TwoSum-POW2-ONE1-D6-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_one1, ex == ey + two, ex < fy + p),
        seltzo_case_zero((sx, 0, 0, ex - one, ey - one, fy)),
    )
    result["SELTZO-TwoSum-POW2-ONE1-D6-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_one1, ey == ex + two, ey < fx + p),
        seltzo_case_zero((sy, 0, 0, ey - one, ex - one, fx)),
    )

    result["SELTZO-TwoSum-POW2-G10-S1-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g10, ex == gy + p),
        z3.Or(
            seltzo_case(
                (sx, 0, 0, ex, ey, (gy + two, fy)), ((sy,), 0, 0, fx, fx - p, fx)
            ),
            seltzo_case(
                (sx, 0, 0, ex, ey, (gy + two, fy - one)), (sy, 0, 0, fx, fx - p, fx)
            ),
            seltzo_case((sx, 0, 0, ex, ey, fy + one), (sy, 0, 0, fx, fx - p, fx)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G10-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g10, ey == gx + p),
        z3.Or(
            seltzo_case(
                (sy, 0, 0, ey, ex, (gx + two, fx)), ((sx,), 0, 0, fy, fy - p, fy)
            ),
            seltzo_case(
                (sy, 0, 0, ey, ex, (gx + two, fx - one)), (sx, 0, 0, fy, fy - p, fy)
            ),
            seltzo_case((sy, 0, 0, ey, ex, fx + one), (sx, 0, 0, fy, fy - p, fy)),
        ),
    )

    result["SELTZO-TwoSum-R1R0-R0R1-S3-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_r0r1,
            ex == ey + p,
            ex == fx + (p - one),
            ey == fy + (p - one),
        ),
        seltzo_case((sx, 1, 1, ex, ey, ex), ((sy,), 1, 0, ey - one, fy - one, fy)),
    )
    result["SELTZO-TwoSum-R1R0-R0R1-S3-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_r0r1,
            ey == ex + p,
            ey == fy + (p - one),
            ex == fx + (p - one),
        ),
        seltzo_case((sy, 1, 1, ey, ex, ey), ((sx,), 1, 0, ex - one, fx - one, fx)),
    )

    result["SELTZO-TwoSum-ONE1-G00-S2-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_one1,
            y_g00,
            ex == ey + one,
            ex == fx + two,
            fx > fy + one,
            ex == gy + (p - one),
        ),
        z3.Or(
            seltzo_case_zero((sx, 1, 1, ex, fx - one, (gy + one, fy - one))),
            seltzo_case_zero((sx, 1, 1, ex, fx - one, fy + one)),
        ),
    )
    result["SELTZO-TwoSum-ONE1-G00-S2-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_one1,
            x_g00,
            ey == ex + one,
            ey == fy + two,
            fy > fx + one,
            ey == gx + (p - one),
        ),
        z3.Or(
            seltzo_case_zero((sy, 1, 1, ey, fy - one, (gx + one, fx - one))),
            seltzo_case_zero((sy, 1, 1, ey, fy - one, fx + one)),
        ),
    )

    result["SELTZO-TwoSum-ONE1-ONE1-D6-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_one1, ex == ey + (p - one)),
        seltzo_case((sx, 0, 1, ex, fx - one, fx), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-ONE1-ONE1-D6-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_one1, ey == ex + (p - one)),
        seltzo_case((sy, 0, 1, ey, fy - one, fy), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-TWO1-R1R0-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_two1, y_r1r0, ex == ey + two, fx < fy + one),
        seltzo_case_zero((sx, 0, 0, ex - one, gy, gx)),
    )
    result["SELTZO-TwoSum-TWO1-R1R0-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_two1, x_r1r0, ey == ex + two, fy < fx + one),
        seltzo_case_zero((sy, 0, 0, ey - one, gx, gy)),
    )

    result["SELTZO-TwoSum-ONE1-R0R1-D3-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_one1,
            y_r0r1,
            ex < ey + (p - one),
            fx == ey + one,
            ey == fy + (p - one),
        ),
        seltzo_case((sx, 0, 0, ex, ey, ey), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-ONE1-R0R1-D3-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_one1,
            x_r0r1,
            ey < ex + (p - one),
            fy == ex + one,
            ex == fx + (p - one),
        ),
        seltzo_case((sy, 0, 0, ey, ex, ex), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-R1R0-R1R0-S3-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_r1r0,
            ex == ey + p,
            ex == fx + (p - one),
            fx == ey + one,
        ),
        seltzo_case(
            (sx, 1, 1, ex, ey, ex), ((sy,), 0, 0, fy + one, fy - (p - one), fy + one)
        ),
    )
    result["SELTZO-TwoSum-R1R0-R1R0-S3-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_r1r0,
            ey == ex + p,
            ey == fy + (p - one),
            fy == ex + one,
        ),
        seltzo_case(
            (sy, 1, 1, ey, ex, ey), ((sx,), 0, 0, fx + one, fx - (p - one), fx + one)
        ),
    )

    result["SELTZO-TwoSum-G11-POW2-S1-X"] = z3.Implies(
        z3.And(same_sign, x_g11, y_pow2, fx == ey),
        seltzo_case_zero((sx, 1, 1, ex, (gx, fx - one), gx)),
    )
    result["SELTZO-TwoSum-G11-POW2-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_g11, x_pow2, fy == ex),
        seltzo_case_zero((sy, 1, 1, ey, (gy, fy - one), gy)),
    )

    result["SELTZO-TwoSum-ALL1-R1R0-S4-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_r1r0, ex < ey + (p - one), ex > fy + (p + one)),
        seltzo_case((sx, 0, 1, ex + one, ey, ey + one), (sy, 1, 0, fx, fy, gy)),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-S4-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_r1r0, ey < ex + (p - one), ey > fx + (p + one)),
        seltzo_case((sy, 0, 1, ey + one, ex, ex + one), (sx, 1, 0, fy, fx, gx)),
    )

    result["SELTZO-TwoSum-ONE1-TWO1-S1-X"] = z3.Implies(
        z3.And(same_sign, x_one1, y_two1, ex < ey + (p - one), fx > ey, ex > fy + p),
        seltzo_case((sx, 0, 0, ex, fx, ey), (sy, 1, 0, fy, gy - one, gy)),
    )
    result["SELTZO-TwoSum-ONE1-TWO1-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_one1, x_two1, ey < ex + (p - one), fy > ex, ey > fx + p),
        seltzo_case((sy, 0, 0, ey, fy, ex), (sx, 1, 0, fx, gx - one, gx)),
    )

    result["SELTZO-TwoSum-POW2-G01-S2-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g01, ex == ey + one, ey < gy + (p - two)),
        seltzo_case((sx, 1, 0, ex, ey - one, gy), ((sy,), 0, 0, fx, fx - p, fx)),
    )
    result["SELTZO-TwoSum-POW2-G01-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g01, ey == ex + one, ex < gx + (p - two)),
        seltzo_case((sy, 1, 0, ey, ex - one, gx), ((sx,), 0, 0, fy, fy - p, fy)),
    )

    result["SELTZO-TwoSum-ONE1-TWO1-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_two1, fx == ey, ex == fy + (p - one)),
        seltzo_case_zero((sx, 1, 1, ex - one, fy, fy)),
    )
    result["SELTZO-TwoSum-ONE1-TWO1-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_two1, fy == ex, ey == fx + (p - one)),
        seltzo_case_zero((sy, 1, 1, ey - one, fx, fx)),
    )

    result["SELTZO-TwoSum-POW2-G00-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g00, ex == ey + (p + one), ey > fy + two),
        seltzo_case(
            (sx, 1, 1, ex - one, ey, ex - one), ((sy,), 1, 0, ey - one, fy, gy)
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g00, ey == ex + (p + one), ex > fx + two),
        seltzo_case(
            (sy, 1, 1, ey - one, ex, ey - one), ((sx,), 1, 0, ex - one, fx, gx)
        ),
    )

    result["SELTZO-TwoSum-ONE1-MM01-S2-X"] = z3.Implies(
        z3.And(same_sign, x_one1, y_mm01, ex < ey + p, fx > ey + one, ex > fy + p),
        seltzo_case((sx, 0, 0, ex, fx, ey + one), ((sy,), 1, 0, fy, gy - one, gy)),
    )
    result["SELTZO-TwoSum-ONE1-MM01-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_one1, x_mm01, ey < ex + p, fy > ex + one, ey > fx + p),
        seltzo_case((sy, 0, 0, ey, fy, ex + one), ((sx,), 1, 0, fx, gx - one, gx)),
    )

    result["SELTZO-TwoSum-POW2-G00-D4-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g00, ex == ey + two, ex < gy + p),
        seltzo_case_zero((sx, 0, 0, ex - one, ey - one, gy)),
    )
    result["SELTZO-TwoSum-POW2-G00-D4-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g00, ey == ex + two, ey < gx + p),
        seltzo_case_zero((sy, 0, 0, ey - one, ex - one, gx)),
    )

    result["SELTZO-TwoSum-G10-G00-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_g10, y_g00, ex == ey + (p - one), fy == gy + three),
        z3.Or(
            seltzo_case((sx, 1, 1, ex, fx, gx), (sy, 0, 0, fy, (gy, gy + one), gy)),
            seltzo_case((sx, 1, 1, ex, fx, gx), (sy, 1, 0, fy, gy - one, gy)),
            seltzo_case((sx, 1, 1, ex, fx, gx), (sy, 1, 0, fy, gy + one, gy)),
        ),
    )
    result["SELTZO-TwoSum-G10-G00-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_g10, x_g00, ey == ex + (p - one), fx == gx + three),
        z3.Or(
            seltzo_case((sy, 1, 1, ey, fy, gy), (sx, 0, 0, fx, (gx, gx + one), gx)),
            seltzo_case((sy, 1, 1, ey, fy, gy), (sx, 1, 0, fx, gx - one, gx)),
            seltzo_case((sy, 1, 1, ey, fy, gy), (sx, 1, 0, fx, gx + one, gx)),
        ),
    )

    result["SELTZO-TwoSum-POW2-G00-S2-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g00, ex < ey + (p - one), ex > fy + p),
        z3.Or(
            seltzo_case((sx, 0, 0, ex, ey, ey), (sy, 0, 0, fy, (gy, fy - two), gy)),
            seltzo_case((sx, 0, 0, ex, ey, ey), (sy, 1, 0, fy, gy - one, gy)),
            seltzo_case(
                (sx, 0, 0, ex, ey, ey), (sy, 1, 0, fy, (gy + one, fy - two), gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g00, ey < ex + (p - one), ey > fx + p),
        z3.Or(
            seltzo_case((sy, 0, 0, ey, ex, ex), (sx, 0, 0, fx, (gx, fx - two), gx)),
            seltzo_case((sy, 0, 0, ey, ex, ex), (sx, 1, 0, fx, gx - one, gx)),
            seltzo_case(
                (sy, 0, 0, ey, ex, ex), (sx, 1, 0, fx, (gx + one, fx - two), gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-TWO1-G10-D1-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_two1,
            y_g10,
            ex == fx + (p - three),
            fx == fy + one,
            ey > fy + two,
            fy == gy + three,
        ),
        z3.Or(
            seltzo_case((sx, 1, 0, ex - one, ey, gx - one), (sy, 0, 0, gy, gy - p, gy)),
            seltzo_case((sx, 1, 0, ex - one, ey, gx), (sy, 0, 0, gy, gy - p, gy)),
            seltzo_case(
                (sx, 1, 0, ex - one, ey, gx - one), ((sy,), 0, 0, gy, gy - p, gy)
            ),
            seltzo_case(
                (sx, 1, 0, ex - one, ey, fx + one), ((sy,), 0, 0, gy, gy - p, gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-TWO1-G10-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_two1,
            x_g10,
            ey == fy + (p - three),
            fy == fx + one,
            ex > fx + two,
            fx == gx + three,
        ),
        z3.Or(
            seltzo_case((sy, 1, 0, ey - one, ex, gy - one), (sx, 0, 0, gx, gx - p, gx)),
            seltzo_case((sy, 1, 0, ey - one, ex, gy), (sx, 0, 0, gx, gx - p, gx)),
            seltzo_case(
                (sy, 1, 0, ey - one, ex, gy - one), ((sx,), 0, 0, gx, gx - p, gx)
            ),
            seltzo_case(
                (sy, 1, 0, ey - one, ex, fy + one), ((sx,), 0, 0, gx, gx - p, gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-POW2-G00-S3-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g00, ex == ey + p, ey == fy + two),
        seltzo_case(
            (sx, 0, 1, ex, fx + one, fx + two),
            ((sy,), 0, 0, fx - one, (gy, fy - one), gy),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g00, ey == ex + p, ex == fx + two),
        seltzo_case(
            (sy, 0, 1, ey, fy + one, fy + two),
            ((sx,), 0, 0, fy - one, (gx, fx - one), gx),
        ),
    )

    result["SELTZO-TwoSum-G01-POW2-S2-X"] = z3.Implies(
        z3.And(same_sign, x_g01, y_pow2, ex == ey, ex == gx + (p - two)),
        seltzo_case(
            (sx, 0, 0, ex + one, fx, (gx + one, fx)),
            (sy, 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-G01-POW2-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_g01, x_pow2, ey == ex, ey == gy + (p - two)),
        seltzo_case(
            (sy, 0, 0, ey + one, fy, (gy + one, fy)),
            (sx, 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-MM01-S3-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_mm01, ex < ey + p, ex > fy + p),
        seltzo_case(
            (sx, 0, 0, ex, ey + one, ey + one), ((sy,), 1, 0, fy, gy - one, gy)
        ),
    )
    result["SELTZO-TwoSum-POW2-MM01-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_mm01, ey < ex + p, ey > fx + p),
        seltzo_case(
            (sy, 0, 0, ey, ex + one, ex + one), ((sx,), 1, 0, fx, gx - one, gx)
        ),
    )

    result["SELTZO-TwoSum-TWO1-ONE1-D3-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_two1,
            y_one1,
            ex < ey + (p - one),
            fx > ey + one,
            ex > fy + (p - one),
        ),
        seltzo_case((sx, 0, 0, ex, fx, ey), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-TWO1-ONE1-D3-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_two1,
            x_one1,
            ey < ex + (p - one),
            fy > ex + one,
            ey > fx + (p - one),
        ),
        seltzo_case((sy, 0, 0, ey, fy, ex), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-POW2-MM10-S3-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_mm10, ex == ey + p, ey > fy + two),
        seltzo_case(
            (sx, 0, 1, ex, fx + one, fx + two),
            ((sy,), 1, 0, fx - one, fy, fx - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-MM10-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_mm10, ey == ex + p, ex > fx + two),
        seltzo_case(
            (sy, 0, 1, ey, fy + one, fy + two),
            ((sx,), 1, 0, fy - one, fx, fy - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-R0R1-R1R0-D1-X"] = z3.Implies(
        z3.And(
            diff_sign, x_r0r1, y_r1r0, ex == ey + one, ex == fx + (p - one), fx < fy
        ),
        seltzo_case_zero((sx, 0, 0, gy, fx, fx)),
    )
    result["SELTZO-TwoSum-R0R1-R1R0-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign, y_r0r1, x_r1r0, ey == ex + one, ey == fy + (p - one), fy < fx
        ),
        seltzo_case_zero((sy, 0, 0, gx, fy, fy)),
    )

    result["SELTZO-TwoSum-POW2-R0R1-S7-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_pow2,
            y_r0r1,
            ex < ey + (p - one),
            ey < fy + (p - one),
            ex > fy + p,
        ),
        seltzo_case((sx, 0, 0, ex, ey, ey), (sy, 1, 0, fy, ey - p, ey - (p - one))),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S7-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_pow2,
            x_r0r1,
            ey < ex + (p - one),
            ex < fx + (p - one),
            ey > fx + p,
        ),
        seltzo_case((sy, 0, 0, ey, ex, ex), (sx, 1, 0, fx, ex - p, ex - (p - one))),
    )

    result["SELTZO-TwoSum-G10-R0R1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_g10, y_r0r1, ex == ey + p, ey == fy + (p - one)),
        seltzo_case((sx, 1, 1, ex, fx, gx), ((sy,), 1, 0, ey - one, fy - one, fy)),
    )
    result["SELTZO-TwoSum-G10-R0R1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_g10, x_r0r1, ey == ex + p, ex == fx + (p - one)),
        seltzo_case((sy, 1, 1, ey, fy, gy), ((sx,), 1, 0, ex - one, fx - one, fx)),
    )

    result["SELTZO-TwoSum-POW2-G10-S2-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g10, ex < ey + p, ex > fy + p),
        z3.Or(
            seltzo_case(
                (sx, 0, 0, ex, ey + one, ey + one),
                ((sy,), 0, 0, fy, (gy, fy - two), gy),
            ),
            seltzo_case(
                (sx, 0, 0, ex, ey + one, ey + one), ((sy,), 1, 0, fy, gy - one, gy)
            ),
            seltzo_case(
                (sx, 0, 0, ex, ey + one, ey + one),
                ((sy,), 1, 0, fy, (gy + one, fy - two), gy),
            ),
        ),
    )
    result["SELTZO-TwoSum-POW2-G10-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g10, ey < ex + p, ey > fx + p),
        z3.Or(
            seltzo_case(
                (sy, 0, 0, ey, ex + one, ex + one),
                ((sx,), 0, 0, fx, (gx, fx - two), gx),
            ),
            seltzo_case(
                (sy, 0, 0, ey, ex + one, ex + one), ((sx,), 1, 0, fx, gx - one, gx)
            ),
            seltzo_case(
                (sy, 0, 0, ey, ex + one, ex + one),
                ((sx,), 1, 0, fx, (gx + one, fx - two), gx),
            ),
        ),
    )

    result["SELTZO-TwoSum-ALL1-G00-S1-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_g00, ex > ey, ex < gy + (p - two)),
        seltzo_case(
            (sx, 0, 0, ex + one, ey, gy),
            ((sy,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-G00-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_g00, ey > ex, ey < gx + (p - two)),
        seltzo_case(
            (sy, 0, 0, ey + one, ex, gx),
            ((sx,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )

    result["SELTZO-TwoSum-MM01-R1R0-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_mm01, y_r1r0, ex > fy + p, ex < ey + p, fx > ey + two),
        seltzo_case(
            (sx, 1, 0, ex, fx, ey + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-MM01-R1R0-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_mm01, x_r1r0, ey > fx + p, ey < ex + p, fy > ex + two),
        seltzo_case(
            (sy, 1, 0, ey, fy, ex + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-TWO1-D5-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_two1, ex == ey + (p + one), ey > fy + two),
        seltzo_case(
            (sx, 1, 1, ex - one, ey, ex - one), ((sy,), 1, 0, ey - one, fy, gy)
        ),
    )
    result["SELTZO-TwoSum-POW2-TWO1-D5-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_two1, ey == ex + (p + one), ex > fx + two),
        seltzo_case(
            (sy, 1, 1, ey - one, ex, ey - one), ((sx,), 1, 0, ex - one, fx, gx)
        ),
    )

    result["SELTZO-TwoSum-ONE1-ALL1-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_all1, ex < ey + p, fx > ey + one),
        seltzo_case(
            (sx, 0, 0, ex, fx - one, ey + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-ONE1-ALL1-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_all1, ey < ex + p, fy > ex + one),
        seltzo_case(
            (sy, 0, 0, ey, fy - one, ex + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-ONE0-POW2-S3-X"] = z3.Implies(
        z3.And(same_sign, x_one0, y_pow2, ex == ey + p),
        seltzo_case((sx, 1, 0, ex, fx - one, fx), ((sy,), 0, 0, ey, fy, ey)),
    )
    result["SELTZO-TwoSum-ONE0-POW2-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_one0, x_pow2, ey == ex + p),
        seltzo_case((sy, 1, 0, ey, fy - one, fy), ((sx,), 0, 0, ex, fx, ex)),
    )

    result["SELTZO-TwoSum-POW2-G01-D4-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_pow2,
            y_g01,
            ex == ey + (p + one),
            ey == fy + two,
            ey == gy + (p - two),
        ),
        seltzo_case(
            (sx, 1, 1, ex - one, ey, ex - one),
            ((sy,), 0, 0, ey - one, (gy, fy - one), gy - one),
        ),
    )
    result["SELTZO-TwoSum-POW2-G01-D4-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_pow2,
            x_g01,
            ey == ex + (p + one),
            ex == fx + two,
            ex == gx + (p - two),
        ),
        seltzo_case(
            (sy, 1, 1, ey - one, ex, ey - one),
            ((sx,), 0, 0, ex - one, (gx, fx - one), gx - one),
        ),
    )

    result["SELTZO-TwoSum-G10-G00-D2-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_g10,
            y_g00,
            ex > gy + (p + two),
            ey > gx,
            ex == fx + two,
            fy == gy + two,
        ),
        z3.Or(
            seltzo_case((sx, 0, 0, ex, fx, gx), (sy, 1, 0, fy, gy - one, gy)),
            seltzo_case((sx, 1, 0, ex, fx, gx), (sy, 1, 0, fy, gy - one, gy)),
            seltzo_case((sx, 0, 0, ex, fx, gx), (sy, 0, 0, fy, gy, gy)),
            seltzo_case((sx, 1, 0, ex, fx, gx), (sy, 0, 0, fy, gy, gy)),
        ),
    )
    result["SELTZO-TwoSum-G10-G00-D2-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_g10,
            x_g00,
            ey > gx + (p + two),
            ex > gy,
            ey == fy + two,
            fx == gx + two,
        ),
        z3.Or(
            seltzo_case((sy, 0, 0, ey, fy, gy), (sx, 1, 0, fx, gx - one, gx)),
            seltzo_case((sy, 1, 0, ey, fy, gy), (sx, 1, 0, fx, gx - one, gx)),
            seltzo_case((sy, 0, 0, ey, fy, gy), (sx, 0, 0, fx, gx, gx)),
            seltzo_case((sy, 1, 0, ey, fy, gy), (sx, 0, 0, fx, gx, gx)),
        ),
    )

    result["SELTZO-TwoSum-R0R1-R0R1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_r0r1, y_r0r1, ex > ey + one, fx + one == ey, ex == fy + p),
        seltzo_case(
            (sx, 1, 0, ex - one, gy, gy + one),
            ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-R0R1-R0R1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_r0r1, x_r0r1, ey > ex + one, fy + one == ex, ey == fx + p),
        seltzo_case(
            (sy, 1, 0, ey - one, gx, gx + one),
            ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-POW2-G01-S3-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g01, ex == ey + two, ex == gy + p),
        z3.Or(
            seltzo_case(
                (sx, 0, 0, ex, ey, (gy + two, fy)),
                (sy, 0, 0, fx - one, fx - (p + one), fx - one),
            ),
            seltzo_case(
                (sx, 0, 1, ex, ey, (gy + two, fy - one)),
                (sy, 0, 0, fx - one, fx - (p + one), fx - one),
            ),
            seltzo_case(
                (sx, 0, 1, ex, ey, fy + one),
                (sy, 0, 0, fx - one, fx - (p + one), fx - one),
            ),
        ),
    )
    result["SELTZO-TwoSum-POW2-G01-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g01, ey == ex + two, ey == gx + p),
        z3.Or(
            seltzo_case(
                (sy, 0, 0, ey, ex, (gx + two, fx)),
                (sx, 0, 0, fy - one, fy - (p + one), fy - one),
            ),
            seltzo_case(
                (sy, 0, 1, ey, ex, (gx + two, fx - one)),
                (sx, 0, 0, fy - one, fy - (p + one), fy - one),
            ),
            seltzo_case(
                (sy, 0, 1, ey, ex, fx + one),
                (sx, 0, 0, fy - one, fy - (p + one), fy - one),
            ),
        ),
    )

    result["SELTZO-TwoSum-ONE1-G10-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_g10, fx == ey, ex == gy + p),
        z3.Or(
            seltzo_case_zero((sx, 1, 1, ex - one, fx - one, (gy + one, fy - one))),
            seltzo_case_zero((sx, 1, 1, ex - one, fx - one, fy + one)),
        ),
    )
    result["SELTZO-TwoSum-ONE1-G10-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_g10, fy == ex, ey == gx + p),
        z3.Or(
            seltzo_case_zero((sy, 1, 1, ey - one, fy - one, (gx + one, fx - one))),
            seltzo_case_zero((sy, 1, 1, ey - one, fy - one, fx + one)),
        ),
    )

    result["SELTZO-TwoSum-R1R0-ONE1-D5-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_one1, ex == ey + (p - one), ex > fx + two),
        seltzo_case((sx, 1, 1, ex, gx, gx), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-R1R0-ONE1-D5-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_one1, ey == ex + (p - one), ey > fy + two),
        seltzo_case((sy, 1, 1, ey, gy, gy), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-R1R0-R0R1-S4-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_r0r1,
            ex == ey + p,
            ex == fx + (p - one),
            ey == fy + (p - two),
        ),
        seltzo_case((sx, 1, 1, ex, ey, ex), ((sy,), 1, 0, ey - one, fy, fy - one)),
    )
    result["SELTZO-TwoSum-R1R0-R0R1-S4-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_r0r1,
            ey == ex + p,
            ey == fy + (p - one),
            ex == fx + (p - two),
        ),
        seltzo_case((sy, 1, 1, ey, ex, ey), ((sx,), 1, 0, ex - one, fx, fx - one)),
    )

    result["SELTZO-TwoSum-POW2-G00-S4-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g00, ex == ey + (p - one), fy == gy + two),
        z3.Or(
            seltzo_case((sx, 0, 1, ex, ey, ey + one), (sy, 1, 0, fy, gy - one, gy)),
            seltzo_case((sx, 0, 1, ex, ey, ey + one), (sy, 0, 0, fy, gy, gy)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-S4-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g00, ey == ex + (p - one), fx == gx + two),
        z3.Or(
            seltzo_case((sy, 0, 1, ey, ex, ex + one), (sx, 1, 0, fx, gx - one, gx)),
            seltzo_case((sy, 0, 1, ey, ex, ex + one), (sx, 0, 0, fx, gx, gx)),
        ),
    )

    result["SELTZO-TwoSum-G00-ONE1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_g00, y_one1, ex > fy + (p - one), gx == ey),
        seltzo_case((sx, 0, 0, ex, fx, (gx + one, fx)), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-G00-ONE1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_g00, x_one1, ey > fx + (p - one), gy == ex),
        seltzo_case((sy, 0, 0, ey, fy, (gy + one, fy)), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-TWO1-TWO1-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_two1, y_two1, fx > ey + one, ex == fy + (p - one)),
        seltzo_case((sx, 0, 0, ex, fx, fy + one), ((sy,), 0, 0, gy, gy - p, gy)),
    )
    result["SELTZO-TwoSum-TWO1-TWO1-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_two1, x_two1, fy > ex + one, ey == fx + (p - one)),
        seltzo_case((sy, 0, 0, ey, fy, fx + one), ((sx,), 0, 0, gx, gx - p, gx)),
    )

    result["SELTZO-TwoSum-MM10-POW2-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_mm10, y_pow2, ex == ey),
        seltzo_case_zero((sx, 0, 0, fx, gx - one, fy + one)),
    )
    result["SELTZO-TwoSum-MM10-POW2-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_mm10, x_pow2, ey == ex),
        seltzo_case_zero((sy, 0, 0, fy, gy - one, fx + one)),
    )

    result["SELTZO-TwoSum-ONE1-G00-S3-X"] = z3.Implies(
        z3.And(
            same_sign, x_one1, y_g00, ex == ey + p, ex < fx + (p - two), ey > fy + two
        ),
        seltzo_case((sx, 0, 1, ex, fx, ey + two), ((sy,), 1, 0, ey - one, fy, gy)),
    )
    result["SELTZO-TwoSum-ONE1-G00-S3-Y"] = z3.Implies(
        z3.And(
            same_sign, y_one1, x_g00, ey == ex + p, ey < fy + (p - two), ex > fx + two
        ),
        seltzo_case((sy, 0, 1, ey, fy, ex + two), ((sx,), 1, 0, ex - one, fx, gx)),
    )

    result["SELTZO-TwoSum-ALL1-MM01-S1-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_mm01, ex > ey, fy + (p - three) > ex),
        seltzo_case(
            (sx, 0, 0, ex + one, ey, gy),
            ((sy,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-MM01-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_mm01, ey > ex, fx + (p - three) > ey),
        seltzo_case(
            (sy, 0, 0, ey + one, ex, gx),
            ((sx,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-ONE0-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_one0, ex == ey + one, ey < fy + (p - two)),
        seltzo_case_zero((sx, 0, 0, fy, fx, fx)),
    )
    result["SELTZO-TwoSum-POW2-ONE0-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_one0, ey == ex + one, ex < fx + (p - two)),
        seltzo_case_zero((sy, 0, 0, fx, fy, fy)),
    )

    result["SELTZO-TwoSum-POW2-G11-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g11, ex == ey + one, ey == gy + (p - two)),
        z3.Or(
            seltzo_case_zero((sx, 0, 0, fy, (gy, fy - two), fx)),
            seltzo_case_zero((sx, 1, 0, fy, gy - two, fx)),
            seltzo_case_zero((sx, 1, 0, fy, (gy + one, fy - two), fx)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G11-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g11, ey == ex + one, ex == gx + (p - two)),
        z3.Or(
            seltzo_case_zero((sy, 0, 0, fx, (gx, fx - two), fy)),
            seltzo_case_zero((sy, 1, 0, fx, gx - two, fy)),
            seltzo_case_zero((sy, 1, 0, fx, (gx + one, fx - two), fy)),
        ),
    )

    result["SELTZO-TwoSum-POW2-G01-S4-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g01, ex > ey + one, ex < gy + (p - one)),
        seltzo_case(
            (sx, 0, 0, ex, ey, gy),
            ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G01-S4-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g01, ey > ex + one, ey < gx + (p - one)),
        seltzo_case(
            (sy, 0, 0, ey, ex, gx),
            ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-POW2-TWO0-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_two0, ex == ey + (p + one), ey < fy + (p - three)),
        seltzo_case(
            (sx, 1, 1, ex - one, ey, ex - one),
            ((sy,), 1, 0, fy, gy - one, ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-TWO0-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_two0, ey == ex + (p + one), ex < fx + (p - three)),
        seltzo_case(
            (sy, 1, 1, ey - one, ex, ey - one),
            ((sx,), 1, 0, fx, gx - one, ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-MM01-POW2-S1-X"] = z3.Implies(
        z3.And(same_sign, x_mm01, y_pow2, ex < ey + (p - one), fx > ey + one),
        seltzo_case_zero((sx, 1, 0, ex, fx, ey)),
    )
    result["SELTZO-TwoSum-MM01-POW2-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_mm01, x_pow2, ey < ex + (p - one), fy > ex + one),
        seltzo_case_zero((sy, 1, 0, ey, fy, ex)),
    )

    result["SELTZO-TwoSum-POW2-R0R1-D9-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_pow2,
            y_r0r1,
            ex < ey + p,
            ey < fy + (p - one),
            fy + (p + one) < ex,
        ),
        seltzo_case(
            (sx, 1, 0, ex - one, ey - one, ey), (sy, 1, 0, fy, ey - p, ey - (p - one))
        ),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D9-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_pow2,
            x_r0r1,
            ey < ex + p,
            ex < fx + (p - one),
            fx + (p + one) < ey,
        ),
        seltzo_case(
            (sy, 1, 0, ey - one, ex - one, ex), (sx, 1, 0, fx, ex - p, ex - (p - one))
        ),
    )

    result["SELTZO-TwoSum-POW2-ONE1-D7-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_one1, ex == ey + p),
        seltzo_case(
            (sx, 1, 1, ex - one, fx - one, ex - one), (sy, 0, 0, fy, fy - p, fy)
        ),
    )
    result["SELTZO-TwoSum-POW2-ONE1-D7-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_one1, ey == ex + p),
        seltzo_case(
            (sy, 1, 1, ey - one, fy - one, ey - one), (sx, 0, 0, fx, fx - p, fx)
        ),
    )

    result["SELTZO-TwoSum-G00-ONE1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_g00, y_one1, fx + one < ey, fy + p < ex),
        seltzo_case((sx, 1, 0, ex - one, ey - one, gx), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-G00-ONE1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_g00, x_one1, fy + one < ex, fx + p < ey),
        seltzo_case((sy, 1, 0, ey - one, ex - one, gy), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-MM01-ONE1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_mm01, y_one1, ex == ey + (p - one)),
        seltzo_case((sx, 1, 1, ex, fx, gx), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-MM01-ONE1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_mm01, x_one1, ey == ex + (p - one)),
        seltzo_case((sy, 1, 1, ey, fy, gy), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-ONE0-ONE1-S1-X"] = z3.Implies(
        z3.And(same_sign, x_one0, y_one1, ex == ey + p),
        seltzo_case(
            (sx, 1, 0, ex, fx - one, fx), ((sy,), 1, 0, ey - one, fy - one, fy)
        ),
    )
    result["SELTZO-TwoSum-ONE0-ONE1-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_one0, x_one1, ey == ex + p),
        seltzo_case(
            (sy, 1, 0, ey, fy - one, fy), ((sx,), 1, 0, ex - one, fx - one, fx)
        ),
    )

    result["SELTZO-TwoSum-TWO0-POW2-S2-X"] = z3.Implies(
        z3.And(same_sign, x_two0, y_pow2, ex < fx + (p - three), fx + one == ey),
        seltzo_case(
            (sx, 0, 0, ex + one, gx, gx),
            ((sy,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-TWO0-POW2-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_two0, x_pow2, ey < fy + (p - three), fy + one == ex),
        seltzo_case(
            (sy, 0, 0, ey + one, gy, gy),
            ((sx,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-ONE1-ALL1-D4-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_all1, ex == ey + one),
        seltzo_case_zero((sx, 0, 0, fx, fy + one, fy + one)),
    )
    result["SELTZO-TwoSum-ONE1-ALL1-D4-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_all1, ey == ex + one),
        seltzo_case_zero((sy, 0, 0, fy, fx + one, fx + one)),
    )

    result["SELTZO-TwoSum-R1R0-G00-S3-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_g00,
            ex + one > ey,
            fx + one < ey,
            ex < gy + (p - two),
            fx + one > fy,
        ),
        seltzo_case_zero((sx, 0, 0, ex + one, ey - one, gy)),
    )
    result["SELTZO-TwoSum-R1R0-G00-S3-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_g00,
            ey + one > ex,
            fy + one < ex,
            ey < gx + (p - two),
            fy + one > fx,
        ),
        seltzo_case_zero((sy, 0, 0, ey + one, ex - one, gx)),
    )

    result["SELTZO-TwoSum-ALL1-G10-S1-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_g10, ex > ey, ex < gy + (p - two)),
        seltzo_case(
            (sx, 0, 0, ex + one, ey, gy),
            ((sy,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )
    result["SELTZO-TwoSum-ALL1-G10-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_g10, ey > ex, ey < gx + (p - two)),
        seltzo_case(
            (sy, 0, 0, ey + one, ex, gx),
            ((sx,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )

    result["SELTZO-TwoSum-TWO1-TWO1-D4-X"] = z3.Implies(
        z3.And(diff_sign, x_two1, y_two1, fx > ey + one, fy + (p - two) > ex),
        seltzo_case_zero((sx, 0, 0, ex, fx, gy)),
    )
    result["SELTZO-TwoSum-TWO1-TWO1-D4-Y"] = z3.Implies(
        z3.And(diff_sign, y_two1, x_two1, fy > ex + one, fx + (p - two) > ey),
        seltzo_case_zero((sy, 0, 0, ey, fy, gx)),
    )

    result["SELTZO-TwoSum-POW2-TWO1-D6-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_two1, ex > ey + two, fy + (p - one) > ex),
        seltzo_case_zero((sx, 1, 0, ex - one, ey, gy)),
    )
    result["SELTZO-TwoSum-POW2-TWO1-D6-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_two1, ey > ex + two, fx + (p - one) > ey),
        seltzo_case_zero((sy, 1, 0, ey - one, ex, gx)),
    )

    result["SELTZO-TwoSum-TWO1-R1R0-D4-X"] = z3.Implies(
        z3.And(diff_sign, x_two1, y_r1r0, fx == ey, fy + (p + one) < ex),
        seltzo_case(
            (sx, 1, 0, ex - one, gx - one, gx), ((sy,), 0, 0, gy, fy - (p - one), gy)
        ),
    )
    result["SELTZO-TwoSum-TWO1-R1R0-D4-Y"] = z3.Implies(
        z3.And(diff_sign, y_two1, x_r1r0, fy == ex, fx + (p + one) < ey),
        seltzo_case(
            (sy, 1, 0, ey - one, gy - one, gy), ((sx,), 0, 0, gx, fx - (p - one), gx)
        ),
    )

    result["SELTZO-TwoSum-ONE1-ONE1-S2-X"] = z3.Implies(
        z3.And(
            same_sign, x_one1, y_one1, ex < ey + (p - one), fx > ey, fy + (p - one) < ex
        ),
        seltzo_case((sx, 0, 0, ex, fx, ey), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-ONE1-ONE1-S2-Y"] = z3.Implies(
        z3.And(
            same_sign, y_one1, x_one1, ey < ex + (p - one), fy > ex, fx + (p - one) < ey
        ),
        seltzo_case((sy, 0, 0, ey, fy, ex), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-POW2-TWO0-S1-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_two0, ex > ey + one, fy + (p - two) > ex),
        seltzo_case(
            (sx, 0, 0, ex, ey, gy),
            ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-TWO0-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_two0, ey > ex + one, fx + (p - two) > ey),
        seltzo_case(
            (sy, 0, 0, ey, ex, gx),
            ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-R0R1-ONE1-S2-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r0r1,
            y_one1,
            ex < ey + (p - one),
            ex > fx + two,
            fx + one > ey,
            fy + p < ex,
        ),
        seltzo_case((sx, 0, 1, ex, gx, ey), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-R0R1-ONE1-S2-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r0r1,
            x_one1,
            ey < ex + (p - one),
            ey > fy + two,
            fy + one > ex,
            fx + p < ey,
        ),
        seltzo_case((sy, 0, 1, ey, gy, ex), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-ONE1-R1R0-D4-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_r1r0, ex < ey + p, fx > ey + one, fy + p < ex),
        seltzo_case(
            (sx, 0, 0, ex, fx - one, ey + one), ((sy,), 0, 0, gy, fy - (p - one), gy)
        ),
    )
    result["SELTZO-TwoSum-ONE1-R1R0-D4-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_r1r0, ey < ex + p, fy > ex + one, fx + p < ey),
        seltzo_case(
            (sy, 0, 0, ey, fy - one, ex + one), ((sx,), 0, 0, gx, fx - (p - one), gx)
        ),
    )

    result["SELTZO-TwoSum-ONE1-R0R1-D4-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_one1,
            y_r0r1,
            ex < ey + (p - one),
            fx > ey,
            ey < fy + (p - one),
            fy + p < ex,
        ),
        seltzo_case(
            (sx, 0, 0, ex, fx - one, ey), (sy, 1, 0, fy, ey - p, ey - (p - one))
        ),
    )
    result["SELTZO-TwoSum-ONE1-R0R1-D4-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_one1,
            x_r0r1,
            ey < ex + (p - one),
            fy > ex,
            ex < fx + (p - one),
            fx + p < ey,
        ),
        seltzo_case(
            (sy, 0, 0, ey, fy - one, ex), (sx, 1, 0, fx, ex - p, ex - (p - one))
        ),
    )

    result["SELTZO-TwoSum-POW2-G00-D5-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g00, ex > ey + two, ex < gy + p),
        seltzo_case_zero((sx, 1, 0, ex - one, ey, gy)),
    )
    result["SELTZO-TwoSum-POW2-G00-D5-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g00, ey > ex + two, ey < gx + p),
        seltzo_case_zero((sy, 1, 0, ey - one, ex, gx)),
    )

    result["SELTZO-TwoSum-MM01-POW2-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_mm01, y_pow2, ex < ey + (p - one), fx > ey + one),
        seltzo_case_zero((sx, 1, 0, ex, fx, ey)),
    )
    result["SELTZO-TwoSum-MM01-POW2-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_mm01, x_pow2, ey < ex + (p - one), fy > ex + one),
        seltzo_case_zero((sy, 1, 0, ey, fy, ex)),
    )

    result["SELTZO-TwoSum-ONE1-R0R1-S1-X"] = z3.Implies(
        z3.And(
            same_sign, x_one1, y_r0r1, ex < ey + (p - one), fx > ey, ey > fy + (p - two)
        ),
        seltzo_case((sx, 0, 0, ex, fx, ey), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-ONE1-R0R1-S1-Y"] = z3.Implies(
        z3.And(
            same_sign, y_one1, x_r0r1, ey < ex + (p - one), fy > ex, ex > fx + (p - two)
        ),
        seltzo_case((sy, 0, 0, ey, fy, ex), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-POW2-G00-D6-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g00, fy + (p - one) == ex, fy == gy + two),
        z3.Or(
            seltzo_case(
                (sx, 1, 0, ex - one, ey, fy + one), ((sy,), 0, 0, gy, gy - p, gy)
            ),
            seltzo_case((sx, 1, 0, ex - one, ey, fy), (sy, 0, 0, gy, gy - p, gy)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-D6-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g00, fx + (p - one) == ey, fx == gx + two),
        z3.Or(
            seltzo_case(
                (sy, 1, 0, ey - one, ex, fx + one), ((sx,), 0, 0, gx, gx - p, gx)
            ),
            seltzo_case((sy, 1, 0, ey - one, ex, fx), (sx, 0, 0, gx, gx - p, gx)),
        ),
    )

    result["SELTZO-TwoSum-ONE0-ONE1-D4-X"] = z3.Implies(
        z3.And(diff_sign, x_one0, y_one1, ex == ey + (p - one), ex < fx + (p - two)),
        seltzo_case((sx, 1, 0, ex, fx, ey + one), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-ONE0-ONE1-D4-Y"] = z3.Implies(
        z3.And(diff_sign, y_one0, x_one1, ey == ex + (p - one), ey < fy + (p - two)),
        seltzo_case((sy, 1, 0, ey, fy, ex + one), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-G10-R1R0-D1-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_g10,
            y_r1r0,
            ex > fx + two,
            fx > ey + one,
            ey + one > gx,
            fy + p < ex,
        ),
        z3.Or(
            seltzo_case((sx, 1, 0, ex, fx, gx), ((sy,), 0, 0, gy, fy - (p - one), gy)),
            seltzo_case(
                (sx, 1, 0, ex, fx + one, gx), ((sy,), 0, 0, gy, fy - (p - one), gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-G10-R1R0-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_g10,
            x_r1r0,
            ey > fy + two,
            fy > ex + one,
            ex + one > gy,
            fx + p < ey,
        ),
        z3.Or(
            seltzo_case((sy, 1, 0, ey, fy, gy), ((sx,), 0, 0, gx, fx - (p - one), gx)),
            seltzo_case(
                (sy, 1, 0, ey, fy + one, gy), ((sx,), 0, 0, gx, fx - (p - one), gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-R1R0-TWO1-S1-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, y_two1, ex > fx + (p - three), fx == fy),
        seltzo_case((sx, 0, 0, ex + one, ey, ey), ((sy,), 0, 0, gy, gy - p, gy)),
    )
    result["SELTZO-TwoSum-R1R0-TWO1-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_two1, ey > fy + (p - three), fy == fx),
        seltzo_case((sy, 0, 0, ey + one, ex, ex), ((sx,), 0, 0, gx, gx - p, gx)),
    )

    result["SELTZO-TwoSum-TWO1-MM01-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_two1, y_mm01, fx > ey + one, fy + (p - one) == ex),
        seltzo_case((sx, 0, 0, ex, fx, fy + one), (sy, 0, 0, gy, gy - p, gy)),
    )
    result["SELTZO-TwoSum-TWO1-MM01-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_two1, x_mm01, fy > ex + one, fx + (p - one) == ey),
        seltzo_case((sy, 0, 0, ey, fy, fx + one), (sx, 0, 0, gx, gx - p, gx)),
    )

    result["SELTZO-TwoSum-G10-R0R1-S1-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_g10,
            y_r0r1,
            ex > ey + (p - one),
            ey > fy + (p - three),
            fx < fy + (p + three),
        ),
        z3.Or(
            seltzo_case((sx, 1, 1, ex, fx, fx), ((sy,), 1, 0, ey - one, fy, fy - one)),
            seltzo_case(
                (sx, 1, 1, ex, fx, fx - one), ((sy,), 1, 0, ey - one, fy, fy - one)
            ),
        ),
    )
    result["SELTZO-TwoSum-G10-R0R1-S1-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_g10,
            x_r0r1,
            ey > ex + (p - one),
            ex > fx + (p - three),
            fy < fx + (p + three),
        ),
        z3.Or(
            seltzo_case((sy, 1, 1, ey, fy, fy), ((sx,), 1, 0, ex - one, fx, fx - one)),
            seltzo_case(
                (sy, 1, 1, ey, fy, fy - one), ((sx,), 1, 0, ex - one, fx, fx - one)
            ),
        ),
    )

    result["SELTZO-TwoSum-POW2-G11-D3-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_pow2,
            y_g11,
            ex == ey + one,
            ey < gy + (p - two),
            fy == gy + two,
        ),
        z3.Or(
            seltzo_case_zero((sx, 0, 0, fy, gy, fx)),
            seltzo_case_zero((sx, 1, 0, fy, gy - one, fx)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G11-D3-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_pow2,
            x_g11,
            ey == ex + one,
            ex < gx + (p - two),
            fx == gx + two,
        ),
        z3.Or(
            seltzo_case_zero((sy, 0, 0, fx, gx, fy)),
            seltzo_case_zero((sy, 1, 0, fx, gx - one, fy)),
        ),
    )

    result["SELTZO-TwoSum-ALL1-R1R0-S5-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_r1r0, ex == ey + (p - three), ey == fy + two),
        seltzo_case((sx, 0, 0, ex + one, ey, ey), (sy, 0, 0, fy, fx - (p - one), fy)),
    )
    result["SELTZO-TwoSum-ALL1-R1R0-S5-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_r1r0, ey == ex + (p - three), ex == fx + two),
        seltzo_case((sy, 0, 0, ey + one, ex, ex), (sx, 0, 0, fx, fy - (p - one), fx)),
    )

    result["SELTZO-TwoSum-G11-POW2-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_g11, y_pow2, ex == ey, ex > fx + two),
        seltzo_case_zero((sx, 1, 0, ex - one, fx, fy + one)),
    )
    result["SELTZO-TwoSum-G11-POW2-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_g11, x_pow2, ey == ex, ey > fy + two),
        seltzo_case_zero((sy, 1, 0, ey - one, fy, fx + one)),
    )

    result["SELTZO-TwoSum-ONE1-R1R0-D5-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_r1r0, fx > ey + one, fy + p > ex),
        seltzo_case_zero((sx, 0, 0, ex, fx - one, gy)),
    )
    result["SELTZO-TwoSum-ONE1-R1R0-D5-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_r1r0, fy > ex + one, fx + p > ey),
        seltzo_case_zero((sy, 0, 0, ey, fy - one, gx)),
    )

    result["SELTZO-TwoSum-G11-R1R0-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_g11, y_r1r0, ex == ey + p, ex < gx + (p - two)),
        seltzo_case(
            (sx, 1, 0, ex, fx, ey + two), ((sy,), 0, 0, gy, fy - (p - one), gy)
        ),
    )
    result["SELTZO-TwoSum-G11-R1R0-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_g11, x_r1r0, ey == ex + p, ey < gy + (p - two)),
        seltzo_case(
            (sy, 1, 0, ey, fy, ex + two), ((sx,), 0, 0, gx, fx - (p - one), gx)
        ),
    )

    result["SELTZO-TwoSum-POW2-G00-D7-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g00, ex == ey + p, fy == gy + two),
        z3.Or(
            seltzo_case(
                (sx, 1, 1, ex - one, fx - one, ex - one), (sy, 1, 0, fy, gy - one, gy)
            ),
            seltzo_case(
                (sx, 1, 1, ex - one, fx - one, ex - one), (sy, 0, 0, fy, gy, gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-D7-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g00, ey == ex + p, fx == gx + two),
        z3.Or(
            seltzo_case(
                (sy, 1, 1, ey - one, fy - one, ey - one), (sx, 1, 0, fx, gx - one, gx)
            ),
            seltzo_case(
                (sy, 1, 1, ey - one, fy - one, ey - one), (sx, 0, 0, fx, gx, gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-ONE1-POW2-S2-X"] = z3.Implies(
        z3.And(same_sign, x_one1, y_pow2, ex < ey + (p - one), fx > ey),
        seltzo_case_zero((sx, 0, 0, ex, fx, ey)),
    )
    result["SELTZO-TwoSum-ONE1-POW2-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_one1, x_pow2, ey < ex + (p - one), fy > ex),
        seltzo_case_zero((sy, 0, 0, ey, fy, ex)),
    )

    result["SELTZO-TwoSum-ONE1-TWO1-D4-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_two1, fx + two == ey, fy + (p + one) < ex),
        seltzo_case((sx, 1, 0, ex - one, fx + one, fx), (sy, 1, 0, fy, gy - one, gy)),
    )
    result["SELTZO-TwoSum-ONE1-TWO1-D4-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_two1, fy + two == ex, fx + (p + one) < ey),
        seltzo_case((sy, 1, 0, ey - one, fy + one, fy), (sx, 1, 0, fx, gx - one, gx)),
    )

    result["SELTZO-TwoSum-POW2-TWO1-D7-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_two1, ex == ey + two, ey < fy + (p - three)),
        seltzo_case_zero((sx, 0, 0, ex - one, ey - one, gy)),
    )
    result["SELTZO-TwoSum-POW2-TWO1-D7-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_two1, ey == ex + two, ex < fx + (p - three)),
        seltzo_case_zero((sy, 0, 0, ey - one, ex - one, gx)),
    )

    result["SELTZO-TwoSum-POW2-R0R1-S8-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_r0r1, ex == ey + one, ey > fy + (p - two)),
        seltzo_case((sx, 1, 0, ex, ey - one, ey), (sy, 0, 0, fx, fx - p, fx)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S8-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_r0r1, ey == ex + one, ex > fx + (p - two)),
        seltzo_case((sy, 1, 0, ey, ex - one, ex), (sx, 0, 0, fy, fy - p, fy)),
    )

    result["SELTZO-TwoSum-POW2-G00-S5-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g00, ex == ey + p, ey > fy + two),
        seltzo_case(
            (sx, 0, 1, ex, fx + one, fx + two), ((sy,), 1, 0, fx - one, fy, gy)
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-S5-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g00, ey == ex + p, ex > fx + two),
        seltzo_case(
            (sy, 0, 1, ey, fy + one, fy + two), ((sx,), 1, 0, fy - one, fx, gx)
        ),
    )

    result["SELTZO-TwoSum-TWO1-ONE0-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_two1, y_one0, ex == ey + one, fx > fy + two),
        seltzo_case_zero((sx, 1, 0, fx, gx - one, ey - (p - one))),
    )
    result["SELTZO-TwoSum-TWO1-ONE0-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_two1, x_one0, ey == ex + one, fy > fx + two),
        seltzo_case_zero((sy, 1, 0, fy, gy - one, ex - (p - one))),
    )

    result["SELTZO-TwoSum-POW2-MM10-D4-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_mm10, ex > ey + two, fy + (p - one) == ex),
        seltzo_case(
            (sx, 1, 1, ex - one, ey, fy),
            ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-MM10-D4-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_mm10, ey > ex + two, fx + (p - one) == ey),
        seltzo_case(
            (sy, 1, 1, ey - one, ex, fx),
            ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-G10-ONE1-S1-X"] = z3.Implies(
        z3.And(same_sign, x_g10, y_one1, fx == ey, fx == gx + two, fy + (p - one) < ex),
        z3.Or(
            seltzo_case((sx, 1, 0, ex, gx - one, gx), (sy, 0, 0, fy, fy - p, fy)),
            seltzo_case((sx, 1, 0, ex, fx - one, gx), (sy, 0, 0, fy, fy - p, fy)),
        ),
    )
    result["SELTZO-TwoSum-G10-ONE1-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_g10, x_one1, fy == ex, fy == gy + two, fx + (p - one) < ey),
        z3.Or(
            seltzo_case((sy, 1, 0, ey, gy - one, gy), (sx, 0, 0, fx, fx - p, fx)),
            seltzo_case((sy, 1, 0, ey, fy - one, gy), (sx, 0, 0, fx, fx - p, fx)),
        ),
    )

    result["SELTZO-TwoSum-G00-POW2-S1-X"] = z3.Implies(
        z3.And(same_sign, x_g00, y_pow2, ex < ey + (p - one), ey < gx),
        seltzo_case_zero((sx, 0, 0, ex, fx, ey)),
    )
    result["SELTZO-TwoSum-G00-POW2-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_g00, x_pow2, ey < ex + (p - one), ex < gy),
        seltzo_case_zero((sy, 0, 0, ey, fy, ex)),
    )

    result["SELTZO-TwoSum-ONE0-R1R0-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_one0, y_r1r0, ex == ey + p, ex < fx + (p - two)),
        seltzo_case(
            (sx, 1, 0, ex, fx, ey + two), ((sy,), 0, 0, gy, fy - (p - one), gy)
        ),
    )
    result["SELTZO-TwoSum-ONE0-R1R0-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_one0, x_r1r0, ey == ex + p, ey < fy + (p - two)),
        seltzo_case(
            (sy, 1, 0, ey, fy, ex + two), ((sx,), 0, 0, gx, fx - (p - one), gx)
        ),
    )

    result["SELTZO-TwoSum-ONE0-POW2-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_one0, y_pow2, ex < ey + (p - one), fx > ey),
        seltzo_case_zero((sx, 1, 1, ex, fx, ey)),
    )
    result["SELTZO-TwoSum-ONE0-POW2-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_one0, x_pow2, ey < ex + (p - one), fy > ex),
        seltzo_case_zero((sy, 1, 1, ey, fy, ex)),
    )

    result["SELTZO-TwoSum-POW2-TWO1-D8-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_two1, ex == ey + p),
        seltzo_case(
            (sx, 1, 1, ex - one, fx - one, ex - one), (sy, 1, 0, fy, gy - one, gy)
        ),
    )
    result["SELTZO-TwoSum-POW2-TWO1-D8-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_two1, ey == ex + p),
        seltzo_case(
            (sy, 1, 1, ey - one, fy - one, ey - one), (sx, 1, 0, fx, gx - one, gx)
        ),
    )

    result["SELTZO-TwoSum-ONE0-ONE1-S2-X"] = z3.Implies(
        z3.And(same_sign, x_one0, y_one1, fx == ey, fy + (p - two) > ex),
        seltzo_case(
            (sx, 0, 0, ex + one, fy, fy),
            ((sy,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-ONE0-ONE1-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_one0, x_one1, fy == ex, fx + (p - two) > ey),
        seltzo_case(
            (sy, 0, 0, ey + one, fx, fx),
            ((sx,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-ONE1-R1R0-D6-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_r1r0, fx == ey + one, fy + p < ex),
        seltzo_case((sx, 0, 0, ex, ex - p, ex), ((sy,), 0, 0, gy, fy - (p - one), gy)),
    )
    result["SELTZO-TwoSum-ONE1-R1R0-D6-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_r1r0, fy == ex + one, fx + p < ey),
        seltzo_case((sy, 0, 0, ey, ey - p, ey), ((sx,), 0, 0, gx, fx - (p - one), gx)),
    )

    result["SELTZO-TwoSum-POW2-TWO1-D9-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_two1, ex == ey + (p + one), ey == fy + two),
        seltzo_case(
            (sx, 1, 1, ex - one, ey, ex - one), ((sy,), 0, 0, ey - one, gy, gy)
        ),
    )
    result["SELTZO-TwoSum-POW2-TWO1-D9-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_two1, ey == ex + (p + one), ex == fx + two),
        seltzo_case(
            (sy, 1, 1, ey - one, ex, ey - one), ((sx,), 0, 0, ex - one, gx, gx)
        ),
    )

    result["SELTZO-TwoSum-ONE1-TWO1-D5-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_two1, fx + one == ey, fy + (p + one) < ex),
        seltzo_case((sx, 1, 0, ex - one, fx - one, fx), (sy, 1, 0, fy, gy - one, gy)),
    )
    result["SELTZO-TwoSum-ONE1-TWO1-D5-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_two1, fy + one == ex, fx + (p + one) < ey),
        seltzo_case((sy, 1, 0, ey - one, fy - one, fy), (sx, 1, 0, fx, gx - one, gx)),
    )

    result["SELTZO-TwoSum-POW2-R0R1-S9-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_r0r1, ex == ey + one, ey > fy + two, fy + p > ex),
        seltzo_case((sx, 1, 0, ex, ey - one, gy), ((sy,), 0, 0, fx, fx - p, fx)),
    )
    result["SELTZO-TwoSum-POW2-R0R1-S9-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_r0r1, ey == ex + one, ex > fx + two, fx + p > ey),
        seltzo_case((sy, 1, 0, ey, ex - one, gx), ((sx,), 0, 0, fy, fy - p, fy)),
    )

    result["SELTZO-TwoSum-R1R0-R0R1-D3-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_r1r0,
            y_r0r1,
            ex == ey + (p - one),
            ex > fx + two,
            ey < fy + (p - one),
        ),
        seltzo_case((sx, 1, 1, ex, gx, gx), (sy, 1, 0, fy, ey - p, ey - (p - one))),
    )
    result["SELTZO-TwoSum-R1R0-R0R1-D3-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_r1r0,
            x_r0r1,
            ey == ex + (p - one),
            ey > fy + two,
            ex < fx + (p - one),
        ),
        seltzo_case((sy, 1, 1, ey, gy, gy), (sx, 1, 0, fx, ex - p, ex - (p - one))),
    )

    result["SELTZO-TwoSum-R1R0-G00-S4-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_g00,
            ex < fx + (p - one),
            fx + two == ey,
            fy + (p - one) < ex,
            fy == gy + two,
        ),
        z3.Or(
            seltzo_case((sx, 0, 0, ex + one, gx, gx), (sy, 1, 0, fy, gy - one, gy)),
            seltzo_case((sx, 0, 0, ex + one, gx, gx), (sy, 0, 0, fy, gy, gy)),
        ),
    )
    result["SELTZO-TwoSum-R1R0-G00-S4-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_g00,
            ey < fy + (p - one),
            fy + two == ex,
            fx + (p - one) < ey,
            fx == gx + two,
        ),
        z3.Or(
            seltzo_case((sy, 0, 0, ey + one, gy, gy), (sx, 1, 0, fx, gx - one, gx)),
            seltzo_case((sy, 0, 0, ey + one, gy, gy), (sx, 0, 0, fx, gx, gx)),
        ),
    )

    result["SELTZO-TwoSum-G00-POW2-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_g00, y_pow2, ex == ey + (p - one)),
        seltzo_case_zero((sx, 0, 1, ex, fx, gx)),
    )
    result["SELTZO-TwoSum-G00-POW2-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_g00, x_pow2, ey == ex + (p - one)),
        seltzo_case_zero((sy, 0, 1, ey, fy, gy)),
    )

    result["SELTZO-TwoSum-POW2-G11-S2-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g11, ex > ey + one, ex < gy + (p - one)),
        seltzo_case(
            (sx, 0, 0, ex, ey, gy),
            ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G11-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g11, ey > ex + one, ey < gx + (p - one)),
        seltzo_case(
            (sy, 0, 0, ey, ex, gx),
            ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-G11-POW2-S2-X"] = z3.Implies(
        z3.And(
            same_sign, x_g11, y_pow2, ex + one > ey, fx + one < ey, ex < gx + (p - two)
        ),
        seltzo_case(
            (sx, 0, 0, ex + one, ey - one, gx),
            ((sy,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-G11-POW2-S2-Y"] = z3.Implies(
        z3.And(
            same_sign, y_g11, x_pow2, ey + one > ex, fy + one < ex, ey < gy + (p - two)
        ),
        seltzo_case(
            (sy, 0, 0, ey + one, ex - one, gy),
            ((sx,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-R1R0-G10-S1-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_g10,
            ex < fx + (p - one),
            fx + one < ey,
            fy == gy + two,
            ex == gy + (p + one),
        ),
        z3.Or(
            seltzo_case((sx, 0, 1, ex + one, ey, gx), (sy, 0, 0, gy, gy - p, gy)),
            seltzo_case(
                (sx, 0, 1, ex + one, ey, gx), (sy, 1, 0, fy - one, gy - one, gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-R1R0-G10-S1-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_g10,
            ey < fy + (p - one),
            fy + one < ex,
            fx == gx + two,
            ey == gx + (p + one),
        ),
        z3.Or(
            seltzo_case((sy, 0, 1, ey + one, ex, gy), (sx, 0, 0, gx, gx - p, gx)),
            seltzo_case(
                (sy, 0, 1, ey + one, ex, gy), (sx, 1, 0, fx - one, gx - one, gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-POW2-R0R1-D10-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_r0r1, ex == ey + two, ey < fy + (p - one)),
        seltzo_case(
            (sx, 0, 0, ex - one, ey - one, gy),
            ((sy,), 0, 0, fx - one, fx - (p + one), fx - one),
        ),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D10-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_r0r1, ey == ex + two, ex < fx + (p - one)),
        seltzo_case(
            (sy, 0, 0, ey - one, ex - one, gx),
            ((sx,), 0, 0, fy - one, fy - (p + one), fy - one),
        ),
    )

    result["SELTZO-TwoSum-POW2-G00-D8-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g00, ex == ey + p, fy == gy + three),
        z3.Or(
            seltzo_case(
                (sx, 1, 1, ex - one, fx - one, ex - one), (sy, 1, 0, fy, gy - one, gy)
            ),
            seltzo_case(
                (sx, 1, 1, ex - one, fx - one, ex - one), (sy, 0, 0, fy, gy, gy)
            ),
            seltzo_case(
                (sx, 1, 1, ex - one, fx - one, ex - one), (sy, 0, 0, fy, gy + one, gy)
            ),
            seltzo_case(
                (sx, 1, 1, ex - one, fx - one, ex - one), (sy, 1, 0, fy, gy + one, gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-D8-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g00, ey == ex + p, fx == gx + three),
        z3.Or(
            seltzo_case(
                (sy, 1, 1, ey - one, fy - one, ey - one), (sx, 1, 0, fx, gx - one, gx)
            ),
            seltzo_case(
                (sy, 1, 1, ey - one, fy - one, ey - one), (sx, 0, 0, fx, gx, gx)
            ),
            seltzo_case(
                (sy, 1, 1, ey - one, fy - one, ey - one), (sx, 0, 0, fx, gx + one, gx)
            ),
            seltzo_case(
                (sy, 1, 1, ey - one, fy - one, ey - one), (sx, 1, 0, fx, gx + one, gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-TWO1-POW2-S2-X"] = z3.Implies(
        z3.And(same_sign, x_two1, y_pow2, ex < ey + (p - one), fx > ey + one),
        seltzo_case_zero((sx, 0, 0, ex, fx, ey)),
    )
    result["SELTZO-TwoSum-TWO1-POW2-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_two1, x_pow2, ey < ex + (p - one), fy > ex + one),
        seltzo_case_zero((sy, 0, 0, ey, fy, ex)),
    )

    result["SELTZO-TwoSum-R1R0-TWO1-S2-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, y_two1, fx + one == ey, fy + (p - two) == ex),
        seltzo_case(
            (sx, 0, 0, ex + one, fy + one, fy + one), ((sy,), 0, 0, gy, gy - p, gy)
        ),
    )
    result["SELTZO-TwoSum-R1R0-TWO1-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_two1, fy + one == ex, fx + (p - two) == ey),
        seltzo_case(
            (sy, 0, 0, ey + one, fx + one, fx + one), ((sx,), 0, 0, gx, gx - p, gx)
        ),
    )

    result["SELTZO-TwoSum-POW2-G00-S6-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g00, ex == ey + (p - one), fy == gy + three),
        z3.Or(
            seltzo_case((sx, 0, 1, ex, ey, ey + one), (sy, 1, 0, fy, gy - one, gy)),
            seltzo_case((sx, 0, 1, ex, ey, ey + one), (sy, 0, 0, fy, gy, gy)),
            seltzo_case((sx, 0, 1, ex, ey, ey + one), (sy, 0, 0, fy, gy + one, gy)),
            seltzo_case((sx, 0, 1, ex, ey, ey + one), (sy, 1, 0, fy, gy + one, gy)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-S6-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g00, ey == ex + (p - one), fx == gx + three),
        z3.Or(
            seltzo_case((sy, 0, 1, ey, ex, ex + one), (sx, 1, 0, fx, gx - one, gx)),
            seltzo_case((sy, 0, 1, ey, ex, ex + one), (sx, 0, 0, fx, gx, gx)),
            seltzo_case((sy, 0, 1, ey, ex, ex + one), (sx, 0, 0, fx, gx + one, gx)),
            seltzo_case((sy, 0, 1, ey, ex, ex + one), (sx, 1, 0, fx, gx + one, gx)),
        ),
    )

    result["SELTZO-TwoSum-G00-R1R0-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_g00, y_r1r0, fx == ey + three, fx == gx + two, fy + p < ex),
        z3.Or(
            seltzo_case((sx, 0, 0, ex, fx, fx), ((sy,), 0, 0, gy, fy - (p - one), gy)),
            seltzo_case(
                (sx, 0, 0, ex, fx, fx - one), ((sy,), 0, 0, gy, fy - (p - one), gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-G00-R1R0-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_g00, x_r1r0, fy == ex + three, fy == gy + two, fx + p < ey),
        z3.Or(
            seltzo_case((sy, 0, 0, ey, fy, fy), ((sx,), 0, 0, gx, fx - (p - one), gx)),
            seltzo_case(
                (sy, 0, 0, ey, fy, fy - one), ((sx,), 0, 0, gx, fx - (p - one), gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-ONE1-R1R0-S1-X"] = z3.Implies(
        z3.And(
            same_sign, x_one1, y_r1r0, ex < fx + (p - two), fx == ey + two, fy + p < ex
        ),
        seltzo_case(
            (sx, 0, 0, ex, fx, fx - one), ((sy,), 0, 0, gy, fy - (p - one), gy)
        ),
    )
    result["SELTZO-TwoSum-ONE1-R1R0-S1-Y"] = z3.Implies(
        z3.And(
            same_sign, y_one1, x_r1r0, ey < fy + (p - two), fy == ex + two, fx + p < ey
        ),
        seltzo_case(
            (sy, 0, 0, ey, fy, fy - one), ((sx,), 0, 0, gx, fx - (p - one), gx)
        ),
    )

    result["SELTZO-TwoSum-ALL1-ONE1-S3-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_one1, ex > ey, fy + (p - two) == ex),
        seltzo_case(
            (sx, 0, 0, ex + one, ey, ey), (sy, 0, 0, fx + one, fx - (p - one), fx + one)
        ),
    )
    result["SELTZO-TwoSum-ALL1-ONE1-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_one1, ey > ex, fx + (p - two) == ey),
        seltzo_case(
            (sy, 0, 0, ey + one, ex, ex), (sx, 0, 0, fy + one, fy - (p - one), fy + one)
        ),
    )

    result["SELTZO-TwoSum-MM10-POW2-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_mm10, y_pow2, ex == ey + p, ex < fx + (p - three)),
        seltzo_case((sx, 0, 0, ex, fx, ey + two), ((sy,), 0, 0, ey, fy, ey)),
    )
    result["SELTZO-TwoSum-MM10-POW2-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_mm10, x_pow2, ey == ex + p, ey < fy + (p - three)),
        seltzo_case((sy, 0, 0, ey, fy, ex + two), ((sx,), 0, 0, ex, fx, ex)),
    )

    result["SELTZO-TwoSum-G10-R0R1-D2-X"] = z3.Implies(
        z3.And(
            diff_sign, x_g10, y_r0r1, ex == ey + p, ey > fy + two, ey < fy + (p - one)
        ),
        seltzo_case(
            (sx, 1, 1, ex, fx, gx), ((sy,), 1, 0, ey - one, fy, ey - (p - one))
        ),
    )
    result["SELTZO-TwoSum-G10-R0R1-D2-Y"] = z3.Implies(
        z3.And(
            diff_sign, y_g10, x_r0r1, ey == ex + p, ex > fx + two, ex < fx + (p - one)
        ),
        seltzo_case(
            (sy, 1, 1, ey, fy, gy), ((sx,), 1, 0, ex - one, fx, ex - (p - one))
        ),
    )

    result["SELTZO-TwoSum-POW2-G01-D5-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g01, ex == ey + two, ex < gy + p),
        seltzo_case(
            (sx, 0, 0, ex - one, ey - one, gy),
            ((sy,), 0, 0, fx - one, fx - (p + one), fx - one),
        ),
    )
    result["SELTZO-TwoSum-POW2-G01-D5-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g01, ey == ex + two, ey < gx + p),
        seltzo_case(
            (sy, 0, 0, ey - one, ex - one, gx),
            ((sx,), 0, 0, fy - one, fy - (p + one), fy - one),
        ),
    )

    result["SELTZO-TwoSum-ONE1-TWO1-D6-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_two1, fx > ey + one, fy + (p - one) == ex),
        seltzo_case((sx, 0, 0, ex, fx - one, fy + one), ((sy,), 0, 0, gy, gy - p, gy)),
    )
    result["SELTZO-TwoSum-ONE1-TWO1-D6-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_two1, fy > ex + one, fx + (p - one) == ey),
        seltzo_case((sy, 0, 0, ey, fy - one, fx + one), ((sx,), 0, 0, gx, gx - p, gx)),
    )

    result["SELTZO-TwoSum-POW2-G01-S5-X"] = z3.Implies(
        z3.And(
            same_sign, x_pow2, y_g01, ex < ey + two, fy == gy + two, ex > gy + (p - two)
        ),
        z3.Or(
            seltzo_case((sx, 1, 0, ex, ey - one, fy - one), (sy, 0, 0, fx, fx - p, fx)),
            seltzo_case((sx, 1, 0, ex, ey - one, fy), (sy, 0, 0, fx, fx - p, fx)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G01-S5-Y"] = z3.Implies(
        z3.And(
            same_sign, y_pow2, x_g01, ey < ex + two, fx == gx + two, ey > gx + (p - two)
        ),
        z3.Or(
            seltzo_case((sy, 1, 0, ey, ex - one, fx - one), (sx, 0, 0, fy, fy - p, fy)),
            seltzo_case((sy, 1, 0, ey, ex - one, fx), (sx, 0, 0, fy, fy - p, fy)),
        ),
    )

    result["SELTZO-TwoSum-R1R0-POW2-D3-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_r1r0,
            y_pow2,
            ex > ey + one,
            ex < ey + (p - one),
            ex == fx + two,
        ),
        seltzo_case_zero((sx, 0, 0, ex, fx, ey)),
    )
    result["SELTZO-TwoSum-R1R0-POW2-D3-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_r1r0,
            x_pow2,
            ey > ex + one,
            ey < ex + (p - one),
            ey == fy + two,
        ),
        seltzo_case_zero((sy, 0, 0, ey, fy, ex)),
    )

    result["SELTZO-TwoSum-TWO0-R1R0-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_two0, y_r1r0, ex == ey + p, ex < fx + (p - three)),
        seltzo_case(
            (sx, 1, 0, ex, fx, ey + two), ((sy,), 0, 0, gy, fy - (p - one), gy)
        ),
    )
    result["SELTZO-TwoSum-TWO0-R1R0-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_two0, x_r1r0, ey == ex + p, ey < fy + (p - three)),
        seltzo_case(
            (sy, 1, 0, ey, fy, ex + two), ((sx,), 0, 0, gx, fx - (p - one), gx)
        ),
    )

    result["SELTZO-TwoSum-POW2-G10-D4-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g10, fy + (p + one) == ex, fy == gy + two),
        z3.Or(
            seltzo_case((sx, 1, 1, ex - one, ey, fx + one), (sy, 0, 0, gy, gy - p, gy)),
            seltzo_case(
                (sx, 1, 1, ex - one, ey, fx + one), (sy, 1, 0, fy - one, gy - one, gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-POW2-G10-D4-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g10, fx + (p + one) == ey, fx == gx + two),
        z3.Or(
            seltzo_case((sy, 1, 1, ey - one, ex, fy + one), (sx, 0, 0, gx, gx - p, gx)),
            seltzo_case(
                (sy, 1, 1, ey - one, ex, fy + one), (sx, 1, 0, fx - one, gx - one, gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-TWO1-R1R0-S1-X"] = z3.Implies(
        z3.And(same_sign, x_two1, y_r1r0, ex < ey + p, fx > ey + two, fy + p < ex),
        seltzo_case(
            (sx, 0, 0, ex, fx, ey + one), ((sy,), 0, 0, gy, fy - (p - one), gy)
        ),
    )
    result["SELTZO-TwoSum-TWO1-R1R0-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_two1, x_r1r0, ey < ex + p, fy > ex + two, fx + p < ey),
        seltzo_case(
            (sy, 0, 0, ey, fy, ex + one), ((sx,), 0, 0, gx, fx - (p - one), gx)
        ),
    )

    result["SELTZO-TwoSum-ONE1-MM01-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_mm01, fx < ey, fy + (p + one) < ex),
        seltzo_case((sx, 1, 0, ex - one, ey, fx), ((sy,), 1, 0, fy, gy - one, gy)),
    )
    result["SELTZO-TwoSum-ONE1-MM01-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_mm01, fy < ex, fx + (p + one) < ey),
        seltzo_case((sy, 1, 0, ey - one, ex, fy), ((sx,), 1, 0, fx, gx - one, gx)),
    )

    result["SELTZO-TwoSum-R1R0-G00-S5-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_g00,
            ex == ey + (p - one),
            ex > fx + (p - two),
            fy == gy + two,
        ),
        z3.Or(
            seltzo_case((sx, 1, 1, ex, fx - one, ex), (sy, 1, 0, fy, gy - one, gy)),
            seltzo_case((sx, 1, 1, ex, fx - one, ex), (sy, 0, 0, fy, gy, gy)),
        ),
    )
    result["SELTZO-TwoSum-R1R0-G00-S5-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_g00,
            ey == ex + (p - one),
            ey > fy + (p - two),
            fx == gx + two,
        ),
        z3.Or(
            seltzo_case((sy, 1, 1, ey, fy - one, ey), (sx, 1, 0, fx, gx - one, gx)),
            seltzo_case((sy, 1, 1, ey, fy - one, ey), (sx, 0, 0, fx, gx, gx)),
        ),
    )

    result["SELTZO-TwoSum-POW2-G00-S7-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g00, ey > fy + two, fy + p == ex, fy == gy + two),
        z3.Or(
            seltzo_case((sx, 0, 1, ex, ey, fx + two), ((sy,), 0, 0, gy, gy - p, gy)),
            seltzo_case(
                (sx, 0, 1, ex, ey, fx + two), ((sy,), 1, 0, fx - one, gy - one, gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-S7-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g00, ex > fx + two, fx + p == ey, fx == gx + two),
        z3.Or(
            seltzo_case((sy, 0, 1, ey, ex, fy + two), ((sx,), 0, 0, gx, gx - p, gx)),
            seltzo_case(
                (sy, 0, 1, ey, ex, fy + two), ((sx,), 1, 0, fy - one, gx - one, gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-ONE1-R1R0-S2-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_one1,
            y_r1r0,
            ex == ey + one,
            ex < fx + (p - two),
            ey > fy + (p - two),
        ),
        seltzo_case(
            (sx, 0, 0, ex + one, fx, fx), ((sy,), 0, 0, gy, fy - (p - one), gy)
        ),
    )
    result["SELTZO-TwoSum-ONE1-R1R0-S2-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_one1,
            x_r1r0,
            ey == ex + one,
            ey < fy + (p - two),
            ex > fx + (p - two),
        ),
        seltzo_case(
            (sy, 0, 0, ey + one, fy, fy), ((sx,), 0, 0, gx, fx - (p - one), gx)
        ),
    )

    result["SELTZO-TwoSum-R1R0-ONE1-S7-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_one1,
            ex + one > ey,
            fx + one < ey,
            fy + (p - two) > ex,
            fx + one > fy,
        ),
        seltzo_case_zero((sx, 0, 0, ex + one, ey - one, fy)),
    )
    result["SELTZO-TwoSum-R1R0-ONE1-S7-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_one1,
            ey + one > ex,
            fy + one < ex,
            fx + (p - two) > ey,
            fy + one > fx,
        ),
        seltzo_case_zero((sy, 0, 0, ey + one, ex - one, fx)),
    )

    result["SELTZO-TwoSum-G11-ONE1-S1-X"] = z3.Implies(
        z3.And(same_sign, x_g11, y_one1, fx == ey, fx == gx + two, ey == fy + two),
        z3.Or(
            seltzo_case_zero((sx, 1, 1, ex, ex - p, ex)),
            seltzo_case_zero((sx, 1, 1, ex, fx - one, fx - one)),
        ),
    )
    result["SELTZO-TwoSum-G11-ONE1-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_g11, x_one1, fy == ex, fy == gy + two, ex == fx + two),
        z3.Or(
            seltzo_case_zero((sy, 1, 1, ey, ey - p, ey)),
            seltzo_case_zero((sy, 1, 1, ey, fy - one, fy - one)),
        ),
    )

    result["SELTZO-TwoSum-G00-R0R1-D1-X"] = z3.Implies(
        z3.And(
            diff_sign, x_g00, y_r0r1, ex < ey + (p - one), ey < gx, ey > fy + (p - two)
        ),
        seltzo_case((sx, 0, 0, ex, fx, ey), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-G00-R0R1-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign, y_g00, x_r0r1, ey < ex + (p - one), ex < gy, ex > fx + (p - two)
        ),
        seltzo_case((sy, 0, 0, ey, fy, ex), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-R0R1-POW2-S4-X"] = z3.Implies(
        z3.And(same_sign, x_r0r1, y_pow2, ex == ey + p, ex > fx + two),
        seltzo_case((sx, 0, 0, ex, gx, gx), ((sy,), 0, 0, ey, fy, ey)),
    )
    result["SELTZO-TwoSum-R0R1-POW2-S4-Y"] = z3.Implies(
        z3.And(same_sign, y_r0r1, x_pow2, ey == ex + p, ey > fy + two),
        seltzo_case((sy, 0, 0, ey, gy, gy), ((sx,), 0, 0, ex, fx, ex)),
    )

    result["SELTZO-TwoSum-R1R0-TWO1-S3-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, y_two1, ex < ey + (p - one), fx == ey, fy + p < ex),
        seltzo_case((sx, 1, 0, ex, fx - one, fx), (sy, 1, 0, fy, gy - one, gy)),
    )
    result["SELTZO-TwoSum-R1R0-TWO1-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_two1, ey < ex + (p - one), fy == ex, fx + p < ey),
        seltzo_case((sy, 1, 0, ey, fy - one, fy), (sx, 1, 0, fx, gx - one, gx)),
    )

    result["SELTZO-TwoSum-ONE0-TWO1-S1-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_one0,
            y_two1,
            ex < fx + (p - three),
            fx < ey,
            fy + (p - three) == ex,
        ),
        seltzo_case(
            (sx, 0, 0, ex + one, ey - one, fy),
            (sy, 0, 0, gy - one, gy - (p + one), gy - one),
        ),
    )
    result["SELTZO-TwoSum-ONE0-TWO1-S1-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_one0,
            x_two1,
            ey < fy + (p - three),
            fy < ex,
            fx + (p - three) == ey,
        ),
        seltzo_case(
            (sy, 0, 0, ey + one, ex - one, fx),
            (sx, 0, 0, gx - one, gx - (p + one), gx - one),
        ),
    )

    result["SELTZO-TwoSum-R1R0-G01-S1-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_g01,
            fx + one == ey,
            fy + (p - one) < ex,
            fy == gy + two,
        ),
        z3.Or(
            seltzo_case(
                (sx, 0, 0, ex + one, ex - (p - one), ex + one),
                (sy, 0, 0, fy, gy - one, fx - (p - two)),
            ),
            seltzo_case(
                (sx, 0, 0, ex + one, ex - (p - one), ex + one),
                (sy, 1, 0, fy, gy, fx - (p - two)),
            ),
        ),
    )
    result["SELTZO-TwoSum-R1R0-G01-S1-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_g01,
            fy + one == ex,
            fx + (p - one) < ey,
            fx == gx + two,
        ),
        z3.Or(
            seltzo_case(
                (sy, 0, 0, ey + one, ey - (p - one), ey + one),
                (sx, 0, 0, fx, gx - one, fy - (p - two)),
            ),
            seltzo_case(
                (sy, 0, 0, ey + one, ey - (p - one), ey + one),
                (sx, 1, 0, fx, gx, fy - (p - two)),
            ),
        ),
    )

    result["SELTZO-TwoSum-POW2-MM10-D5-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_mm10, ex < ey + three, fy + (p - two) < ex),
        seltzo_case(
            (sx, 0, 0, ex - one, ey - one, fy),
            (sy, 0, 0, fx - one, fx - (p + one), fx - one),
        ),
    )
    result["SELTZO-TwoSum-POW2-MM10-D5-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_mm10, ey < ex + three, fx + (p - two) < ey),
        seltzo_case(
            (sy, 0, 0, ey - one, ex - one, fx),
            (sx, 0, 0, fy - one, fy - (p + one), fy - one),
        ),
    )

    result["SELTZO-TwoSum-R1R0-G00-S6-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_g00,
            ex < ey + (p - one),
            fx == ey,
            fy + p < ex,
            fy == gy + two,
        ),
        z3.Or(
            seltzo_case((sx, 1, 0, ex, fx - one, fx), (sy, 1, 0, fy, gy - one, gy)),
            seltzo_case((sx, 1, 0, ex, fx - one, fx), (sy, 0, 0, fy, gy, gy)),
        ),
    )
    result["SELTZO-TwoSum-R1R0-G00-S6-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_g00,
            ey < ex + (p - one),
            fy == ex,
            fx + p < ey,
            fx == gx + two,
        ),
        z3.Or(
            seltzo_case((sy, 1, 0, ey, fy - one, fy), (sx, 1, 0, fx, gx - one, gx)),
            seltzo_case((sy, 1, 0, ey, fy - one, fy), (sx, 0, 0, fx, gx, gx)),
        ),
    )

    result["SELTZO-TwoSum-POW2-G00-D9-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g00, fy + (p + one) == ex, fy == gy + three),
        z3.Or(
            seltzo_case((sx, 1, 1, ex - one, ey, ey), ((sy,), 0, 0, gy, gy - p, gy)),
            seltzo_case(
                (sx, 1, 1, ex - one, ey, ey), ((sy,), 1, 0, gy + one, gy - one, gy)
            ),
            seltzo_case(
                (sx, 1, 1, ex - one, ey, ey), ((sy,), 1, 0, fy - one, gy - one, gy)
            ),
            seltzo_case((sx, 1, 1, ex - one, ey, ey), ((sy,), 0, 0, fy - one, gy, gy)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-D9-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g00, fx + (p + one) == ey, fx == gx + three),
        z3.Or(
            seltzo_case((sy, 1, 1, ey - one, ex, ex), ((sx,), 0, 0, gx, gx - p, gx)),
            seltzo_case(
                (sy, 1, 1, ey - one, ex, ex), ((sx,), 1, 0, gx + one, gx - one, gx)
            ),
            seltzo_case(
                (sy, 1, 1, ey - one, ex, ex), ((sx,), 1, 0, fx - one, gx - one, gx)
            ),
            seltzo_case((sy, 1, 1, ey - one, ex, ex), ((sx,), 0, 0, fx - one, gx, gx)),
        ),
    )

    result["SELTZO-TwoSum-R1R0-R0R1-S5-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_r0r1,
            ex == ey + (p - one),
            ex > fx + (p - two),
            ey < fy + (p - one),
        ),
        seltzo_case(
            (sx, 1, 1, ex, fx - one, ex), (sy, 1, 0, fy, fx - p, fx - (p - one))
        ),
    )
    result["SELTZO-TwoSum-R1R0-R0R1-S5-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_r0r1,
            ey == ex + (p - one),
            ey > fy + (p - two),
            ex < fx + (p - one),
        ),
        seltzo_case(
            (sy, 1, 1, ey, fy - one, ey), (sx, 1, 0, fx, fy - p, fy - (p - one))
        ),
    )

    result["SELTZO-TwoSum-G00-R0R1-D2-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_g00,
            y_r0r1,
            fx == ey,
            fx == gx + two,
            ey < fy + (p - one),
            fy + p < ex,
        ),
        z3.Or(
            seltzo_case(
                (sx, 0, 0, ex, gx, gx), (sy, 1, 0, fy, gx - (p - two), gx - (p - three))
            ),
            seltzo_case(
                (sx, 0, 0, ex, fx - one, gx),
                (sy, 1, 0, fy, gx - (p - two), gx - (p - three)),
            ),
        ),
    )
    result["SELTZO-TwoSum-G00-R0R1-D2-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_g00,
            x_r0r1,
            fy == ex,
            fy == gy + two,
            ex < fx + (p - one),
            fx + p < ey,
        ),
        z3.Or(
            seltzo_case(
                (sy, 0, 0, ey, gy, gy), (sx, 1, 0, fx, gy - (p - two), gy - (p - three))
            ),
            seltzo_case(
                (sy, 0, 0, ey, fy - one, gy),
                (sx, 1, 0, fx, gy - (p - two), gy - (p - three)),
            ),
        ),
    )

    result["SELTZO-TwoSum-ONE0-MM10-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_one0, y_mm10, ex > ey + (p - two), fx < ey + two),
        seltzo_case(
            (sx, 1, 0, ex, fx, fx + one), (sy, 0, 0, fy, gy - one, ey - (p - one))
        ),
    )
    result["SELTZO-TwoSum-ONE0-MM10-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_one0, x_mm10, ey > ex + (p - two), fy < ex + two),
        seltzo_case(
            (sy, 1, 0, ey, fy, fy + one), (sx, 0, 0, fx, gx - one, ex - (p - one))
        ),
    )

    result["SELTZO-TwoSum-POW2-G10-D5-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_pow2,
            y_g10,
            ex < ey + (p + two),
            ey == fy + two,
            fy + (p + two) < ex,
        ),
        z3.Or(
            seltzo_case(
                (sx, 1, 1, ex - one, ey, ex - one), ((sy,), 1, 0, fy, gy - one, gy)
            ),
            seltzo_case(
                (sx, 1, 1, ex - one, ey, ex - one),
                ((sy,), 1, 0, fy, (gy + one, fy - two), gy),
            ),
            seltzo_case(
                (sx, 1, 1, ex - one, ey, ex - one),
                ((sy,), 0, 0, fy, (gy, fy - two), gy),
            ),
        ),
    )
    result["SELTZO-TwoSum-POW2-G10-D5-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_pow2,
            x_g10,
            ey < ex + (p + two),
            ex == fx + two,
            fx + (p + two) < ey,
        ),
        z3.Or(
            seltzo_case(
                (sy, 1, 1, ey - one, ex, ey - one), ((sx,), 1, 0, fx, gx - one, gx)
            ),
            seltzo_case(
                (sy, 1, 1, ey - one, ex, ey - one),
                ((sx,), 1, 0, fx, (gx + one, fx - two), gx),
            ),
            seltzo_case(
                (sy, 1, 1, ey - one, ex, ey - one),
                ((sx,), 0, 0, fx, (gx, fx - two), gx),
            ),
        ),
    )

    result["SELTZO-TwoSum-R1R0-R1R0-S4-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_r1r0,
            ex < ey + (p - two),
            ex > fx + (p - two),
            fy + p == ex,
        ),
        seltzo_case(
            (sx, 0, 0, ex + one, ey, gx + one), (sy, 0, 0, fx, fy - (p - one), fx)
        ),
    )
    result["SELTZO-TwoSum-R1R0-R1R0-S4-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_r1r0,
            ey < ex + (p - two),
            ey > fy + (p - two),
            fx + p == ey,
        ),
        seltzo_case(
            (sy, 0, 0, ey + one, ex, gy + one), (sx, 0, 0, fy, fx - (p - one), fy)
        ),
    )

    result["SELTZO-TwoSum-POW2-ONE0-D4-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_pow2,
            y_one0,
            ex < ey + (p + one),
            ey < fy + (p - two),
            fy + (p + one) < ex,
        ),
        seltzo_case(
            (sx, 1, 0, ex - one, ey, ey + one),
            ((sy,), 0, 0, fy, ey - (p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-ONE0-D4-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_pow2,
            x_one0,
            ey < ex + (p + one),
            ex < fx + (p - two),
            fx + (p + one) < ey,
        ),
        seltzo_case(
            (sy, 1, 0, ey - one, ex, ex + one),
            ((sx,), 0, 0, fx, ex - (p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-POW2-MM10-D6-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_mm10, ex > ey + two, fy + (p - one) > ex),
        seltzo_case(
            (sx, 1, 0, ex - one, ey, gy),
            ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-MM10-D6-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_mm10, ey > ex + two, fx + (p - one) > ey),
        seltzo_case(
            (sy, 1, 0, ey - one, ex, gx),
            ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-G10-POW2-S2-X"] = z3.Implies(
        z3.And(
            same_sign, x_g10, y_pow2, ex + one > ey, fx + one < ey, ex < gx + (p - two)
        ),
        seltzo_case_zero((sx, 0, 0, ex + one, ey - one, gx)),
    )
    result["SELTZO-TwoSum-G10-POW2-S2-Y"] = z3.Implies(
        z3.And(
            same_sign, y_g10, x_pow2, ey + one > ex, fy + one < ex, ey < gy + (p - two)
        ),
        seltzo_case_zero((sy, 0, 0, ey + one, ex - one, gy)),
    )

    result["SELTZO-TwoSum-G10-R1R0-D2-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_g10,
            y_r1r0,
            ex > fx + two,
            fx + one > ey,
            fx < ey + two,
            fy + p < ex,
        ),
        seltzo_case(
            (sx, 1, 0, ex, fx + one, gx), ((sy,), 0, 0, gy, fy - (p - one), gy)
        ),
    )
    result["SELTZO-TwoSum-G10-R1R0-D2-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_g10,
            x_r1r0,
            ey > fy + two,
            fy + one > ex,
            fy < ex + two,
            fx + p < ey,
        ),
        seltzo_case(
            (sy, 1, 0, ey, fy + one, gy), ((sx,), 0, 0, gx, fx - (p - one), gx)
        ),
    )

    result["SELTZO-TwoSum-ONE1-G00-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_g00, fx == ey, fy + (p + one) < ex, fy == gy + two),
        z3.Or(
            seltzo_case((sx, 0, 0, ex, ex - p, ex), (sy, 1, 0, fy, gy - one, gy)),
            seltzo_case((sx, 0, 0, ex, ex - p, ex), (sy, 0, 0, fy, gy, gy)),
        ),
    )
    result["SELTZO-TwoSum-ONE1-G00-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_g00, fy == ex, fx + (p + one) < ey, fx == gx + two),
        z3.Or(
            seltzo_case((sy, 0, 0, ey, ey - p, ey), (sx, 1, 0, fx, gx - one, gx)),
            seltzo_case((sy, 0, 0, ey, ey - p, ey), (sx, 0, 0, fx, gx, gx)),
        ),
    )

    result["SELTZO-TwoSum-TWO1-ONE1-S1-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_two1,
            y_one1,
            ex < ey + (p - one),
            fx > ey + one,
            fy + (p - one) < ex,
        ),
        seltzo_case((sx, 0, 0, ex, fx, ey), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-TWO1-ONE1-S1-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_two1,
            x_one1,
            ey < ex + (p - one),
            fy > ex + one,
            fx + (p - one) < ey,
        ),
        seltzo_case((sy, 0, 0, ey, fy, ex), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-MM01-TWO1-D1-X"] = z3.Implies(
        z3.And(
            diff_sign, x_mm01, y_two1, ex < ey + (p - one), fx > ey + one, fy + p < ex
        ),
        seltzo_case((sx, 1, 0, ex, fx, ey), (sy, 1, 0, fy, gy - one, gy)),
    )
    result["SELTZO-TwoSum-MM01-TWO1-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign, y_mm01, x_two1, ey < ex + (p - one), fy > ex + one, fx + p < ey
        ),
        seltzo_case((sy, 1, 0, ey, fy, ex), (sx, 1, 0, fx, gx - one, gx)),
    )

    result["SELTZO-TwoSum-G00-ONE1-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_g00, y_one1, fx == ey, fx == gx + two, fy + (p - one) < ex),
        z3.Or(
            seltzo_case((sx, 0, 0, ex, gx, gx), (sy, 0, 0, fy, fy - p, fy)),
            seltzo_case((sx, 0, 0, ex, fx - one, gx), (sy, 0, 0, fy, fy - p, fy)),
        ),
    )
    result["SELTZO-TwoSum-G00-ONE1-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_g00, x_one1, fy == ex, fy == gy + two, fx + (p - one) < ey),
        z3.Or(
            seltzo_case((sy, 0, 0, ey, gy, gy), (sx, 0, 0, fx, fx - p, fx)),
            seltzo_case((sy, 0, 0, ey, fy - one, gy), (sx, 0, 0, fx, fx - p, fx)),
        ),
    )

    result["SELTZO-TwoSum-ONE1-ONE1-D7-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_one1, ex == ey + p),
        seltzo_case(
            (sx, 0, 1, ex, fx - one, fx), ((sy,), 1, 0, ey - one, fy - one, fy)
        ),
    )
    result["SELTZO-TwoSum-ONE1-ONE1-D7-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_one1, ey == ex + p),
        seltzo_case(
            (sy, 0, 1, ey, fy - one, fy), ((sx,), 1, 0, ex - one, fx - one, fx)
        ),
    )

    result["SELTZO-TwoSum-POW2-G10-S3-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g10, ex == ey + p, fy == gy + two),
        z3.Or(
            seltzo_case(
                (sx, 0, 1, ex, fx + one, fx + two), ((sy,), 1, 0, fy, gy - one, gy)
            ),
            seltzo_case((sx, 0, 1, ex, fx + one, fx + two), ((sy,), 0, 0, fy, gy, gy)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G10-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g10, ey == ex + p, fx == gx + two),
        z3.Or(
            seltzo_case(
                (sy, 0, 1, ey, fy + one, fy + two), ((sx,), 1, 0, fx, gx - one, gx)
            ),
            seltzo_case((sy, 0, 1, ey, fy + one, fy + two), ((sx,), 0, 0, fx, gx, gx)),
        ),
    )

    result["SELTZO-TwoSum-ONE1-G10-D3-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_one1,
            y_g10,
            ex < fx + (p - two),
            fx < ey,
            fy == gy + three,
            ex == gy + (p + two),
        ),
        z3.Or(
            seltzo_case((sx, 1, 0, ex - one, ey, fy + one), (sy, 0, 0, gy, gy - p, gy)),
            seltzo_case((sx, 1, 0, ex - one, ey, fy), ((sy,), 0, 0, gy, gy - p, gy)),
            seltzo_case((sx, 1, 1, ex - one, ey, fy + one), (sy, 0, 0, gy, gy - p, gy)),
            seltzo_case(
                (sx, 1, 1, ex - one, ey, fy + one), ((sy,), 0, 0, gy, gy - p, gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-ONE1-G10-D3-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_one1,
            x_g10,
            ey < fy + (p - two),
            fy < ex,
            fx == gx + three,
            ey == gx + (p + two),
        ),
        z3.Or(
            seltzo_case((sy, 1, 0, ey - one, ex, fx + one), (sx, 0, 0, gx, gx - p, gx)),
            seltzo_case((sy, 1, 0, ey - one, ex, fx), ((sx,), 0, 0, gx, gx - p, gx)),
            seltzo_case((sy, 1, 1, ey - one, ex, fx + one), (sx, 0, 0, gx, gx - p, gx)),
            seltzo_case(
                (sy, 1, 1, ey - one, ex, fx + one), ((sx,), 0, 0, gx, gx - p, gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-POW2-G00-D10-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g00, fy + p == ex, fy == gy + three),
        z3.Or(
            seltzo_case((sx, 1, 1, ex - one, ey, ey), (sy, 0, 0, gy, gy - p, gy)),
            seltzo_case(
                (sx, 1, 1, ex - one, ey, ey), (sy, 1, 0, gy + one, gy - one, gy)
            ),
            seltzo_case(
                (sx, 1, 0, ex - one, ey, fx + one), ((sy,), 0, 0, gy, gy - p, gy)
            ),
            seltzo_case(
                (sx, 1, 0, ex - one, ey, fx + one),
                ((sy,), 1, 0, gy + one, gy - one, gy),
            ),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-D10-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g00, fx + p == ey, fx == gx + three),
        z3.Or(
            seltzo_case((sy, 1, 1, ey - one, ex, ex), (sx, 0, 0, gx, gx - p, gx)),
            seltzo_case(
                (sy, 1, 1, ey - one, ex, ex), (sx, 1, 0, gx + one, gx - one, gx)
            ),
            seltzo_case(
                (sy, 1, 0, ey - one, ex, fy + one), ((sx,), 0, 0, gx, gx - p, gx)
            ),
            seltzo_case(
                (sy, 1, 0, ey - one, ex, fy + one),
                ((sx,), 1, 0, gx + one, gx - one, gx),
            ),
        ),
    )

    result["SELTZO-TwoSum-ONE0-R1R0-S1-X"] = z3.Implies(
        z3.And(same_sign, x_one0, y_r1r0, ex > ey, ex < fx + (p - two), fx < fy + one),
        seltzo_case(
            (sx, 0, 0, ex + one, ey, fx),
            ((sy,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-ONE0-R1R0-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_one0, x_r1r0, ey > ex, ey < fy + (p - two), fy < fx + one),
        seltzo_case(
            (sy, 0, 0, ey + one, ex, fy),
            ((sx,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-G10-ONE1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_g10, y_one1, ex == ey + (p - one)),
        seltzo_case((sx, 1, 1, ex, fx, gx), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-G10-ONE1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_g10, x_one1, ey == ex + (p - one)),
        seltzo_case((sy, 1, 1, ey, fy, gy), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-ONE1-ONE1-D8-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_one1, fx + one == ey, fy + p < ex),
        seltzo_case((sx, 1, 0, ex - one, fx - one, fx), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-ONE1-ONE1-D8-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_one1, fy + one == ex, fx + p < ey),
        seltzo_case((sy, 1, 0, ey - one, fy - one, fy), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-POW2-MM10-D7-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_mm10, ey < fy + (p - three), fy + p == ex),
        seltzo_case(
            (sx, 1, 1, ex - one, ey, ey), (sy, 1, 0, gy - one, ey - p, ey - (p - one))
        ),
    )
    result["SELTZO-TwoSum-POW2-MM10-D7-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_mm10, ex < fx + (p - three), fx + p == ey),
        seltzo_case(
            (sy, 1, 1, ey - one, ex, ex), (sx, 1, 0, gx - one, ex - p, ex - (p - one))
        ),
    )

    result["SELTZO-TwoSum-ONE1-TWO1-D7-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_two1, fx < ey, fy + p == ex),
        seltzo_case(
            (sx, 1, 0, ex - one, ey - one, fy + one), ((sy,), 0, 0, gy, gy - p, gy)
        ),
    )
    result["SELTZO-TwoSum-ONE1-TWO1-D7-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_two1, fy < ex, fx + p == ey),
        seltzo_case(
            (sy, 1, 0, ey - one, ex - one, fx + one), ((sx,), 0, 0, gx, gx - p, gx)
        ),
    )

    result["SELTZO-TwoSum-G10-ONE1-S2-X"] = z3.Implies(
        z3.And(
            same_sign, x_g10, y_one1, ex < ey + (p - one), ey < gx, fy + (p - one) < ex
        ),
        seltzo_case((sx, 1, 0, ex, fx, ey), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-G10-ONE1-S2-Y"] = z3.Implies(
        z3.And(
            same_sign, y_g10, x_one1, ey < ex + (p - one), ex < gy, fx + (p - one) < ey
        ),
        seltzo_case((sy, 1, 0, ey, fy, ex), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-POW2-ONE0-D5-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_one0, ex == ey + (p + one), ey > fy + (p - three)),
        seltzo_case(
            (sx, 1, 1, ex - one, ey, ex - one), ((sy,), 1, 0, fy, fy - two, fy - one)
        ),
    )
    result["SELTZO-TwoSum-POW2-ONE0-D5-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_one0, ey == ex + (p + one), ex > fx + (p - three)),
        seltzo_case(
            (sy, 1, 1, ey - one, ex, ey - one), ((sx,), 1, 0, fx, fx - two, fx - one)
        ),
    )

    result["SELTZO-TwoSum-TWO1-ALL1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_two1, y_all1, ex == ey + two, fx < ey),
        seltzo_case(
            (sx, 0, 0, ex - one, fx, gx),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-TWO1-ALL1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_two1, x_all1, ey == ex + two, fy < ex),
        seltzo_case(
            (sy, 0, 0, ey - one, fy, gy),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-TWO0-POW2-S3-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_two0,
            y_pow2,
            ex + one > ey,
            ex < fx + (p - three),
            fx + one < ey,
        ),
        seltzo_case(
            (sx, 0, 0, ex + one, ey - one, gx),
            ((sy,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-TWO0-POW2-S3-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_two0,
            x_pow2,
            ey + one > ex,
            ey < fy + (p - three),
            fy + one < ex,
        ),
        seltzo_case(
            (sy, 0, 0, ey + one, ex - one, gy),
            ((sx,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-G10-R1R0-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_g10, y_r1r0, ex == ey + (p - one), ex > gx + (p - three)),
        z3.Or(
            seltzo_case(
                (sx, 1, 0, ex, fx, (gx + one, fx - one)),
                ((sy,), 0, 0, gy, fy - (p - one), gy),
            ),
            seltzo_case(
                (sx, 1, 0, ex, fx, fx + one), ((sy,), 0, 0, gy, fy - (p - one), gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-G10-R1R0-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_g10, x_r1r0, ey == ex + (p - one), ey > gy + (p - three)),
        z3.Or(
            seltzo_case(
                (sy, 1, 0, ey, fy, (gy + one, fy - one)),
                ((sx,), 0, 0, gx, fx - (p - one), gx),
            ),
            seltzo_case(
                (sy, 1, 0, ey, fy, fy + one), ((sx,), 0, 0, gx, fx - (p - one), gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-POW2-G00-D11-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g00, ex == ey + (p + one), ey == fy + two),
        seltzo_case(
            (sx, 1, 1, ex - one, ey, ex - one),
            ((sy,), 0, 0, ey - one, (gy, fy - one), gy),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-D11-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g00, ey == ex + (p + one), ex == fx + two),
        seltzo_case(
            (sy, 1, 1, ey - one, ex, ey - one),
            ((sx,), 0, 0, ex - one, (gx, fx - one), gx),
        ),
    )

    result["SELTZO-TwoSum-ONE1-R0R1-D5-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_r0r1, ex == ey + p, ey > fy + (p - two)),
        seltzo_case(
            (sx, 0, 1, ex, fx - one, fx), ((sy,), 1, 0, ey - one, fy - one, fy)
        ),
    )
    result["SELTZO-TwoSum-ONE1-R0R1-D5-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_r0r1, ey == ex + p, ex > fx + (p - two)),
        seltzo_case(
            (sy, 0, 1, ey, fy - one, fy), ((sx,), 1, 0, ex - one, fx - one, fx)
        ),
    )

    result["SELTZO-TwoSum-R1R0-G00-S7-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_g00,
            fy == gy + three,
            ex == gy + (p - one),
            fx + one == fy,
        ),
        z3.Or(
            seltzo_case((sx, 0, 0, ex + one, ey, ey), (sy, 0, 0, gy, gy - p, gy)),
            seltzo_case((sx, 0, 0, ex + one, ey, fx), (sy, 0, 0, gy, gy - p, gy)),
            seltzo_case((sx, 0, 0, ex + one, ey, fx), ((sy,), 0, 0, gy, gy - p, gy)),
            seltzo_case((sx, 0, 0, ex + one, ey, gx), ((sy,), 0, 0, gy, gy - p, gy)),
        ),
    )
    result["SELTZO-TwoSum-R1R0-G00-S7-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_g00,
            fx == gx + three,
            ey == gx + (p - one),
            fy + one == fx,
        ),
        z3.Or(
            seltzo_case((sy, 0, 0, ey + one, ex, ex), (sx, 0, 0, gx, gx - p, gx)),
            seltzo_case((sy, 0, 0, ey + one, ex, fy), (sx, 0, 0, gx, gx - p, gx)),
            seltzo_case((sy, 0, 0, ey + one, ex, fy), ((sx,), 0, 0, gx, gx - p, gx)),
            seltzo_case((sy, 0, 0, ey + one, ex, gy), ((sx,), 0, 0, gx, gx - p, gx)),
        ),
    )

    result["SELTZO-TwoSum-G01-POW2-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_g01, y_pow2, ex == ey + p, ex < gx + (p - two)),
        seltzo_case((sx, 0, 0, ex, fx, ey + two), ((sy,), 0, 0, ey, fy, ey)),
    )
    result["SELTZO-TwoSum-G01-POW2-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_g01, x_pow2, ey == ex + p, ey < gy + (p - two)),
        seltzo_case((sy, 0, 0, ey, fy, ex + two), ((sx,), 0, 0, ex, fx, ex)),
    )

    result["SELTZO-TwoSum-TWO1-R1R0-D5-X"] = z3.Implies(
        z3.And(diff_sign, x_two1, y_r1r0, fx > ey + one, fy + p > ex),
        seltzo_case_zero((sx, 0, 0, ex, fx, gy)),
    )
    result["SELTZO-TwoSum-TWO1-R1R0-D5-Y"] = z3.Implies(
        z3.And(diff_sign, y_two1, x_r1r0, fy > ex + one, fx + p > ey),
        seltzo_case_zero((sy, 0, 0, ey, fy, gx)),
    )

    result["SELTZO-TwoSum-POW2-G10-D6-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g10, ex == ey + one, fy == gy + three),
        z3.Or(
            seltzo_case_zero((sx, 1, 0, fy, gy - one, gy)),
            seltzo_case_zero((sx, 0, 0, fy, gy, gy)),
            seltzo_case_zero((sx, 0, 0, fy, gy + one, gy)),
            seltzo_case_zero((sx, 1, 0, fy, gy + one, gy)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G10-D6-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g10, ey == ex + one, fx == gx + three),
        z3.Or(
            seltzo_case_zero((sy, 1, 0, fx, gx - one, gx)),
            seltzo_case_zero((sy, 0, 0, fx, gx, gx)),
            seltzo_case_zero((sy, 0, 0, fx, gx + one, gx)),
            seltzo_case_zero((sy, 1, 0, fx, gx + one, gx)),
        ),
    )

    result["SELTZO-TwoSum-ONE1-G10-D4-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_g10, fx == ey, fy + (p + one) < ex, fy == gy + two),
        z3.Or(
            seltzo_case(
                (sx, 1, 0, ex - one, fx - one, fx), ((sy,), 1, 0, fy, gy - one, gy)
            ),
            seltzo_case((sx, 1, 0, ex - one, fx - one, fx), ((sy,), 0, 0, fy, gy, gy)),
        ),
    )
    result["SELTZO-TwoSum-ONE1-G10-D4-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_g10, fy == ex, fx + (p + one) < ey, fx == gx + two),
        z3.Or(
            seltzo_case(
                (sy, 1, 0, ey - one, fy - one, fy), ((sx,), 1, 0, fx, gx - one, gx)
            ),
            seltzo_case((sy, 1, 0, ey - one, fy - one, fy), ((sx,), 0, 0, fx, gx, gx)),
        ),
    )

    result["SELTZO-TwoSum-R1R0-ONE1-D6-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_r1r0,
            y_one1,
            ex < ey + (p - one),
            ex == fx + two,
            fy + (p - one) < ex,
        ),
        seltzo_case((sx, 0, 0, ex, fx, ey), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-R1R0-ONE1-D6-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_r1r0,
            x_one1,
            ey < ex + (p - one),
            ey == fy + two,
            fx + (p - one) < ey,
        ),
        seltzo_case((sy, 0, 0, ey, fy, ex), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-R1R0-POW2-S2-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_pow2,
            ex + one > ey,
            ex < ey + (p - two),
            ex > fx + (p - two),
        ),
        seltzo_case_zero((sx, 0, 1, ex + one, ey - one, ey)),
    )
    result["SELTZO-TwoSum-R1R0-POW2-S2-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_pow2,
            ey + one > ex,
            ey < ex + (p - two),
            ey > fy + (p - two),
        ),
        seltzo_case_zero((sy, 0, 1, ey + one, ex - one, ex)),
    )

    result["SELTZO-TwoSum-G00-TWO1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_g00, y_two1, ey < gx, fy + (p - one) == ex),
        seltzo_case((sx, 0, 0, ex, fx, fy + one), ((sy,), 0, 0, gy, gy - p, gy)),
    )
    result["SELTZO-TwoSum-G00-TWO1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_g00, x_two1, ex < gy, fx + (p - one) == ey),
        seltzo_case((sy, 0, 0, ey, fy, fx + one), ((sx,), 0, 0, gx, gx - p, gx)),
    )

    result["SELTZO-TwoSum-G11-ONE1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_g11, y_one1, ex == fx + two, ey > gx, fy + p < ex),
        z3.Or(
            seltzo_case((sx, 0, 1, ex, fx, gx), (sy, 0, 0, fy, fy - p, fy)),
            seltzo_case((sx, 1, 1, ex, fx, gx), (sy, 0, 0, fy, fy - p, fy)),
        ),
    )
    result["SELTZO-TwoSum-G11-ONE1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_g11, x_one1, ey == fy + two, ex > gy, fx + p < ey),
        z3.Or(
            seltzo_case((sy, 0, 1, ey, fy, gy), (sx, 0, 0, fx, fx - p, fx)),
            seltzo_case((sy, 1, 1, ey, fy, gy), (sx, 0, 0, fx, fx - p, fx)),
        ),
    )

    result["SELTZO-TwoSum-ONE0-ALL1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_one0, y_all1, ex == ey + p, ex == fx + (p - three)),
        seltzo_case(
            (sx, 1, 0, ex, fx, fx - one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-ONE0-ALL1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_one0, x_all1, ey == ex + p, ey == fy + (p - three)),
        seltzo_case(
            (sy, 1, 0, ey, fy, fy - one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-MM10-D8-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_mm10, ex == ey + two, fy + (p - one) > ex),
        seltzo_case(
            (sx, 0, 0, ex - one, ey - one, gy),
            ((sy,), 0, 0, fx - one, fx - (p + one), fx - one),
        ),
    )
    result["SELTZO-TwoSum-POW2-MM10-D8-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_mm10, ey == ex + two, fx + (p - one) > ey),
        seltzo_case(
            (sy, 0, 0, ey - one, ex - one, gx),
            ((sx,), 0, 0, fy - one, fy - (p + one), fy - one),
        ),
    )

    result["SELTZO-TwoSum-POW2-MM10-S4-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_mm10, ex == ey + one, ey < fy + (p - three)),
        seltzo_case((sx, 1, 0, ex, ey - one, gy), ((sy,), 0, 0, fx, fx - p, fx)),
    )
    result["SELTZO-TwoSum-POW2-MM10-S4-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_mm10, ey == ex + one, ex < fx + (p - three)),
        seltzo_case((sy, 1, 0, ey, ex - one, gx), ((sx,), 0, 0, fy, fy - p, fy)),
    )

    result["SELTZO-TwoSum-TWO0-ONE1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_two0, y_one1, ex == ey + (p - one), ex < fx + (p - three)),
        seltzo_case((sx, 1, 0, ex, fx, ey + one), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-TWO0-ONE1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_two0, x_one1, ey == ex + (p - one), ey < fy + (p - three)),
        seltzo_case((sy, 1, 0, ey, fy, ex + one), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-ONE1-MM10-D1-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_one1,
            y_mm10,
            ex > ey + one,
            fx < ey,
            fy + (p - one) > ex,
            fx > fy,
        ),
        seltzo_case(
            (sx, 1, 0, ex - one, ey - one, gy),
            ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-ONE1-MM10-D1-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_one1,
            x_mm10,
            ey > ex + one,
            fy < ex,
            fx + (p - one) > ey,
            fy > fx,
        ),
        seltzo_case(
            (sy, 1, 0, ey - one, ex - one, gx),
            ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-ONE1-ONE0-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_one0, ex == ey + p, ey < fy + (p - two)),
        seltzo_case(
            (sx, 0, 1, ex, fx - one, fx),
            ((sy,), 0, 0, fy, ey - (p - one), ey - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-ONE1-ONE0-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_one0, ey == ex + p, ex < fx + (p - two)),
        seltzo_case(
            (sy, 0, 1, ey, fy - one, fy),
            ((sx,), 0, 0, fx, ex - (p - one), ex - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-G11-ONE1-D2-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_g11,
            y_one1,
            ex > ey + (p - two),
            fx == gx + three,
            ey + two > gx,
        ),
        z3.Or(
            seltzo_case((sx, 1, 0, ex, fx, fx + one), (sy, 0, 0, fy, fy - p, fy)),
            seltzo_case((sx, 1, 0, ex, fx, fx - one), (sy, 0, 0, fy, fy - p, fy)),
            seltzo_case((sx, 1, 0, ex, fx, gx + one), (sy, 0, 0, fy, fy - p, fy)),
        ),
    )
    result["SELTZO-TwoSum-G11-ONE1-D2-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_g11,
            x_one1,
            ey > ex + (p - two),
            fy == gy + three,
            ex + two > gy,
        ),
        z3.Or(
            seltzo_case((sy, 1, 0, ey, fy, fy + one), (sx, 0, 0, fx, fx - p, fx)),
            seltzo_case((sy, 1, 0, ey, fy, fy - one), (sx, 0, 0, fx, fx - p, fx)),
            seltzo_case((sy, 1, 0, ey, fy, gy + one), (sx, 0, 0, fx, fx - p, fx)),
        ),
    )

    result["SELTZO-TwoSum-TWO1-R1R0-D6-X"] = z3.Implies(
        z3.And(diff_sign, x_two1, y_r1r0, fx < ey, fy + (p + one) < ex),
        seltzo_case(
            (sx, 1, 0, ex - one, ey, gx), ((sy,), 0, 0, gy, fy - (p - one), gy)
        ),
    )
    result["SELTZO-TwoSum-TWO1-R1R0-D6-Y"] = z3.Implies(
        z3.And(diff_sign, y_two1, x_r1r0, fy < ex, fx + (p + one) < ey),
        seltzo_case(
            (sy, 1, 0, ey - one, ex, gy), ((sx,), 0, 0, gx, fx - (p - one), gx)
        ),
    )

    result["SELTZO-TwoSum-POW2-G00-D12-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g00, fy + (p + one) == ex, fy == gy + two),
        z3.Or(
            seltzo_case((sx, 1, 1, ex - one, ey, ey), ((sy,), 0, 0, gy, gy - p, gy)),
            seltzo_case(
                (sx, 1, 1, ex - one, ey, ey), ((sy,), 1, 0, fy - one, gy - one, gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-D12-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g00, fx + (p + one) == ey, fx == gx + two),
        z3.Or(
            seltzo_case((sy, 1, 1, ey - one, ex, ex), ((sx,), 0, 0, gx, gx - p, gx)),
            seltzo_case(
                (sy, 1, 1, ey - one, ex, ex), ((sx,), 1, 0, fx - one, gx - one, gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-ONE0-POW2-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_one0, y_pow2, ex == ey + (p - one), ex < fx + (p - two)),
        seltzo_case_zero((sx, 1, 0, ex, fx, ey + one)),
    )
    result["SELTZO-TwoSum-ONE0-POW2-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_one0, x_pow2, ey == ex + (p - one), ey < fy + (p - two)),
        seltzo_case_zero((sy, 1, 0, ey, fy, ex + one)),
    )

    result["SELTZO-TwoSum-POW2-R1R0-D4-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_r1r0, ex == ey + two, ey < fy + (p - one)),
        seltzo_case_zero((sx, 0, 0, ex - one, gy, gy)),
    )
    result["SELTZO-TwoSum-POW2-R1R0-D4-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_r1r0, ey == ex + two, ex < fx + (p - one)),
        seltzo_case_zero((sy, 0, 0, ey - one, gx, gx)),
    )

    result["SELTZO-TwoSum-POW2-TWO0-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_two0, ex == ey + two, fy + (p - one) > ex),
        seltzo_case(
            (sx, 0, 0, ex - one, fy, gy),
            ((sy,), 0, 0, fx - one, fx - (p + one), fx - one),
        ),
    )
    result["SELTZO-TwoSum-POW2-TWO0-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_two0, ey == ex + two, fx + (p - one) > ey),
        seltzo_case(
            (sy, 0, 0, ey - one, fx, gx),
            ((sx,), 0, 0, fy - one, fy - (p + one), fy - one),
        ),
    )

    result["SELTZO-TwoSum-R1R0-MM10-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_mm10, ex == ey + p, ex > fx + two, ey > fy + two),
        seltzo_case(
            (sx, 1, 1, ex, gx, gx), ((sy,), 1, 0, ey - one, fy, ey - (p - one))
        ),
    )
    result["SELTZO-TwoSum-R1R0-MM10-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_mm10, ey == ex + p, ey > fy + two, ex > fx + two),
        seltzo_case(
            (sy, 1, 1, ey, gy, gy), ((sx,), 1, 0, ex - one, fx, ex - (p - one))
        ),
    )

    result["SELTZO-TwoSum-ONE1-ALL1-S1-X"] = z3.Implies(
        z3.And(same_sign, x_one1, y_all1, ex < ey + p, fx > ey + one),
        seltzo_case(
            (sx, 0, 0, ex, fx, ey + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-ONE1-ALL1-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_one1, x_all1, ey < ex + p, fy > ex + one),
        seltzo_case(
            (sy, 0, 0, ey, fy, ex + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-R1R0-R1R0-S5-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, y_r1r0, ex < ey + p, fx == ey + one, fy + p < ex),
        seltzo_case((sx, 1, 0, ex, ey, fx), ((sy,), 0, 0, gy, fy - (p - one), gy)),
    )
    result["SELTZO-TwoSum-R1R0-R1R0-S5-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_r1r0, ey < ex + p, fy == ex + one, fx + p < ey),
        seltzo_case((sy, 1, 0, ey, ex, fy), ((sx,), 0, 0, gx, fx - (p - one), gx)),
    )

    result["SELTZO-TwoSum-ONE0-POW2-D4-X"] = z3.Implies(
        z3.And(diff_sign, x_one0, y_pow2, ex == ey, ex > fx + two),
        seltzo_case_zero((sx, 1, 0, ex - one, fx, fy + one)),
    )
    result["SELTZO-TwoSum-ONE0-POW2-D4-Y"] = z3.Implies(
        z3.And(diff_sign, y_one0, x_pow2, ey == ex, ey > fy + two),
        seltzo_case_zero((sy, 1, 0, ey - one, fy, fx + one)),
    )

    result["SELTZO-TwoSum-POW2-G00-D13-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g00, fy + p == ex, fy == gy + two),
        z3.Or(
            seltzo_case((sx, 1, 1, ex - one, ey, ey), (sy, 0, 0, gy, gy - p, gy)),
            seltzo_case(
                (sx, 1, 0, ex - one, ey, fx + one), ((sy,), 0, 0, gy, gy - p, gy)
            ),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-D13-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g00, fx + p == ey, fx == gx + two),
        z3.Or(
            seltzo_case((sy, 1, 1, ey - one, ex, ex), (sx, 0, 0, gx, gx - p, gx)),
            seltzo_case(
                (sy, 1, 0, ey - one, ex, fy + one), ((sx,), 0, 0, gx, gx - p, gx)
            ),
        ),
    )

    result["SELTZO-TwoSum-POW2-G01-S6-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_pow2,
            y_g01,
            ex > ey + one,
            fy == gy + three,
            ex == gy + (p - one),
        ),
        z3.Or(
            seltzo_case(
                (sx, 0, 1, ex, ey, gy + one),
                ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
            ),
            seltzo_case(
                (sx, 0, 1, ex, ey, fy - one),
                ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
            ),
            seltzo_case(
                (sx, 0, 1, ex, ey, fy + one),
                ((sy,), 0, 0, ey - (p - one), ey - (p + p - one), ey - (p - one)),
            ),
        ),
    )
    result["SELTZO-TwoSum-POW2-G01-S6-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_pow2,
            x_g01,
            ey > ex + one,
            fx == gx + three,
            ey == gx + (p - one),
        ),
        z3.Or(
            seltzo_case(
                (sy, 0, 1, ey, ex, gx + one),
                ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
            ),
            seltzo_case(
                (sy, 0, 1, ey, ex, fx - one),
                ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
            ),
            seltzo_case(
                (sy, 0, 1, ey, ex, fx + one),
                ((sx,), 0, 0, ex - (p - one), ex - (p + p - one), ex - (p - one)),
            ),
        ),
    )

    result["SELTZO-TwoSum-ONE1-MM01-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_mm01, fx > ey + one, fy + (p - one) == ex),
        seltzo_case((sx, 0, 0, ex, fx - one, fy + one), (sy, 0, 0, gy, gy - p, gy)),
    )
    result["SELTZO-TwoSum-ONE1-MM01-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_mm01, fy > ex + one, fx + (p - one) == ey),
        seltzo_case((sy, 0, 0, ey, fy - one, fx + one), (sx, 0, 0, gx, gx - p, gx)),
    )

    result["SELTZO-TwoSum-POW2-G00-D14-X"] = z3.Implies(
        z3.And(
            diff_sign, x_pow2, y_g00, ex < ey + p, fy + (p + one) < ex, fy == gy + two
        ),
        z3.Or(
            seltzo_case(
                (sx, 1, 0, ex - one, ey - one, ey), (sy, 1, 0, fy, gy - one, gy)
            ),
            seltzo_case((sx, 1, 0, ex - one, ey - one, ey), (sy, 0, 0, fy, gy, gy)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-D14-Y"] = z3.Implies(
        z3.And(
            diff_sign, y_pow2, x_g00, ey < ex + p, fx + (p + one) < ey, fx == gx + two
        ),
        z3.Or(
            seltzo_case(
                (sy, 1, 0, ey - one, ex - one, ex), (sx, 1, 0, fx, gx - one, gx)
            ),
            seltzo_case((sy, 1, 0, ey - one, ex - one, ex), (sx, 0, 0, fx, gx, gx)),
        ),
    )

    result["SELTZO-TwoSum-MM01-R0R1-S1-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_mm01,
            y_r0r1,
            ex + one > ey,
            ex < fx + (p - three),
            fx + one < ey,
            ey > fy + (p - two),
        ),
        seltzo_case((sx, 0, 0, ex + one, ey - one, gx), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-MM01-R0R1-S1-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_mm01,
            x_r0r1,
            ey + one > ex,
            ey < fy + (p - three),
            fy + one < ex,
            ex > fx + (p - two),
        ),
        seltzo_case((sy, 0, 0, ey + one, ex - one, gy), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-POW2-R0R1-D11-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_r0r1, ex == ey + p, ey < fy + (p - one)),
        seltzo_case(
            (sx, 1, 1, ex - one, fx - one, ex - one),
            (sy, 1, 0, fy, fx - p, fx - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-R0R1-D11-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_r0r1, ey == ex + p, ex < fx + (p - one)),
        seltzo_case(
            (sy, 1, 1, ey - one, fy - one, ey - one),
            (sx, 1, 0, fx, fy - p, fy - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-R1R0-G00-S8-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_g00,
            ex < fx + (p - one),
            fx + three == ey,
            fy + (p - one) < ex,
            fy == gy + two,
        ),
        z3.Or(
            seltzo_case(
                (sx, 0, 0, ex + one, gx + one, gx), (sy, 1, 0, fy, gy - one, gy)
            ),
            seltzo_case((sx, 0, 0, ex + one, gx + one, gx), (sy, 0, 0, fy, gy, gy)),
        ),
    )
    result["SELTZO-TwoSum-R1R0-G00-S8-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_g00,
            ey < fy + (p - one),
            fy + three == ex,
            fx + (p - one) < ey,
            fx == gx + two,
        ),
        z3.Or(
            seltzo_case(
                (sy, 0, 0, ey + one, gy + one, gy), (sx, 1, 0, fx, gx - one, gx)
            ),
            seltzo_case((sy, 0, 0, ey + one, gy + one, gy), (sx, 0, 0, fx, gx, gx)),
        ),
    )

    result["SELTZO-TwoSum-G00-ALL1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_g00, y_all1, fx == ey, fx == gx + two),
        z3.Or(
            seltzo_case(
                (sx, 1, 0, ex - one, gx - one, gx),
                ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
            ),
            seltzo_case(
                (sx, 1, 0, ex - one, fx - one, gx),
                ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
            ),
        ),
    )
    result["SELTZO-TwoSum-G00-ALL1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_g00, x_all1, fy == ex, fy == gy + two),
        z3.Or(
            seltzo_case(
                (sy, 1, 0, ey - one, gy - one, gy),
                ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
            ),
            seltzo_case(
                (sy, 1, 0, ey - one, fy - one, gy),
                ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
            ),
        ),
    )

    result["SELTZO-TwoSum-R1R0-G00-S9-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_g00,
            ex == fx + (p - two),
            fy == gy + two,
            fx + one == fy,
        ),
        z3.Or(
            seltzo_case((sx, 0, 0, ex + one, ey, ey), (sy, 0, 0, gy, gy - p, gy)),
            seltzo_case((sx, 0, 0, ex + one, ey, gx), ((sy,), 0, 0, gy, gy - p, gy)),
        ),
    )
    result["SELTZO-TwoSum-R1R0-G00-S9-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_g00,
            ey == fy + (p - two),
            fx == gx + two,
            fy + one == fx,
        ),
        z3.Or(
            seltzo_case((sy, 0, 0, ey + one, ex, ex), (sx, 0, 0, gx, gx - p, gx)),
            seltzo_case((sy, 0, 0, ey + one, ex, gy), ((sx,), 0, 0, gx, gx - p, gx)),
        ),
    )

    result["SELTZO-TwoSum-G11-ONE1-D3-X"] = z3.Implies(
        z3.And(diff_sign, x_g11, y_one1, ex == ey + (p - one), ex < gx + (p - two)),
        seltzo_case((sx, 1, 0, ex, fx, ey + one), (sy, 0, 0, fy, fy - p, fy)),
    )
    result["SELTZO-TwoSum-G11-ONE1-D3-Y"] = z3.Implies(
        z3.And(diff_sign, y_g11, x_one1, ey == ex + (p - one), ey < gy + (p - two)),
        seltzo_case((sy, 1, 0, ey, fy, ex + one), (sx, 0, 0, fx, fx - p, fx)),
    )

    result["SELTZO-TwoSum-ONE1-R0R1-D6-X"] = z3.Implies(
        z3.And(
            diff_sign, x_one1, y_r0r1, ex > ey + two, fx == ey, fy + (p + one) == ex
        ),
        seltzo_case(
            (sx, 1, 1, ex - one, fy, ex - one),
            ((sy,), 0, 0, fx - (p - one), fx - (p + p - one), fx - (p - one)),
        ),
    )
    result["SELTZO-TwoSum-ONE1-R0R1-D6-Y"] = z3.Implies(
        z3.And(
            diff_sign, y_one1, x_r0r1, ey > ex + two, fy == ex, fx + (p + one) == ey
        ),
        seltzo_case(
            (sy, 1, 1, ey - one, fx, ey - one),
            ((sx,), 0, 0, fy - (p - one), fy - (p + p - one), fy - (p - one)),
        ),
    )

    result["SELTZO-TwoSum-TWO1-R1R0-D7-X"] = z3.Implies(
        z3.And(diff_sign, x_two1, y_r1r0, ex < ey + p, fx > ey + two, fy + p < ex),
        seltzo_case(
            (sx, 0, 0, ex, fx, ey + one), ((sy,), 0, 0, gy, fy - (p - one), gy)
        ),
    )
    result["SELTZO-TwoSum-TWO1-R1R0-D7-Y"] = z3.Implies(
        z3.And(diff_sign, y_two1, x_r1r0, ey < ex + p, fy > ex + two, fx + p < ey),
        seltzo_case(
            (sy, 0, 0, ey, fy, ex + one), ((sx,), 0, 0, gx, fx - (p - one), gx)
        ),
    )

    result["SELTZO-TwoSum-ONE1-TWO1-D8-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_two1, ex == ey + (p - one)),
        seltzo_case((sx, 0, 1, ex, fx - one, fx), (sy, 1, 0, fy, gy - one, gy)),
    )
    result["SELTZO-TwoSum-ONE1-TWO1-D8-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_two1, ey == ex + (p - one)),
        seltzo_case((sy, 0, 1, ey, fy - one, fy), (sx, 1, 0, fx, gx - one, gx)),
    )

    result["SELTZO-TwoSum-TWO0-ALL1-D1-X"] = z3.Implies(
        z3.And(diff_sign, x_two0, y_all1, ex == ey + p, ex < fx + (p - three)),
        seltzo_case(
            (sx, 1, 0, ex, fx, ey + two),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-TWO0-ALL1-D1-Y"] = z3.Implies(
        z3.And(diff_sign, y_two0, x_all1, ey == ex + p, ey < fy + (p - three)),
        seltzo_case(
            (sy, 1, 0, ey, fy, ex + two),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-TWO1-D10-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_two1, ex > ey + two, fy + (p - one) == ex),
        seltzo_case_zero((sx, 1, 1, ex - one, ey, fy)),
    )
    result["SELTZO-TwoSum-POW2-TWO1-D10-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_two1, ey > ex + two, fx + (p - one) == ey),
        seltzo_case_zero((sy, 1, 1, ey - one, ex, fx)),
    )

    result["SELTZO-TwoSum-ALL1-TWO1-D2-X"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_two1, ex == ey, ey == fy + two),
        seltzo_case_zero((sx, 0, 0, ex - one, gy - one, fx + one)),
    )
    result["SELTZO-TwoSum-ALL1-TWO1-D2-Y"] = z3.Implies(
        z3.And(diff_sign, y_all1, x_two1, ey == ex, ex == fx + two),
        seltzo_case_zero((sy, 0, 0, ey - one, gx - one, fy + one)),
    )

    result["SELTZO-TwoSum-R1R0-ALL1-S2-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, y_all1, ex < ey + p, fx > ey + one),
        seltzo_case(
            (sx, 1, 0, ex, fx, ey + one),
            ((sy,), 0, 0, fy + one, fy - (p - one), fy + one),
        ),
    )
    result["SELTZO-TwoSum-R1R0-ALL1-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_all1, ey < ex + p, fy > ex + one),
        seltzo_case(
            (sy, 1, 0, ey, fy, ex + one),
            ((sx,), 0, 0, fx + one, fx - (p - one), fx + one),
        ),
    )

    result["SELTZO-TwoSum-POW2-G00-D15-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_g00, ex > ey + two, fy == gy + two, ex == gy + p),
        z3.Or(
            seltzo_case_zero((sx, 1, 1, ex - one, ey, fx + one)),
            seltzo_case_zero((sx, 1, 1, ex - one, ey, fy)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-D15-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_g00, ey > ex + two, fx == gx + two, ey == gx + p),
        z3.Or(
            seltzo_case_zero((sy, 1, 1, ey - one, ex, fy + one)),
            seltzo_case_zero((sy, 1, 1, ey - one, ex, fx)),
        ),
    )

    result["SELTZO-TwoSum-POW2-G01-S7-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g01, ex == ey + (p - one), ey > gy + (p - three)),
        z3.Or(
            seltzo_case(
                (sx, 0, 1, ex, ey, ey + one), (sy, 0, 0, fy, gy - one, gy - one)
            ),
            seltzo_case(
                (sx, 0, 1, ex, ey, ey + one),
                (sy, 0, 0, fy, (gy + one, fy - two), gy - one),
            ),
            seltzo_case(
                (sx, 0, 1, ex, ey, ey + one), (sy, 1, 0, fy, (gy, fy - two), gy - one)
            ),
        ),
    )
    result["SELTZO-TwoSum-POW2-G01-S7-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g01, ey == ex + (p - one), ex > gx + (p - three)),
        z3.Or(
            seltzo_case(
                (sy, 0, 1, ey, ex, ex + one), (sx, 0, 0, fx, gx - one, gx - one)
            ),
            seltzo_case(
                (sy, 0, 1, ey, ex, ex + one),
                (sx, 0, 0, fx, (gx + one, fx - two), gx - one),
            ),
            seltzo_case(
                (sy, 0, 1, ey, ex, ex + one), (sx, 1, 0, fx, (gx, fx - two), gx - one)
            ),
        ),
    )

    result["SELTZO-TwoSum-R1R0-G11-S1-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_r1r0,
            y_g11,
            fx < ey + one,
            ey == fy + two,
            fy + p < ex,
            ey > gy + (p - three),
        ),
        z3.Or(
            seltzo_case(
                (sx, 0, 0, ex + one, fx, ex + one),
                ((sy,), 0, 0, fy, (gy, fy - two), gy - one),
            ),
            seltzo_case(
                (sx, 0, 0, ex + one, fx, ex + one),
                ((sy,), 1, 0, fy, gy - two, gy - one),
            ),
            seltzo_case(
                (sx, 0, 0, ex + one, fx, ex + one),
                ((sy,), 1, 0, fy, (gy + one, fy - two), gy - one),
            ),
        ),
    )
    result["SELTZO-TwoSum-R1R0-G11-S1-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_r1r0,
            x_g11,
            fy < ex + one,
            ex == fx + two,
            fx + p < ey,
            ex > gx + (p - three),
        ),
        z3.Or(
            seltzo_case(
                (sy, 0, 0, ey + one, fy, ey + one),
                ((sx,), 0, 0, fx, (gx, fx - two), gx - one),
            ),
            seltzo_case(
                (sy, 0, 0, ey + one, fy, ey + one),
                ((sx,), 1, 0, fx, gx - two, gx - one),
            ),
            seltzo_case(
                (sy, 0, 0, ey + one, fy, ey + one),
                ((sx,), 1, 0, fx, (gx + one, fx - two), gx - one),
            ),
        ),
    )

    result["SELTZO-TwoSum-POW2-ONE1-S4-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_one1, ex > ey + one, gy == fx + one),
        seltzo_case_zero((sx, 0, 1, ex, ey, gy + one)),
    )
    result["SELTZO-TwoSum-POW2-ONE1-S4-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_one1, ey > ex + one, gx == fy + one),
        seltzo_case_zero((sy, 0, 1, ey, ex, gx + one)),
    )

    result["SELTZO-TwoSum-POW2-MM01-S4-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_mm01, ex > ey + one, gy == fx + one),
        seltzo_case_zero((sx, 0, 1, ex, ey, gy + one)),
    )
    result["SELTZO-TwoSum-POW2-MM01-S4-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_mm01, ey > ex + one, gx == fy + one),
        seltzo_case_zero((sy, 0, 1, ey, ex, gx + one)),
    )

    result["SELTZO-TwoSum-POW2-TWO1-S5-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_two1, ex > ey + one, gy == fx + one),
        seltzo_case_zero((sx, 0, 1, ex, ey, gy + two)),
    )
    result["SELTZO-TwoSum-POW2-TWO1-S5-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_two1, ey > ex + one, gx == fy + one),
        seltzo_case_zero((sy, 0, 1, ey, ex, gx + two)),
    )

    result["SELTZO-TwoSum-POW2-R1R0-S4-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_r1r0, ex > ey + one, gy == fx + one),
        seltzo_case_zero((sx, 0, 1, ex, ey, ey + one)),
    )
    result["SELTZO-TwoSum-POW2-R1R0-S4-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_r1r0, ey > ex + one, gx == fy + one),
        seltzo_case_zero((sy, 0, 1, ey, ex, ex + one)),
    )

    result["SELTZO-TwoSum-POW2-G00-S8-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g00, ex > ey + one, gy == fx + one),
        z3.Or(
            seltzo_case_zero((sx, 0, 1, ex, ey, (gy + one, fy - one))),
            seltzo_case_zero((sx, 0, 1, ex, ey, fy + one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-S8-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g00, ey > ex + one, gx == fy + one),
        z3.Or(
            seltzo_case_zero((sy, 0, 1, ey, ex, (gx + one, fx - one))),
            seltzo_case_zero((sy, 0, 1, ey, ex, fx + one)),
        ),
    )

    result["SELTZO-TwoSum-POW2-G10-S4-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g10, ex > ey + one, gy == fx + one),
        seltzo_case_zero((sx, 0, 1, ex, ey, (gy + one, fy))),
    )
    result["SELTZO-TwoSum-POW2-G10-S4-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g10, ey > ex + one, gx == fy + one),
        seltzo_case_zero((sy, 0, 1, ey, ex, (gx + one, fx))),
    )

    result["SELTZO-TwoSum-POW2-R1R0-S5-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_r1r0, ex == ey + one, gy == fx + one),
        seltzo_case_zero((sx, 1, 1, ex, ex - p, ex)),
    )
    result["SELTZO-TwoSum-POW2-R1R0-S5-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_r1r0, ey == ex + one, gx == fy + one),
        seltzo_case_zero((sy, 1, 1, ey, ey - p, ey)),
    )

    result["SELTZO-TwoSum-POW2-ONE1-S5-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_one1, ex == ey + one, gy == fx + one),
        seltzo_case_zero((sx, 1, 1, ex, ey - one, gy + one)),
    )
    result["SELTZO-TwoSum-POW2-ONE1-S5-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_one1, ey == ex + one, gx == fy + one),
        seltzo_case_zero((sy, 1, 1, ey, ex - one, gx + one)),
    )

    result["SELTZO-TwoSum-POW2-TWO1-S6-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_two1, ex == ey + one, gy == fx + one),
        seltzo_case_zero((sx, 1, 1, ex, ey - one, gy + two)),
    )
    result["SELTZO-TwoSum-POW2-TWO1-S6-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_two1, ey == ex + one, gx == fy + one),
        seltzo_case_zero((sy, 1, 1, ey, ex - one, gx + two)),
    )

    result["SELTZO-TwoSum-POW2-MM01-S5-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_mm01, ex == ey + one, gy == fx + one),
        seltzo_case_zero((sx, 1, 1, ex, fy, gy + one)),
    )
    result["SELTZO-TwoSum-POW2-MM01-S5-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_mm01, ey == ex + one, gx == fy + one),
        seltzo_case_zero((sy, 1, 1, ey, fx, gx + one)),
    )

    result["SELTZO-TwoSum-POW2-G00-S9-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g00, ex == ey + one, gy == fx + one),
        z3.Or(
            seltzo_case_zero((sx, 1, 1, ex, ey - one, (gy + one, fy - one))),
            seltzo_case_zero((sx, 1, 1, ex, ey - one, fy + one)),
        ),
    )
    result["SELTZO-TwoSum-POW2-G00-S9-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g00, ey == ex + one, gx == fy + one),
        z3.Or(
            seltzo_case_zero((sy, 1, 1, ey, ex - one, (gx + one, fx - one))),
            seltzo_case_zero((sy, 1, 1, ey, ex - one, fx + one)),
        ),
    )

    result["SELTZO-TwoSum-POW2-G10-S5-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_g10, ex == ey + one, gy == fx + one),
        seltzo_case_zero((sx, 1, 1, ex, fy, (gy + one, fy))),
    )
    result["SELTZO-TwoSum-POW2-G10-S5-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_g10, ey == ex + one, gx == fy + one),
        seltzo_case_zero((sy, 1, 1, ey, fx, (gx + one, fx))),
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
        z3.And(diff_sign, f1x > ey, xy_nonzero, ~x_pow2),
        z3.And(ss == sx, es == ex, f0s >= ey),
    )
    result["SELTZO-TwoSum-P02B-Y"] = z3.Implies(
        z3.And(diff_sign, f1y > ex, xy_nonzero, ~y_pow2),
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

    # Lemma P05: A trailing bit that is not cancelled out must remain intact.
    result["SELTZO-TwoSum-P05-X"] = z3.Implies(
        z3.And(g1x > g1y, xy_nonzero),
        z3.Or(g1s == g1y, g1e == g1y),
    )
    result["SELTZO-TwoSum-P05-Y"] = z3.Implies(
        z3.And(g1y > g1x, xy_nonzero),
        z3.Or(g1s == g1x, g1e == g1x),
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

    # Lemma T02A: One addend fits inside the leading zeros of the other.
    # This should eventually be replaced by complete case-by-case lemmas.
    result["SELTZO-TwoSum-T02A-X"] = z3.Implies(
        z3.And(same_sign, ex > ey, ~lbx, g1y > f1x, ~x_pow2, xy_nonzero),
        z3.And(
            ss == sx, lbs == (ex == ey + one), tbs == tbx, es == ex, f1s == ey, gs >= gx
        ),
    )
    result["SELTZO-TwoSum-T02A-Y"] = z3.Implies(
        z3.And(same_sign, ey > ex, ~lby, g1x > f1y, ~y_pow2, xy_nonzero),
        z3.And(
            ss == sy, lbs == (ey == ex + one), tbs == tby, es == ey, f1s == ex, gs >= gy
        ),
    )

    return result
