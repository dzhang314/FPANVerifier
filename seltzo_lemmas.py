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
    lbe: z3.BoolRef,  # pyright: ignore[reportUnusedParameter]
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
    nlbe: IntVar,  # pyright: ignore[reportUnusedParameter]
    ntbx: IntVar,
    ntby: IntVar,
    ntbs: IntVar,
    ntbe: IntVar,
    is_zero: Callable[[FloatVar], z3.BoolRef],
    is_positive: Callable[[FloatVar], z3.BoolRef],
    is_negative: Callable[  # pyright: ignore[reportUnusedParameter]
        [FloatVar], z3.BoolRef
    ],
    is_equal: Callable[  # pyright: ignore[reportUnusedParameter]
        [FloatVar, FloatVar], z3.BoolRef
    ],
    p: IntVar,
    one: IntVar,
    two: IntVar,
    three: IntVar,  # pyright: ignore[reportUnusedParameter]
) -> dict[str, z3.BoolRef]:

    result: dict[str, z3.BoolRef] = {}

    x_zero: z3.BoolRef = is_zero(x)
    y_zero: z3.BoolRef = is_zero(y)
    xy_nonzero: z3.BoolRef = z3.And(z3.Not(x_zero), z3.Not(y_zero))
    s_nonzero: z3.BoolRef = z3.Not(is_zero(s))
    e_nonzero: z3.BoolRef = z3.Not(is_zero(e))
    e_pos_zero: z3.BoolRef = z3.And(is_positive(e), is_zero(e))

    # cx - index of first 0
    # dx - index of last 0
    # ex - exponent
    # fx - index of last 1
    # gx - index of first 1

    #   1 . 0 ... 0 1 ? ? ? 1 0 ... 0
    #   |   |       |       |       |
    #   ex  cx      gx      fx      dx

    #   1 . 0 ... 0 1 ? ? ? 0 1 ... 1
    #   |   |       |       |       |
    #   ex  cx      gx      dx      fx

    #   1 . 1 ... 1 0 ? ? ? 1 0 ... 0
    #   |   |       |       |       |
    #   ex  gx      cx      fx      dx

    #   1 . 1 ... 1 0 ? ? ? 0 1 ... 1
    #   |   |       |       |       |
    #   ex  gx      cx      dx      fx

    cx: IntVar = ex - z3_If(lbx, nlbx + one, one)
    cy: IntVar = ey - z3_If(lby, nlby + one, one)
    cs: IntVar = es - z3_If(lbs, nlbs + one, one)
    # ce: IntVar = ee - z3_If(lbe, nlbe + one, one)

    # dx: IntVar = ex - z3_If(tbx, (p - one) - ntbx, (p - one))
    # dy: IntVar = ey - z3_If(tby, (p - one) - ntby, (p - one))
    # ds: IntVar = es - z3_If(tbs, (p - one) - ntbs, (p - one))
    # de: IntVar = ee - z3_If(tbe, (p - one) - ntbe, (p - one))

    fx: IntVar = ex - z3_If(tbx, (p - one), (p - one) - ntbx)
    fy: IntVar = ey - z3_If(tby, (p - one), (p - one) - ntby)
    fs: IntVar = es - z3_If(tbs, (p - one), (p - one) - ntbs)
    fe: IntVar = ee - z3_If(tbe, (p - one), (p - one) - ntbe)

    gx: IntVar = ex - z3_If(lbx, one, nlbx + one)
    gy: IntVar = ey - z3_If(lby, one, nlby + one)
    gs: IntVar = es - z3_If(lbs, one, nlbs + one)
    # ge: IntVar = ee - z3_If(lbe, one, nlbe + one)

    same_sign: z3.BoolRef = sx == sy
    diff_sign: z3.BoolRef = sx != sy

    ############################################################################

    # Lemma SELTZO-1A: Adding a small number to a number with multiple
    # leading zeros destroys at most one of its leading zeros.
    result["SELTZO-TwoSum-1A-X"] = z3.Implies(
        z3.And(same_sign, ex > gx + one, gx + one > ey),
        z3.And(ss == sx, es == ex, gs <= gx + one),
    )
    result["SELTZO-TwoSum-1A-Y"] = z3.Implies(
        z3.And(same_sign, ey > gy + one, gy + one > ex),
        z3.And(ss == sy, es == ey, gs <= gy + one),
    )

    # Lemma SELTZO-1B: Subtracting a small number from a number with
    # multiple leading ones destroys at most one of its leading ones.
    result["SELTZO-TwoSum-1B-X"] = z3.Implies(
        z3.And(diff_sign, ex > cx + one, cx + one > ey),
        z3.And(ss == sx, es == ex, cs <= cx + one),
    )
    result["SELTZO-TwoSum-1B-Y"] = z3.Implies(
        z3.And(diff_sign, ey > cy + one, cy + one > ex),
        z3.And(ss == sy, es == ey, cs <= cy + one),
    )

    # Lemma SELTZO-2A: Leading zeros insulate the exponent from increasing.
    result["SELTZO-TwoSum-2A-X"] = z3.Implies(
        z3.And(same_sign, ex > ey + one, ey + one > gx),
        z3.And(ss == sx, es == ex, gs <= ey + one),
    )
    result["SELTZO-TwoSum-2A-Y"] = z3.Implies(
        z3.And(same_sign, ey > ex + one, ex + one > gy),
        z3.And(ss == sy, es == ey, gs <= ex + one),
    )

    # Lemma SELTZO-2B: Leading ones insulate the exponent from decreasing.
    result["SELTZO-TwoSum-2B-X"] = z3.Implies(
        z3.And(diff_sign, ex > ey + one, ey + one > cx),
        z3.And(ss == sx, es == ex, cs <= ey + one),
    )
    result["SELTZO-TwoSum-2B-Y"] = z3.Implies(
        z3.And(diff_sign, ey > ex + one, ex + one > cy),
        z3.And(ss == sy, es == ey, cs <= ex + one),
    )

    # Lemma SELTZO-3A: One number fits completely inside the other's leading zeros.
    result["SELTZO-TwoSum-3A-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex > ey, fy > gx),
        z3.And(ss == sx, es == ex, gs == ey, e_pos_zero),
    )
    result["SELTZO-TwoSum-3A-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey > ex, fx > gy),
        z3.And(ss == sy, es == ey, gs == ex, e_pos_zero),
    )

    # Lemma SELTZO-3B: One number fits completely inside the other's leading ones.
    result["SELTZO-TwoSum-3B-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex > ey, fy > cx),
        z3.And(ss == sx, es == ex, cs == ey, e_pos_zero),
    )
    result["SELTZO-TwoSum-3B-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey > ex, fx > cy),
        z3.And(ss == sy, es == ey, cs == ex, e_pos_zero),
    )

    # These lemmas suggest a notion of duality between addition/subtraction
    # and leading zeros/ones. This should be investigated further...

    # Lemma SELTZO-4: Addition preserves leading ones or increases the exponent.
    result["SELTZO-TwoSum-4-X"] = z3.Implies(same_sign, z3.Or(es > ex, cs <= cx))
    result["SELTZO-TwoSum-4-Y"] = z3.Implies(same_sign, z3.Or(es > ey, cs <= cy))

    # Lemma SELTZO-5A: If the difference has a smaller exponent,
    # then it must have a lot of leading ones.
    result["SELTZO-TwoSum-5A-X"] = z3.Implies(es < ex, cs <= ey)
    result["SELTZO-TwoSum-5A-Y"] = z3.Implies(es < ey, cs <= ex)

    # Lemma SELTZO-5B: If the sum has a larger exponent,
    # then it must have a lot of leading zeros.
    result["SELTZO-TwoSum-5B-X"] = z3.Implies(es > ex, gs <= ey + one)
    result["SELTZO-TwoSum-5B-Y"] = z3.Implies(es > ey, gs <= ex + one)

    result["SELTZO-TwoSum-6-X"] = z3.Implies(z3.And(es < ex, ex > ey + one), gs >= cy)
    result["SELTZO-TwoSum-6-Y"] = z3.Implies(z3.And(es < ey, ey > ex + one), gs >= cx)

    result["SELTZO-TwoSum-7-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey > cx), es > ex
    )
    result["SELTZO-TwoSum-7-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex > cy), es > ey
    )

    result["SELTZO-TwoSum-8-X"] = z3.Implies(
        z3.And(xy_nonzero, fx < fy),
        z3.Or(
            z3.And(s_nonzero, e_pos_zero, fs == fx),
            z3.And(s_nonzero, e_nonzero, fe == fx),
        ),
    )
    result["SELTZO-TwoSum-8-Y"] = z3.Implies(
        z3.And(xy_nonzero, fx > fy),
        z3.Or(
            z3.And(s_nonzero, e_pos_zero, fs == fy),
            z3.And(s_nonzero, e_nonzero, fe == fy),
        ),
    )

    result["SELTZO-TwoSum-9"] = z3.Or(
        e_pos_zero,
        es > ee + (p + one),
        z3.And(es == ee + (p + one), z3.Or(ee == fe, ss == se, es > fs)),
        z3.And(es == ee + p, ee == fe, z3.Or(ss == se, es > fs), es < fs + (p + one)),
    )

    result["SELTZO-TwoSum-10-X"] = z3.Implies(
        z3.And(diff_sign, ex == cx + two, cx > ey),
        z3.And(ss == sx, es == ex, gs >= cx),
    )
    result["SELTZO-TwoSum-10-Y"] = z3.Implies(
        z3.And(diff_sign, ey == cy + two, cy > ex),
        z3.And(ss == sy, es == ey, gs >= cy),
    )

    return result
