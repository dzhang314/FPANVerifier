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

    x_nonzero: z3.BoolRef = z3.Not(x_zero)
    y_nonzero: z3.BoolRef = z3.Not(y_zero)
    s_nonzero: z3.BoolRef = z3.Not(s_zero)
    e_nonzero: z3.BoolRef = z3.Not(e_zero)

    xy_nonzero: z3.BoolRef = z3.And(x_nonzero, y_nonzero)
    e_pos_zero: z3.BoolRef = z3.And(is_positive(e), e_zero)

    fx: IntVar = ex - (nlbx + one)
    fy: IntVar = ey - (nlby + one)
    fs: IntVar = es - (nlbs + one)
    fe: IntVar = ee - (nlbe + one)

    f0x: IntVar = ex - z3_If(lbx, nlbx + one, one)
    f0y: IntVar = ey - z3_If(lby, nlby + one, one)
    f0s: IntVar = es - z3_If(lbs, nlbs + one, one)
    f0e: IntVar = ee - z3_If(lbe, nlbe + one, one)

    f1x: IntVar = ex - z3_If(lbx, one, nlbx + one)
    f1y: IntVar = ey - z3_If(lby, one, nlby + one)
    f1s: IntVar = es - z3_If(lbs, one, nlbs + one)
    f1e: IntVar = ee - z3_If(lbe, one, nlbe + one)

    gx: IntVar = ex - (p - (ntbx + one))
    gy: IntVar = ey - (p - (ntby + one))
    gs: IntVar = es - (p - (ntbs + one))
    ge: IntVar = ee - (p - (ntbe + one))

    g0x: IntVar = ex - (p - z3_If(tbx, ntbx + one, one))
    g0y: IntVar = ey - (p - z3_If(tby, ntby + one, one))
    g0s: IntVar = es - (p - z3_If(tbs, ntbs + one, one))
    g0e: IntVar = ee - (p - z3_If(tbe, ntbe + one, one))

    g1x: IntVar = ex - (p - z3_If(tbx, one, ntbx + one))
    g1y: IntVar = ey - (p - z3_If(tby, one, ntby + one))
    g1s: IntVar = es - (p - z3_If(tbs, one, ntbs + one))
    g1e: IntVar = ee - (p - z3_If(tbe, one, ntbe + one))

    x_pow2: z3.BoolRef = z3.And(
        x_nonzero, z3.Not(lbx), z3.Not(tbx), nlbx == p - one, ntbx == p - one
    )
    y_pow2: z3.BoolRef = z3.And(
        y_nonzero, z3.Not(lby), z3.Not(tby), nlby == p - one, ntby == p - one
    )
    s_pow2: z3.BoolRef = z3.And(
        s_nonzero, z3.Not(lbs), z3.Not(tbs), nlbs == p - one, ntbs == p - one
    )
    e_pow2: z3.BoolRef = z3.And(
        e_nonzero, z3.Not(lbe), z3.Not(tbe), nlbe == p - one, ntbe == p - one
    )

    x_all1: z3.BoolRef = z3.And(lbx, tbx, nlbx == p - one, ntbx == p - one)
    y_all1: z3.BoolRef = z3.And(lby, tby, nlby == p - one, ntby == p - one)
    s_all1: z3.BoolRef = z3.And(lbs, tbs, nlbs == p - one, ntbs == p - one)
    e_all1: z3.BoolRef = z3.And(lbe, tbe, nlbe == p - one, ntbe == p - one)

    ############################################################ COMPLETE LEMMAS

    # Lemma C1: Sum where one number fits entirely into the other's leading
    # zeros, with padding on both sides.
    result["SELTZO-TwoSum-C1-X"] = z3.Implies(
        z3.And(y_nonzero, same_sign, tbx, ex > ey + one, g1y > f1x + one),
        z3.And(
            ss == sx,
            z3.Not(lbs),
            tbs,
            es == ex,
            fs == ey,
            gs == gx,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C1-Y"] = z3.Implies(
        z3.And(x_nonzero, same_sign, tby, ey > ex + one, g1x > f1y + one),
        z3.And(
            ss == sy,
            z3.Not(lbs),
            tbs,
            es == ey,
            fs == ex,
            gs == gy,
            e_pos_zero,
        ),
    )

    # Lemma C1A: Sum where one number fits entirely into the other's leading
    # zeros, with padding only on the right.
    result["SELTZO-TwoSum-C1A-X"] = z3.Implies(
        z3.And(y_nonzero, same_sign, tbx, ex == ey + one, g1y > f1x + one),
        z3.And(
            ss == sx,
            lbs,
            tbs,
            es == ex,
            fs == f0y,
            gs == gx,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C1A-Y"] = z3.Implies(
        z3.And(x_nonzero, same_sign, tby, ey == ex + one, g1x > f1y + one),
        z3.And(
            ss == sy,
            lbs,
            tbs,
            es == ey,
            fs == f0x,
            gs == gy,
            e_pos_zero,
        ),
    )

    # Lemma C1AB: Sum where one number fits entirely into the other's leading
    # zeros, with no padding on either side.
    result["SELTZO-TwoSum-C1AB-X"] = z3.Implies(
        z3.And(y_nonzero, same_sign, tbx, ex == ey + one, g1y == f1x + one),
        z3.And(
            ss == sx,
            lbs,
            tbs,
            es == ex,
            fs + one <= ey,  # TODO: This bound is not complete.
            gs >= g0y + two,  # TODO: This bound is not complete.
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C1AB-Y"] = z3.Implies(
        z3.And(x_nonzero, same_sign, tby, ey == ex + one, g1x == f1y + one),
        z3.And(
            ss == sy,
            lbs,
            tbs,
            es == ey,
            fs + one <= ex,  # TODO: This bound is not complete.
            gs >= g0x + two,  # TODO: This bound is not complete.
            e_pos_zero,
        ),
    )

    ############################################################# PARTIAL LEMMAS

    # Lemma P1A: If the exponent increases, then the sum must have a number of
    # leading zeros proportional to the exponent gap.
    result["SELTZO-TwoSum-P1A-X"] = z3.Implies(es > ex, f1s <= ey + one)
    result["SELTZO-TwoSum-P1A-Y"] = z3.Implies(es > ey, f1s <= ex + one)

    # Lemma P1B: If the exponent decreases, then the difference must have a
    # number of leading ones proportional to the exponent gap.
    result["SELTZO-TwoSum-P1B-X"] = z3.Implies(es < ex, f0s <= ey)
    result["SELTZO-TwoSum-P1B-Y"] = z3.Implies(es < ey, f0s <= ex)

    # Lemma P2A: The exponent can only increase if the addends have the same
    # sign and one touches the other's leading ones.
    result["SELTZO-TwoSum-P2A-X"] = z3.Implies(
        z3.And(es > ex, ex + one > ey),
        z3.And(same_sign, ey >= f0x),
    )
    result["SELTZO-TwoSum-P2A-Y"] = z3.Implies(
        z3.And(es > ey, ey + one > ex),
        z3.And(same_sign, ex >= f0y),
    )

    # Lemma P2B: The exponent can only decrease if the addends have different
    # signs and one touches the other's leading zeros.
    result["SELTZO-TwoSum-P2B-X"] = z3.Implies(
        es < ex,
        z3.And(diff_sign, ey + one >= f1x),
    )
    result["SELTZO-TwoSum-P2B-Y"] = z3.Implies(
        es < ey,
        z3.And(diff_sign, ex + one >= f1y),
    )

    # Lemma P3A: If one addend has leading zeros that the other does not touch,
    # then the sum must have as many leading zeros.
    result["SELTZO-TwoSum-P3A-X"] = z3.Implies(
        z3.And(same_sign, f1x + one > ey),
        z3.And(ss == sx, f1s <= f1x + one),
    )
    result["SELTZO-TwoSum-P3A-Y"] = z3.Implies(
        z3.And(same_sign, f1y + one > ex),
        z3.And(ss == sy, f1s <= f1y + one),
    )

    # Lemma P3B: If the minuend has leading ones that the subtrahend does not
    # touch, then the difference must have as many leading ones.
    result["SELTZO-TwoSum-P3B-X"] = z3.Implies(
        z3.And(diff_sign, f0x + one > ey),
        z3.And(ss == sx, f0s <= f0x + one),
    )
    result["SELTZO-TwoSum-P3B-Y"] = z3.Implies(
        z3.And(diff_sign, f0y + one > ex),
        z3.And(ss == sy, f0s <= f0y + one),
    )

    # Lemma P4A: Zeros in the mantissa shield the exponent from increasing and
    # leading ones from being destroyed.
    result["SELTZO-TwoSum-P4A-X"] = z3.Implies(
        z3.And(same_sign, f0x > ey),
        z3.And(ss == sx, es == ex, f0s <= f0x),
    )
    result["SELTZO-TwoSum-P4A-Y"] = z3.Implies(
        z3.And(same_sign, f0y > ex),
        z3.And(ss == sy, es == ey, f0s <= f0y),
    )

    # Lemma P4B: Ones in the mantissa shield the exponent from decreasing and
    # leading zeros from being destroyed.
    result["SELTZO-TwoSum-P4B-X"] = z3.Implies(
        z3.And(diff_sign, z3.Not(x_pow2), f1x > ey),
        z3.And(ss == sx, es == ex, f1s <= f1x),
    )
    result["SELTZO-TwoSum-P4B-Y"] = z3.Implies(
        z3.And(diff_sign, z3.Not(y_pow2), f1y > ex),
        z3.And(ss == sy, es == ey, f1s <= f1y),
    )

    """
    # Lemma 1A: Adding into leading ones increases the exponent.
    result["SELTZO-TwoSum-1A-X"] = z3.Implies(
        z3.And(y_nonzero, same_sign, ey > f0x),
        es > ex,
    )
    result["SELTZO-TwoSum-1A-Y"] = z3.Implies(
        z3.And(x_nonzero, same_sign, ex > f0y),
        es > ey,
    )

    # Lemma 1B: Subtracting from leading zeros decreases the exponent.
    result["SELTZO-TwoSum-1B-X"] = z3.Implies(
        z3.And(y_nonzero, diff_sign, ex >= ey, ey > f1x),
        es < ex,
    )
    result["SELTZO-TwoSum-1B-Y"] = z3.Implies(
        z3.And(x_nonzero, diff_sign, ey >= ex, ex > f1y),
        es < ey,
    )

    # Lemma 2A: Zeros insulate the exponent from increasing.
    result["SELTZO-TwoSum-2A-X"] = z3.Implies(
        z3.And(same_sign, ey < f0x),
        es == ex,
    )
    result["SELTZO-TwoSum-2A-Y"] = z3.Implies(
        z3.And(same_sign, ex < f0y),
        es == ey,
    )

    # Lemma 2B: Ones insulate the exponent from decreasing.
    result["SELTZO-TwoSum-2B-X"] = z3.Implies(
        z3.And(diff_sign, z3.Not(x_pow2), ey < f1x),
        es == ex,
    )
    result["SELTZO-TwoSum-2B-Y"] = z3.Implies(
        z3.And(diff_sign, z3.Not(y_pow2), ex < f1y),
        es == ey,
    )
    """

    """
    # Lemma SELTZO-1A: Adding a small number to a number with multiple
    # leading zeros destroys at most one of its leading zeros.
    result["SELTZO-TwoSum-1A-X"] = z3.Implies(
        z3.And(same_sign, ex > f1x + one, f1x + one > ey),
        z3.And(ss == sx, es == ex, f1s <= f1x + one),
    )
    result["SELTZO-TwoSum-1A-Y"] = z3.Implies(
        z3.And(same_sign, ey > f1y + one, f1y + one > ex),
        z3.And(ss == sy, es == ey, f1s <= f1y + one),
    )

    # Lemma SELTZO-1B: Subtracting a small number from a number with
    # multiple leading ones destroys at most one of its leading ones.
    result["SELTZO-TwoSum-1B-X"] = z3.Implies(
        z3.And(diff_sign, ex > f0x + one, f0x + one > ey),
        z3.And(ss == sx, es == ex, f0s <= f0x + one),
    )
    result["SELTZO-TwoSum-1B-Y"] = z3.Implies(
        z3.And(diff_sign, ey > f0y + one, f0y + one > ex),
        z3.And(ss == sy, es == ey, f0s <= f0y + one),
    )

    # Lemma SELTZO-2A: Leading zeros insulate the exponent from increasing.
    result["SELTZO-TwoSum-2A-X"] = z3.Implies(
        z3.And(same_sign, ex > ey + one, ey + one > f1x),
        z3.And(ss == sx, es == ex, f1s <= ey + one),
    )
    result["SELTZO-TwoSum-2A-Y"] = z3.Implies(
        z3.And(same_sign, ey > ex + one, ex + one > f1y),
        z3.And(ss == sy, es == ey, f1s <= ex + one),
    )

    # Lemma SELTZO-2B: Leading ones insulate the exponent from decreasing.
    result["SELTZO-TwoSum-2B-X"] = z3.Implies(
        z3.And(diff_sign, ex > ey + one, ey + one > f0x),
        z3.And(ss == sx, es == ex, f0s <= ey + one),
    )
    result["SELTZO-TwoSum-2B-Y"] = z3.Implies(
        z3.And(diff_sign, ey > ex + one, ex + one > f0y),
        z3.And(ss == sy, es == ey, f0s <= ex + one),
    )

    # Lemma SELTZO-3A: One number fits completely inside the other's leading zeros.
    result["SELTZO-TwoSum-3A-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex > ey, g1y > f1x),
        z3.And(ss == sx, es == ex, f1s == ey, e_pos_zero),
    )
    result["SELTZO-TwoSum-3A-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey > ex, g1x > f1y),
        z3.And(ss == sy, es == ey, f1s == ex, e_pos_zero),
    )

    # Lemma SELTZO-3B: One number fits completely inside the other's leading ones.
    result["SELTZO-TwoSum-3B-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex > ey, g1y > f0x),
        z3.And(ss == sx, es == ex, f0s == ey, e_pos_zero),
    )
    result["SELTZO-TwoSum-3B-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey > ex, g1x > f0y),
        z3.And(ss == sy, es == ey, f0s == ex, e_pos_zero),
    )

    # These lemmas suggest a notion of duality between addition/subtraction
    # and leading zeros/ones. This should be investigated further...

    # Lemma SELTZO-4: Addition preserves leading ones or increases the exponent.
    result["SELTZO-TwoSum-4-X"] = z3.Implies(same_sign, z3.Or(es > ex, f0s <= f0x))
    result["SELTZO-TwoSum-4-Y"] = z3.Implies(same_sign, z3.Or(es > ey, f0s <= f0y))

    result["SELTZO-TwoSum-6-X"] = z3.Implies(z3.And(es < ex, ex > ey + one), f1s >= f0y)
    result["SELTZO-TwoSum-6-Y"] = z3.Implies(z3.And(es < ey, ey > ex + one), f1s >= f0x)

    result["SELTZO-TwoSum-7-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey > f0x), es > ex
    )
    result["SELTZO-TwoSum-7-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex > f0y), es > ey
    )

    result["SELTZO-TwoSum-8-X"] = z3.Implies(
        z3.And(xy_nonzero, g1x < g1y),
        z3.Or(
            z3.And(s_nonzero, e_pos_zero, g1s == g1x),
            z3.And(s_nonzero, e_nonzero, g1e == g1x),
        ),
    )
    result["SELTZO-TwoSum-8-Y"] = z3.Implies(
        z3.And(xy_nonzero, g1x > g1y),
        z3.Or(
            z3.And(s_nonzero, e_pos_zero, g1s == g1y),
            z3.And(s_nonzero, e_nonzero, g1e == g1y),
        ),
    )

    result["SELTZO-TwoSum-9"] = z3.Or(
        e_pos_zero,
        es > ee + (p + one),
        z3.And(es == ee + (p + one), z3.Or(ee == g1e, ss == se, es > g1s)),
        z3.And(
            es == ee + p, ee == g1e, z3.Or(ss == se, es > g1s), es < g1s + (p + one)
        ),
    )

    result["SELTZO-TwoSum-10-X"] = z3.Implies(
        z3.And(diff_sign, ex == f0x + two, f0x > ey),
        z3.And(ss == sx, es == ex, f1s >= f0x),
    )
    result["SELTZO-TwoSum-10-Y"] = z3.Implies(
        z3.And(diff_sign, ey == f0y + two, f0y > ex),
        z3.And(ss == sy, es == ey, f1s >= f0y),
    )
    """

    return result
