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

    x_pow2: z3.BoolRef = z3.And(~x_zero, ~lbx, ~tbx, nlbx == p - one, ntbx == p - one)
    y_pow2: z3.BoolRef = z3.And(~y_zero, ~lby, ~tby, nlby == p - one, ntby == p - one)
    s_pow2: z3.BoolRef = z3.And(~s_zero, ~lbs, ~tbs, nlbs == p - one, ntbs == p - one)
    e_pow2: z3.BoolRef = z3.And(~e_zero, ~lbe, ~tbe, nlbe == p - one, ntbe == p - one)

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

    # Lemma 01A: Addition either preserves the exponent of the larger addend,
    # in which case the sum has at least as many leading ones as that addend,
    # or increases the exponent by one, in which case the sum must have leading
    # zeros in the exponent gap.
    result["SELTZO-TwoSum-01A-X"] = z3.Implies(
        z3.And(same_sign, ex >= ey),
        z3.Or(
            z3.And(es == ex, f0s <= f0x),
            z3.And(es == ex + one, f1s <= ey + one),
        ),
    )
    result["SELTZO-TwoSum-01A-Y"] = z3.Implies(
        z3.And(same_sign, ey >= ex),
        z3.Or(
            z3.And(es == ey, f0s <= f0y),
            z3.And(es == ey + one, f1s <= ex + one),
        ),
    )

    # Lemma 01B: Subtraction either preserves the exponent of the minuend,
    # in which case the difference has at least as many leading zeros as the
    # minuend, or decreases the exponent, in which case the difference must
    # have leading ones in the exponent gap.
    result["SELTZO-TwoSum-01B-X"] = z3.Implies(
        z3.And(diff_sign, ex >= ey),
        z3.Or(
            z3.And(es == ex, f1s <= f1x),
            z3.And(es < ex, f0s <= ey),
        ),
    )
    result["SELTZO-TwoSum-01B-Y"] = z3.Implies(
        z3.And(diff_sign, ey >= ex),
        z3.Or(
            z3.And(es == ey, f1s <= f1y),
            z3.And(es < ey, f0s <= ex),
        ),
    )

    # Lemma 02A: A zero between the exponents of the addends
    # insulates the exponent of the sum from increasing.
    result["SELTZO-TwoSum-02A-X"] = z3.Implies(
        z3.And(same_sign, f0x > ey, xy_nonzero),
        z3.And(ss == sx, es == ex, f1s >= ey),
    )
    result["SELTZO-TwoSum-02A-Y"] = z3.Implies(
        z3.And(same_sign, f0y > ex, xy_nonzero),
        z3.And(ss == sy, es == ey, f1s >= ex),
    )

    # Lemma 02B: A one between the exponents of the minuend and subtrahend
    # insulates the exponent of the difference from decreasing.
    result["SELTZO-TwoSum-02B-X"] = z3.Implies(
        z3.And(diff_sign, f1x > ey, xy_nonzero, ~x_pow2),
        z3.And(ss == sx, es == ex, f0s >= ey),
    )
    result["SELTZO-TwoSum-02B-Y"] = z3.Implies(
        z3.And(diff_sign, f1y > ex, xy_nonzero, ~y_pow2),
        z3.And(ss == sy, es == ey, f0s >= ex),
    )

    # Lemma 03A: Adding into leading zeros preserves the exponent.
    result["SELTZO-TwoSum-03A-X"] = z3.Implies(
        z3.And(same_sign, ex > ey + one, ey + one > f1x),
        z3.And(ss == sx, es == ex, f1s <= ey + one),
    )
    result["SELTZO-TwoSum-03A-Y"] = z3.Implies(
        z3.And(same_sign, ey > ex + one, ex + one > f1y),
        z3.And(ss == sy, es == ey, f1s <= ex + one),
    )

    # Lemma 03B: Subtracting from leading ones preserves the exponent.
    result["SELTZO-TwoSum-03B-X"] = z3.Implies(
        z3.And(diff_sign, ex > ey + one, ey + one > f0x),
        z3.And(ss == sx, es == ex, f0s <= ey + one),
    )
    result["SELTZO-TwoSum-03B-Y"] = z3.Implies(
        z3.And(diff_sign, ey > ex + one, ex + one > f0y),
        z3.And(ss == sy, es == ey, f0s <= ex + one),
    )

    # Lemma 04A: Adding into leading ones increases the exponent.
    result["SELTZO-TwoSum-04A-X"] = z3.Implies(
        z3.And(same_sign, ex >= ey, ey > f0x, xy_nonzero),
        z3.And(ss == sx, es == ex + one, f1s <= ey),
    )
    result["SELTZO-TwoSum-04A-Y"] = z3.Implies(
        z3.And(same_sign, ey >= ex, ex > f0y, xy_nonzero),
        z3.And(ss == sy, es == ey + one, f1s <= ex),
    )

    # Lemma 04B: Subtracting from leading zeros decreases the exponent.
    result["SELTZO-TwoSum-04B-X"] = z3.Implies(
        z3.And(diff_sign, ex > ey + one, ey > f1x, xy_nonzero),
        z3.And(ss == sx, es == ex - one, f0s <= ey),
    )
    result["SELTZO-TwoSum-04B-Y"] = z3.Implies(
        z3.And(diff_sign, ey > ex + one, ex > f1y, xy_nonzero),
        z3.And(ss == sy, es == ey - one, f0s <= ex),
    )

    # Lemma 05: A trailing bit that is not cancelled out must remain intact.
    result["SELTZO-TwoSum-05-X"] = z3.Implies(
        z3.And(g1x > g1y, xy_nonzero),
        z3.Or(g1s == g1y, g1e == g1y),
    )
    result["SELTZO-TwoSum-05-Y"] = z3.Implies(
        z3.And(g1y > g1x, xy_nonzero),
        z3.Or(g1s == g1x, g1e == g1x),
    )

    return result
