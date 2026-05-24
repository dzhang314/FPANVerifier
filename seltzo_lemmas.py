# pyright: reportUnusedParameter=false, reportUnusedVariable=false
import z3
from smt_utils import BoolVar, IntVar, FloatVar, z3_If
from systematic_lemmas import seltzo_two_sum_systematic_lemmas
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
    x_all1: z3.BoolRef = z3.And(~x_zero, lbx, tbx, nlbx == p - one, ntbx == p - one)
    y_all1: z3.BoolRef = z3.And(~y_zero, lby, tby, nlby == p - one, ntby == p - one)
    s_all1: z3.BoolRef = z3.And(~s_zero, lbs, tbs, nlbs == p - one, ntbs == p - one)
    x_r0r1: z3.BoolRef = z3.And(~x_zero, ~lbx, tbx, nlbx + ntbx == p - one)
    y_r0r1: z3.BoolRef = z3.And(~y_zero, ~lby, tby, nlby + ntby == p - one)
    x_r1r0: z3.BoolRef = z3.And(~x_zero, lbx, ~tbx, nlbx + ntbx == p - one)
    y_r1r0: z3.BoolRef = z3.And(~y_zero, lby, ~tby, nlby + ntby == p - one)

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

    result.update(
        seltzo_two_sum_systematic_lemmas(
            sx,
            sy,
            ss,
            se,
            lbx,
            lby,
            lbs,
            lbe,
            tbx,
            tby,
            tbs,
            tbe,
            ex,
            ey,
            es,
            ee,
            fx,
            fy,
            fs,
            fe,
            gx,
            gy,
            gs,
            ge,
            same_sign,
            diff_sign,
            xy_nonzero,
            x_pow2,
            y_pow2,
            x_all1,
            y_all1,
            x_r0r1,
            y_r0r1,
            x_r1r0,
            y_r1r0,
            s_pos_zero,
            e_pos_zero,
            p,
            one,
            two,
            three,
        )
    )

    # Lemma 01A: Addition either preserves the exponent of the larger addend,
    # in which case the sum has at least as many leading ones as that addend,
    # or increases the exponent by one, in which case the sum must have leading
    # zeros in the exponent gap.
    result["SELTZO-TwoSum-01A-X"] = z3.Implies(
        z3.And(same_sign, ex >= ey),
        z3.And(
            ss == sx,
            z3.Or(
                z3.And(es == ex, f0s <= f0x),
                z3.And(es == ex + one, f1s <= ey + one),
            ),
        ),
    )
    result["SELTZO-TwoSum-01A-Y"] = z3.Implies(
        z3.And(same_sign, ey >= ex),
        z3.And(
            ss == sy,
            z3.Or(
                z3.And(es == ey, f0s <= f0y),
                z3.And(es == ey + one, f1s <= ex + one),
            ),
        ),
    )

    # Lemma 01B: Subtraction either preserves the exponent of the minuend,
    # in which case the difference has at least as many leading zeros as the
    # minuend, or decreases the exponent, in which case the difference must
    # have leading ones in the exponent gap.
    result["SELTZO-TwoSum-01B-X"] = z3.Implies(
        z3.And(diff_sign, ex >= ey),
        z3.And(
            z3.Or(ex == ey, ss == sx),
            z3.Or(
                z3.And(es == ex, f1s <= f1x),
                z3.And(es < ex, f0s <= ey),
            ),
        ),
    )
    result["SELTZO-TwoSum-01B-Y"] = z3.Implies(
        z3.And(diff_sign, ey >= ex),
        z3.And(
            z3.Or(ey == ex, ss == sy),
            z3.Or(
                z3.And(es == ey, f1s <= f1y),
                z3.And(es < ey, f0s <= ex),
            ),
        ),
    )

    # Lemma 02A: A zero between the exponents of the addends
    # insulates the exponent of the sum from increasing.
    result["SELTZO-TwoSum-02A-X"] = z3.Implies(
        z3.And(same_sign, f0x > ey, ~y_zero),
        z3.And(ss == sx, es == ex, f1s >= ey),
    )
    result["SELTZO-TwoSum-02A-Y"] = z3.Implies(
        z3.And(same_sign, f0y > ex, ~x_zero),
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
        z3.And(same_sign, ex >= ey, ey > f0x, ~y_zero),
        z3.And(ss == sx, es == ex + one, f1s <= ey),
    )
    result["SELTZO-TwoSum-04A-Y"] = z3.Implies(
        z3.And(same_sign, ey >= ex, ex > f0y, ~x_zero),
        z3.And(ss == sy, es == ey + one, f1s <= ex),
    )

    # Lemma 04B: Subtracting from leading zeros decreases the exponent.
    result["SELTZO-TwoSum-04B-X"] = z3.Implies(
        z3.And(diff_sign, ex > ey + one, ey > f1x, ~y_zero),
        z3.And(ss == sx, es == ex - one, f0s <= ey),
    )
    result["SELTZO-TwoSum-04B-Y"] = z3.Implies(
        z3.And(diff_sign, ey > ex + one, ex > f1y, ~x_zero),
        z3.And(ss == sy, es == ey - one, f0s <= ex),
    )

    result["SELTZO-TwoSum-E63-X"] = z3.Implies(
        z3.And(same_sign, x_r0r1, y_r1r0, ex == ey + one, fx == fy),
        z3.And(ss == sx, s_all1, es == ex, e_pos_zero),
    )
    result["SELTZO-TwoSum-E63-Y"] = z3.Implies(
        z3.And(same_sign, y_r0r1, x_r1r0, ey == ex + one, fy == fx),
        z3.And(ss == sy, s_all1, es == ey, e_pos_zero),
    )

    result["SELTZO-TwoSum-19-X"] = z3.Implies(
        z3.And(same_sign, ~y_zero, ex == ey + one, ~lbx, fx < f0y),
        z3.And(ss == sx, lbs, es == ex, f1s == ey),
    )
    result["SELTZO-TwoSum-19-Y"] = z3.Implies(
        z3.And(same_sign, ~x_zero, ey == ex + one, ~lby, fy < f0x),
        z3.And(ss == sy, lbs, es == ey, f1s == ex),
    )

    result["SELTZO-TwoSum-156-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, ~y_zero, ex > ey, f0y >= ex - p),
        z3.And(ss == sx, es == ex, f1s == ey),
    )
    result["SELTZO-TwoSum-156-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, ~x_zero, ey > ex, f0x >= ey - p),
        z3.And(ss == sy, es == ey, f1s == ex),
    )

    result["SELTZO-TwoSum-162-X"] = z3.Implies(
        z3.And(diff_sign, f1x > ey + one),
        z3.And(ss == sx, f1s >= f1x - one),
    )
    result["SELTZO-TwoSum-162-Y"] = z3.Implies(
        z3.And(diff_sign, f1y > ex + one),
        z3.And(ss == sy, f1s >= f1y - one),
    )

    result["SELTZO-TwoSum-178-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, ex == ey + p, ~lby, f1y > ey - p),
        z3.And(ss == sx, es >= ex - one, es <= ex, ~e_zero, se == sy),
    )
    result["SELTZO-TwoSum-178-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, ey == ex + p, ~lbx, f1x > ex - p),
        z3.And(ss == sy, es >= ey - one, es <= ey, ~e_zero, se == sx),
    )

    result["SELTZO-TwoSum-182-X"] = z3.Implies(
        z3.And(same_sign, ex == ey + one, f0x == ey, es == ex + one),
        z3.And(ss == sx, ~lbs),
    )
    result["SELTZO-TwoSum-182-Y"] = z3.Implies(
        z3.And(same_sign, ey == ex + one, f0y == ex, es == ey + one),
        z3.And(ss == sy, ~lbs),
    )

    result["SELTZO-TwoSum-183-X"] = z3.Implies(
        z3.And(
            diff_sign,
            ~y_zero,
            ex > ey + one,
            f1x < f0y,
            f0y < ex - one,
        ),
        z3.And(ss == sx, es == ex - one, f1s >= f0y),
    )
    result["SELTZO-TwoSum-183-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            ~x_zero,
            ey > ex + one,
            f1y < f0x,
            f0x < ey - one,
        ),
        z3.And(ss == sy, es == ey - one, f1s >= f0x),
    )

    result["SELTZO-TwoSum-232-X"] = z3.Implies(
        z3.And(
            diff_sign,
            ~x_pow2,
            ex == ey + two,
        ),
        z3.And(ss == sx, z3.Or(es == ex, z3.And(es == ex - one, f1s >= f1x))),
    )
    result["SELTZO-TwoSum-232-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            ~y_pow2,
            ey == ex + two,
        ),
        z3.And(ss == sy, z3.Or(es == ey, z3.And(es == ey - one, f1s >= f1y))),
    )

    result["SELTZO-TwoSum-236-X"] = z3.Implies(
        z3.And(
            diff_sign,
            ~y_zero,
            ex == ey + two,
            f1x == f0y,
        ),
        z3.And(ss == sx, es == ex - one, f1s > f1x),
    )
    result["SELTZO-TwoSum-236-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            ~x_zero,
            ey == ex + two,
            f1y == f0x,
        ),
        z3.And(ss == sy, es == ey - one, f1s > f1y),
    )

    result["SELTZO-TwoSum-238-X"] = z3.Implies(
        z3.And(
            diff_sign,
            x_r0r1,
            nlby + ntby <= p - two,
            ex == ey + two,
            f1x > f0y,
            f1y > f1x,
        ),
        z3.And(ss == sx, es == ex - one, f1s > f1x),
    )
    result["SELTZO-TwoSum-238-Y"] = z3.Implies(
        z3.And(
            diff_sign,
            y_r0r1,
            nlbx + ntbx <= p - two,
            ey == ex + two,
            f1y > f0x,
            f1x > f1y,
        ),
        z3.And(ss == sy, es == ey - one, f1s > f1y),
    )

    result["SELTZO-TwoSum-264-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, ~y_zero, ~lby, ex == ey + one),
        z3.And(ss == sx, es >= ey - one, es <= ey),
    )
    result["SELTZO-TwoSum-264-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, ~x_zero, ~lbx, ey == ex + one),
        z3.And(ss == sy, es >= ex - one, es <= ex),
    )

    result["SELTZO-TwoSum-289-X"] = z3.Implies(
        z3.And(same_sign, ~x_zero, ~lbx, ~lby, ex == ey, f1x >= f1y),
        z3.And(ss == sx, es == ex + one, f1s <= f1x + one),
    )
    result["SELTZO-TwoSum-289-Y"] = z3.Implies(
        z3.And(same_sign, ~y_zero, ~lbx, ~lby, ex == ey, f1y >= f1x),
        z3.And(ss == sy, es == ey + one, f1s <= f1y + one),
    )

    result["SELTZO-TwoSum-429-X"] = z3.Implies(
        z3.And(same_sign, lby, lbx, ~tbx, f0x == g0x, ey == f0x),
        z3.And(
            ss == sx, s_pow2, es == ex + one, se != sx, ~e_zero, ee >= f0y, ee <= f1y
        ),
    )
    result["SELTZO-TwoSum-429-Y"] = z3.Implies(
        z3.And(same_sign, lbx, lby, ~tby, f0y == g0y, ex == f0y),
        z3.And(
            ss == sy, s_pow2, es == ey + one, se != sy, ~e_zero, ee >= f0x, ee <= f1x
        ),
    )

    result["SELTZO-TwoSum-440-X"] = z3.Implies(
        z3.And(same_sign, f0x == f1y, g1x >= f0y, es > ex),
        z3.And(ss == sx, es == ex + one, f1s >= f0x),
    )
    result["SELTZO-TwoSum-440-Y"] = z3.Implies(
        z3.And(same_sign, f0y == f1x, g1y >= f0x, es > ey),
        z3.And(ss == sy, es == ey + one, f1s >= f0y),
    )

    return result
