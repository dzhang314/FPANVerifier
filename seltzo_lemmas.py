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

    x_one0: z3.BoolRef = z3.And(lbx, tbx, nlbx + ntbx == p - two)
    y_one0: z3.BoolRef = z3.And(lby, tby, nlby + ntby == p - two)

    x_one1: z3.BoolRef = z3.And(~lbx, ~tbx, nlbx + ntbx == p - two)
    y_one1: z3.BoolRef = z3.And(~lby, ~tby, nlby + ntby == p - two)

    x_r0r1: z3.BoolRef = z3.And(~lbx, tbx, nlbx + ntbx == p - one)
    y_r0r1: z3.BoolRef = z3.And(~lby, tby, nlby + ntby == p - one)

    x_r1r0: z3.BoolRef = z3.And(lbx, ~tbx, nlbx + ntbx == p - one)
    y_r1r0: z3.BoolRef = z3.And(lby, ~tby, nlby + ntby == p - one)

    ############################################################ COMPLETE LEMMAS

    # Lemma C01: Sum where one number fits entirely into the other's leading
    # zeros, with padding on both sides.
    result["SELTZO-TwoSum-C01-X"] = z3.Implies(
        z3.And(~y_zero, same_sign, tbx, ex > ey + one, g1y > f1x + one),
        z3.And(
            ss == sx,
            ~lbs,
            tbs,
            es == ex,
            nlbs == ex - ey - one,
            ntbs == ntbx,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C01-Y"] = z3.Implies(
        z3.And(~x_zero, same_sign, tby, ey > ex + one, g1x > f1y + one),
        z3.And(
            ss == sy,
            ~lbs,
            tbs,
            es == ey,
            nlbs == ey - ex - one,
            ntbs == ntby,
            e_pos_zero,
        ),
    )

    # Lemma C01A: Sum where one number fits entirely into the other's leading
    # zeros, with padding only on the right.
    result["SELTZO-TwoSum-C01A-X"] = z3.Implies(
        z3.And(~y_zero, same_sign, tbx, ex == ey + one, g1y > f1x + one),
        z3.And(
            ss == sx,
            lbs,
            tbs,
            es == ex,
            nlbs == es - f0y - one,
            ntbs == ntbx,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C01A-Y"] = z3.Implies(
        z3.And(~x_zero, same_sign, tby, ey == ex + one, g1x > f1y + one),
        z3.And(
            ss == sy,
            lbs,
            tbs,
            es == ey,
            nlbs == es - f0x - one,
            ntbs == ntby,
            e_pos_zero,
        ),
    )

    # Lemma C01B: Sum where one number fits entirely into the other's leading
    # zeros, with padding only on the left.
    result["SELTZO-TwoSum-C01B-X"] = z3.Implies(
        z3.And(
            ~y_zero,
            same_sign,
            tbx,
            nlbx + ntbx < p - one,
            ex > ey + one,
            g1y == f1x + one,
        ),
        z3.And(
            ss == sx,
            ~lbs,
            tbs,
            es == ex,
            nlbs == ex - ey - one,
            ntbs == ntbx,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C01B-Y"] = z3.Implies(
        z3.And(
            ~x_zero,
            same_sign,
            tby,
            nlby + ntby < p - one,
            ey > ex + one,
            g1x == f1y + one,
        ),
        z3.And(
            ss == sy,
            ~lbs,
            tbs,
            es == ey,
            nlbs == ey - ex - one,
            ntbs == ntby,
            e_pos_zero,
        ),
    )

    # Lemma C02: Sum of powers of two (general case).
    result["SELTZO-TwoSum-C02-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_pow2, ex > ey + one, ey > ex - (p - one)),
        z3.And(
            ss == sx,
            ~lbs,
            ~tbs,
            es == ex,
            nlbs == (ex - ey) - one,
            ntbs == (p - one) - (ex - ey),
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C02-Y"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_pow2, ey > ex + one, ex > ey - (p - one)),
        z3.And(
            ss == sy,
            ~lbs,
            ~tbs,
            es == ey,
            nlbs == (ey - ex) - one,
            ntbs == (p - one) - (ey - ex),
            e_pos_zero,
        ),
    )

    # Lemma C02A: Sum of powers of two (adjacent case).
    result["SELTZO-TwoSum-C02A-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_pow2, ex == ey + one),
        z3.And(
            ss == sx,
            lbs,
            ~tbs,
            es == ex,
            nlbs == one,
            ntbs == p - two,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C02A-Y"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_pow2, ey == ex + one),
        z3.And(
            ss == sy,
            lbs,
            ~tbs,
            es == ey,
            nlbs == one,
            ntbs == p - two,
            e_pos_zero,
        ),
    )

    # Lemma C02B: Sum of powers of two (boundary case).
    result["SELTZO-TwoSum-C02B-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_pow2, ex == ey + (p - one)),
        z3.And(
            ss == sx,
            ~lbs,
            tbs,
            es == ex,
            nlbs == p - two,
            ntbs == one,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C02B-Y"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_pow2, ey == ex + (p - one)),
        z3.And(
            ss == sy,
            ~lbs,
            tbs,
            es == ey,
            nlbs == p - two,
            ntbs == one,
            e_pos_zero,
        ),
    )

    # Lemma C02S: Sum of powers of two (identical case).
    result["SELTZO-TwoSum-C02S"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_pow2, ex == ey),
        z3.And(
            ss == sx,
            ~lbs,
            ~tbs,
            es == ex + one,
            es == ey + one,
            nlbs == p - one,
            ntbs == p - one,
            e_pos_zero,
        ),
    )

    # Lemma C03: Sum of two adjacent r1r0 numbers.
    result["SELTZO-TwoSum-C03-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, y_r1r0, ey == fx, ex > fy + p),
        z3.And(
            ss == sx,
            ~lbs,
            ~tbs,
            es == ex + one,
            nlbs == p - one,
            ntbs == p - one,
            se != sx,
            ~lbe,
            ~tbe,
            ee == f0y + one,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )
    result["SELTZO-TwoSum-C03-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_r1r0, ex == fy, ey > fx + p),
        z3.And(
            ss == sy,
            ~lbs,
            ~tbs,
            es == ey + one,
            nlbs == p - one,
            ntbs == p - one,
            se != sy,
            ~lbe,
            ~tbe,
            ee == f0x + one,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )

    # Lemma C04: Sum of all1 and pow2.
    result["SELTZO-TwoSum-C04-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_pow2, ex > ey, ex < ey + (p - two)),
        z3.And(
            ss == sx,
            ~lbs,
            ~tbs,
            es == ex + one,
            nlbs == ex - ey,
            ntbs == (p - two) - (ex - ey),
            se != sx,
            ~lbe,
            ~tbe,
            ee == ex - (p - one),
            nlbe == p - one,
            ntbe == p - one,
        ),
    )
    result["SELTZO-TwoSum-C04-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_pow2, ey > ex, ey < ex + (p - two)),
        z3.And(
            ss == sx,
            ~lbs,
            ~tbs,
            es == ey + one,
            nlbs == ey - ex,
            ntbs == (p - two) - (ey - ex),
            se != sx,
            ~lbe,
            ~tbe,
            ee == ey - (p - one),
            nlbe == p - one,
            ntbe == p - one,
        ),
    )

    # Lemma C05: Sum of adjacent r1r0 and one1.
    result["SELTZO-TwoSum-C05-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, ntbx == one, y_one1, ey == fx),
        z3.And(
            ss == sx,
            lbs,
            tbs,
            es == ex,
            nlbs == p - one,
            ntbs == p - one,
            se == sx,
            ~lbe,
            ~tbe,
            ee == f1y,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )
    result["SELTZO-TwoSum-C05-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, ntby == one, x_one1, ex == fy),
        z3.And(
            ss == sy,
            lbs,
            tbs,
            es == ey,
            nlbs == p - one,
            ntbs == p - one,
            se == sy,
            ~lbe,
            ~tbe,
            ee == f1x,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )

    # Lemma C06: Sum of all1 and one1.
    result["SELTZO-TwoSum-C06-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_one1, ex > ey, gy > ex - (p - two)),
        z3.And(
            ss == sx,
            ~lbs,
            ~tbs,
            es == ex + one,
            nlbs == ex - ey,
            ntbs == gy - (ex - (p - two)),
            se != sx,
            ~lbe,
            ~tbe,
            ee == ex - (p - one),
            nlbe == p - one,
            ntbe == p - one,
        ),
    )
    result["SELTZO-TwoSum-C06-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_one1, ey > ex, gx > ey - (p - two)),
        z3.And(
            ss == sy,
            ~lbs,
            ~tbs,
            es == ey + one,
            nlbs == ey - ex,
            ntbs == gx - (ey - (p - two)),
            se != sy,
            ~lbe,
            ~tbe,
            ee == ey - (p - one),
            nlbe == p - one,
            ntbe == p - one,
        ),
    )

    # Lemma C07: Difference of aligned r1r0 and pow2.
    result["SELTZO-TwoSum-C07-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_pow2, ex == ey, gx < ey - one),
        z3.And(
            ss == sx,
            lbs,
            ~tbs,
            es == ex - one,
            nlbs == nlbx - one,
            ntbs == ntbx + one,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C07-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_pow2, ey == ex, gy < ex - one),
        z3.And(
            ss == sy,
            lbs,
            ~tbs,
            es == ey - one,
            nlbs == nlby - one,
            ntbs == ntby + one,
            e_pos_zero,
        ),
    )

    # Lemma C08: Difference of an r1r0 just past the end of a pow2.
    result["SELTZO-TwoSum-C08-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_r1r0, ex == ey + (p + one)),
        z3.And(
            ss == sx,
            lbs,
            tbs,
            es == ex - one,
            nlbs == p - one,
            ntbs == p - one,
            se == sx,
            ~lbe,
            ~tbe,
            ee == gy,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )
    result["SELTZO-TwoSum-C08-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_r1r0, ey == ex + (p + one)),
        z3.And(
            ss == sy,
            lbs,
            tbs,
            es == ey - one,
            nlbs == p - one,
            ntbs == p - one,
            se == sy,
            ~lbe,
            ~tbe,
            ee == gx,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )

    # Lemma C09: Sum of an r1r0 just past the end of a pow2.
    result["SELTZO-TwoSum-C09-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_r1r0, ex == ey + p),
        z3.And(
            ss == sx,
            ~lbs,
            tbs,
            es == ex,
            nlbs == p - two,
            ntbs == one,
            se != sx,
            ~lbe,
            ~tbe,
            ee == gy,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )
    result["SELTZO-TwoSum-C09-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_r1r0, ey == ex + p),
        z3.And(
            ss == sy,
            ~lbs,
            tbs,
            es == ey,
            nlbs == p - two,
            ntbs == one,
            se != sy,
            ~lbe,
            ~tbe,
            ee == gx,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )

    # Lemma C10: Sum of a pow2 just before the end of an r1r0 (general case).
    result["SELTZO-TwoSum-C10-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, y_pow2, ex == ey + (p - one), ntbx > one),
        z3.And(
            ss == sx,
            lbs,
            tbs,
            es == ex,
            nlbs == nlbx,
            ntbs == one,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C10-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_pow2, ey == ex + (p - one), ntby > one),
        z3.And(
            ss == sy,
            lbs,
            tbs,
            es == ey,
            nlbs == nlby,
            ntbs == one,
            e_pos_zero,
        ),
    )

    # Lemma C10A: Sum of a pow2 just before the end of an r1r0 (boundary case).
    result["SELTZO-TwoSum-C10A-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, y_pow2, ex == ey + (p - one), ntbx == one),
        z3.And(
            ss == sx,
            lbs,
            tbs,
            es == ex,
            nlbs == p - one,
            ntbs == p - one,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C10A-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, x_pow2, ey == ex + (p - one), ntby == one),
        z3.And(
            ss == sy,
            lbs,
            tbs,
            es == ey,
            nlbs == p - one,
            ntbs == p - one,
            e_pos_zero,
        ),
    )

    # Lemma C11: Sum of an r1r0 inside the zeros of an r0r1.
    result["SELTZO-TwoSum-C11-X"] = z3.Implies(
        z3.And(same_sign, x_r0r1, y_r1r0, ex > ey + one, fx + one == gy),
        z3.And(
            ss == sx,
            ~lbs,
            tbs,
            es == ex,
            ntbs == ntbx + nlby + one,
            nlbs == p - (ntbx + nlby + two),
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C11-Y"] = z3.Implies(
        z3.And(same_sign, y_r0r1, x_r1r0, ey > ex + one, fy + one == gx),
        z3.And(
            ss == sy,
            ~lbs,
            tbs,
            es == ey,
            ntbs == ntby + nlbx + one,
            nlbs == p - (ntby + nlbx + two),
            e_pos_zero,
        ),
    )

    # Lemma C12: Sum of a pow2 and a number that fits inside its zeros.
    result["SELTZO-TwoSum-C12-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_pow2,
            ~y_zero,
            ~tby,
            ex > ey + one,
            gy > ex - (p - one),
        ),
        z3.And(
            ss == sx,
            ~lbs,
            ~tbs,
            es == ex,
            nlbs == (ex - ey) - one,
            ntbs == (p - one) - (ex - gy),
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C12-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_pow2,
            ~x_zero,
            ~tbx,
            ey > ex + one,
            gx > ey - (p - one),
        ),
        z3.And(
            ss == sy,
            ~lbs,
            ~tbs,
            es == ey,
            nlbs == (ey - ex) - one,
            ntbs == (p - one) - (ey - gx),
            e_pos_zero,
        ),
    )

    # Lemma C13: Difference of powers of two (general case).
    result["SELTZO-TwoSum-C13-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_pow2, ex > ey + one, ex < ey + p),
        z3.And(
            ss == sx,
            lbs,
            ~tbs,
            es == ex - one,
            nlbs == (ex - ey) - one,
            ntbs == p - (ex - ey),
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C13-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_pow2, ey > ex + one, ey < ex + p),
        z3.And(
            ss == sy,
            lbs,
            ~tbs,
            es == ey - one,
            nlbs == (ey - ex) - one,
            ntbs == p - (ey - ex),
            e_pos_zero,
        ),
    )

    # Lemma C13A: Difference of powers of two (adjacent case).
    result["SELTZO-TwoSum-C13A-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_pow2, ex == ey + one),
        z3.And(
            ss == sx,
            ~lbs,
            ~tbs,
            es == ex - one,
            nlbs == p - one,
            ntbs == p - one,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C13A-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_pow2, ey == ex + one),
        z3.And(
            ss == sy,
            ~lbs,
            ~tbs,
            es == ey - one,
            nlbs == p - one,
            ntbs == p - one,
            e_pos_zero,
        ),
    )

    # Lemma C13B: Difference of powers of two (boundary case).
    result["SELTZO-TwoSum-C13B-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_pow2, ex == ey + p),
        z3.And(
            ss == sx,
            lbs,
            tbs,
            es == ex - one,
            nlbs == p - one,
            ntbs == p - one,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C13B-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_pow2, ey == ex + p),
        z3.And(
            ss == sy,
            lbs,
            tbs,
            es == ey - one,
            nlbs == p - one,
            ntbs == p - one,
            e_pos_zero,
        ),
    )

    # Lemma C13S: Difference of powers of two (identical case).
    result["SELTZO-TwoSum-C13S"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_pow2, ex == ey),
        z3.And(s_pos_zero, e_pos_zero),
    )

    # Lemma C14: Sum of an one1 that just overlaps the end of an all1.
    result["SELTZO-TwoSum-C14-X"] = z3.Implies(
        z3.And(same_sign, x_all1, y_one1, ex == ey + (p - one)),
        z3.And(
            ss == sx,
            ~lbs,
            ~tbs,
            es == ex + one,
            nlbs == p - one,
            ntbs == p - one,
            se == sx,
            ~lbe,
            ~tbe,
            ee == fy,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )
    result["SELTZO-TwoSum-C14-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, x_one1, ey == ex + (p - one)),
        z3.And(
            ss == sy,
            ~lbs,
            ~tbs,
            es == ey + one,
            nlbs == p - one,
            ntbs == p - one,
            se == sy,
            ~lbe,
            ~tbe,
            ee == fx,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )

    # Lemma C15: Sum of a one1 that straddles a pow2.
    result["SELTZO-TwoSum-C15-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_one1, ex < ey + (p - one), ex > fy + (p - one)),
        z3.And(
            ss == sx,
            ~lbs,
            ~tbs,
            es == ex,
            nlbs == (ex - ey) - one,
            ntbs == (p - one) - (ex - ey),
            se == sx,
            ~lbe,
            ~tbe,
            ee == fy,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )
    result["SELTZO-TwoSum-C15-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_one1, ey < ex + (p - one), ey > fx + (p - one)),
        z3.And(
            ss == sy,
            ~lbs,
            ~tbs,
            es == ey,
            nlbs == (ey - ex) - one,
            ntbs == (p - one) - (ey - ex),
            se == sy,
            ~lbe,
            ~tbe,
            ee == fx,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )

    # Lemma C16: Difference of an all1 just past the end of a pow2.
    result["SELTZO-TwoSum-C16-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_all1, ex == ey + (p + one)),
        z3.And(
            ss == sx,
            lbs,
            tbs,
            es == ex - one,
            nlbs == p - one,
            ntbs == p - one,
            se == sx,
            ~lbe,
            ~tbe,
            ee == ey - (p - one),
            nlbe == p - one,
            ntbe == p - one,
        ),
    )
    result["SELTZO-TwoSum-C16-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_all1, ey == ex + (p + one)),
        z3.And(
            ss == sy,
            lbs,
            tbs,
            es == ey - one,
            nlbs == p - one,
            ntbs == p - one,
            se == sy,
            ~lbe,
            ~tbe,
            ee == ex - (p - one),
            nlbe == p - one,
            ntbe == p - one,
        ),
    )

    # Lemma C17: Cancellation in a difference between two one1s.
    result["SELTZO-TwoSum-C17-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_one1, ey == fx, ex > fy + p),
        z3.And(
            ss == sx,
            ~lbs,
            ~tbs,
            es == ex,
            nlbs == p - one,
            ntbs == p - one,
            se == sy,
            ~lbe,
            ~tbe,
            ee == fy,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )
    result["SELTZO-TwoSum-C17-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_one1, ex == fy, ey > fx + p),
        z3.And(
            ss == sy,
            ~lbs,
            ~tbs,
            es == ey,
            nlbs == p - one,
            ntbs == p - one,
            se == sx,
            ~lbe,
            ~tbe,
            ee == fx,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )

    # Lemma C17A: Cancellation in a difference between two one1s.
    result["SELTZO-TwoSum-C17A-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_one1, ey == fx, ex == fy + p),
        z3.And(
            ss == sx,
            lbs,
            tbs,
            es == ex - one,
            nlbs == p - one,
            ntbs == p - one,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C17A-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_one1, ex == fy, ey == fx + p),
        z3.And(
            ss == sy,
            lbs,
            tbs,
            es == ey - one,
            nlbs == p - one,
            ntbs == p - one,
            e_pos_zero,
        ),
    )

    # Lemma C18: Cancellation in a difference between a pow2 and a one1.
    result["SELTZO-TwoSum-C18-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_pow2, ex == ey),
        z3.And(
            ss == sx,
            ~lbs,
            ~tbs,
            es == fx,
            nlbs == p - one,
            ntbs == p - one,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C18-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_pow2, ey == ex),
        z3.And(
            ss == sy,
            ~lbs,
            ~tbs,
            es == fy,
            nlbs == p - one,
            ntbs == p - one,
            e_pos_zero,
        ),
    )

    # Lemma C19: Cancellation in a difference between a pow2 and a one1.
    result["SELTZO-TwoSum-C19-X"] = z3.Implies(
        z3.And(diff_sign, x_one1, y_pow2, fx == ey),
        z3.And(
            ss == sx,
            ~lbs,
            ~tbs,
            es == ex,
            nlbs == p - one,
            ntbs == p - one,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C19-Y"] = z3.Implies(
        z3.And(diff_sign, y_one1, x_pow2, fy == ex),
        z3.And(
            ss == sy,
            ~lbs,
            ~tbs,
            es == ey,
            nlbs == p - one,
            ntbs == p - one,
            e_pos_zero,
        ),
    )

    # Lemma C20: Sum of an r1r0 that just hangs off the end of a pow2.
    result["SELTZO-TwoSum-C20-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_r1r0, nlby > one, ex == gy + (p + one)),
        z3.And(
            ss == sx,
            ~lbs,
            ~tbs,
            es == ex,
            nlbs == (ex - ey) - two,
            ntbs == p - (ex - ey),
            se != sx,
            ~lbe,
            ~tbe,
            ee == gy,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )
    result["SELTZO-TwoSum-C20-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_r1r0, nlbx > one, ey == gx + (p + one)),
        z3.And(
            ss == sy,
            ~lbs,
            ~tbs,
            es == ey,
            nlbs == (ey - ex) - two,
            ntbs == p - (ey - ex),
            se != sy,
            ~lbe,
            ~tbe,
            ee == gx,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )

    # Lemma C21: Sum of an r1r0 that fills in the end of a pow2.
    result["SELTZO-TwoSum-C21-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_r1r0, ex > ey + one, gy == ex - (p - one)),
        z3.And(
            ss == sx,
            ~lbs,
            tbs,
            es == ex,
            nlbs == (ex - ey) - one,
            ntbs == p - (ex - ey),
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C21-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_r1r0, ey > ex + one, gx == ey - (p - one)),
        z3.And(
            ss == sy,
            ~lbs,
            tbs,
            es == ey,
            nlbs == (ey - ex) - one,
            ntbs == p - (ey - ex),
            e_pos_zero,
        ),
    )

    # Lemma C22: Sum of a pow2 that fills in the gap of a one0.
    result["SELTZO-TwoSum-C22-X"] = z3.Implies(
        z3.And(same_sign, x_one0, y_pow2, ey == fx),
        z3.And(
            ss == sx,
            lbs,
            tbs,
            es == ex,
            nlbs == p - one,
            ntbs == p - one,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C22-Y"] = z3.Implies(
        z3.And(same_sign, y_one0, x_pow2, ex == fy),
        z3.And(
            ss == sy,
            lbs,
            tbs,
            es == ey,
            nlbs == p - one,
            ntbs == p - one,
            e_pos_zero,
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

    x_mm01: z3.BoolRef = z3.And(lbx, ~tbx, nlbx + ntbx == p - three)
    y_mm01: z3.BoolRef = z3.And(lby, ~tby, nlby + ntby == p - three)
    s_mm01: z3.BoolRef = z3.And(lbs, ~tbs, nlbs + ntbs == p - three)
    e_mm01: z3.BoolRef = z3.And(lbe, ~tbe, nlbe + ntbe == p - three)

    x_mm10: z3.BoolRef = z3.And(~lbx, tbx, nlbx + ntbx == p - three)
    y_mm10: z3.BoolRef = z3.And(~lby, tby, nlby + ntby == p - three)
    s_mm10: z3.BoolRef = z3.And(~lbs, tbs, nlbs + ntbs == p - three)
    e_mm10: z3.BoolRef = z3.And(~lbe, tbe, nlbe + ntbe == p - three)

    """

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
        z3.And(diff_sign, ~x_pow2, f1x > ey),
        z3.And(ss == sx, es == ex, f1s <= f1x),
    )
    result["SELTZO-TwoSum-P4B-Y"] = z3.Implies(
        z3.And(diff_sign, ~y_pow2, f1y > ex),
        z3.And(ss == sy, es == ey, f1s <= f1y),
    )

    # Lemma P5A: Less-significant zeros in the mantissa shield more-significant
    # zeros from being affected by addition.
    result["SELTZO-TwoSum-P5A-X"] = z3.Implies(
        z3.And(same_sign, f0x > g0x, g0x > ey),
        z3.And(ss == sx, es == ex, f0s == f0x),
    )
    result["SELTZO-TwoSum-P5A-Y"] = z3.Implies(
        z3.And(same_sign, f0y > g0y, g0y > ex),
        z3.And(ss == sy, es == ey, f0s == f0y),
    )

    # Lemma P5B: Less-significant ones in the mantissa shield more-significant
    # ones from being subtracted off.
    result["SELTZO-TwoSum-P5B-X"] = z3.Implies(
        z3.And(diff_sign, f1x > g1x, g1x > ey),
        z3.And(ss == sx, es == ex, f1s == f1x),
    )
    result["SELTZO-TwoSum-P5B-Y"] = z3.Implies(
        z3.And(diff_sign, f1y > g1y, g1y > ex),
        z3.And(ss == sy, es == ey, f1s == f1y),
    )

    # Lemma P6: If there is a gap between the addends, then the exponent cannot
    # change, and at most one leading bit can be destroyed.
    result["SELTZO-TwoSum-P6-X"] = z3.Implies(
        z3.And(~x_pow2, ey + one < g1x),
        z3.And(ss == sx, es == ex, f0s >= f0x - one, f1s >= f1x - one),
    )
    result["SELTZO-TwoSum-P6-Y"] = z3.Implies(
        z3.And(~y_pow2, ex + one < g1y),
        z3.And(ss == sy, es == ey, f0s >= f0y - one, f1s >= f1y - one),
    )

    # Lemma P7A: Adding into leading ones increases the exponent.
    result["SELTZO-TwoSum-P7A-X"] = z3.Implies(
        z3.And(~y_zero, same_sign, ey > f0x),
        es >= ex + one,
    )
    result["SELTZO-TwoSum-P7A-Y"] = z3.Implies(
        z3.And(~x_zero, same_sign, ex > f0y),
        es >= ey + one,
    )

    # Lemma P7B: Subtracting from leading zeros decreases the exponent.
    result["SELTZO-TwoSum-P7B-X"] = z3.Implies(
        z3.And(~y_zero, diff_sign, ex + one > ey, ey > f1x),
        es <= ex - one,
    )
    result["SELTZO-TwoSum-P7B-Y"] = z3.Implies(
        z3.And(~x_zero, diff_sign, ey + one > ex, ex > f1y),
        es <= ey - one,
    )

    # Lemma P8: Adding a number to a power of two cannot increase the exponent
    # as long as it contains a zero not too far away.
    result["SELTZO-TwoSum-P8-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, ~y_zero, ex > ey, f0y + (p + one) > ex),
        z3.And(ss == sx, es == ex, f1s == ey),
    )
    result["SELTZO-TwoSum-P8-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, ~x_zero, ey > ex, f0x + (p + one) > ey),
        z3.And(ss == sy, es == ey, f1s == ex),
    )

    # Lemma P9: One specific output is impossible.
    result["SELTZO-TwoSum-P9"] = ~z3.And(s_pow2, e_pow2, ss != se, es < ee + (p + one))

    # Lemma P10A: Adding a small number cannot destroy leading zeros past its
    # exponent.
    result["SELTZO-TwoSum-P10A-X"] = z3.Implies(
        z3.And(same_sign, ex > ey + one, ey + one > f1x),
        z3.And(ss == sx, es == ex, f1s <= ey + one),
    )
    result["SELTZO-TwoSum-P10A-Y"] = z3.Implies(
        z3.And(same_sign, ey > ex + one, ex + one > f1y),
        z3.And(ss == sy, es == ey, f1s <= ex + one),
    )

    # Lemma P10B: Subtracting a small number cannot destroy leading ones past
    # its exponent.
    result["SELTZO-TwoSum-P10B-X"] = z3.Implies(
        z3.And(diff_sign, ex > ey + one, ey + one > f0x),
        z3.And(ss == sx, es == ex, f0s <= ey + one),
    )
    result["SELTZO-TwoSum-P10B-Y"] = z3.Implies(
        z3.And(diff_sign, ey > ex + one, ex + one > f0y),
        z3.And(ss == sy, es == ey, f0s <= ex + one),
    )

    # Lemma P11A: Adding just past the end of an all-1 mantissa increments the
    # sum to the following power of 2.
    result["SELTZO-TwoSum-P11A-X"] = z3.Implies(
        z3.And(same_sign, x_all1, ~y_zero, ex == ey + p),
        z3.And(s_pow2, ss == sx, es == ex + one),
    )
    result["SELTZO-TwoSum-P11A-Y"] = z3.Implies(
        z3.And(same_sign, y_all1, ~x_zero, ey == ex + p),
        z3.And(s_pow2, ss == sy, es == ey + one),
    )

    # Lemma P11B: Subtracting just past the end of a power of 2 decrements the
    # sum to the previous all-1 number.
    result["SELTZO-TwoSum-P11B-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, ~y_zero, ~lby, ex == ey + p),
        z3.And(s_all1, ss == sx, es == ex - one),
    )
    result["SELTZO-TwoSum-P11B-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, ~x_zero, ~lbx, ey == ex + p),
        z3.And(s_all1, ss == sy, es == ey - one),
    )

    # Lemma P12: Adding a small number flips the parity of the mantissa.
    result["SELTZO-TwoSum-P12-X"] = z3.Implies(
        z3.And(
            ~x_pow2,
            ~y_zero,
            ~tbx,
            ~lby,
            ex == ey + (p - one),
        ),
        z3.And(ss == sx, es == ex, tbs),
    )
    result["SELTZO-TwoSum-P12-Y"] = z3.Implies(
        z3.And(
            ~y_pow2,
            ~x_zero,
            ~tby,
            ~lbx,
            ey == ex + (p - one),
        ),
        z3.And(ss == sy, es == ey, tbs),
    )

    # Lemma P13: Another case of subtracting just past the end of a power of 2.
    result["SELTZO-TwoSum-P13-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, lby, ex == ey + p),
        z3.And(
            ss == sx,
            lbs,
            ~tbs,
            es == ex - one,
            nlbs == p - two,
            ntbs == one,
            ee <= ey - nlby,
            ee >= ey - (nlby + one),
        ),
    )
    result["SELTZO-TwoSum-P13-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, lbx, ey == ex + p),
        z3.And(
            ss == sy,
            lbs,
            ~tbs,
            es == ey - one,
            nlbs == p - two,
            ntbs == one,
            ee <= ex - nlbx,
            ee >= ex - (nlbx + one),
        ),
    )

    # Lemma P14: The leading zeros of the smaller addend straddle the boundary
    # of the mantissa of the larger addend.
    result["SELTZO-TwoSum-P14-X"] = z3.Implies(
        z3.And(~y_zero, same_sign, g1x > ey, ey + p > ex, ~y_pow2, f1y + p < ex),
        z3.And(ss == sx, es == ex, se == sx, ee == f1y),
    )
    result["SELTZO-TwoSum-P14-Y"] = z3.Implies(
        z3.And(~x_zero, same_sign, g1y > ex, ex + p > ey, ~x_pow2, f1x + p < ey),
        z3.And(ss == sy, es == ey, se == sy, ee == f1x),
    )

    # Lemma P15: Adding leading ones to the end of an r1r0 number pushes it up
    # to the next power of two.
    result["SELTZO-TwoSum-P15-X"] = z3.Implies(
        z3.And(same_sign, x_r1r0, ey == f0x, ex > f0y + p),
        z3.And(s_pow2, ss == sx, es == ex + one),
    )
    result["SELTZO-TwoSum-P15-Y"] = z3.Implies(
        z3.And(same_sign, y_r1r0, ex == f0y, ey > f0x + p),
        z3.And(s_pow2, ss == sy, es == ey + one),
    )

    # Lemma P16: If addition does not change the exponent, then it must
    # preserve the number of leading ones.
    result["SELTZO-TwoSum-P16-X"] = z3.Implies(
        z3.And(same_sign, es == ex, lbx),
        z3.And(ss == sx, lbs, nlbs >= nlbx),
    )
    result["SELTZO-TwoSum-P16-Y"] = z3.Implies(
        z3.And(same_sign, es == ey, lby),
        z3.And(ss == sy, lbs, nlbs >= nlby),
    )

    # Lemma P17: Adding a non-power-of-two just past the end of a power of two
    # increments the final bit and creates an error term with leading ones.
    result["SELTZO-TwoSum-P17-X"] = z3.Implies(
        z3.And(
            same_sign,
            x_pow2,
            ex == ey + p,
            ~y_zero,
            ~y_pow2,
            ~lby,
            nlby > one,
        ),
        z3.And(
            s_r0r1,
            ss == sx,
            es == ex,
            ntbs == one,
            se != sx,
            ee == ey - one,
            lbe,
            nlbe >= nlby - one,
        ),
    )
    result["SELTZO-TwoSum-P17-Y"] = z3.Implies(
        z3.And(
            same_sign,
            y_pow2,
            ey == ex + p,
            ~x_zero,
            ~x_pow2,
            ~lbx,
            nlbx > one,
        ),
        z3.And(
            s_r0r1,
            ss == sy,
            es == ey,
            ntbs == one,
            se != sy,
            ee == ex - one,
            lbe,
            nlbe >= nlbx - one,
        ),
    )

    # Lemma P18: When cancellation occurs, the exponent of the difference is
    # bounded above by the number of common leading bits.
    result["SELTZO-TwoSum-P18"] = z3.Implies(
        z3.And(diff_sign, ex == ey),
        z3.Or(
            s_pos_zero,
            z3.And(
                z3.Or(es <= f0x, es <= f0y),
                z3.Or(es <= f1x, es <= f1y),
            ),
        ),
    )

    # Lemma P19: If the inputs are different, then the result cannot be zero.
    result["SELTZO-TwoSum-P19"] = z3.Implies(
        z3.Or(ex != ey, f0x != f0y, f1x != f1y, g0x != g0y, g1x != g1y),
        ~s_zero,
    )

    # Lemma P20: The amount of cancellation is limited if the subtrahend has
    # leading zeros.
    result["SELTZO-TwoSum-P20-X"] = z3.Implies(
        z3.And(diff_sign, ex > ey, ~lby),
        z3.And(ss == sx, es >= ey - one),
    )
    result["SELTZO-TwoSum-P20-Y"] = z3.Implies(
        z3.And(diff_sign, ey > ex, ~lbx),
        z3.And(ss == sy, es >= ex - one),
    )

    # Lemma P21: When subtracting an adjacent number from from a power of 2,
    # cancellation is determined by leading ones in the subtrahend.
    result["SELTZO-TwoSum-P21-X"] = z3.Implies(
        z3.And(~y_zero, diff_sign, x_pow2, ex == ey + one),
        z3.And(ss == sx, z3.Or(es == f0y, es == f0y + one), e_pos_zero),
    )
    result["SELTZO-TwoSum-P21-Y"] = z3.Implies(
        z3.And(~x_zero, diff_sign, y_pow2, ey == ex + one),
        z3.And(ss == sy, z3.Or(es == f0x, es == f0x + one), e_pos_zero),
    )

    """

    return result
