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

    def seltzo_case_zero(
        s_values: tuple[
            tuple[BoolVar] | BoolVar | None,
            int | None,
            int | None,
            IntVar | None,
            IntVar | None,
            IntVar | None,
        ],
    ) -> z3.BoolRef:
        ss_value, lbs_value, tbs_value, es_value, fs_value, gs_value = s_values
        assert ss_value is not ss
        assert lbs_value is not lbs
        assert tbs_value is not tbs
        assert es_value is not es
        clauses: list[z3.BoolRef] = []
        if isinstance(ss_value, tuple):
            clauses.append(ss != ss_value[0])
        elif ss_value is not None:
            clauses.append(ss == ss_value)
        if isinstance(lbs_value, int):
            assert lbs_value == 0 or lbs_value == 1
            clauses.append(lbs if lbs_value else ~lbs)
        if isinstance(tbs_value, int):
            assert tbs_value == 0 or tbs_value == 1
            clauses.append(tbs if tbs_value else ~tbs)
        if es_value is not None:
            clauses.append(es == es_value)
        if es_value is not None and fs_value is not None:
            clauses.append(nlbs == es_value - fs_value - one)
        if es_value is not None and gs_value is not None:
            clauses.append(ntbs == (p - one) - (es_value - gs_value))
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
        ss_value, lbs_value, tbs_value, es_value, fs_value, gs_value = s_values
        se_value, lbe_value, tbe_value, ee_value, fe_value, ge_value = e_values
        assert ss_value is not ss
        assert lbs_value is not lbs
        assert tbs_value is not tbs
        assert es_value is not es
        assert se_value is not se
        assert lbe_value is not lbe
        assert tbe_value is not tbe
        assert ee_value is not ee
        clauses: list[z3.BoolRef] = []
        if isinstance(ss_value, tuple):
            clauses.append(ss != ss_value[0])
        elif ss_value is not None:
            clauses.append(ss == ss_value)
        if isinstance(lbs_value, int):
            assert lbs_value == 0 or lbs_value == 1
            clauses.append(lbs if lbs_value else ~lbs)
        if isinstance(tbs_value, int):
            assert tbs_value == 0 or tbs_value == 1
            clauses.append(tbs if tbs_value else ~tbs)
        if es_value is not None:
            clauses.append(es == es_value)
        if es_value is not None and fs_value is not None:
            clauses.append(nlbs == es_value - fs_value - one)
        if es_value is not None and gs_value is not None:
            clauses.append(ntbs == (p - one) - (es_value - gs_value))
        if isinstance(se_value, tuple):
            clauses.append(se != se_value[0])
        elif se_value is not None:
            clauses.append(se == se_value)
        if isinstance(lbe_value, int):
            assert lbe_value == 0 or lbe_value == 1
            clauses.append(lbe if lbe_value else ~lbe)
        if isinstance(tbe_value, int):
            assert tbe_value == 0 or tbe_value == 1
            clauses.append(tbe if tbe_value else ~tbe)
        if ee_value is not None:
            clauses.append(ee == ee_value)
        if ee_value is not None and fe_value is not None:
            clauses.append(nlbe == ee_value - fe_value - one)
        if ee_value is not None and ge_value is not None:
            clauses.append(ntbe == (p - one) - (ee_value - ge_value))
        return z3.And(*clauses)

    ############################################################################

    # Sum of two powers of two (equal exponent case).
    result["SELTZO-TwoSum-POW2-POW2-SE"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_pow2, ex == ey),
        seltzo_case_zero((sx, 0, 0, ex + one, fx + one, gx + one)),
    )

    # Sum of two powers of two (adjacent case).
    result["SELTZO-TwoSum-POW2-POW2-SA-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_pow2, ex == ey + one),
        seltzo_case_zero((sx, 1, 0, ex, ey - one, ey)),
    )
    result["SELTZO-TwoSum-POW2-POW2-SA-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_pow2, ey == ex + one),
        seltzo_case_zero((sy, 1, 0, ey, ex - one, ex)),
    )

    # Sum of two powers of two (general case).
    result["SELTZO-TwoSum-POW2-POW2-SG-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_pow2, ex > ey + one, ex < ey + (p - one)),
        seltzo_case_zero((sx, 0, 0, ex, ey, ey)),
    )
    result["SELTZO-TwoSum-POW2-POW2-SG-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_pow2, ey > ex + one, ey < ex + (p - one)),
        seltzo_case_zero((sy, 0, 0, ey, ex, ex)),
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

    result["SELTZO-TwoSum-ALL1-POW2-DG-X"] = z3.Implies(
        z3.And(diff_sign, x_all1, y_pow2, ex > ey + one, ex < ey + (p - one)),
        seltzo_case_zero((sx, 1, 1, ex, ey, ey)),
    )
    result["SELTZO-TwoSum-ALL1-POW2-DG-Y"] = z3.Implies(
        z3.And(diff_sign, y_all1, x_pow2, ey > ex + one, ey < ex + (p - one)),
        seltzo_case_zero((sy, 1, 1, ey, ex, ex)),
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

    result["SELTZO-TwoSum-POW2-R1R0-S1-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_r1r0, ex == fy + p, ex > ey + one),
        seltzo_case_zero((sx, 0, 1, ex, ey, ey + one)),
    )
    result["SELTZO-TwoSum-POW2-R1R0-S1-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_r1r0, ey == fx + p, ey > ex + one),
        seltzo_case_zero((sy, 0, 1, ey, ex, ex + one)),
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

    result["SELTZO-TwoSum-POW2-R1R0-S2-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_r1r0, ex == ey + p),
        seltzo_case((sx, 0, 1, ex, ey + one, ey + two), ((sy,), 0, 0, gy, gy - p, gy)),
    )
    result["SELTZO-TwoSum-POW2-R1R0-S2-Y"] = z3.Implies(
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

    result["SELTZO-TwoSum-R0R1-R1R0-S3-X"] = z3.Implies(
        z3.And(same_sign, x_r0r1, y_r1r0, ex > ey + one, fy > fx),
        seltzo_case_zero((sx, 0, 1, ex, ey, gx)),
    )
    result["SELTZO-TwoSum-R0R1-R1R0-S3-Y"] = z3.Implies(
        z3.And(same_sign, y_r0r1, x_r1r0, ey > ex + one, fx > fy),
        seltzo_case_zero((sy, 0, 1, ey, ex, gy)),
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

    result["SELTZO-TwoSum-POW2-ONE1-S2-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_one1, ex > ey + one, ex < fy + (p - one)),
        seltzo_case_zero((sx, 0, 0, ex, ey, gy)),
    )
    result["SELTZO-TwoSum-POW2-ONE1-S2-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_one1, ey > ex + one, ey < fx + (p - one)),
        seltzo_case_zero((sy, 0, 0, ey, ex, gx)),
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

    ############################################################ COMPLETE LEMMAS

    """

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

    # Lemma C23: Sum of a one0 and a trailing pow2.
    result["SELTZO-TwoSum-C23-X"] = z3.Implies(
        z3.And(same_sign, x_one0, y_pow2, ex == ey + (p - one)),
        z3.And(
            ss == sx,
            lbs,
            ~tbs,
            es == ex,
            nlbs == nlbx + one,
            ntbs == (p - two) - nlbx,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C23-Y"] = z3.Implies(
        z3.And(same_sign, y_one0, x_pow2, ey == ex + (p - one)),
        z3.And(
            ss == sy,
            lbs,
            ~tbs,
            es == ey,
            nlbs == nlby + one,
            ntbs == (p - two) - nlby,
            e_pos_zero,
        ),
    )

    # Lemma C25: Difference of two r1r0s with the same exponent.
    result["SELTZO-TwoSum-C25-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_r1r0, ex == ey, nlbx > nlby + one),
        z3.And(
            ss == sx,
            lbs,
            ~tbs,
            es == fy,
            nlbs == (nlbx - nlby) - one,
            ntbs == p - (nlbx - nlby),
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C25-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_r1r0, ey == ex, nlby > nlbx + one),
        z3.And(
            ss == sy,
            lbs,
            ~tbs,
            es == fx,
            nlbs == (nlby - nlbx) - one,
            ntbs == p - (nlby - nlbx),
            e_pos_zero,
        ),
    )

    # Lemma C25A: Difference of two r1r0s with the same exponent.
    result["SELTZO-TwoSum-C25A-X"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_r1r0, ex == ey, nlbx == nlby + one),
        z3.And(
            ss == sx,
            ~lbs,
            ~tbs,
            es == fy,
            nlbs == p - one,
            ntbs == p - one,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C25A-Y"] = z3.Implies(
        z3.And(diff_sign, y_r1r0, x_r1r0, ey == ex, nlby == nlbx + one),
        z3.And(
            ss == sy,
            ~lbs,
            ~tbs,
            es == fx,
            nlbs == p - one,
            ntbs == p - one,
            e_pos_zero,
        ),
    )

    # Lemma C25S: Difference of two r1r0s with the same exponent.
    result["SELTZO-TwoSum-C25S"] = z3.Implies(
        z3.And(diff_sign, x_r1r0, y_r1r0, ex == ey, nlbx == nlby),
        z3.And(s_pos_zero, e_pos_zero),
    )

    # Lemma C26: Difference of a one1 just past the end of a pow2.
    result["SELTZO-TwoSum-C26-X"] = z3.Implies(
        z3.And(diff_sign, x_pow2, y_one1, ex == ey + p),
        z3.And(
            ss == sx,
            lbs,
            tbs,
            es == ex - one,
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
    result["SELTZO-TwoSum-C26-Y"] = z3.Implies(
        z3.And(diff_sign, y_pow2, x_one1, ey == ex + p),
        z3.And(
            ss == sy,
            lbs,
            tbs,
            es == ey - one,
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

    # Lemma C27: Sum of a pow2 and an all1.
    result["SELTZO-TwoSum-C27-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_all1, ex > ey + two, ex < ey + p),
        z3.And(
            ss == sx,
            ~lbs,
            ~tbs,
            es == ex,
            nlbs == (ex - ey) - two,
            ntbs == p - (ex - ey),
            se != sy,
            ~lbe,
            ~tbe,
            ee == ey - (p - one),
            nlbe == p - one,
            ntbe == p - one,
        ),
    )
    result["SELTZO-TwoSum-C27-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_all1, ey > ex + two, ey < ex + p),
        z3.And(
            ss == sy,
            ~lbs,
            ~tbs,
            es == ey,
            nlbs == (ey - ex) - two,
            ntbs == p - (ey - ex),
            se != sx,
            ~lbe,
            ~tbe,
            ee == ex - (p - one),
            nlbe == p - one,
            ntbe == p - one,
        ),
    )

    # Lemma C28: Sum of a one1 just past the end of a pow2.
    result["SELTZO-TwoSum-C28-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_one1, ex == ey + p),
        z3.And(
            ss == sx,
            ~lbs,
            tbs,
            es == ex,
            nlbs == p - two,
            ntbs == one,
            se != sy,
            lbe,
            ~tbe,
            ee == ey - one,
            nlbe == nlby,
            ntbe == p - (nlby + one),
        ),
    )
    result["SELTZO-TwoSum-C28-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_one1, ey == ex + p),
        z3.And(
            ss == sy,
            ~lbs,
            tbs,
            es == ey,
            nlbs == p - two,
            ntbs == one,
            se != sx,
            lbe,
            ~tbe,
            ee == ex - one,
            nlbe == nlbx,
            ntbe == p - (nlbx + one),
        ),
    )

    # Lemma C29: Sum of a pow2 and a number of the form 1.01 -> 1.10.
    result["SELTZO-TwoSum-C29-X"] = z3.Implies(
        z3.And(
            same_sign,
            ~lbx,
            nlbx == one,
            nlbx + ntbx < p - two,
            y_pow2,
            ex == ey + two,
        ),
        z3.And(
            ss == sx,
            lbs,
            tbs == tbx,
            es == ex,
            nlbs == one,
            ntbs == ntbx,
            e_pos_zero,
        ),
    )
    result["SELTZO-TwoSum-C29-Y"] = z3.Implies(
        z3.And(
            same_sign,
            ~lby,
            nlby == one,
            nlby + ntby < p - two,
            x_pow2,
            ey == ex + two,
        ),
        z3.And(
            ss == sy,
            lbs,
            tbs == tby,
            es == ey,
            nlbs == one,
            ntbs == ntby,
            e_pos_zero,
        ),
    )

    # Lemma C30: Sum of an r1r0 that fills one past the tail of a pow2.
    result["SELTZO-TwoSum-C30-X"] = z3.Implies(
        z3.And(same_sign, x_pow2, y_r1r0, ex > ey + two, gy == ex - p),
        z3.And(
            ss == sx,
            ~lbs,
            ~tbs,
            es == ex,
            nlbs == (ex - ey) - two,
            ntbs == p - (ex - ey),
            se != sy,
            ~lbe,
            ~tbe,
            ee == ex - p,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )
    result["SELTZO-TwoSum-C30-Y"] = z3.Implies(
        z3.And(same_sign, y_pow2, x_r1r0, ey > ex + two, gx == ey - p),
        z3.And(
            ss == sy,
            ~lbs,
            ~tbs,
            es == ey,
            nlbs == (ey - ex) - two,
            ntbs == p - (ey - ex),
            se != sx,
            ~lbe,
            ~tbe,
            ee == ey - p,
            nlbe == p - one,
            ntbe == p - one,
        ),
    )

    """

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

    ############################################################# PARTIAL LEMMAS

    """

    # Lemma P01A: If the exponent increases, then the sum must have a number of
    # leading zeros proportional to the exponent gap.
    result["SELTZO-TwoSum-P01A-X"] = z3.Implies(es > ex, f1s <= ey + one)
    result["SELTZO-TwoSum-P01A-Y"] = z3.Implies(es > ey, f1s <= ex + one)

    # Lemma P01B: If the exponent decreases, then the difference must have a
    # number of leading ones proportional to the exponent gap.
    result["SELTZO-TwoSum-P01B-X"] = z3.Implies(es < ex, f0s <= ey)
    result["SELTZO-TwoSum-P01B-Y"] = z3.Implies(es < ey, f0s <= ex)

    # Lemma P02A: Adding into leading zeros preserves the exponent.
    result["SELTZO-TwoSum-P02A-X"] = z3.Implies(
        z3.And(same_sign, ex > ey + one, ey + one > f1x),
        z3.And(ss == sx, es == ex, f1s <= ey + one),
    )
    result["SELTZO-TwoSum-P02A-Y"] = z3.Implies(
        z3.And(same_sign, ey > ex + one, ex + one > f1y),
        z3.And(ss == sy, es == ey, f1s <= ex + one),
    )

    # Lemma P02B: Subtracting from leading ones preserves the exponent.
    result["SELTZO-TwoSum-P02B-X"] = z3.Implies(
        z3.And(diff_sign, ex > ey + one, ey + one > f0x),
        z3.And(ss == sx, es == ex, f0s <= ey + one),
    )
    result["SELTZO-TwoSum-P02B-Y"] = z3.Implies(
        z3.And(diff_sign, ey > ex + one, ex + one > f0y),
        z3.And(ss == sy, es == ey, f0s <= ex + one),
    )

    """

    return result
