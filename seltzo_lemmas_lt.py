import z3
from smt_utils import BoolVar, IntVar, z3_If


def _min(a: IntVar, b: IntVar) -> IntVar:
    return z3_If(a < b, a, b)


def seltzo_two_sum_lt_lemmas(
    sx: BoolVar,
    sy: BoolVar,
    ss: BoolVar,
    lbx: z3.BoolRef,
    lby: z3.BoolRef,
    lbs: z3.BoolRef,
    tbx: z3.BoolRef,
    tby: z3.BoolRef,
    tbs: z3.BoolRef,
    ex: IntVar,
    ey: IntVar,
    es: IntVar,
    fx: IntVar,
    fy: IntVar,
    fs: IntVar,
    gx: IntVar,
    gy: IntVar,
    gs: IntVar,
    same_sign: z3.BoolRef,
    diff_sign: z3.BoolRef,
    xy_nonzero: z3.BoolRef,
    x_pow2: z3.BoolRef,
    y_pow2: z3.BoolRef,
    x_all1: z3.BoolRef,
    y_all1: z3.BoolRef,
    e_pos_zero: z3.BoolRef,
    p: IntVar,
    one: IntVar,
) -> dict[str, z3.BoolRef]:

    def seltzo_lemma_zero(
        hypotheses: tuple[z3.BoolRef, ...],
        s_val: tuple[BoolVar, int, int, IntVar, IntVar, IntVar],
    ) -> z3.BoolRef:
        ss_val, lbs_val, tbs_val, es_val, fs_val, gs_val = s_val
        return z3.Implies(
            z3.And(xy_nonzero, *hypotheses),
            z3.And(
                ss == ss_val,
                lbs if lbs_val else ~lbs,
                tbs if tbs_val else ~tbs,
                es == es_val,
                fs == fs_val,
                gs == gs_val,
                e_pos_zero,
            ),
        )

    result: dict[str, z3.BoolRef] = {}

    result["SELTZO-TwoSum-LS-POW2-G-X"] = seltzo_lemma_zero(
        (same_sign, x_pow2, ~tby, ex > ey + one, gy > fx + one),
        (sx, 0, 0, ex, ey, gy),
    )
    result["SELTZO-TwoSum-LS-POW2-G-Y"] = seltzo_lemma_zero(
        (same_sign, y_pow2, ~tbx, ey > ex + one, gx > fy + one),
        (sy, 0, 0, ey, ex, gx),
    )
    result["SELTZO-TwoSum-LS-POW2-A0-X"] = seltzo_lemma_zero(
        (same_sign, x_pow2, ~lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 1, 0, ex, ey - one, gy),
    )
    result["SELTZO-TwoSum-LS-POW2-A0-Y"] = seltzo_lemma_zero(
        (same_sign, y_pow2, ~lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 1, 0, ey, ex - one, gx),
    )
    result["SELTZO-TwoSum-LS-POW2-A1-X"] = seltzo_lemma_zero(
        (same_sign, x_pow2, lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 1, 0, ex, fy, gy),
    )
    result["SELTZO-TwoSum-LS-POW2-A1-Y"] = seltzo_lemma_zero(
        (same_sign, y_pow2, lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 1, 0, ey, fx, gx),
    )

    result["SELTZO-TwoSum-LS-T0-G-X"] = seltzo_lemma_zero(
        (same_sign, ~lbx, ~tbx, ~x_pow2, ~tby, ex > ey + one, gy > fx + one),
        (sx, 0, 0, ex, ey, gx),
    )
    result["SELTZO-TwoSum-LS-T0-G-Y"] = seltzo_lemma_zero(
        (same_sign, ~lby, ~tby, ~y_pow2, ~tbx, ey > ex + one, gx > fy + one),
        (sy, 0, 0, ey, ex, gy),
    )
    result["SELTZO-TwoSum-LS-T0-A0-X"] = seltzo_lemma_zero(
        (same_sign, ~lbx, ~tbx, ~x_pow2, ~lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 1, 0, ex, ey - one, gx),
    )
    result["SELTZO-TwoSum-LS-T0-A0-Y"] = seltzo_lemma_zero(
        (same_sign, ~lby, ~tby, ~y_pow2, ~lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 1, 0, ey, ex - one, gy),
    )
    result["SELTZO-TwoSum-LS-T0-A1-X"] = seltzo_lemma_zero(
        (same_sign, ~lbx, ~tbx, ~x_pow2, lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 1, 0, ex, fy, gx),
    )
    result["SELTZO-TwoSum-LS-T0-A1-Y"] = seltzo_lemma_zero(
        (same_sign, ~lby, ~tby, ~y_pow2, lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 1, 0, ey, fx, gy),
    )

    result["SELTZO-TwoSum-LS-T1-G-X"] = seltzo_lemma_zero(
        (same_sign, ~lbx, tbx, ~tby, ex > ey + one, gy > fx + one),
        (sx, 0, 1, ex, ey, gx),
    )
    result["SELTZO-TwoSum-LS-T1-G-Y"] = seltzo_lemma_zero(
        (same_sign, ~lby, tby, ~tbx, ey > ex + one, gx > fy + one),
        (sy, 0, 1, ey, ex, gy),
    )
    result["SELTZO-TwoSum-LS-T1-A0-X"] = seltzo_lemma_zero(
        (same_sign, ~lbx, tbx, ~lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 1, 1, ex, ey - one, gx),
    )
    result["SELTZO-TwoSum-LS-T1-A0-Y"] = seltzo_lemma_zero(
        (same_sign, ~lby, tby, ~lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 1, 1, ey, ex - one, gy),
    )
    result["SELTZO-TwoSum-LS-T1-A1-X"] = seltzo_lemma_zero(
        (same_sign, ~lbx, tbx, lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 1, 1, ex, fy, gx),
    )
    result["SELTZO-TwoSum-LS-T1-A1-Y"] = seltzo_lemma_zero(
        (same_sign, ~lby, tby, lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 1, 1, ey, fx, gy),
    )

    result["SELTZO-TwoSum-LD-ALL1-G-X"] = seltzo_lemma_zero(
        (diff_sign, x_all1, ~tby, ex > ey + one, gy > fx + one),
        (sx, 1, 1, ex, ey, gy),
    )
    result["SELTZO-TwoSum-LD-ALL1-G-Y"] = seltzo_lemma_zero(
        (diff_sign, y_all1, ~tbx, ey > ex + one, gx > fy + one),
        (sy, 1, 1, ey, ex, gx),
    )
    result["SELTZO-TwoSum-LD-ALL1-A0-X"] = seltzo_lemma_zero(
        (diff_sign, x_all1, ~lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 0, 1, ex, ey - one, gy),
    )
    result["SELTZO-TwoSum-LD-ALL1-A0-Y"] = seltzo_lemma_zero(
        (diff_sign, y_all1, ~lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 0, 1, ey, ex - one, gx),
    )
    result["SELTZO-TwoSum-LD-ALL1-A1-X"] = seltzo_lemma_zero(
        (diff_sign, x_all1, lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 0, 1, ex, fy, gy),
    )
    result["SELTZO-TwoSum-LD-ALL1-A1-Y"] = seltzo_lemma_zero(
        (diff_sign, y_all1, lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 0, 1, ey, fx, gx),
    )

    result["SELTZO-TwoSum-LD-T0-G-X"] = seltzo_lemma_zero(
        (diff_sign, lbx, ~tbx, ~tby, ex > ey + one, gy > fx + one),
        (sx, 1, 0, ex, ey, gx),
    )
    result["SELTZO-TwoSum-LD-T0-G-Y"] = seltzo_lemma_zero(
        (diff_sign, lby, ~tby, ~tbx, ey > ex + one, gx > fy + one),
        (sy, 1, 0, ey, ex, gy),
    )
    result["SELTZO-TwoSum-LD-T0-A0-X"] = seltzo_lemma_zero(
        (diff_sign, lbx, ~tbx, ~lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 0, 0, ex, ey - one, gx),
    )
    result["SELTZO-TwoSum-LD-T0-A0-Y"] = seltzo_lemma_zero(
        (diff_sign, lby, ~tby, ~lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 0, 0, ey, ex - one, gy),
    )
    result["SELTZO-TwoSum-LD-T0-A1-X"] = seltzo_lemma_zero(
        (diff_sign, lbx, ~tbx, lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 0, 0, ex, fy, gx),
    )
    result["SELTZO-TwoSum-LD-T0-A1-Y"] = seltzo_lemma_zero(
        (diff_sign, lby, ~tby, lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 0, 0, ey, fx, gy),
    )

    result["SELTZO-TwoSum-LD-T1-G-X"] = seltzo_lemma_zero(
        (diff_sign, lbx, tbx, ~x_all1, ~tby, ex > ey + one, gy > fx + one),
        (sx, 1, 1, ex, ey, gx),
    )
    result["SELTZO-TwoSum-LD-T1-G-Y"] = seltzo_lemma_zero(
        (diff_sign, lby, tby, ~y_all1, ~tbx, ey > ex + one, gx > fy + one),
        (sy, 1, 1, ey, ex, gy),
    )
    result["SELTZO-TwoSum-LD-T1-A0-X"] = seltzo_lemma_zero(
        (diff_sign, lbx, tbx, ~x_all1, ~lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 0, 1, ex, ey - one, gx),
    )
    result["SELTZO-TwoSum-LD-T1-A0-Y"] = seltzo_lemma_zero(
        (diff_sign, lby, tby, ~y_all1, ~lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 0, 1, ey, ex - one, gy),
    )
    result["SELTZO-TwoSum-LD-T1-A1-X"] = seltzo_lemma_zero(
        (diff_sign, lbx, tbx, ~x_all1, lby, ~tby, ex == ey + one, gy > fx + one),
        (sx, 0, 1, ex, fy, gx),
    )
    result["SELTZO-TwoSum-LD-T1-A1-Y"] = seltzo_lemma_zero(
        (diff_sign, lby, tby, ~y_all1, lbx, ~tbx, ey == ex + one, gx > fy + one),
        (sy, 0, 1, ey, fx, gy),
    )

    result["SELTZO-TwoSum-TS-L0-G-X"] = seltzo_lemma_zero(
        (same_sign, ~lbx, ~tbx, ~x_pow2, ~tby, gx > ey, gy + (p - one) > ex),
        (sx, 0, 0, ex, fx, gy),
    )
    result["SELTZO-TwoSum-TS-L0-G-Y"] = seltzo_lemma_zero(
        (same_sign, ~lby, ~tby, ~y_pow2, ~tbx, gy > ex, gx + (p - one) > ey),
        (sy, 0, 0, ey, fy, gx),
    )
    result["SELTZO-TwoSum-TS-L1-G-X"] = seltzo_lemma_zero(
        (same_sign, lbx, ~tbx, ~tby, _min(fx, gx) > ey, gy + (p - one) > ex),
        (sx, 1, 0, ex, fx, gy),
    )
    result["SELTZO-TwoSum-TS-L1-G-Y"] = seltzo_lemma_zero(
        (same_sign, lby, ~tby, ~tbx, _min(fy, gy) > ex, gx + (p - one) > ey),
        (sy, 1, 0, ey, fy, gx),
    )
    result["SELTZO-TwoSum-TD-L0-G-X"] = seltzo_lemma_zero(
        (diff_sign, ~lbx, tbx, ~tby, _min(fx, gx) > ey, gy + (p - one) > ex),
        (sx, 0, 1, ex, fx, gy),
    )
    result["SELTZO-TwoSum-TD-L0-G-Y"] = seltzo_lemma_zero(
        (diff_sign, ~lby, tby, ~tbx, _min(fy, gy) > ex, gx + (p - one) > ey),
        (sy, 0, 1, ey, fy, gx),
    )
    result["SELTZO-TwoSum-TD-L1-G-X"] = seltzo_lemma_zero(
        (diff_sign, lbx, tbx, ~x_all1, ~tby, gx > ey, gy + (p - one) > ex),
        (sx, 1, 1, ex, fx, gy),
    )
    result["SELTZO-TwoSum-TD-L1-G-Y"] = seltzo_lemma_zero(
        (diff_sign, lby, tby, ~y_all1, ~tbx, gy > ex, gx + (p - one) > ey),
        (sy, 1, 1, ey, fy, gx),
    )

    return result
