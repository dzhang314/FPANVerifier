# FPANVerifier

> ⚠️ **WARNING:** FPANVerifier's SELTZO lemma system is currently being
> redesigned to improve verification performance, causing some temporary
> regressions in the strength of the results that FPANVerifier can prove.
> Please wait until the redesign is complete to obtain precise error bounds
> and non-overlapping guarantees.

**FPANVerifier** is an automatic theorem prover that verifies the correctness
of floating-point algorithms. It uses a novel reasoning technique called the
[SELTZO abstraction][1] to precisely track the propagation of rounding errors
through multiple interdependent operations.

**FPANVerifier** handles a specific class of algorithms called
[**floating-point accumulation networks** (**FPANs**)][2], which are
branch-free sequences of floating-point sum and [TwoSum][3] operations.
These algorithms are used to implement
[high-precision arithmetic with native machine-precision operations][4]
and form the backbone of high-performance libraries like
[MultiFloats.jl][5], [QD][6], [XBLAS][7], and [CAMPARY][8].

**FPANVerifier** is **several *million* times faster** than standard
floating-point verification tools, including [Z3][9], [CVC5][10],
[MathSAT][11], and [Bitwuzla][12]. It solves problems in *seconds* that other
tools need *hours* to *days* to answer, if at all. The bit-precise reasoning
capability of the SELTZO abstraction allows **FPANVerifier** to solve problems
that are impossible for interval-based tools like [COLIBRI][13] and [dReal][14].

|          | Z3       | CVC5       | MathSAT  | Bitwuzla  | Colibri2 | dReal | **FPANVerifier** |
|----------|----------|------------|----------|-----------|----------|-------|------------------|
| Float16  | > 3 days | 2.0 hours  | 2.7 days | 1.2 hours | N/A      | N/A   | **0.7 sec**      |
| BFloat16 | > 3 days | 15.8 hours | > 3 days | 1.7 hours | N/A      | N/A   | **0.7 sec**      |
| Float32  | > 3 days | 17.0 hours | > 3 days | 8.6 hours | N/A      | N/A   | **0.7 sec**      |
| Float64  | > 3 days | > 3 days   | > 3 days | > 3 days  | N/A      | N/A   | **0.9 sec**      |
| Float128 | > 3 days | > 3 days   | > 3 days | > 3 days  | N/A      | N/A   | **1.0 sec**      |

⚠️ **IMPORTANT NOTE:** **FPANVerifier** is a **sound but incomplete** reasoning
tool. This means that every result proven by **FPANVerifier** is definitely
true, but a statement that FPANVerifier fails to prove is not necessarily false.
In some cases, a statement that is true for concrete floating-point numbers
may fail to hold in the SELTZO abstract domain.

[1]: https://arxiv.org/pdf/2505.18791#page=10
[2]: https://link.springer.com/chapter/10.1007/978-3-031-98682-6_12
[3]: https://en.wikipedia.org/wiki/2Sum
[4]: https://en.wikipedia.org/wiki/Quadruple-precision_floating-point_format#Double-double_arithmetic
[5]: https://github.com/dzhang314/MultiFloats.jl
[6]: https://github.com/BL-highprecision/QD
[7]: https://www.netlib.org/xblas/
[8]: https://homepages.laas.fr/mmjoldes/campary/
[9]: https://github.com/Z3Prover/z3
[10]: https://cvc5.github.io/
[11]: https://mathsat.fbk.eu/
[12]: https://bitwuzla.github.io/
[13]: https://colibri.frama-c.com/
[14]: https://dreal.github.io/
