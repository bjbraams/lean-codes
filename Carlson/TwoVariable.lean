/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.Basic
public import Carlson.TwoVariable.RPolynomial
public import Carlson.TwoVariable.R
public import Carlson.TwoVariable.L
public import Carlson.TwoVariable.Associated
public import Carlson.TwoVariable.Inversion
public import Carlson.TwoVariable.S
public import Carlson.TwoVariable.T
public import Carlson.TwoVariable.Quadratic
public import Carlson.TwoVariable.QuadraticContinuation
public import Carlson.TwoVariable.QuadraticSlit
public import Carlson.TwoVariable.QuadraticHybrid
public import Carlson.TwoVariable.BilateralGenerating
public import Carlson.TwoVariable.BilateralContinuation
public import Carlson.TwoVariable.SEqualParameter
public import Carlson.TwoVariable.FractionalIntegral
public import Carlson.TwoVariable.FractionalContinuation
public import Carlson.TwoVariable.RPolynomial.Hypergeometric
public import Carlson.TwoVariable.RPolynomial.EqualParameter
public import Carlson.TwoVariable.RPolynomial.SpecialValues
public import Carlson.TwoVariable.RPolynomial.QuadraticGenerating
public import Carlson.TwoVariable.RPolynomial.BetaIntegral
public import Carlson.TwoVariable.SHypergeometric
public import Carlson.TwoVariable.QuadraticGauss
public import Carlson.TwoVariable.R.ElementaryValues
public import Carlson.TwoVariable.LQuadratic
public import Carlson.TwoVariable.EqualParameterSlit
public import Carlson.TwoVariable.ConfluentHypergeometric
public import Carlson.TwoVariable.Borchardt
public import Carlson.TwoVariable.RCAsymptotic
public import Carlson.TwoVariable.GaussHypergeometric
public import Carlson.TwoVariable.Reduction
public import Carlson.TwoVariable.R.Elementary

/-!
# Two-variable Carlson functions and polynomials

Umbrella module for the two-node specializations of Carlson's functions: the R-polynomials
and R-, L-, S- and T-functions on the index type `Fin 2`, their associated and inversion
identities, the quadratic transformations 6.9-3 and 6.10-1, the equal-parameter family, and
parameter symmetries. The S-function is identified with Mathlib's confluent hypergeometric and
Bessel functions.

## Main results

* `Carlson.TwoVariable.regularizedHGFun_kummer_second`: Kummer's second formula (6.9-6).
* `Carlson.TwoVariable.quadraticGammaRatio_mul_besselJ`: Bessel functions as S-functions (6.9-18).
* `Carlson.TwoVariable.exists_borchardtSigma_expansion`: the accelerated Borchardt algorithm
  (6.10-28).
* `Carlson.TwoVariable.regCarlsonR_pair_one_one_log`: `(x - y) R_{-1}(1, 1; x, y) = log x - log y`
  (Exercise 5.9-13).
* `Carlson.TwoVariable.exists_fractionalIntegral_continuation`,
  `Carlson.TwoVariable.exists_real_fractionalIntegral_continuation`: the fractional integral
  continued in its order, with `I^{-n} f = f⁽ⁿ⁾` (5.5-16).
* `Carlson.hasSum_gaussCoeff`, `Carlson.ordinaryHypergeometric_one`: Gauss's theorem (8.3-4).
* `Carlson.TwoVariable.eventually_hasSum_quadratic_generating`: the expansion of
  `(at² + 2bt + c)^(-ν)` (Exercises 6.6-4 and 6.10-6).
* `Carlson.TwoVariable.isBigO_carlsonRC_sub_diagonal`,
  `Carlson.TwoVariable.tendsto_carlsonRC_sub_log`: asymptotics of `R_C` (Exercise 6.9-18).

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
* [Carl87] B. C. Carlson, *Dirichlet averages of `x^t log x`*, SIAM J. Math. Anal. 18 (1987).
-/
