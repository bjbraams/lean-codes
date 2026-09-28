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
public import Carlson.TwoVariable.SEqualParameter
public import Carlson.TwoVariable.FractionalIntegral
public import Carlson.TwoVariable.EqualParameter
public import Carlson.TwoVariable.LQuadratic
public import Carlson.TwoVariable.EqualParameterSlit
public import Carlson.TwoVariable.ConfluentHypergeometric
public import Carlson.TwoVariable.Borchardt

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

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
* [Carl87] B. C. Carlson, *Dirichlet averages of `x^t log x`*, SIAM J. Math. Anal. 18 (1987).
-/
