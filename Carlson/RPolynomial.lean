/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.Basic
public import Carlson.RPolynomial.Coefficients
public import Carlson.RPolynomial.Estimates
public import Carlson.RPolynomial.SharpEstimates
public import Carlson.RPolynomial.Binomial
public import Carlson.RPolynomial.Transform
public import Carlson.RPolynomial.Generating
public import Carlson.RPolynomial.Concentration
public import Carlson.RPolynomial.Growth
public import Carlson.RPolynomial.PowerSeries
public import Carlson.RPolynomial.TaylorContinuation
public import Carlson.RPolynomial.Differential
public import Carlson.RPolynomial.Appell
public import Carlson.RPolynomial.NumeratorBinomial
public import Carlson.RPolynomial.GeneratingIdentities
public import Carlson.RPolynomial.RootsOfUnity
public import Carlson.RPolynomial.SmallParameters
public import Carlson.RPolynomial.EqualParameterBounds
public import Carlson.RPolynomial.PolygonSpecial
public import Carlson.RPolynomial.NearDiagonal

/-!
# Carlson's R-polynomials

Umbrella import for the algebraic, transformation, and generating-function theory.

## Main results

This module re-exports the following developments:

* `Carlson.RPolynomial.Basic`: Carlson's R-polynomials.
* `Carlson.RPolynomial.Coefficients`: Coefficients of Carlson's R-polynomials.
* `Carlson.RPolynomial.Estimates`: Estimates for Carlson's R-polynomials.
* `Carlson.RPolynomial.SharpEstimates`: Sharp bounds for Carlson polynomials.
* `Carlson.RPolynomial.Binomial`: The binomial theorem for Carlson's R-polynomials.
* `Carlson.RPolynomial.Transform`: Linear transformations of Carlson's R-polynomials.
* `Carlson.RPolynomial.Generating`: Generating functions of Carlson's R-polynomials.
* `Carlson.RPolynomial.Growth`: Exponential growth of Carlson's R-polynomials.
* `Carlson.RPolynomial.PowerSeries`: Power-series representations using Carlson R-polynomials.
* `Carlson.RPolynomial.TaylorContinuation`: Carlson's continued Taylor representation.
* `Carlson.RPolynomial.Differential`: Differentiation of Carlson's Pochhammer numerators.
* `Carlson.RPolynomial.NumeratorBinomial`: the binomial theorem for Pochhammer numerators.
* `Carlson.RPolynomial.GeneratingIdentities`: Chapter 6 exercises from the generating relation.
* `Carlson.RPolynomial.RootsOfUnity`: roots of unity as nodes and regular polygons.
* `Carlson.RPolynomial.SmallParameters`: small parameters (Exercises 6.2-6, 6.2-8, 6.3-4).
* `Carlson.RPolynomial.Appell`: R-polynomials as sequences satisfying a binomial theorem
  (Theorem 6.4-1, (6.4-4)).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/
