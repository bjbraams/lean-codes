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
public import Carlson.RPolynomial.PowerSeries
public import Carlson.RPolynomial.TaylorContinuation
public import Carlson.RPolynomial.Differential

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
* `Carlson.RPolynomial.PowerSeries`: Power-series representations using Carlson R-polynomials.
* `Carlson.RPolynomial.TaylorContinuation`: Carlson's continued Taylor representation.
* `Carlson.RPolynomial.Differential`: Differentiation of Carlson's Pochhammer numerators.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/
