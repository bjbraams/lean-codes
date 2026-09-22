/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial
public import Carlson.R
public import Carlson.L
public import Carlson.S
public import Carlson.T
public import Carlson.TwoVariable
public import Carlson.Aggregation
public import Carlson.ZeroParameter

/-!
# Carlson special functions

Umbrella module for Carlson's theory of special functions defined through Dirichlet averages:
the R-polynomials, the R-, L-, S- and T-functions, their analytic continuations, and the
two-variable specializations. The Dirichlet-average foundation is imported from `Dirichlet`.

* `Carlson.RPolynomial`: the polynomial averages `Rₙ(b, z)` and their estimates.
* `Carlson.R`: the R-function with arbitrary complex exponent, its single-integral
  representation, continuation in the parameters and in the slit-plane nodes, recurrences and
  the Euler–Poisson system.
* `Carlson.L`: the exponent derivative of R, Carlson's 1987 L-function.
* `Carlson.S`, `Carlson.T`: the confluent exponential and exponential-of-reciprocal averages.
* `Carlson.TwoVariable`: two-node specializations, quadratic transformations and inversion.
* `Carlson.Aggregation`, `Carlson.ZeroParameter`: coarsening of nodes and vanishing parameters.

All functions are stated for a finite index type `ι`, which may be empty.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
* [Carl87] B. C. Carlson, *Dirichlet averages of `x^t log x`*, SIAM J. Math. Anal. 18 (1987).
-/
