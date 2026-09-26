/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.L.Basic
public import Carlson.L.Continuation
public import Carlson.L.Relations
public import Carlson.L.Properties
public import Carlson.L.Deriv
public import Carlson.L.Series
public import Carlson.L.Associated
public import Carlson.L.SlitIntegral
public import Carlson.L.SlitRelations
public import Carlson.L.SlitDeriv
public import Carlson.L.EulerPoisson
public import Carlson.L.JointRecurrence

/-!
# Carlson's Dirichlet averages of the power-logarithm kernel

`regCarlsonL`, the exponent derivative of `regCarlsonR`, is jointly holomorphic in all
complex exponents and Dirichlet parameters and all slit-plane nodes, and agrees with the
native power-logarithm Dirichlet average on its convergence domain. See
`CarlsonLCoverage.md` for the paper correspondence.

## Main results

This module re-exports the following developments:

* `Carlson.L.Basic`: Carlson's L-function: native integrals.
* `Carlson.L.Continuation`: Carlson's L-function.
* `Carlson.L.Relations`: Associated relations for Carlson's L-function.
* `Carlson.L.Properties`: Symmetry, aggregation, and scaling of Carlson's L-function.
* `Carlson.L.Deriv`: Node derivatives and the Euler–Poisson system for L.
* `Carlson.L.Series`: R-polynomial expansions of Carlson's L-function.
* `Carlson.L.Associated`: Further associated and differential identities for L.
* `Carlson.L.SlitIntegral`: Native power-logarithm averages on the slit plane.
* `Carlson.L.SlitRelations`: Associated relations for L on the full product slit plane.
* `Carlson.L.SlitDeriv`: Node derivatives and translations on the slit domain.
* `Carlson.L.EulerPoisson`: The full Euler–Poisson system for Carlson's L-function.
* `Carlson.L.JointRecurrence`: Associated L-relations with polynomial correction coefficients.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/
