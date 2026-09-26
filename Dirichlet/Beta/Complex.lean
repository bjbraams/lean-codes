/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Beta.Complex.Basic
public import Dirichlet.Beta.Complex.Integral

/-!
# Complex multivariate beta: algebra and integral evaluation

Umbrella module for the complex multivariate beta function `Complex.mvBeta`: its Gamma-quotient
definition, parameter identities and convergence domain (`Dirichlet.Beta.Complex.Basic`), and
its evaluation as a solid-simplex integral (`Dirichlet.Beta.Complex.Integral`).

## Main results

This module re-exports the following developments:

* `Dirichlet.Beta.Complex.Basic`: The complex multivariate beta function.
* `Dirichlet.Beta.Complex.Integral`: Solid-simplex integral evaluation of multivariate beta.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977
  (Dirichlet averages).
* NIST Digital Library of Mathematical Functions, §5.14, *Multidimensional Integrals*,
  https://dlmf.nist.gov/5.14.
-/
