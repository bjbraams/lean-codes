/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Beta.Real
public import Dirichlet.Beta.Complex
public import Dirichlet.Integral.Real
public import Dirichlet.Integral.Complex
public import Dirichlet.Real
public import Dirichlet.Complex
public import Dirichlet.ParameterShift
public import Dirichlet.Complex.Analytic
public import Dirichlet.Bridge
public import Dirichlet.Moments
public import Dirichlet.Gamma
public import Dirichlet.Polynomial
public import Dirichlet.IntegrationByParts
public import Dirichlet.Transform
public import Dirichlet.Transform.Aggregation
public import Dirichlet.Transform.Basic
public import Dirichlet.Transform.Joint
public import Dirichlet.Transform.Euler
public import Dirichlet.Transform.Laws
public import Dirichlet.Transform.Series
public import Dirichlet.Average

/-!
# Dirichlet measures, averages and transforms

Umbrella module for the Dirichlet theory underlying Carlson's special functions.

* `Dirichlet.Beta`: the real and complex multivariate beta functions and their simplex integral
  evaluations.
* `Dirichlet.Integral`, `Dirichlet.Real`, `Dirichlet.Complex`, `Dirichlet.Bridge`: real Dirichlet
  monomial integrals and the Dirichlet probability distribution; regularized complex Dirichlet
  densities and integrals; compatibility between the two.
* `Dirichlet.Moments`, `Dirichlet.ParameterShift`, `Dirichlet.Polynomial`,
  `Dirichlet.IntegrationByParts`, `Dirichlet.Gamma`: moments, unit parameter shifts, polynomial
  transforms, integration by parts, and the Gamma-variable construction of the distribution.
* `Dirichlet.Transform`: the entire regularized Dirichlet transform of a smooth simplex kernel,
  with its structural laws, aggregation, Euler integrals, series, and auxiliary holomorphic
  parameters.
* `Dirichlet.Average`: Carlson's Dirichlet averages of a univariate function, their derivatives
  and relations, and their analytic continuation in parameters and nodes.

The real distribution lives in the `ProbabilityTheory` namespace; the complex densities,
transforms and averages live in the `Dirichlet` namespace.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/
