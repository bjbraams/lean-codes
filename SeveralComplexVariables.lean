/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.AnalyticUniqueness
public import SeveralComplexVariables.Basic
public import SeveralComplexVariables.CauchyCoefficients
public import SeveralComplexVariables.CauchyDerivatives
public import SeveralComplexVariables.CauchyEstimates
public import SeveralComplexVariables.CauchyIntegral
public import SeveralComplexVariables.CauchyRiemann
public import SeveralComplexVariables.CauchySeries
public import SeveralComplexVariables.ContourIntegral
public import SeveralComplexVariables.Derivatives
public import SeveralComplexVariables.PolynomialDerivatives
public import SeveralComplexVariables.DominatedIntegral
public import SeveralComplexVariables.FunctionSpace
public import SeveralComplexVariables.LocallyBounded
public import SeveralComplexVariables.LocallyUniform
public import SeveralComplexVariables.Montel
public import SeveralComplexVariables.Osgood
public import SeveralComplexVariables.ParametricIntegral
public import SeveralComplexVariables.Polydisc
public import SeveralComplexVariables.PolydiscTaylor
public import SeveralComplexVariables.Reindex

/-!
# Several-complex-variables infrastructure

This umbrella imports finite-dimensional complex analyticity, polydisc Cauchy formulas and
series, locally bounded Osgood, coordinate derivatives and Cauchy–Riemann equations, locally
uniform limits and their derivatives, compact-open holomorphic function spaces, Montel's theorem,
and analytic parameter-dependent integrals. Taylor coefficients, convergence and remainder
estimates allow separate radii in each coordinate.
The modules are independent of the simplex-measure and Carlson developments. See `COVERAGE.md`
for the Mathlib inventory, proved textbook coverage, and remaining work.
-/
