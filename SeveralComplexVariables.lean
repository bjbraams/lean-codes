/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SeveralComplexVariables.Analyticity
public import SeveralComplexVariables.CauchyEstimates
public import SeveralComplexVariables.CauchyIntegral
public import SeveralComplexVariables.CauchySeries
public import SeveralComplexVariables.ContourIntegral
public import SeveralComplexVariables.Derivatives
public import SeveralComplexVariables.DominatedIntegral
public import SeveralComplexVariables.LocallyBounded
public import SeveralComplexVariables.LocallyUniform
public import SeveralComplexVariables.Osgood
public import SeveralComplexVariables.ParametricIntegral
public import SeveralComplexVariables.Polydisc
public import SeveralComplexVariables.PolynomialDerivatives
public import SeveralComplexVariables.RealUniqueness
public import SeveralComplexVariables.Reinhardt
public import SeveralComplexVariables.RemovableSingularity.Cauchy
public import SeveralComplexVariables.SeparateAnalytic
public import SeveralComplexVariables.SeparateAnalytic.Baire
public import SeveralComplexVariables.SeparateAnalytic.FiberExtension
public import SeveralComplexVariables.SeparateAnalytic.HartogsLemma
public import SeveralComplexVariables.SeparateAnalytic.MeanValue

/-!
# Several complex variables (subset)

The modules of the several-complex-variables library that the Carlson and Dirichlet
developments in this repository use: polydisc Cauchy theory and estimates, analyticity of
holomorphic maps, holomorphic parameter integrals, locally uniform limits, Osgood's theorem, and
Hartogs' separate-analyticity theorem. Every file is an exact copy of the corresponding file in
the separate `lean-SCV` project, which is the primary source; do not edit them here.
Single-variable foundations are imported from `ComplexAnalysis` and general support from
`ToMathlib`.

## Main results

This module re-exports the following developments:

* `SeveralComplexVariables.Analyticity`: Analyticity of holomorphic maps in finite dimension.
* `SeveralComplexVariables.CauchyEstimates`: Cauchy estimates and local derivative bounds.
* `SeveralComplexVariables.CauchyIntegral`: Cauchy's integral formula on a polydisc.
* `SeveralComplexVariables.CauchySeries`: Multivariable Cauchy coefficients and series.
* `SeveralComplexVariables.ContourIntegral`: Holomorphic parameters in compact contour integrals.
* `SeveralComplexVariables.Derivatives`: Coordinate derivatives of holomorphic functions.
* `SeveralComplexVariables.DominatedIntegral`: Locally dominated holomorphic integrals.
* `SeveralComplexVariables.LocallyBounded`: Locally bounded separate holomorphy.
* `SeveralComplexVariables.LocallyUniform`: Locally uniform limits of analytic maps in several
  variables.
* `SeveralComplexVariables.Osgood`: Osgood's theorem in finite products.
* `SeveralComplexVariables.ParametricIntegral`: Analytic dependence of integrals on several complex
  parameters.
* `SeveralComplexVariables.Polydisc`: Polydiscs and distinguished boundaries.
* `SeveralComplexVariables.PolynomialDerivatives`: Formal and analytic coordinate derivatives of
  complex polynomials.
* `SeveralComplexVariables.RealUniqueness`: Analytic uniqueness from positive real parameters.
* `SeveralComplexVariables.Reinhardt`: Reinhardt sets.
* `SeveralComplexVariables.RemovableSingularity.Cauchy`: Banach-valued holomorphic circle integrals.
* `SeveralComplexVariables.SeparateAnalytic`: Separate analyticity.
* `SeveralComplexVariables.SeparateAnalytic.Baire`: The Baire step in Hartogs' separate-analyticity
  theorem.
* `SeveralComplexVariables.SeparateAnalytic.FiberExtension`: Hartogs' fiber extension lemma.
* `SeveralComplexVariables.SeparateAnalytic.HartogsLemma`: Hartogs' lemma for powers of holomorphic
  norms.
* `SeveralComplexVariables.SeparateAnalytic.MeanValue`: Ball submean estimates for holomorphic
  norms.
-/
