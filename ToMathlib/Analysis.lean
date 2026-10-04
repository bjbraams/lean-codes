/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Analytic.PolynomialApproximation
public import ToMathlib.Analysis.Connected
public import ToMathlib.Analysis.Calculus.MeanWeights
public import ToMathlib.Analysis.Convex.GeometricMean
public import ToMathlib.Analysis.Convex.LogReciprocal
public import ToMathlib.Analysis.Convex.NegativePower
public import ToMathlib.Analysis.Convex.NormalizedAddition
public import ToMathlib.Analysis.ConvexHullDomain
public import ToMathlib.Analysis.Holomorphic.FunctionSpace
public import ToMathlib.Analysis.Holomorphic.LocallyUniformLimit
public import ToMathlib.Analysis.Holomorphic.NormalFamily
public import ToMathlib.Analysis.Holomorphic.PolynomialApproximation
public import ToMathlib.Analysis.Integral.CauchyBoundary
public import ToMathlib.Analysis.Integral.CompactSupport
public import ToMathlib.Analysis.Integral.CurveIntegral
public import ToMathlib.Analysis.Integral.CurveIntegral.Map
public import ToMathlib.Analysis.Integral.CurveIntegral.Improper
public import ToMathlib.Analysis.Integral.CurveIntegral.Bounds
public import ToMathlib.Analysis.Integral.Laplace
public import ToMathlib.Analysis.Integral.Parametric
public import ToMathlib.Analysis.Integral.Pi
public import ToMathlib.Analysis.Integral.ProdAbsRPow
public import ToMathlib.Analysis.Integral.Reciprocal
public import ToMathlib.Analysis.Integral.Tail
public import ToMathlib.Analysis.Integral.StrictMono
public import ToMathlib.Analysis.Integral.TwoCrossings
public import ToMathlib.Analysis.OpenMapping
public import ToMathlib.Analysis.SpecialFunctions.Bessel
public import ToMathlib.Analysis.SpecialFunctions.BetaDensity
public import ToMathlib.Analysis.SpecialFunctions.BetaKernel
public import ToMathlib.Analysis.SpecialFunctions.BetaConcentration
public import ToMathlib.Analysis.SpecialFunctions.Pochhammer
public import ToMathlib.Analysis.SpecialFunctions.Gamma
public import ToMathlib.Analysis.SpecialFunctions.GammaRatio
public import ToMathlib.Analysis.TaylorBounds
public import ToMathlib.Analysis.UpperHalfPlaneMaximum

/-!
# General analysis support

Normed-space geometry, continuous linear maps, diagonal differentiation, real Taylor and
geometric estimates, Banach-valued and finite-product nonnegative integration, and the
complex-rate Gamma/Laplace integral. Curve integration includes pullback of one-forms,
finite-interval parametrizations, improper endpoint formulas, and limits of finite
path integrals. Reciprocal substitution compactifies positive half-lines and preserves
integrability with its Jacobian. Operator-norm and speed bounds control curve integrals;
common integrable majorants give uniformly vanishing tails. Power-decay estimates give
explicit rates for tails and growing connecting paths. Declarations use the namespaces of their
underlying Mathlib APIs. This library depends only on Mathlib.

## Main results

This module re-exports the following developments:

* `ToMathlib.Analysis.Connected`: Connectedness of shells and exteriors of balls.
* `ToMathlib.Analysis.Convex.GeometricMean`: Strict finite Hölder for geometric interpolation.
* `ToMathlib.Analysis.Convex.LogReciprocal`: Strict decrease and log-convexity of positive
  constants plus shifted reciprocals.
* `ToMathlib.Analysis.Convex.NormalizedAddition`: Strict convexity and concavity under
  normalization by positive homogeneous quantities.
* `ToMathlib.Analysis.ConvexHullDomain`: Connectedness of convex-hull-admissible configurations.
* `ToMathlib.Analysis.Analytic.PolynomialApproximation`: Explicit polynomial partial sums
  and locally uniform convergence over a nontrivially normed field.
* `ToMathlib.Analysis.Holomorphic.FunctionSpace`: Bundled holomorphic maps with evaluation,
  restriction, and the compact-open topology.
* `ToMathlib.Analysis.Holomorphic.LocallyUniformLimit`: Closedness and completeness of
  holomorphic-map spaces on open subsets of the complex plane.
* `ToMathlib.Analysis.Holomorphic.PolynomialApproximation`: Polynomial approximation
  of holomorphic functions on disks and entire functions on the plane.
* `ToMathlib.Analysis.Holomorphic.NormalFamily`: Montel and Vitali theorems on the complex
  plane, and conditional versions for general finite-dimensional sources.
* `ToMathlib.Analysis.Integral.CauchyBoundary`: Segment Plemelj formulas, separate
  vertical boundary limits and symmetric-truncation principal values.
* `ToMathlib.Analysis.Integral.CompactSupport`: Integration helpers for compactly supported
  and weighted functions.
* `ToMathlib.Analysis.Integral.CurveIntegral`: Integrating exact one-forms along curves.
* `ToMathlib.Analysis.Integral.CurveIntegral.Map`: Pullback of one-forms along mapped paths.
* `ToMathlib.Analysis.Integral.CurveIntegral.Improper`: Endpoint formulas for improper
  integrals of exact one-forms.
* `ToMathlib.Analysis.Integral.CurveIntegral.Bounds`: Norm bounds and vanishing criteria for curve
  integrals.
* `ToMathlib.Analysis.Integral.Laplace`: Quantitative complex-phase Laplace asymptotics,
  explicit Gaussian error bounds and uniform finite-interval limits.
* `ToMathlib.Analysis.Integral.Parametric`: Differentiation of weighted compact integrals.
* `ToMathlib.Analysis.Integral.Pi`: Nonnegative integration on finite product spaces.
* `ToMathlib.Analysis.Integral.ProdAbsRPow`: Integrability of products of powers with distinct
  real singularities.
* `ToMathlib.Analysis.Integral.Reciprocal`: Compactifying a positive half-line by inversion.
* `ToMathlib.Analysis.Integral.TwoCrossings`: Strict convex integral comparison for signed
  kernels with two crossings and vanishing zeroth and first moments.
* `ToMathlib.Analysis.Integral.Tail`: Uniform control of integral tails.
* `ToMathlib.Analysis.OpenMapping`: Open mapping for complete metrizable real or complex
  vector spaces.
* `ToMathlib.Analysis.SpecialFunctions.BetaDensity`, `BetaKernel`, `BetaConcentration`:
  Real beta density moments, unimodality of positive-power beta kernels, and strict
  decrease of convex beta averages under increasing concentration.
* `ToMathlib.Analysis.SpecialFunctions.Pochhammer`: Decrease and log-convexity of
  Pochhammer concentration ratios, strict from natural order two onward.
* `ToMathlib.Analysis.SpecialFunctions.Bessel`: Series and bounds for Bessel functions of
  integer order.
* `ToMathlib.Analysis.SpecialFunctions.GammaRatio`: The bound `Γ(x)/|Γ(x + iy)| ≤ √(cosh (π y))`
  for `x ≥ 1/2`.
* `ToMathlib.Analysis.SpecialFunctions.Gamma`: The Gamma integral with a complex Laplace parameter.
* `ToMathlib.Analysis.TaylorBounds`: Elementary bounds for Taylor remainders.
* `ToMathlib.Analysis.UpperHalfPlaneMaximum`: A minimum principle for the imaginary part on the
  upper half-plane.

## References

* `ToMathlib.Analysis.Connected`: formal background used by this module.
* `ToMathlib.Analysis.ConvexHullDomain`: formal background used by this module.
-/
