/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Connected
public import ToMathlib.Analysis.ConvexHullDomain
public import ToMathlib.Analysis.Deriv
public import ToMathlib.Analysis.GeometricBounds
public import ToMathlib.Analysis.Holomorphic.FunctionSpace
public import ToMathlib.Analysis.Holomorphic.NormalFamily
public import ToMathlib.Analysis.Integral.CompactSupport
public import ToMathlib.Analysis.Integral.CurveIntegral
public import ToMathlib.Analysis.Integral.CurveIntegral.Map
public import ToMathlib.Analysis.Integral.CurveIntegral.Improper
public import ToMathlib.Analysis.Integral.CurveIntegral.Bounds
public import ToMathlib.Analysis.Integral.Parametric
public import ToMathlib.Analysis.Integral.Pi
public import ToMathlib.Analysis.Integral.Reciprocal
public import ToMathlib.Analysis.Integral.Tail
public import ToMathlib.Analysis.LinearFunctional
public import ToMathlib.Analysis.OpenMapping
public import ToMathlib.Analysis.SpecialFunctions.Gamma
public import ToMathlib.Analysis.TaylorBounds

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
* `ToMathlib.Analysis.ConvexHullDomain`: Connectedness of convex-hull-admissible configurations.
* `ToMathlib.Analysis.Deriv`: Differentiation along the diagonal.
* `ToMathlib.Analysis.GeometricBounds`: Real root limits and geometric bounds.
* `ToMathlib.Analysis.Holomorphic.FunctionSpace`: Shared spaces of holomorphic maps.
* `ToMathlib.Analysis.Holomorphic.NormalFamily`: Shared Montel and Vitali arguments.
* `ToMathlib.Analysis.Integral.CompactSupport`: Integration helpers for compactly supported
  and weighted functions.
* `ToMathlib.Analysis.Integral.CurveIntegral`: Integrating exact one-forms along curves.
* `ToMathlib.Analysis.Integral.CurveIntegral.Map`: Pullback of one-forms along mapped paths.
* `ToMathlib.Analysis.Integral.CurveIntegral.Improper`: Endpoint formulas for improper
  integrals of exact one-forms.
* `ToMathlib.Analysis.Integral.CurveIntegral.Bounds`: Norm bounds and vanishing criteria for curve
  integrals.
* `ToMathlib.Analysis.Integral.Parametric`: Differentiation of weighted compact integrals.
* `ToMathlib.Analysis.Integral.Pi`: Nonnegative integration on finite product spaces.
* `ToMathlib.Analysis.Integral.Reciprocal`: Compactifying a positive half-line by inversion.
* `ToMathlib.Analysis.Integral.Tail`: Uniform control of integral tails.
* `ToMathlib.Analysis.LinearFunctional`: Elementary facts on scalar actions and continuous linear
  functionals.
* `ToMathlib.Analysis.OpenMapping`: Open mapping for complete metrizable real or complex
  vector spaces.
* `ToMathlib.Analysis.SpecialFunctions.Gamma`: The Gamma integral with a complex Laplace parameter.
* `ToMathlib.Analysis.TaylorBounds`: Elementary bounds for Taylor remainders.

## References

* `ToMathlib.Analysis.Connected`: formal background used by this module.
* `ToMathlib.Analysis.ConvexHullDomain`: formal background used by this module.
* `ToMathlib.Analysis.Deriv`: formal background used by this module.
-/
