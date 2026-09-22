/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Analysis.Connected
public import Analysis.ConvexHullDomain
public import Analysis.Deriv
public import Analysis.GeometricBounds
public import Analysis.Holomorphic.FunctionSpace
public import Analysis.Holomorphic.NormalFamily
public import Analysis.Integral.CompactSupport
public import Analysis.Integral.CurveIntegral
public import Analysis.Integral.CurveIntegral.Map
public import Analysis.Integral.CurveIntegral.Improper
public import Analysis.Integral.CurveIntegral.Bounds
public import Analysis.Integral.Parametric
public import Analysis.Integral.Pi
public import Analysis.Integral.Reciprocal
public import Analysis.Integral.Tail
public import Analysis.LinearFunctional
public import Analysis.OpenMapping
public import Analysis.SpecialFunctions.Gamma
public import Analysis.TaylorBounds

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
underlying
Mathlib APIs. This library depends only on Mathlib.
-/
