/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.BranchLog
public import ComplexAnalysis.BranchLog.Analytic
public import ComplexAnalysis.CauchyDerivatives
public import ComplexAnalysis.CauchyEstimates
public import ComplexAnalysis.CauchyFormula
public import ComplexAnalysis.CauchyIntegral
public import ComplexAnalysis.CauchySeries
public import ComplexAnalysis.CurveIndex
public import ComplexAnalysis.CurveIndex.Continuity
public import ComplexAnalysis.Cycle
public import ComplexAnalysis.Cycle.Cauchy
public import ComplexAnalysis.ExteriorPath
public import ComplexAnalysis.HalfPlane
public import ComplexAnalysis.HasPrimitives
public import ComplexAnalysis.HolomorphicIntegral
public import ComplexAnalysis.Integral.CirclePath
public import ComplexAnalysis.LogDerivIntegral
public import ComplexAnalysis.ParametricIntegral
public import ComplexAnalysis.Pow
public import ComplexAnalysis.RealUniqueness
public import ComplexAnalysis.Subharmonic.Submean

/-!
# Single-variable complex analysis (subset)

The modules of the one-variable complex analysis library that the Carlson and Dirichlet
developments in this repository use, directly or through the several-variable modules. Every
file is an exact copy of the corresponding file in the separate `lean-CA` project, which is the
primary source; do not edit them here. General analysis and topology support is imported from
`ToMathlib`.

## Main results

This module re-exports the following developments:

* `ComplexAnalysis.BranchLog`: Holomorphic logarithm branches.
* `ComplexAnalysis.BranchLog.Analytic`: Analytic dependence of logarithm branches.
* `ComplexAnalysis.CauchyDerivatives`: Cauchy's derivative formula at an arbitrary point of a disk.
* `ComplexAnalysis.CauchyEstimates`: Derivative and Taylor-coefficient bounds.
* `ComplexAnalysis.CauchyFormula`: Cauchy's formula along closed curves in simply connected domains.
* `ComplexAnalysis.CauchyIntegral`: Complex curve integrals and primitives.
* `ComplexAnalysis.CauchySeries`: Bounds and convergence of one-variable Cauchy power series.
* `ComplexAnalysis.CurveIndex`: The analytic index of a closed complex curve.
* `ComplexAnalysis.CurveIndex.Continuity`: Dependence of the curve index on the pole.
* `ComplexAnalysis.Cycle`: Cycles in the complex plane.
* `ComplexAnalysis.Cycle.Cauchy`: The homology form of Cauchy's theorem.
* `ComplexAnalysis.ExteriorPath`: Compactified paths to infinity.
* `ComplexAnalysis.HalfPlane`: Geometry of the right half-plane.
* `ComplexAnalysis.HasPrimitives`: Primitives on simply connected open domains.
* `ComplexAnalysis.HolomorphicIntegral`: Holomorphic dependence of interval integrals on a complex
  parameter.
* `ComplexAnalysis.Integral.CirclePath`: Circles as paths.
* `ComplexAnalysis.LogDerivIntegral`: Integrals of logarithmic derivatives along curves.
* `ComplexAnalysis.ParametricIntegral`: Differentiation of compact integrals in one complex
  parameter.
* `ComplexAnalysis.Pow`: Principal powers on the right half-plane.
* `ComplexAnalysis.RealUniqueness`: Uniqueness of holomorphic functions from real parameters.
* `ComplexAnalysis.Subharmonic.Submean`: Submean estimates for positive powers of holomorphic norms.
-/
