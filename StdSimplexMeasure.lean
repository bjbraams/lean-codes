/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.Normalization
public import StdSimplexMeasure.Aggregation
public import StdSimplexMeasure.Coordinates
public import StdSimplexMeasure.CoordinateRealization
public import StdSimplexMeasure.IntrinsicMeasure
public import StdSimplexMeasure.FiniteDimensionalHyperplane
public import StdSimplexMeasure.EuclideanCrossSection
public import StdSimplexMeasure.PiSnoc
public import StdSimplexMeasure.ProdSlices
public import StdSimplexMeasure.PositiveSimplex
public import StdSimplexMeasure.Measure
public import StdSimplexMeasure.Interior
public import StdSimplexMeasure.Integral
public import StdSimplexMeasure.Integral.Interval
public import StdSimplexMeasure.Radial
public import StdSimplexMeasure.SimplexFTC
public import StdSimplexMeasure.Smooth
public import StdSimplexMeasure.MomentDetermination

/-!
# Standard-simplex geometry, measure and integration

Umbrella module for the ambient coordinate description of the standard simplex used by the
Dirichlet and Carlson developments.

* `StdSimplexMeasure.Coordinates`, `Intrinsic`, `CoordinateRealization`, `Normalization`: the
  affine coordinate hyperplane, the coordinate embedding of Mathlib's intrinsic
  `Convexity.StdSimplex`, free-coordinate charts, and normalization by coordinate sum.
* `StdSimplexMeasure.Measure`, `IntrinsicMeasure`: the Lebesgue measure on the sum-one hyperplane
  and its transport to the intrinsic simplex.
* `StdSimplexMeasure.Integral`, `PositiveSimplex`, `ProdSlices`, `PiSnoc`, `SimplexFTC`:
  integration on the simplex and the solid simplex, slicing, monomial integrals, and the simplex
  fundamental theorem of calculus.
* `StdSimplexMeasure.Interior`, `Smooth`, `Aggregation`, `MomentDetermination`: the positive
  interior, smooth simplex functions with tangential derivatives, coordinate aggregation, and
  moment determination of measures on the simplex.
-/
