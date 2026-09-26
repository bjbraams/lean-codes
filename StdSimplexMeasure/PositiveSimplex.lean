/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.PositiveSimplex.Basic
public import StdSimplexMeasure.PositiveSimplex.SumIntegral
public import StdSimplexMeasure.PositiveSimplex.Aggregation

/-!
# Solid simplex volume and integration

Umbrella module for the solid (positive) simplex `{x | 0 ≤ x i, ∑ i, x i ≤ r}`: its geometry
and volume, integration by coordinate sum, and coordinate aggregation.

## Main results

This module re-exports the following developments:

* `StdSimplexMeasure.PositiveSimplex.Basic`: Solid simplex geometry and volume.
* `StdSimplexMeasure.PositiveSimplex.SumIntegral`: Solid simplex integration by coordinate sum.
* `StdSimplexMeasure.PositiveSimplex.Aggregation`: Aggregation of solid-simplex volume.

## References

* `StdSimplexMeasure.PositiveSimplex.Basic`: formal background used by this module.
* `StdSimplexMeasure.PositiveSimplex.SumIntegral`: formal background used by this module.
* `StdSimplexMeasure.PositiveSimplex.Aggregation`: formal background used by this module.
-/
