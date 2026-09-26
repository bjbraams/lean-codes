/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import StdSimplexMeasure.Integral.Basic
public import StdSimplexMeasure.Integral.Slicing
public import StdSimplexMeasure.Integral.Monomial
public import StdSimplexMeasure.Integral.Aggregation

/-!
# Standard-simplex integration

Basic integration, slicing, monomial formulas, and aggregation have separate modules.

## Main results

This module re-exports the following developments:

* `StdSimplexMeasure.Integral.Basic`: Basic integration with the affine-hyperplane coordinate
  measure.
* `StdSimplexMeasure.Integral.Slicing`: Slicing and scaling standard-simplex integrals.
* `StdSimplexMeasure.Integral.Monomial`: Monomial and polynomial integrals on the standard
  simplex.
* `StdSimplexMeasure.Integral.Aggregation`: Coordinate aggregation in standard-simplex
  integrals.

## References

* `StdSimplexMeasure.Integral.Basic`: formal background used by this module.
* `StdSimplexMeasure.Integral.Slicing`: formal background used by this module.
* `StdSimplexMeasure.Integral.Monomial`: formal background used by this module.
-/
