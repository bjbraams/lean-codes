/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Algebra.LinearMap.Ordered
public import ToMathlib.Algebra.LinearDependence
public import ToMathlib.Algebra.Submodule.SaturationLocalization

/-!
# General algebra support

Saturation of submodules at arbitrary multiplicative sets and linear dependence in
saturated spans. Declarations extend Mathlib's `Submodule` and `LinearIndependent` APIs.

Ordered-field linear functionals and inclusion of their negative half-spaces are also included.

## Main results

This module re-exports the following developments:

* `ToMathlib.Algebra.LinearMap.Ordered`: Half-space inclusion and proportionality of linear
  functionals.

* `ToMathlib.Algebra.Submodule.Saturation`: Saturation, its closure operator, and saturated
  submodules.
* `ToMathlib.Algebra.Submodule.SaturationLocalization`: Compatibility with localized submodules.
* `ToMathlib.Algebra.LinearDependence`: Dependence in saturated spans when zero is not a
  denominator.

## References

* `ToMathlib.Algebra.LinearDependence`: formal background used by this module.
-/
