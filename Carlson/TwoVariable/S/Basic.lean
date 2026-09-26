/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.Basic
public import Carlson.S.Series

/-!
# Two-variable S definitions

The two-node specializations of the native S-integrals and of the entire regularized S-series.

## Main statements

* `Carlson.TwoVariable.regSIntegral`, `Carlson.TwoVariable.sIntegral`,
  `Carlson.TwoVariable.regSSeries`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The canonical two-variable specialization of the native regularized Carlson S-integral. -/
abbrev regSIntegral (b₀ b₁ z₀ z₁ : ℂ) : ℂ :=
  regCarlsonSIntegral (pair b₀ b₁) (pair z₀ z₁)

/-- The canonical two-variable specialization of the native Carlson S-integral. -/
abbrev sIntegral (b₀ b₁ z₀ z₁ : ℂ) : ℂ :=
  carlsonSIntegral (pair b₀ b₁) (pair z₀ z₁)

/-- The canonical two-variable specialization of Carlson's entire regularized S-series. -/
abbrev regSSeries (b₀ b₁ z₀ z₁ : ℂ) : ℂ :=
  regCarlsonSSeries (pair z₀ z₁) (pair b₀ b₁)

end Carlson.TwoVariable
