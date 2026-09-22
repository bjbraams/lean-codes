/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.Basic
public import Carlson.R.Basic

/-!
# Two-variable R definitions

The two-node specializations of the native regularized and ordinary Carlson R-integrals.

## Main definitions

* `Carlson.TwoVariable.regRIntegral`, `Carlson.TwoVariable.rIntegral`: the R-integrals with
  parameters `b₀, b₁` and nodes `z₀, z₁`.
-/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- The canonical two-variable specialization of the native regularized Carlson R-integral. -/
abbrev regRIntegral (t b₀ b₁ z₀ z₁ : ℂ) : ℂ :=
  regCarlsonRIntegral t (pair b₀ b₁) (pair z₀ z₁)

/-- The canonical two-variable specialization of the native Carlson R-integral. -/
abbrev rIntegral (t b₀ b₁ z₀ z₁ : ℂ) : ℂ :=
  carlsonRIntegral t (pair b₀ b₁) (pair z₀ z₁)

end Carlson.TwoVariable
