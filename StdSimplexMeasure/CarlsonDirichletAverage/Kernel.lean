/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# The affine kernel for Carlson's Dirichlet averages

This file contains the common algebraic kernel used by both the real probability average and
the complex regularized integral.
-/

open Complex
open scoped Classical

@[expose] public noncomputable section CarlsonDirichletKernel

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- The affine form on the standard simplex associated with the complex parameters `z`. -/
def carlsonAffineForm (z : ι → ℂ) (u : ι → ℝ) : ℂ :=
  ∑ i, (u i : ℂ) * z i

/-- The affine form associated with `z` is continuous in the simplex variable. -/
theorem continuous_carlsonAffineForm (z : ι → ℂ) :
    Continuous (carlsonAffineForm z) := by
  unfold carlsonAffineForm
  fun_prop

end DirichletTransform

end CarlsonDirichletKernel
