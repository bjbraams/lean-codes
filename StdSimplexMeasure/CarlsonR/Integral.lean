/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

import StdSimplexMeasure.CarlsonR.Basic
import StdSimplexMeasure.CarlsonRPolynomial.Basic
import StdSimplexMeasure.CarlsonDirichletAverage.Continuation

/-! # Carlson's R-function: native integral representation -/

open Complex ProbabilityTheory
open scoped Classical
public noncomputable section CarlsonR
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- For a natural exponent, the general-power integral is the polynomial Carlson average. -/
theorem regCarlsonRIntegral_natCast (n : ℕ) (z : ι → ℂ)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonRIntegral (n : ℂ) b z = regCarlsonR n z b := by
  rw [regCarlsonRIntegral, ← regCarlsonDirichletAverage_pow n z hb]
  congr 2
  funext w
  exact cpow_natCast w n

end DirichletTransform
end CarlsonR
