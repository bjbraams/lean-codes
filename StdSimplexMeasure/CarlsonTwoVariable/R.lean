/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonTwoVariable.Basic
import StdSimplexMeasure.CarlsonR

/-! # The two-variable Carlson R-function -/

open Complex Filter
open scoped Classical Topology
public noncomputable section CarlsonTwoVariable
namespace DirichletTransform.TwoVariable

/-- The two-variable integral at a natural exponent agrees with the Carlson polynomial. -/
theorem regRIntegral_natCast (n : ℕ) (b₀ b₁ z₀ z₁ : ℂ)
    (hb : pair b₀ b₁ ∈ mvBetaConvergent) :
    regRIntegral n b₀ b₁ z₀ z₁ = regRPolynomial n b₀ b₁ z₀ z₁ := by
  exact regCarlsonRIntegral_natCast n (pair z₀ z₁) hb

end DirichletTransform.TwoVariable
end CarlsonTwoVariable
