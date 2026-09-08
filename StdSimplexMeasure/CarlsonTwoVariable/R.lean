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

/-- Simultaneously exchanging the two parameters and variables leaves the native
regularized two-variable R-integral unchanged. -/
theorem regRIntegral_swap (t b₀ b₁ z₀ z₁ : ℂ) :
    regRIntegral t b₁ b₀ z₁ z₀ = regRIntegral t b₀ b₁ z₀ z₁ := by
  have h := regCarlsonDirichletAverage_perm (pair b₀ b₁) (pair z₀ z₁)
    (fun w => w ^ t) (Equiv.swap 0 1)
  rw [show pair b₀ b₁ ∘ Equiv.swap 0 1 = pair b₁ b₀ by
      funext i; fin_cases i <;> rfl,
    show pair z₀ z₁ ∘ Equiv.swap 0 1 = pair z₁ z₀ by
      funext i; fin_cases i <;> rfl] at h
  exact h

/-- Positive-real homogeneity of the native regularized two-variable R-integral. -/
theorem regRIntegral_smul_of_pos (t b₀ b₁ x y : ℂ) {a : ℝ} (ha : 0 < a)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    regRIntegral t b₀ b₁ ((a : ℂ) * x) ((a : ℂ) * y) =
      (a : ℂ) ^ t * regRIntegral t b₀ b₁ x y := by
  change regCarlsonRIntegral t (pair b₀ b₁)
      (pair ((a : ℂ) * x) ((a : ℂ) * y)) = _
  rw [show pair ((a : ℂ) * x) ((a : ℂ) * y) =
      fun i => (a : ℂ) * pair x y i by funext i; fin_cases i <;> rfl]
  exact DirichletTransform.regCarlsonRIntegral_smul_of_pos t hz ha

end DirichletTransform.TwoVariable
end CarlsonTwoVariable
