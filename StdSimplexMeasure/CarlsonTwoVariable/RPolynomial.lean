/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonTwoVariable.Basic
import StdSimplexMeasure.CarlsonRPolynomial.Transform

/-! # Two-variable Carlson R-polynomials -/

open Complex
open scoped Classical
public noncomputable section CarlsonTwoVariable
namespace DirichletTransform.TwoVariable

/-- The two-variable Carlson power kernel is homogeneous of degree `n`. -/
theorem carlsonPowerPolynomial_pair_smul (n : ℕ) (a x y : ℂ) :
    carlsonPowerPolynomial n (pair (a * x) (a * y)) =
      MvPolynomial.C (a ^ n) * carlsonPowerPolynomial n (pair x y) := by
  have h : pair (a * x) (a * y) = fun i ↦ a * pair x y i := by
    funext i
    fin_cases i <;> rfl
  rw [h]
  exact carlsonPowerPolynomial_smul n a (pair x y)

end DirichletTransform.TwoVariable
end CarlsonTwoVariable
