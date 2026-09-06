/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonRPolynomial.Basic

/-!
# Linear transformations of Carlson's R-polynomials

This file contains the algebraic infrastructure for [Carl77, Section 6.5].
-/

open Complex
open scoped Classical
public noncomputable section CarlsonRPolynomial
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Scaling all Carlson variables scales their degree-`n` polynomial kernel by `a ^ n`. -/
theorem eval_carlsonPowerPolynomial_smul (n : ℕ) (a : ℂ) (z x : ι → ℂ) :
    (carlsonPowerPolynomial n (fun i ↦ a * z i)).eval x =
      a ^ n * (carlsonPowerPolynomial n z).eval x := by
  rw [carlsonPowerPolynomial_smul]
  simp

/- Carlson's parameter-changing transformation (6.5-3) will be stated here after the
Pochhammer reflection identity needed for its prefactor has been isolated in `MvBeta`. -/

end DirichletTransform
end CarlsonRPolynomial
