/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonRPolynomial.Coefficients
/-! # Estimates for Carlson's R-polynomials

Home for the Section 6.2 bounds used in normally convergent series.
-/

open Complex ProbabilityTheory
open scoped Classical
public noncomputable section CarlsonRPolynomial
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The power kernel represented by `carlsonPowerPolynomial` is uniformly bounded on the
standard simplex by the corresponding power of the sum of the variable norms. -/
theorem norm_eval_carlsonPowerPolynomial_le (n : ℕ) (z : ι → ℂ) {u : ι → ℝ}
    (hu : u ∈ stdSimplex ℝ ι) :
    ‖(carlsonPowerPolynomial n z).eval (fun i ↦ (u i : ℂ))‖ ≤
      (∑ i, ‖z i‖) ^ n := by
  rw [eval_carlsonPowerPolynomial, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_carlsonAffineForm_le_sum_norm z hu) n

end DirichletTransform
end CarlsonRPolynomial
