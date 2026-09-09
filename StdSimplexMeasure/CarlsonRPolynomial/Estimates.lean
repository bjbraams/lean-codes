/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonRPolynomial.Coefficients
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
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

/-- On every compact set of Dirichlet parameters, the exponential generating terms of the
regularized Carlson R-polynomials admit a common summable majorant.  This is the compact-local
estimate underlying Carlson's entire continuation of the S-function in its parameters. -/
theorem exists_summable_norm_regCarlsonR_div_factorial_on_compact_parameters
    (z : ι → ℂ) {K : Set (ι → ℂ)} (hK : IsCompact K) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ n b, b ∈ K →
      ‖(Nat.factorial n : ℂ)⁻¹ * regCarlsonR n z b‖ ≤ M n := by
  /- By `regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma`, the required estimate reduces
  to a compact-uniform bound for products of ascending Pochhammer symbols divided by
  `Gamma ((∑ i, b i) + n)`.  A polynomial factor in `n`, times
  `(1 + ∑ i, ‖z i‖) ^ n / n!`, is sufficient.  Mathlib currently has pointwise Gamma
  asymptotics but no ready compact-uniform Gamma-ratio estimate, so that analytic estimate is
  isolated here rather than hidden in the S-function proof. -/
  sorry

end DirichletTransform
end CarlsonRPolynomial
