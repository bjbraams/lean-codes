/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonRPolynomial.Estimates
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Generating functions of Carlson's R-polynomials

This file develops [Carl77, Section 6.6].  The scalar geometric kernel is recorded separately
from the subsequent coefficient and convergence argument.
-/

open Complex Filter
open scoped Classical Topology
public noncomputable section CarlsonRPolynomial
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The scalar kernels used in Carlson's generating relation converge to the exponential
kernel under confluence. -/
theorem tendsto_carlsonGeneratingKernel (w : ℂ) :
    Tendsto (fun n : ℕ ↦ (1 + w / n) ^ n) atTop (𝓝 (exp w)) :=
  Complex.tendsto_one_add_div_pow_exp w

/-- The scalar binomial series used in each factor of Carlson's generating relation 6.6-1,
written with ascending Pochhammer coefficients. -/
theorem hasSum_ascPochhammer_mul_pow_div_factorial (a t : ℂ) (ht : ‖t‖ < 1) :
    HasSum (fun n : ℕ ↦
      (ascPochhammer ℂ n).eval a / (n.factorial : ℂ) * t ^ n)
      (1 / (1 - t) ^ a) := by
  have h := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero a).hasSum
    (show t ∈ Metric.eball (0 : ℂ) 1 by
      simp only [Metric.mem_eball, edist_zero_right]
      rw [enorm_eq_nnnorm]
      exact_mod_cast ht)
  have hmulti : HasSum (fun n : ℕ ↦ Ring.multichoose a n * t ^ n)
      (1 / (1 - t) ^ a) := by
    simpa [FormalMultilinearSeries.ofScalars, Ring.multichoose_eq] using h
  convert hmulti using 1 with n
  funext n
  congr 1
  symm
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n)).2
  rw [mul_comm]
  simpa [Polynomial.ascPochhammer_smeval_cast,
    Polynomial.ascPochhammer_smeval_eq_eval] using
      (Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n)

/-- The finite product on the left side of Carlson's generating relation 6.6-1. -/
def carlsonRGeneratingKernel (b z : ι → ℂ) (t : ℂ) : ℂ :=
  ∏ i, 1 / (1 - t * z i) ^ (b i)

/-- Carlson's generating relation 6.6-1 in the division-free Pochhammer-numerator
normalization.

The hypothesis puts every scalar binomial series inside its disk of convergence.  The
coefficient of `t ^ n` is the Pochhammer numerator divided by `n!`; consequently this
statement continues to make sense at exceptional values of the total parameter. -/
theorem hasSum_carlsonRPolynomialNumerator_div_factorial (b z : ι → ℂ) (t : ℂ)
    (ht : ∀ i, ‖t * z i‖ < 1) :
    HasSum (fun n : ℕ =>
      carlsonRPolynomialNumerator n b z / (n.factorial : ℂ) * t ^ n)
      (carlsonRGeneratingKernel b z t) := by
  sorry

/-- Within the common disk `‖t * z i‖ < 1`, the series of Carlson numerator
coefficients is summable. -/
theorem summable_carlsonRPolynomialNumerator_div_factorial (b z : ι → ℂ) (t : ℂ)
    (ht : ∀ i, ‖t * z i‖ < 1) :
    Summable (fun n : ℕ =>
      carlsonRPolynomialNumerator n b z / (n.factorial : ℂ) * t ^ n) :=
  (hasSum_carlsonRPolynomialNumerator_div_factorial b z t ht).summable

/- Generating Relation 6.6-1 in Carlson's usual normalization is

  `∏ i, (1 - t * z i) ^ (-b i) =
    ∑' n, (ascPochhammer ℂ n).eval (∑ i, b i) / n! * Rₙ(b,z) * t^n`.

The theorem above records its parameter-robust numerator form. -/

end DirichletTransform
end CarlsonRPolynomial
