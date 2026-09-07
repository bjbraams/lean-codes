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

/- TODO: Generating Relation 6.6-1 is

  `∏ i, (1 - t * z i) ^ (-b i) =
    ∑' n, (ascPochhammer ℂ n).eval (∑ i, b i) / n! * Rₙ(b,z) * t^n`.

In the present normalization, the coefficient of `t ^ n` is
`carlsonRPolynomialNumerator n b z / n!`.  The scalar binomial series needed for each factor
is `hasSum_ascPochhammer_mul_pow_div_factorial`; what remains is a theorem rearranging their
finite product by total multi-index degree. -/

end DirichletTransform
end CarlsonRPolynomial
