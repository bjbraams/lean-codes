/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Inequalities

/-!
# Monotonicity in the real order

The hypergeometric mean is monotone in its order on the whole real line. Jensen's
inequality applied to powers proves comparisons between orders of the same sign;
Jensen's inequality for the exponential supplies the comparisons through zero.
All parameters and nodes are positive, and no Euler convergence strip is needed.

## References

* B. C. Carlson, *A hypergeometric mean value*, Proc. AMS 16 (1965), Theorem 3.
-/

open MeasureTheory ProbabilityTheory Set
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Jensen's exponential inequality compares every real R-average with its logarithmic
average. This is the comparison needed to pass through order zero. -/
theorem mul_carlsonLReal_zero_le_log_carlsonRReal (t : ℝ) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    t * carlsonLReal 0 b x ≤ Real.log (carlsonRReal t b x) := by
  let := isProbabilityMeasure_dirichletMeasure hb
  have hl : Integrable (fun u => Real.log (∑ i, u i * x i)) (dirichletMeasure b) := by
    simpa only [Real.rpow_zero, one_mul] using integrable_carlsonLReal 0 hb hx
  have heq : (fun u => Real.exp (t * Real.log (∑ i, u i * x i))) =ᵐ[dirichletMeasure b]
      (fun u => (∑ i, u i * x i) ^ t) := by
    filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
    rw [Real.rpow_def_of_pos (dirichlet_affine_mem (convex_Ioi 0) hx hu), mul_comm]
  have he := (integrable_carlsonRReal t hb hx).congr heq.symm
  have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => mem_univ _) (hl.const_mul t) he
  rw [integral_const_mul, integral_congr_ae heq] at h
  have h' := Real.log_le_log (Real.exp_pos _) h
  simpa only [Real.log_exp, carlsonLReal, Real.rpow_zero, one_mul, carlsonRReal] using h'

/-- The zero-order mean is bounded above by every positive-order mean. -/
theorem carlsonMeanReal_zero_le {t : ℝ} (ht : 0 < t) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonMeanReal 0 b x ≤ carlsonMeanReal t b x := by
  simp only [carlsonMeanReal, ht.ne', ↓reduceIte, Real.exp_le_exp]
  apply (le_div_iff₀ ht).mpr
  simpa only [mul_comm] using mul_carlsonLReal_zero_le_log_carlsonRReal t hb hx

/-- Every negative-order mean is bounded above by the zero-order mean. -/
theorem carlsonMeanReal_le_zero {t : ℝ} (ht : t < 0) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonMeanReal t b x ≤ carlsonMeanReal 0 b x := by
  simp only [carlsonMeanReal, ht.ne, ↓reduceIte, Real.exp_le_exp]
  apply (div_le_iff_of_neg ht).mpr
  simpa only [mul_comm] using mul_carlsonLReal_zero_le_log_carlsonRReal t hb hx

omit [Nonempty ι] in
/-- Iterated real powers of the affine form simplify almost everywhere under the Dirichlet
measure, even for negative exponents. -/
theorem ae_carlsonAffine_rpow_rpow (s t : ℝ) (b : ι → ℝ) {x : ι → ℝ}
    (hx : ∀ i, 0 < x i) :
    (fun u => ((∑ i, u i * x i) ^ s) ^ t) =ᵐ[dirichletMeasure b]
      (fun u => (∑ i, u i * x i) ^ (s * t)) := by
  filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
  exact (Real.rpow_mul (dirichlet_affine_mem (convex_Ioi 0) hx hu).le s t).symm

/-- Positive orders satisfy the power-mean comparison. -/
theorem carlsonMeanReal_mono_of_pos {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    {b x : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonMeanReal s b x ≤ carlsonMeanReal t b x := by
  let := isProbabilityMeasure_dirichletMeasure hb
  have ht := hs.trans_le hst
  have hq : 1 ≤ t / s := (le_div_iff₀ hs).mpr (by simpa using hst)
  have heq := ae_carlsonAffine_rpow_rpow s (t / s) b hx
  have hst' : s * (t / s) = t := by field_simp
  rw [hst'] at heq
  have hgi := (integrable_carlsonRReal t hb hx).congr heq.symm
  have h := (convexOn_rpow hq).map_integral_le
    (Real.continuous_rpow_const (by positivity : 0 ≤ t / s)).continuousOn isClosed_Ici
    (by
      filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
      exact (Real.rpow_pos_of_pos (dirichlet_affine_mem (convex_Ioi 0) hx hu) s).le)
    (integrable_carlsonRReal s hb hx) hgi
  rw [integral_congr_ae heq] at h
  apply (Real.rpow_le_rpow_iff (carlsonMeanReal_pos s b x).le
    (carlsonMeanReal_pos t b x).le ht).mp
  rw [carlsonMeanReal_rpow ht.ne' hb hx, carlsonMeanReal_eq_rpow hs.ne' hb hx,
    ← Real.rpow_mul (carlsonRReal_pos s hb hx).le]
  simpa only [carlsonRReal, div_eq_mul_inv, mul_comm] using h

/-- Negative orders satisfy the power-mean comparison, with the root reversing the
concave Jensen inequality. -/
theorem carlsonMeanReal_mono_of_neg {s t : ℝ} (ht : t < 0) (hst : s ≤ t)
    {b x : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonMeanReal s b x ≤ carlsonMeanReal t b x := by
  let := isProbabilityMeasure_dirichletMeasure hb
  have hs := hst.trans_lt ht
  have hq0 : 0 ≤ t / s := div_nonneg_of_nonpos ht.le hs.le
  have hq1 : t / s ≤ 1 := (div_le_iff_of_neg hs).mpr (by simpa using hst)
  have heq := ae_carlsonAffine_rpow_rpow s (t / s) b hx
  have hst' : s * (t / s) = t := by field_simp [hs.ne]
  rw [hst'] at heq
  have hgi := (integrable_carlsonRReal t hb hx).congr heq.symm
  have h := (Real.concaveOn_rpow hq0 hq1).le_map_integral
    (Real.continuous_rpow_const hq0).continuousOn isClosed_Ici
    (by
      filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
      exact (Real.rpow_pos_of_pos (dirichlet_affine_mem (convex_Ioi 0) hx hu) s).le)
    (integrable_carlsonRReal s hb hx) hgi
  rw [integral_congr_ae heq] at h
  apply (Real.rpow_le_rpow_iff_of_neg (carlsonMeanReal_pos t b x)
    (carlsonMeanReal_pos s b x) ht).mp
  rw [carlsonMeanReal_rpow ht.ne hb hx, carlsonMeanReal_eq_rpow hs.ne hb hx,
    ← Real.rpow_mul (carlsonRReal_pos s hb hx).le]
  simpa only [carlsonRReal, div_eq_mul_inv, mul_comm] using h

/-- Carlson's hypergeometric mean is monotone in its order on the entire real line. -/
theorem monotone_carlsonMeanReal {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    Monotone (fun t : ℝ => carlsonMeanReal t b x) := by
  intro s t hst
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · rcases lt_trichotomy t 0 with ht | rfl | ht
    · exact carlsonMeanReal_mono_of_neg ht hst hb hx
    · exact carlsonMeanReal_le_zero hs hb hx
    · exact (carlsonMeanReal_le_zero hs hb hx).trans (carlsonMeanReal_zero_le ht hb hx)
  · rcases hst.eq_or_lt with rfl | ht
    · exact le_rfl
    · exact carlsonMeanReal_zero_le ht hb hx
  · exact carlsonMeanReal_mono_of_pos hs hst hb hx

end Carlson
