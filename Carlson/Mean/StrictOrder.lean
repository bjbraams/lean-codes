/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Order
public import Carlson.Mean.Properties
public import Carlson.Mean.Euler
public import Dirichlet.Real.StrictAverage

/-!
# Strict order comparisons and equality cases

For positive parameters and nonconstant positive nodes, Carlson's mean is strictly
increasing on the entire real order axis. Equality between different orders holds
exactly for constant node vectors. In particular the arithmetic and geometric
comparisons have their expected strictness and equality conditions.

## References

* B. C. Carlson, *A hypergeometric mean value*, Proc. AMS 16 (1965), Theorems 3 and 6.
-/

open MeasureTheory ProbabilityTheory Set
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Strict exponential Jensen compares a nonzero-order R-average with its logarithmic
average when the nodes are nonconstant. -/
theorem mul_carlsonLReal_zero_lt_log_carlsonRReal {t : ℝ} (ht : t ≠ 0) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    t * carlsonLReal 0 b x < Real.log (carlsonRReal t b x) := by
  let := isProbabilityMeasure_dirichletMeasure hb
  have hl : Integrable (fun u => Real.log (∑ i, u i * x i)) (dirichletMeasure b) := by
    simpa only [Real.rpow_zero, one_mul] using integrable_carlsonLReal 0 hb hx
  have heq : (fun u => Real.exp (t * Real.log (∑ i, u i * x i))) =ᵐ[dirichletMeasure b]
      (fun u => (∑ i, u i * x i) ^ t) := by
    filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
    rw [Real.rpow_def_of_pos (dirichlet_affine_mem (convex_Ioi 0) hx hu), mul_comm]
  have he := (integrable_carlsonRReal t hb hx).congr heq.symm
  have h := strictConvexOn_exp.ae_eq_const_or_map_average_lt Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => mem_univ _) (hl.const_mul t) he
  have hn := not_ae_dirichlet_affine_comp_eq_const hb (convex_Ioi 0) hx hne
    (f := fun y => t * Real.log y)
    (fun y hy z hz he => Real.log_injOn_pos hy hz (mul_left_cancel₀ ht he))
  have h := h.resolve_left (hn _)
  simp only [average_eq_integral] at h
  rw [integral_const_mul, integral_congr_ae heq] at h
  have h' := Real.log_lt_log (Real.exp_pos _) h
  simpa only [Real.log_exp, carlsonLReal, Real.rpow_zero, one_mul, carlsonRReal] using h'

/-- The zero-order mean is strictly below every positive-order mean for nonconstant nodes. -/
theorem carlsonMeanReal_zero_lt {t : ℝ} (ht : 0 < t) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    carlsonMeanReal 0 b x < carlsonMeanReal t b x := by
  simp only [carlsonMeanReal, ht.ne', ↓reduceIte, Real.exp_lt_exp]
  apply (lt_div_iff₀ ht).mpr
  simpa only [mul_comm] using mul_carlsonLReal_zero_lt_log_carlsonRReal ht.ne' hb hx hne

/-- Every negative-order mean is strictly below the zero-order mean for nonconstant nodes. -/
theorem carlsonMeanReal_lt_zero {t : ℝ} (ht : t < 0) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    carlsonMeanReal t b x < carlsonMeanReal 0 b x := by
  simp only [carlsonMeanReal, ht.ne, ↓reduceIte, Real.exp_lt_exp]
  apply (div_lt_iff_of_neg ht).mpr
  simpa only [mul_comm] using mul_carlsonLReal_zero_lt_log_carlsonRReal ht.ne hb hx hne

/-- Distinct positive orders satisfy the strict power-mean comparison. -/
theorem carlsonMeanReal_strict_mono_of_pos {s t : ℝ} (hs : 0 < s) (hst : s < t)
    {b x : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    carlsonMeanReal s b x < carlsonMeanReal t b x := by
  let := isProbabilityMeasure_dirichletMeasure hb
  have ht := hs.trans hst
  have hq : 1 < t / s := (lt_div_iff₀ hs).mpr (by simpa using hst)
  have heq := ae_carlsonAffine_rpow_rpow s (t / s) b hx
  have hst' : s * (t / s) = t := by field_simp
  rw [hst'] at heq
  have hgi := (integrable_carlsonRReal t hb hx).congr heq.symm
  have h := (strictConvexOn_rpow hq).ae_eq_const_or_map_average_lt
    (Real.continuous_rpow_const (by positivity : 0 ≤ t / s)).continuousOn isClosed_Ici
    (by
      filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
      exact (Real.rpow_pos_of_pos (dirichlet_affine_mem (convex_Ioi 0) hx hu) s).le)
    (integrable_carlsonRReal s hb hx) hgi
  have hn := not_ae_dirichlet_affine_comp_eq_const hb (convex_Ioi 0) hx hne
    (f := fun y => y ^ s)
    (fun y hy z hz he => (Real.rpow_left_inj hy.le hz.le hs.ne').mp he)
  have h := h.resolve_left (hn _)
  simp only [average_eq_integral] at h
  rw [integral_congr_ae heq] at h
  apply (Real.rpow_lt_rpow_iff (carlsonMeanReal_pos s b x).le
    (carlsonMeanReal_pos t b x).le ht).mp
  rw [carlsonMeanReal_rpow ht.ne' hb hx, carlsonMeanReal_eq_rpow hs.ne' hb hx,
    ← Real.rpow_mul (carlsonRReal_pos s hb hx).le]
  simpa only [carlsonRReal, div_eq_mul_inv, mul_comm] using h

/-- Distinct negative orders satisfy the strict power-mean comparison, with the root reversing the
concave Jensen inequality. -/
theorem carlsonMeanReal_strict_mono_of_neg {s t : ℝ} (ht : t < 0) (hst : s < t)
    {b x : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    carlsonMeanReal s b x < carlsonMeanReal t b x := by
  let := isProbabilityMeasure_dirichletMeasure hb
  have hs := hst.trans ht
  have hq0 : 0 < t / s := div_pos_of_neg_of_neg ht hs
  have hq1 : t / s < 1 := (div_lt_iff_of_neg hs).mpr (by simpa using hst)
  have heq := ae_carlsonAffine_rpow_rpow s (t / s) b hx
  have hst' : s * (t / s) = t := by field_simp [hs.ne]
  rw [hst'] at heq
  have hgi := (integrable_carlsonRReal t hb hx).congr heq.symm
  have h := (Real.strictConcaveOn_rpow hq0 hq1).ae_eq_const_or_lt_map_average
    (Real.continuous_rpow_const hq0.le).continuousOn isClosed_Ici
    (by
      filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
      exact (Real.rpow_pos_of_pos (dirichlet_affine_mem (convex_Ioi 0) hx hu) s).le)
    (integrable_carlsonRReal s hb hx) hgi
  have hn := not_ae_dirichlet_affine_comp_eq_const hb (convex_Ioi 0) hx hne
    (f := fun y => y ^ s)
    (fun y hy z hz he => (Real.rpow_left_inj hy.le hz.le hs.ne).mp he)
  have h := h.resolve_left (hn _)
  simp only [average_eq_integral] at h
  rw [integral_congr_ae heq] at h
  apply (Real.rpow_lt_rpow_iff_of_neg (carlsonMeanReal_pos t b x)
    (carlsonMeanReal_pos s b x) ht).mp
  rw [carlsonMeanReal_rpow ht.ne hb hx, carlsonMeanReal_eq_rpow hs.ne hb hx,
    ← Real.rpow_mul (carlsonRReal_pos s hb hx).le]
  simpa only [carlsonRReal, div_eq_mul_inv, mul_comm] using h

/-- The hypergeometric mean is strictly increasing in order for nonconstant positive nodes. -/
theorem strictMono_carlsonMeanReal {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    StrictMono (fun t : ℝ => carlsonMeanReal t b x) := by
  intro s t hst
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · rcases lt_trichotomy t 0 with ht | rfl | ht
    · exact carlsonMeanReal_strict_mono_of_neg ht hst hb hx hne
    · exact carlsonMeanReal_lt_zero hs hb hx hne
    · exact (carlsonMeanReal_lt_zero hs hb hx hne).trans
        (carlsonMeanReal_zero_lt ht hb hx hne)
  · exact carlsonMeanReal_zero_lt hst hb hx hne
  · exact carlsonMeanReal_strict_mono_of_pos hs hst hb hx hne

/-- Means at distinct orders agree exactly for constant positive node vectors. -/
theorem carlsonMeanReal_eq_iff_of_ne {s t : ℝ} (hst : s ≠ t) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonMeanReal s b x = carlsonMeanReal t b x ↔ ∀ i j, x i = x j := by
  constructor
  · intro he
    by_contra! hne
    exact hst ((strictMono_carlsonMeanReal hb hx hne).injective he)
  · intro hc
    let i := Classical.arbitrary ι
    have he : x = fun _ => x i := funext (fun j => hc j i)
    rw [he, carlsonMeanReal_const s (hx i) hb, carlsonMeanReal_const t (hx i) hb]

/-- Above order one, nonconstant means strictly exceed the weighted arithmetic mean. -/
theorem arithmetic_lt_carlsonMeanReal {t : ℝ} (ht : 1 < t) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    (∑ i, (b i / ∑ j, b j) * x i) < carlsonMeanReal t b x := by
  rw [← carlsonMeanReal_one hb hx]
  exact strictMono_carlsonMeanReal hb hx hne ht

/-- Below order one, nonconstant means lie strictly below the weighted arithmetic mean. -/
theorem carlsonMeanReal_lt_arithmetic {t : ℝ} (ht : t < 1) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    carlsonMeanReal t b x < ∑ i, (b i / ∑ j, b j) * x i := by
  rw [← carlsonMeanReal_one hb hx]
  exact strictMono_carlsonMeanReal hb hx hne ht

/-- Equality with the arithmetic mean occurs precisely at order one or on constant nodes. -/
theorem carlsonMeanReal_eq_arithmetic_iff (t : ℝ) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonMeanReal t b x = (∑ i, (b i / ∑ j, b j) * x i) ↔
      t = 1 ∨ ∀ i j, x i = x j := by
  rw [← carlsonMeanReal_one hb hx]
  by_cases ht : t = 1
  · simp [ht]
  · simp [ht, carlsonMeanReal_eq_iff_of_ne ht hb hx]

/-- Above minus the total parameter, nonconstant means strictly exceed the geometric mean. -/
theorem geometric_lt_carlsonMeanReal {t : ℝ} {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j)
    (ht : -(∑ i, b i) < t) :
    Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i)) < carlsonMeanReal t b x := by
  rw [← carlsonMeanReal_neg_sum hb hx]
  exact strictMono_carlsonMeanReal hb hx hne ht

/-- Below minus the total parameter, nonconstant means lie strictly below the geometric mean. -/
theorem carlsonMeanReal_lt_geometric {t : ℝ} {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j)
    (ht : t < -(∑ i, b i)) :
    carlsonMeanReal t b x < Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i)) := by
  rw [← carlsonMeanReal_neg_sum hb hx]
  exact strictMono_carlsonMeanReal hb hx hne ht

/-- Equality with the geometric mean occurs precisely at minus the total parameter
or on constant nodes. -/
theorem carlsonMeanReal_eq_geometric_iff (t : ℝ) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonMeanReal t b x = Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i)) ↔
      t = -(∑ i, b i) ∨ ∀ i j, x i = x j := by
  rw [← carlsonMeanReal_neg_sum hb hx]
  by_cases ht : t = -(∑ i, b i)
  · simp [ht]
  · simp [ht, carlsonMeanReal_eq_iff_of_ne ht hb hx]

end Carlson
