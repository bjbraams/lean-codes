/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Inequalities
public import Dirichlet.Real.BetaAverage

/-!
# Carlson–Tobey concentration monotonicity for two nodes

For positive distinct nodes, R strictly decreases in concentration at orders
below zero or above one, and strictly increases between zero and one. The
hypergeometric mean strictly increases below order one (including order zero)
and strictly decreases above order one. Positive parameters need not be
normalized. All real orders are allowed by the compact Dirichlet integral.

## References

* B. C. Carlson and M. D. Tobey, *A property of the hypergeometric mean value*,
  Proc. AMS 19 (1968), 255–262, Theorems 1, 3, and 4 (two-node case).
-/

open MeasureTheory ProbabilityTheory Set
public noncomputable section
namespace Carlson

/-- Real powers are continuous on the positive axis for every real exponent. -/
private theorem continuousOn_positive_rpow (t : ℝ) :
    ContinuousOn (fun u : ℝ => u ^ t) (Ioi 0) := by
  intro u hu
  exact (Real.continuousAt_rpow_const u t (Or.inl (ne_of_gt hu))).continuousWithinAt

/-- At orders above one, the two-node R-average strictly decreases in concentration. -/
theorem strictAntiOn_carlsonRReal_fin_two_concentration_of_one_lt {t a b x y : ℝ}
    (ht : 1 < t) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    StrictAntiOn (fun c : ℝ => carlsonRReal t (![c * a, c * b]) (![x, y])) (Ioi 0) := by
  intro c hc d _ hcd
  exact integral_dirichletMeasure_fin_two_lt_of_concentration ha hb hc hcd
    ((strictConvexOn_rpow ht).subset (fun _ hu => hu.le) (convex_Ioi 0))
    (continuousOn_positive_rpow t) (by fun_prop) hx hy hxy

/-- At negative orders, the two-node R-average strictly decreases in concentration. -/
theorem strictAntiOn_carlsonRReal_fin_two_concentration_of_neg {t a b x y : ℝ}
    (ht : t < 0) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    StrictAntiOn (fun c : ℝ => carlsonRReal t (![c * a, c * b]) (![x, y])) (Ioi 0) := by
  intro c hc d _ hcd
  exact integral_dirichletMeasure_fin_two_lt_of_concentration ha hb hc hcd
    (Real.strictConvexOn_rpow_of_neg ht) (continuousOn_positive_rpow t)
    (by fun_prop) hx hy hxy

/-- Between orders zero and one, the two-node R-average strictly increases in concentration. -/
theorem strictMonoOn_carlsonRReal_fin_two_concentration {t a b x y : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    StrictMonoOn (fun c : ℝ => carlsonRReal t (![c * a, c * b]) (![x, y])) (Ioi 0) := by
  intro c hc d _ hcd
  exact integral_dirichletMeasure_fin_two_lt_of_concentration_concave ha hb hc hcd
    ((Real.strictConcaveOn_rpow ht ht1).subset (fun _ hu => hu.le) (convex_Ioi 0))
    (continuousOn_positive_rpow t) (by fun_prop) hx hy hxy

/-- The logarithmic two-node average strictly increases in concentration. -/
theorem strictMonoOn_carlsonLReal_zero_fin_two_concentration {a b x y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    StrictMonoOn (fun c : ℝ => carlsonLReal 0 (![c * a, c * b]) (![x, y])) (Ioi 0) := by
  intro c hc d _ hcd
  have h := integral_dirichletMeasure_fin_two_lt_of_concentration_concave ha hb hc hcd
    strictConcaveOn_log_Ioi (Real.continuousOn_log.mono (fun _ hu => ne_of_gt hu))
    Real.measurable_log hx hy hxy
  simpa only [carlsonLReal, Real.rpow_zero, one_mul] using h

/-- Above order one, the two-node hypergeometric mean strictly decreases in concentration. -/
theorem strictAntiOn_carlsonMeanReal_fin_two_concentration {t a b x y : ℝ}
    (ht : 1 < t) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    StrictAntiOn (fun c : ℝ => carlsonMeanReal t (![c * a, c * b]) (![x, y])) (Ioi 0) := by
  intro c hc d hd hcd
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hR := strictAntiOn_carlsonRReal_fin_two_concentration_of_one_lt ht ha hb hx hy hxy hc hd hcd
  have hpos := carlsonRReal_pos t
    (show (![d * a, d * b] : Fin 2 → ℝ) ∈ mvRealBetaDomain by
      simpa using And.intro (mul_pos hd ha) (mul_pos hd hb))
    (show ∀ i, 0 < (![x, y] : Fin 2 → ℝ) i by simpa using And.intro hx hy)
  simp only [carlsonMeanReal, ite_eq_right ht0.ne']
  exact Real.exp_lt_exp.mpr (div_lt_div_of_pos_right (Real.log_lt_log hpos hR) ht0)

/-- Below order one, including order zero, the two-node mean strictly increases in concentration. -/
theorem strictMonoOn_carlsonMeanReal_fin_two_concentration {t a b x y : ℝ}
    (ht : t < 1) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    StrictMonoOn (fun c : ℝ => carlsonMeanReal t (![c * a, c * b]) (![x, y])) (Ioi 0) := by
  intro c hc d hd hcd
  rcases lt_trichotomy t 0 with ht0 | rfl | ht0
  · have hR := strictAntiOn_carlsonRReal_fin_two_concentration_of_neg ht0 ha hb hx hy hxy hc hd hcd
    have hpos := carlsonRReal_pos t
      (show (![d * a, d * b] : Fin 2 → ℝ) ∈ mvRealBetaDomain by
        simpa using And.intro (mul_pos hd ha) (mul_pos hd hb))
      (show ∀ i, 0 < (![x, y] : Fin 2 → ℝ) i by simpa using And.intro hx hy)
    simp only [carlsonMeanReal, ite_eq_right ht0.ne]
    exact Real.exp_lt_exp.mpr (div_lt_div_of_neg_of_lt ht0 (Real.log_lt_log hpos hR))
  · simp only [carlsonMeanReal, ↓reduceIte]
    exact Real.exp_lt_exp.mpr
      (strictMonoOn_carlsonLReal_zero_fin_two_concentration ha hb hx hy hxy hc hd hcd)
  · have hR := strictMonoOn_carlsonRReal_fin_two_concentration ht0 ht ha hb hx hy hxy hc hd hcd
    have hpos := carlsonRReal_pos t
      (show (![c * a, c * b] : Fin 2 → ℝ) ∈ mvRealBetaDomain by
        simpa using And.intro (mul_pos hc ha) (mul_pos hc hb))
      (show ∀ i, 0 < (![x, y] : Fin 2 → ℝ) i by simpa using And.intro hx hy)
    simp only [carlsonMeanReal, ite_eq_right ht0.ne']
    exact Real.exp_lt_exp.mpr (div_lt_div_of_pos_right (Real.log_lt_log hpos hR) ht0)

end Carlson
