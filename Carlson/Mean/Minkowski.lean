/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Properties
public import Dirichlet.Real.StrictAverage
public import ToMathlib.Analysis.Convex.NormalizedAddition

/-!
# Minkowski inequalities for hypergeometric means

The hypergeometric mean is subadditive above order one and superadditive below
order one, including at order zero and at negative orders. Away from order one,
equality holds precisely for proportional positive node vectors.

The proof normalizes each vector by its mean and applies convexity or concavity
of the scalar kernel to the resulting convex combination.

## References

* B. C. Carlson, *A hypergeometric mean value*, Proc. AMS 16 (1965), Theorem 5.
-/

open MeasureTheory ProbabilityTheory Set
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Dividing a positive node vector by its hypergeometric mean normalizes its mean to one. -/
theorem carlsonMeanReal_normalize (t : ℝ) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonMeanReal t b (fun i => (carlsonMeanReal t b x)⁻¹ * x i) = 1 := by
  rw [carlsonMeanReal_mul t hb hx (inv_pos.mpr (carlsonMeanReal_pos t b x)),
    inv_mul_cancel₀ (carlsonMeanReal_pos t b x).ne']

/-- At nonzero order, normalizing the mean also normalizes its R-average. -/
theorem carlsonRReal_normalize {t : ℝ} (ht : t ≠ 0) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonRReal t b (fun i => (carlsonMeanReal t b x)⁻¹ * x i) = 1 := by
  rw [← carlsonMeanReal_rpow ht hb (fun i =>
    mul_pos (inv_pos.mpr (carlsonMeanReal_pos t b x)) (hx i)),
    carlsonMeanReal_normalize t hb hx, Real.one_rpow]

/-- At order zero, normalizing the mean makes its logarithmic average zero. -/
theorem carlsonLReal_zero_normalize {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonLReal 0 b (fun i => (carlsonMeanReal 0 b x)⁻¹ * x i) = 0 := by
  have h := congrArg Real.log (carlsonMeanReal_normalize 0 hb hx)
  simpa only [carlsonMeanReal, ↓reduceIte, Real.log_exp, Real.log_one] using h

/-- Strict Minkowski inequality above order one, for nonproportional positive vectors. -/
theorem carlsonMeanReal_add_lt {t : ℝ} (ht : 1 < t) {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hne : ¬ ∃ a : ℝ, 0 < a ∧ ∀ i, y i = a * x i) :
    carlsonMeanReal t b (fun i => x i + y i) < carlsonMeanReal t b x + carlsonMeanReal t b y := by
  have ht0 := zero_lt_one.trans ht
  have hF : StrictConvexOn ℝ {x : ι → ℝ | ∀ i, 0 < x i} (carlsonRReal t b) :=
    strictConvexOn_dirichlet_average hb
      ((strictConvexOn_rpow ht).subset (fun _ h => h.le) (convex_Ioi 0))
      (fun z hz => (Real.continuousAt_rpow_const z t (Or.inl hz.ne')).continuousWithinAt)
  have h := hF.map_normalized_add_lt hx hy
    (inv_mul_ne_inv_mul_of_not_proportional hne (carlsonMeanReal_pos t b x)
      (carlsonMeanReal_pos t b y)) (carlsonMeanReal_pos t b x) (carlsonMeanReal_pos t b y)
  rw [carlsonRReal_normalize ht0.ne' hb hx, carlsonRReal_normalize ht0.ne' hb hy,
    mul_one, mul_one, ← add_div, div_self (add_pos (carlsonMeanReal_pos t b x)
      (carlsonMeanReal_pos t b y)).ne'] at h
  have hz i := mul_pos (inv_pos.mpr (add_pos (carlsonMeanReal_pos t b x)
    (carlsonMeanReal_pos t b y))) (add_pos (hx i) (hy i))
  have hm := Real.rpow_lt_rpow (carlsonRReal_pos t hb hz).le h (inv_pos.mpr ht0)
  rw [Real.one_rpow, ← carlsonMeanReal_eq_rpow ht0.ne' hb hz,
    carlsonMeanReal_mul t hb (fun i => add_pos (hx i) (hy i))
      (inv_pos.mpr (add_pos (carlsonMeanReal_pos t b x) (carlsonMeanReal_pos t b y))),
    inv_mul_eq_div] at hm
  exact (div_lt_one (add_pos (carlsonMeanReal_pos t b x) (carlsonMeanReal_pos t b y))).mp hm

/-- Strict reverse Minkowski inequality below order one, including zero and negative orders. -/
theorem lt_carlsonMeanReal_add {t : ℝ} (ht : t < 1) {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hne : ¬ ∃ a : ℝ, 0 < a ∧ ∀ i, y i = a * x i) :
    carlsonMeanReal t b x + carlsonMeanReal t b y < carlsonMeanReal t b (fun i => x i + y i) := by
  have hA := carlsonMeanReal_pos t b x
  have hB := carlsonMeanReal_pos t b y
  have hS := add_pos hA hB
  have hz i := mul_pos (inv_pos.mpr hS) (add_pos (hx i) (hy i))
  suffices hm : 1 < carlsonMeanReal t b
      (fun i => (carlsonMeanReal t b x + carlsonMeanReal t b y)⁻¹ * (x i + y i)) by
    rw [carlsonMeanReal_mul t hb (fun i => add_pos (hx i) (hy i))
      (inv_pos.mpr hS), inv_mul_eq_div] at hm
    exact (one_lt_div hS).mp hm
  rcases lt_trichotomy t 0 with hn | rfl | hp
  · have hF : StrictConvexOn ℝ {x : ι → ℝ | ∀ i, 0 < x i} (carlsonRReal t b) :=
      strictConvexOn_dirichlet_average hb (Real.strictConvexOn_rpow_of_neg hn)
        (fun z hz => (Real.continuousAt_rpow_const z t (Or.inl hz.ne')).continuousWithinAt)
    have h := hF.map_normalized_add_lt hx hy
      (inv_mul_ne_inv_mul_of_not_proportional hne hA hB) hA hB
    rw [carlsonRReal_normalize hn.ne hb hx, carlsonRReal_normalize hn.ne hb hy,
      mul_one, mul_one, ← add_div, div_self hS.ne'] at h
    have hm := Real.rpow_lt_rpow_of_neg (carlsonRReal_pos t hb hz) h (inv_lt_zero.mpr hn)
    simpa only [Real.one_rpow, ← carlsonMeanReal_eq_rpow hn.ne hb hz] using hm
  · have hF : StrictConcaveOn ℝ {x : ι → ℝ | ∀ i, 0 < x i} (carlsonLReal 0 b) := by
      change StrictConcaveOn ℝ {x : ι → ℝ | ∀ i, 0 < x i} (fun x => carlsonLReal 0 b x)
      simpa only [carlsonLReal, Real.rpow_zero, one_mul, mem_Ioi] using
        strictConcaveOn_dirichlet_average hb strictConcaveOn_log_Ioi
          (Real.continuousOn_log.mono (fun _ hz => hz.ne'))
    have h := hF.lt_map_normalized_add hx hy
      (inv_mul_ne_inv_mul_of_not_proportional hne hA hB) hA hB
    rw [carlsonLReal_zero_normalize hb hx, carlsonLReal_zero_normalize hb hy,
      mul_zero, mul_zero, add_zero] at h
    simpa only [carlsonMeanReal, ↓reduceIte, Real.exp_zero] using Real.exp_lt_exp.mpr h
  · have hF : StrictConcaveOn ℝ {x : ι → ℝ | ∀ i, 0 < x i} (carlsonRReal t b) :=
      strictConcaveOn_dirichlet_average hb
        ((Real.strictConcaveOn_rpow hp ht).subset (fun _ h => h.le) (convex_Ioi 0))
        (fun z hz => (Real.continuousAt_rpow_const z t (Or.inl hz.ne')).continuousWithinAt)
    have h := hF.lt_map_normalized_add hx hy
      (inv_mul_ne_inv_mul_of_not_proportional hne hA hB) hA hB
    rw [carlsonRReal_normalize hp.ne' hb hx, carlsonRReal_normalize hp.ne' hb hy,
      mul_one, mul_one, ← add_div, div_self hS.ne'] at h
    have hm := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) h (inv_pos.mpr hp)
    simpa only [Real.one_rpow, ← carlsonMeanReal_eq_rpow hp.ne' hb hz] using hm

/-- Proportional positive vectors give equality in Minkowski at every real order. -/
theorem carlsonMeanReal_add_eq_of_proportional (t : ℝ) {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i)
    (hxy : ∃ a : ℝ, 0 < a ∧ ∀ i, y i = a * x i) :
    carlsonMeanReal t b (fun i => x i + y i) = carlsonMeanReal t b x + carlsonMeanReal t b y := by
  obtain ⟨a, ha, hxy⟩ := hxy
  have he : (fun i => x i + y i) = fun i => (1 + a) * x i := by
    funext i
    rw [hxy i]
    ring
  rw [he, carlsonMeanReal_mul t hb hx (by positivity), funext hxy,
    carlsonMeanReal_mul t hb hx ha]
  ring

/-- Order one is additive, since it is the weighted arithmetic mean. -/
theorem carlsonMeanReal_one_add {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    carlsonMeanReal 1 b (fun i => x i + y i) = carlsonMeanReal 1 b x + carlsonMeanReal 1 b y := by
  rw [carlsonMeanReal_one hb (fun i => add_pos (hx i) (hy i)),
    carlsonMeanReal_one hb hx, carlsonMeanReal_one hb hy]
  simp only [mul_add, Finset.sum_add_distrib]

/-- Minkowski inequality for hypergeometric means at all orders at least one. -/
theorem carlsonMeanReal_add_le {t : ℝ} (ht : 1 ≤ t) {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    carlsonMeanReal t b (fun i => x i + y i) ≤ carlsonMeanReal t b x + carlsonMeanReal t b y := by
  rcases ht.eq_or_lt with rfl | ht
  · exact (carlsonMeanReal_one_add hb hx hy).le
  by_cases hxy : ∃ a : ℝ, 0 < a ∧ ∀ i, y i = a * x i
  · exact (carlsonMeanReal_add_eq_of_proportional t hb hx hxy).le
  · exact (carlsonMeanReal_add_lt ht hb hx hy hxy).le

/-- Reverse Minkowski inequality for all orders at most one, with no lower order bound. -/
theorem le_carlsonMeanReal_add {t : ℝ} (ht : t ≤ 1) {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    carlsonMeanReal t b x + carlsonMeanReal t b y ≤ carlsonMeanReal t b (fun i => x i + y i) := by
  rcases ht.eq_or_lt with rfl | ht
  · exact (carlsonMeanReal_one_add hb hx hy).ge
  by_cases hxy : ∃ a : ℝ, 0 < a ∧ ∀ i, y i = a * x i
  · exact (carlsonMeanReal_add_eq_of_proportional t hb hx hxy).ge
  · exact (lt_carlsonMeanReal_add ht hb hx hy hxy).le

/-- Equality in either Minkowski inequality holds precisely at order one or for
proportional positive node vectors. This includes singleton index types. -/
theorem carlsonMeanReal_add_eq_iff (t : ℝ) {b x y : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    carlsonMeanReal t b (fun i => x i + y i) = carlsonMeanReal t b x + carlsonMeanReal t b y ↔
      t = 1 ∨ ∃ a : ℝ, 0 < a ∧ ∀ i, y i = a * x i := by
  constructor
  · intro he
    by_contra h
    have h := not_or.mp h
    rcases lt_or_gt_of_ne h.1 with ht | ht
    · exact (lt_carlsonMeanReal_add ht hb hx hy h.2).ne he.symm
    · exact (carlsonMeanReal_add_lt ht hb hx hy h.2).ne he
  · rintro (rfl | hxy)
    · exact carlsonMeanReal_one_add hb hx hy
    · exact carlsonMeanReal_add_eq_of_proportional t hb hx hxy

/-- Above order one, the hypergeometric mean is convex as a function of its positive nodes. -/
theorem convexOn_carlsonMeanReal {t : ℝ} (ht : 1 ≤ t) {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) :
    ConvexOn ℝ {x : ι → ℝ | ∀ i, 0 < x i} (carlsonMeanReal t b) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy a c ha hc hac i
    exact (convex_Ioi (0 : ℝ)) (hx i) (hy i) ha hc hac
  · intro x hx y hy a c ha hc hac
    rcases ha.eq_or_lt with ha | ha
    · subst a
      have hc : c = 1 := by simpa using hac
      simp [hc]
    rcases hc.eq_or_lt with hc | hc
    · subst c
      have ha : a = 1 := by simpa using hac
      simp [ha]
    have h := carlsonMeanReal_add_le ht hb (fun i => mul_pos ha (hx i))
      (fun i => mul_pos hc (hy i))
    rw [carlsonMeanReal_mul t hb hx ha, carlsonMeanReal_mul t hb hy hc] at h
    exact h

/-- Below order one, including zero and negative orders, the hypergeometric mean is
concave as a function of its positive nodes. -/
theorem concaveOn_carlsonMeanReal {t : ℝ} (ht : t ≤ 1) {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) :
    ConcaveOn ℝ {x : ι → ℝ | ∀ i, 0 < x i} (carlsonMeanReal t b) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy a c ha hc hac i
    exact (convex_Ioi (0 : ℝ)) (hx i) (hy i) ha hc hac
  · intro x hx y hy a c ha hc hac
    rcases ha.eq_or_lt with ha | ha
    · subst a
      have hc : c = 1 := by simpa using hac
      simp [hc]
    rcases hc.eq_or_lt with hc | hc
    · subst c
      have ha : a = 1 := by simpa using hac
      simp [ha]
    have h := le_carlsonMeanReal_add ht hb (fun i => mul_pos ha (hx i))
      (fun i => mul_pos hc (hy i))
    rw [carlsonMeanReal_mul t hb hx ha, carlsonMeanReal_mul t hb hy hc] at h
    exact h

end Carlson
