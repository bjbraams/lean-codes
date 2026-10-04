/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.Basic
public import Dirichlet.Real.Average
public import Dirichlet.Average.Bridge

/-!
# Real hypergeometric means and their complex counterparts

Positive parameters define a Dirichlet probability measure. Positive nodes keep
every affine combination away from zero, so every real power and power-logarithm
is integrable, without the exponent restrictions of the positive-ray Euler integral.
The real definitions below agree with the existing continued complex functions.
-/

open MeasureTheory ProbabilityTheory Dirichlet Set
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι]

/-- The real power average underlying the hypergeometric mean. -/
def carlsonRReal (t : ℝ) (b x : ι → ℝ) : ℝ :=
  ∫ u, (∑ i, u i * x i) ^ t ∂dirichletMeasure b

/-- The real power-logarithm average underlying the limiting and ratio means. -/
def carlsonLReal (t : ℝ) (b x : ι → ℝ) : ℝ :=
  ∫ u, (∑ i, u i * x i) ^ t * Real.log (∑ i, u i * x i) ∂dirichletMeasure b

/-- The real hypergeometric mean, with its logarithmic definition at order zero. -/
def carlsonMeanReal (t : ℝ) (b x : ι → ℝ) : ℝ :=
  Real.exp (if t = 0 then carlsonLReal 0 b x else Real.log (carlsonRReal t b x) / t)

/-- The real two-order ratio mean, with the logarithmic derivative on its diagonal. -/
def carlsonRatioMeanReal (s t : ℝ) (b x : ι → ℝ) : ℝ :=
  Real.exp (if s = t then carlsonLReal t b x / carlsonRReal t b x
    else (Real.log (carlsonRReal t b x) - Real.log (carlsonRReal s b x)) / (t - s))

/-- The real power-transformed family, including its weighted geometric limit at power zero. -/
def carlsonPowerMeanReal (s t : ℝ) (b x : ι → ℝ) : ℝ :=
  if s = 0 then Real.exp (∑ i, (b i / ∑ j, b j) * Real.log (x i))
  else carlsonMeanReal t b (fun i => x i ^ s) ^ s⁻¹

/-- Every real power of the positive affine form is integrable. -/
theorem integrable_carlsonRReal [Nonempty ι] (t : ℝ) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    Integrable (fun u => (∑ i, u i * x i) ^ t) (dirichletMeasure b) := by
  refine integrable_dirichletMeasure_comp_affine hb (convex_Ioi 0) hx
    (f := fun y : ℝ => y ^ t) ?_
  intro y hy
  exact (Real.continuousAt_rpow_const y t (Or.inl (ne_of_gt hy))).continuousWithinAt

/-- Every real power of the affine form belongs to each positive finite Lp space. -/
theorem memLp_carlsonAffine_rpow [Nonempty ι] (r : ℝ) {p : ℝ} (hp : 0 < p)
    {b x : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    MemLp (fun u => (∑ i, u i * x i) ^ r) (ENNReal.ofReal p) (dirichletMeasure b) := by
  have h0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have ht : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← memLp_norm_rpow_iff (integrable_carlsonRReal r hb hx).aestronglyMeasurable h0 ht,
    ENNReal.toReal_ofReal hp.le, ENNReal.div_self h0 ht, memLp_one_iff_integrable]
  apply (integrable_carlsonRReal (r * p) hb hx).congr
  filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
  have hy := dirichlet_affine_mem (convex_Ioi 0) hx hu
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy r), ← Real.rpow_mul hy.le]

/-- Every real power-logarithm of the positive affine form is integrable. -/
theorem integrable_carlsonLReal [Nonempty ι] (t : ℝ) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    Integrable (fun u => (∑ i, u i * x i) ^ t * Real.log (∑ i, u i * x i))
      (dirichletMeasure b) := by
  refine integrable_dirichletMeasure_comp_affine hb (convex_Ioi 0) hx
    (f := fun y : ℝ => y ^ t * Real.log y) ?_
  intro y hy
  exact ((Real.continuousAt_rpow_const y t (Or.inl (ne_of_gt hy))).mul
    (Real.continuousAt_log (ne_of_gt hy))).continuousWithinAt

/-- The real R-average is strictly positive for every real exponent. -/
theorem carlsonRReal_pos [Nonempty ι] (t : ℝ) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) : 0 < carlsonRReal t b x := by
  let := isProbabilityMeasure_dirichletMeasure hb
  have hp : ∀ᵐ u ∂dirichletMeasure b, 0 < (∑ i, u i * x i) ^ t := by
    filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
    exact Real.rpow_pos_of_pos (dirichlet_affine_mem (convex_Ioi 0) hx hu) t
  apply (integral_pos_iff_support_of_nonneg_ae (hp.mono fun _ h => h.le)
    (integrable_carlsonRReal t hb hx)).mpr
  have hm : dirichletMeasure b (Function.support (fun u => (∑ i, u i * x i) ^ t)) =
      dirichletMeasure b univ := by
    apply measure_congr
    filter_upwards [hp] with u hu
    simp [Function.mem_support, ne_of_gt hu]
  rw [hm, measure_univ]
  exact zero_lt_one

/-- The complex affine combination of real nodes is the coercion of the real combination. -/
theorem carlsonAffineForm_ofReal (x u : ι → ℝ) :
    carlsonAffineForm (fun i => (x i : ℂ)) u = ((∑ i, u i * x i : ℝ) : ℂ) := by
  simp [carlsonAffineForm]

/-- The continued complex R-function agrees with the real probability average. -/
theorem ofReal_carlsonRReal [Nonempty ι] (t : ℝ) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    (carlsonRReal t b x : ℂ) = carlsonR t (fun i => (b i : ℂ)) (fun i => (x i : ℂ)) := by
  rw [carlsonR, regCarlsonR_eq_regCarlsonRIntegral t (fun i => hb i) (fun i => hx i),
    regCarlsonRIntegral, regCarlsonDirichletAverage_ofReal hb]
  have hG := Complex.Gamma_ne_zero_of_re_pos
    (Complex.sum_re_pos_of_mem_mvBetaConvergent (b := fun i => (b i : ℂ)) (fun i => hb i))
  rw [mul_div_cancel₀ _ hG]
  unfold realCarlsonDirichletAverage carlsonRReal
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
  rw [carlsonAffineForm_ofReal, Complex.ofReal_cpow
    (le_of_lt (dirichlet_affine_mem (convex_Ioi 0) hx hu))]

/-- The continued complex L-function agrees with the real power-logarithm average. -/
theorem ofReal_carlsonLReal [Nonempty ι] (t : ℝ) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    (carlsonLReal t b x : ℂ) = carlsonL t (fun i => (b i : ℂ)) (fun i => (x i : ℂ)) := by
  rw [carlsonL, regCarlsonL_eq_regCarlsonLIntegral t (fun i => hb i) (fun i => hx i),
    regCarlsonLIntegral, regCarlsonDirichletAverage_ofReal hb]
  have hG := Complex.Gamma_ne_zero_of_re_pos
    (Complex.sum_re_pos_of_mem_mvBetaConvergent (b := fun i => (b i : ℂ)) (fun i => hb i))
  rw [mul_div_cancel₀ _ hG]
  unfold realCarlsonDirichletAverage carlsonLReal
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
  have hy := le_of_lt (dirichlet_affine_mem (convex_Ioi 0) hx hu)
  simp only [carlsonLKernel, carlsonAffineForm_ofReal, Complex.ofReal_mul,
    Complex.ofReal_cpow hy, Complex.ofReal_log hy]

/-- The real hypergeometric mean is positive, including at order zero. -/
theorem carlsonMeanReal_pos (t : ℝ) (b x : ι → ℝ) : 0 < carlsonMeanReal t b x :=
  Real.exp_pos _

/-- The real and complex hypergeometric means agree on positive data. -/
theorem ofReal_carlsonMeanReal [Nonempty ι] (t : ℝ) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    (carlsonMeanReal t b x : ℂ) =
      carlsonMean t (fun i => (b i : ℂ)) (fun i => (x i : ℂ)) := by
  by_cases ht : t = 0
  · subst t
    simp [carlsonMeanReal, Complex.ofReal_exp, ofReal_carlsonLReal 0 hb hx]
  · simp [carlsonMeanReal, carlsonMean, carlsonMeanLog, ht, Complex.ofReal_exp,
      Complex.ofReal_div, Complex.ofReal_log (carlsonRReal_pos t hb hx).le,
      ofReal_carlsonRReal t hb hx]

/-- The real ratio mean agrees with the complex ratio mean, including coincident orders. -/
theorem ofReal_carlsonRatioMeanReal [Nonempty ι] (s t : ℝ) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    (carlsonRatioMeanReal s t b x : ℂ) =
      carlsonRatioMean s t (fun i => (b i : ℂ)) (fun i => (x i : ℂ)) := by
  by_cases h : s = t
  · subst s
    simp [carlsonRatioMeanReal, Complex.ofReal_exp, ofReal_carlsonLReal t hb hx,
      ofReal_carlsonRReal t hb hx]
  · simp [carlsonRatioMeanReal, carlsonRatioMean, carlsonRatioMeanLog, h,
      Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_log (carlsonRReal_pos s hb hx).le,
      Complex.ofReal_log (carlsonRReal_pos t hb hx).le,
      ofReal_carlsonRReal s hb hx, ofReal_carlsonRReal t hb hx]

/-- R of order zero is the mass of the Dirichlet probability measure. -/
@[simp] theorem carlsonRReal_zero [Nonempty ι] {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (x : ι → ℝ) : carlsonRReal 0 b x = 1 := by
  let := isProbabilityMeasure_dirichletMeasure hb
  simp [carlsonRReal]

/-- R of order one is the weighted arithmetic mean. -/
theorem carlsonRReal_one [Nonempty ι] {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (x : ι → ℝ) :
    carlsonRReal 1 b x = ∑ i, (b i / ∑ j, b j) * x i := by
  simpa [carlsonRReal] using integral_dirichletMeasure_affine hb x

/-- The hypergeometric mean of order one is the weighted arithmetic mean. -/
theorem carlsonMeanReal_one [Nonempty ι] {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    carlsonMeanReal 1 b x = ∑ i, (b i / ∑ j, b j) * x i := by
  rw [carlsonMeanReal, ite_eq_right one_ne_zero, div_one,
    Real.exp_log (carlsonRReal_pos 1 hb hx), carlsonRReal_one hb]

/-- The power-transformed real family agrees with its complex definition, including both
zero power and zero order. -/
theorem ofReal_carlsonPowerMeanReal [Nonempty ι] (s t : ℝ) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    (carlsonPowerMeanReal s t b x : ℂ) =
      carlsonPowerMean s t (fun i => (b i : ℂ)) (fun i => (x i : ℂ)) := by
  by_cases hs : s = 0
  · subst s
    simp [carlsonPowerMeanReal, carlsonPowerMean_zero, Complex.ofReal_exp,
      Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_log (hx _).le]
  · have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
    have hp i := Real.rpow_pos_of_pos (hx i) s
    have hnodes : (fun i => (x i : ℂ) ^ (s : ℂ)) = (fun i => ((x i ^ s : ℝ) : ℂ)) := by
      ext i; exact (Complex.ofReal_cpow (hx i).le s).symm
    rw [carlsonPowerMeanReal, ite_eq_right hs,
      Real.rpow_def_of_pos (carlsonMeanReal_pos t b (fun i => x i ^ s)), carlsonMeanReal,
      Real.log_exp, Complex.ofReal_exp, carlsonPowerMean, carlsonPowerMeanLog,
      ite_eq_right hs', hnodes]
    by_cases ht : t = 0
    · subst t
      simp [carlsonMeanLog, Complex.ofReal_mul, ofReal_carlsonLReal 0 hb hp, div_eq_mul_inv]
    · simp [carlsonMeanLog, ht, Complex.ofReal_mul,
        Complex.ofReal_log (carlsonRReal_pos t hb hp).le, ofReal_carlsonRReal t hb hp,
        div_eq_mul_inv]

/-- Positive real parameters avoid every pole of the ordinary complex normalization. -/
theorem sum_ofReal_parameters_ne_neg_nat [Nonempty ι] {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (n : ℕ) : (∑ i, (b i : ℂ)) ≠ -(n : ℂ) := by
  have hpos := Complex.sum_re_pos_of_mem_mvBetaConvergent
    (b := fun i => (b i : ℂ)) (fun i => hb i)
  intro h
  rw [h, Complex.neg_re, Complex.natCast_re] at hpos
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- The real hypergeometric mean is continuous in its order, including at zero. -/
theorem continuous_carlsonMeanReal_order [Nonempty ι] {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    Continuous (fun t : ℝ => carlsonMeanReal t b x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have ha : AnalyticAt ℂ (fun a => carlsonMean a (fun i => (b i : ℂ))
      (fun i => (x i : ℂ))) (t : ℂ) := by
    by_cases ht : t = 0
    · subst t
      exact analyticAt_carlsonMean_order_zero (fun i => Complex.ofReal_mem_slitPlane.mpr (hx i))
        (sum_ofReal_parameters_ne_neg_nat hb)
    · apply analyticAt_carlsonMean_order_of_ne_zero (by exact_mod_cast ht) _
        (fun i => Complex.ofReal_mem_slitPlane.mpr (hx i))
      rw [← ofReal_carlsonRReal t hb hx]
      exact Complex.ofReal_mem_slitPlane.mpr (carlsonRReal_pos t hb hx)
  have h := Complex.continuous_re.continuousAt.comp
    (ha.continuousAt.comp Complex.continuous_ofReal.continuousAt)
  simpa only [Function.comp_def, ← ofReal_carlsonMeanReal _ hb hx, Complex.ofReal_re] using h

/-- At fixed positive parameters, the real mean is continuous on positive node vectors. -/
theorem continuousOn_carlsonMeanReal_nodes [Nonempty ι] (t : ℝ) {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) :
    ContinuousOn (carlsonMeanReal t b) {x : ι → ℝ | ∀ i, 0 < x i} := by
  have h : ContinuousOn (fun x : ι → ℝ =>
      (carlsonMean (t : ℂ) (fun i => (b i : ℂ)) (fun i => (x i : ℂ))).re)
      {x : ι → ℝ | ∀ i, 0 < x i} := by
    intro x hx
    have ha : AnalyticAt ℂ (fun z : ι → ℂ => carlsonMean (t : ℂ)
        (fun i => (b i : ℂ)) z) (fun i => (x i : ℂ)) := by
      apply analyticAt_carlsonMean_comp _ analyticAt_const analyticAt_id
        (fun i => Complex.ofReal_mem_slitPlane.mpr (hx i))
        (sum_ofReal_parameters_ne_neg_nat hb)
      intro _
      change carlsonR (t : ℂ) (fun i => (b i : ℂ)) (fun i => (x i : ℂ)) ∈ Complex.slitPlane
      rw [← ofReal_carlsonRReal t hb hx]
      exact Complex.ofReal_mem_slitPlane.mpr (carlsonRReal_pos t hb hx)
    have hc : Continuous (fun y : ι → ℝ => fun i => (y i : ℂ)) := by fun_prop
    exact (Complex.continuous_re.continuousAt.comp
      (ha.continuousAt.comp hc.continuousAt)).continuousWithinAt
  apply h.congr
  intro x hx
  simp only [← ofReal_carlsonMeanReal t hb hx, Complex.ofReal_re]

end Carlson
