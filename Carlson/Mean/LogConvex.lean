/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Mean.StrictOrder

/-!
# Log-convexity in the order

The logarithm of the real R-average is convex on the whole real line, and strictly
convex when the positive nodes are nonconstant. The proof applies exponential
convexity to normalized power kernels; the equality case reduces to almost-sure
constancy of the affine form under a positive Dirichlet law.

## References

* B. C. Carlson, *A hypergeometric mean value*, Proc. AMS 16 (1965), Theorem 4.
-/

open MeasureTheory ProbabilityTheory Set
@[expose] public noncomputable section
namespace Carlson
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A shifted exponential of the logarithmic affine form is an integrable power kernel. -/
private theorem integrable_exp_log_affine (t d : ℝ) {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    Integrable (fun u => Real.exp (t * Real.log (∑ i, u i * x i) - d)) (dirichletMeasure b) := by
  apply ((integrable_carlsonRReal t hb hx).div_const (Real.exp d)).congr
  filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
  rw [Real.exp_sub, Real.rpow_def_of_pos (dirichlet_affine_mem (convex_Ioi 0) hx hu), mul_comm]

omit [Nonempty ι] in
/-- Integrating a shifted exponential gives the corresponding normalized R-average. -/
private theorem integral_exp_log_affine (t d : ℝ) {b x : ι → ℝ}
    (hx : ∀ i, 0 < x i) :
    (∫ u, Real.exp (t * Real.log (∑ i, u i * x i) - d) ∂dirichletMeasure b) =
      carlsonRReal t b x / Real.exp d := by
  unfold carlsonRReal
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
  rw [Real.exp_sub, Real.rpow_def_of_pos (dirichlet_affine_mem (convex_Ioi 0) hx hu), mul_comm]

/-- Log-convexity of R on the entire real order axis. -/
theorem convexOn_log_carlsonRReal {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    ConvexOn ℝ univ (fun t : ℝ => Real.log (carlsonRReal t b x)) := by
  refine ⟨convex_univ, ?_⟩
  intro s _ t _ a c ha hc hac
  let F (v : ℝ) (u : ι → ℝ) := v * Real.log (∑ i, u i * x i) - Real.log (carlsonRReal v b x)
  have hi v := integrable_exp_log_affine v (Real.log (carlsonRReal v b x)) hb hx
  have he v : (∫ u, Real.exp (F v u) ∂dirichletMeasure b) = 1 := by
    rw [integral_exp_log_affine _ _ hx, Real.exp_log (carlsonRReal_pos v hb hx),
      div_self (carlsonRReal_pos v hb hx).ne']
  have hform u : a * F s u + c * F t u =
      (a * s + c * t) * Real.log (∑ i, u i * x i) -
        (a * Real.log (carlsonRReal s b x) + c * Real.log (carlsonRReal t b x)) := by
    dsimp [F]; ring
  have hk : Integrable (fun u => Real.exp (a * F s u + c * F t u)) (dirichletMeasure b) := by
    simp_rw [hform]
    exact integrable_exp_log_affine _ _ hb hx
  have hle : ∀ᵐ u ∂dirichletMeasure b,
      Real.exp (a * F s u + c * F t u) ≤ a * Real.exp (F s u) + c * Real.exp (F t u) :=
    Filter.Eventually.of_forall fun u => convexOn_exp.2 (mem_univ _) (mem_univ _) ha hc hac
  have h := integral_mono_ae hk (((hi s).const_mul a).add ((hi t).const_mul c)) hle
  simp only [Pi.add_apply] at h
  rw [integral_add ((hi s).const_mul a) ((hi t).const_mul c), integral_const_mul,
    integral_const_mul, he s, he t, mul_one, mul_one, hac] at h
  simp_rw [hform] at h
  rw [integral_exp_log_affine _ _ hx, div_le_one (Real.exp_pos _)] at h
  have hlog := Real.log_le_log (carlsonRReal_pos _ hb hx) h
  simpa only [Real.log_exp, smul_eq_mul] using hlog

/-- Log-convexity is strict for nonconstant positive nodes. -/
theorem strictConvexOn_log_carlsonRReal {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    StrictConvexOn ℝ univ (fun t : ℝ => Real.log (carlsonRReal t b x)) := by
  refine ⟨convex_univ, ?_⟩
  intro s _ t _ hst a c ha hc hac
  apply lt_of_le_of_ne ((convexOn_log_carlsonRReal hb hx).2 (mem_univ _) (mem_univ _) ha.le hc.le hac)
  intro heq
  simp only [smul_eq_mul] at heq
  let F (v : ℝ) (u : ι → ℝ) := v * Real.log (∑ i, u i * x i) - Real.log (carlsonRReal v b x)
  have hi v := integrable_exp_log_affine v (Real.log (carlsonRReal v b x)) hb hx
  have he v : (∫ u, Real.exp (F v u) ∂dirichletMeasure b) = 1 := by
    rw [integral_exp_log_affine _ _ hx, Real.exp_log (carlsonRReal_pos v hb hx),
      div_self (carlsonRReal_pos v hb hx).ne']
  have hform u : a * F s u + c * F t u =
      (a * s + c * t) * Real.log (∑ i, u i * x i) -
        (a * Real.log (carlsonRReal s b x) + c * Real.log (carlsonRReal t b x)) := by
    dsimp [F]; ring
  have hk : Integrable (fun u => Real.exp (a * F s u + c * F t u)) (dirichletMeasure b) := by
    simp_rw [hform]
    exact integrable_exp_log_affine _ _ hb hx
  have hle : ∀ᵐ u ∂dirichletMeasure b,
      Real.exp (a * F s u + c * F t u) ≤ a * Real.exp (F s u) + c * Real.exp (F t u) :=
    Filter.Eventually.of_forall fun u => convexOn_exp.2 (mem_univ _) (mem_univ _) ha.le hc.le hac
  have heint : (∫ u, Real.exp (a * F s u + c * F t u) ∂dirichletMeasure b) =
      ∫ u, (a * Real.exp (F s u) + c * Real.exp (F t u)) ∂dirichletMeasure b := by
    rw [integral_add ((hi s).const_mul a) ((hi t).const_mul c), integral_const_mul,
      integral_const_mul, he s, he t, mul_one, mul_one, hac]
    simp_rw [hform]
    rw [integral_exp_log_affine _ _ hx, ← heq,
      Real.exp_log (carlsonRReal_pos _ hb hx), div_self (carlsonRReal_pos _ hb hx).ne']
  have heae := (integral_eq_iff_of_ae_le hk (((hi s).const_mul a).add ((hi t).const_mul c)) hle).mp heint
  apply not_ae_dirichlet_affine_comp_eq_const hb (convex_Ioi 0) hx hne
    (f := fun y => (s - t) * Real.log y)
    (fun y hy z hz he => Real.log_injOn_pos hy hz (mul_left_cancel₀ (sub_ne_zero.mpr hst) he))
    (Real.log (carlsonRReal s b x) - Real.log (carlsonRReal t b x))
  filter_upwards [heae] with u hu
  have he : F s u = F t u := by
    by_contra h
    exact (strictConvexOn_exp.2 (mem_univ _) (mem_univ _) h ha hc hac).ne hu
  dsimp [F] at he
  nlinarith

/-- Carlson's original formulation: order times log mean is convex. -/
theorem convexOn_mul_log_carlsonMeanReal {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) :
    ConvexOn ℝ univ (fun t : ℝ => t * Real.log (carlsonMeanReal t b x)) := by
  convert convexOn_log_carlsonRReal hb hx using 1
  ext t
  by_cases ht : t = 0
  · simp [ht, carlsonRReal_zero hb]
  · simp [carlsonMeanReal, ht, Real.log_exp, mul_div_cancel₀ _ ht]

/-- The order-times-log-mean formulation is strictly convex for nonconstant nodes. -/
theorem strictConvexOn_mul_log_carlsonMeanReal {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    StrictConvexOn ℝ univ (fun t : ℝ => t * Real.log (carlsonMeanReal t b x)) := by
  convert strictConvexOn_log_carlsonRReal hb hx hne using 1
  ext t
  by_cases ht : t = 0
  · simp [ht, carlsonRReal_zero hb]
  · simp [carlsonMeanReal, ht, Real.log_exp, mul_div_cancel₀ _ ht]

end Carlson
