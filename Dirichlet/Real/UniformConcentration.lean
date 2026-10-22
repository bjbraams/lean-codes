/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Dirichlet.Real.Variance
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Concentration estimates independent of the number of nodes

An affine Dirichlet combination of nodes in a fixed compact interval has variance
bounded by the squared interval width divided by one plus the total parameter.
This gives convergence of smooth scalar averages even when the finite index type
and normalized weights vary. It proves the growing-family mechanism in
Brenner–Carlson (1987), Theorem 2, without their partition expansion.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal
@[expose] public noncomputable section
namespace ProbabilityTheory
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The variance of an affine Dirichlet combination is its weighted node variance
 divided by one plus the total parameter. -/
theorem integral_dirichletMeasure_affine_sub_mean_sq {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) (x : ι → ℝ) :
    (∫ u, ((∑ i, u i * x i) - ∑ i, (b i / ∑ j, b j) * x i) ^ 2
      ∂dirichletMeasure b) =
      ((∑ i, (b i / ∑ j, b j) * x i ^ 2) -
        (∑ i, (b i / ∑ j, b j) * x i) ^ 2) / ((∑ i, b i) + 1) := by
  let c := ∑ i, b i
  let A := ∑ i, (b i / c) * x i
  have hc : 0 < c := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have hA : A = (∑ i, b i * x i) / c := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hcenter : (∑ i, b i * (x i - A)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    change (∑ i, b i * x i) - c * A = 0
    rw [hA, mul_div_cancel₀ _ hc.ne']
    ring
  have he : (∫ u, ((∑ i, u i * x i) - A) ^ 2 ∂dirichletMeasure b) =
      ∫ u, (∑ i, u i * (x i - A)) ^ 2 ∂dirichletMeasure b := by
    apply integral_congr_ae
    filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hu.2, one_mul]
  change (∫ u, ((∑ i, u i * x i) - A) ^ 2 ∂dirichletMeasure b) = _
  rw [he, integral_dirichletMeasure_affine_sq hb, hcenter, zero_pow (by decide), zero_add]
  have hsum : (∑ i, b i * (x i - A) ^ 2) =
      (∑ i, b i * x i ^ 2) - 2 * A * (∑ i, b i * x i) + A ^ 2 * c := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, c]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (∑ i, b i * (x i - A) ^ 2) / (c * (c + 1)) = _
  rw [hsum]
  have hsum2 : (∑ i, (b i / c) * x i ^ 2) = (∑ i, b i * x i ^ 2) / c := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change _ = ((∑ i, (b i / c) * x i ^ 2) - A ^ 2) / (c + 1)
  rw [hsum2, hA]
  field_simp [hc.ne', (show c + 1 ≠ 0 by positivity)]
  ring

/-- A dimension-independent bound for the mean absolute deviation of a Dirichlet
 affine combination of nodes bounded in absolute value by `B`. -/
theorem integral_dirichletMeasure_abs_affine_sub_mean_le {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) {B : ℝ} (hx : ∀ i, |x i| ≤ B) :
    (∫ u, |(∑ i, u i * x i) - ∑ i, (b i / ∑ j, b j) * x i|
      ∂dirichletMeasure b) ≤ Real.sqrt (B ^ 2 / ((∑ i, b i) + 1)) := by
  let := isProbabilityMeasure_dirichletMeasure hb
  have hc : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have hw : ∑ i, b i / ∑ j, b j = 1 := by rw [← Finset.sum_div, div_self hc.ne']
  have hB : 0 ≤ B := (abs_nonneg _).trans (hx (Classical.arbitrary ι))
  have hi : MemLp (fun u => (∑ i, u i * x i) - ∑ i, (b i / ∑ j, b j) * x i)
      2 (dirichletMeasure b) := by
    exact (memLp_finsetSum _ (fun i _ =>
      (memLp_dirichletMeasure_coordinate hb i 2).mul_const (x i))).sub (memLp_const _)
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr
    ⟨by norm_num, by norm_num⟩
  have h := integral_mul_norm_le_Lp_mul_Lq hpq (by simpa using hi)
    (memLp_const (1 : ℝ) : MemLp (fun _ : ι → ℝ => (1 : ℝ)) (ENNReal.ofReal 2)
      (dirichletMeasure b))
  have h' : (∫ u, |(∑ i, u i * x i) - ∑ i, (b i / ∑ j, b j) * x i|
      ∂dirichletMeasure b) ≤ Real.sqrt
        ((∑ i, (b i / ∑ j, b j) * x i ^ 2 -
          (∑ i, (b i / ∑ j, b j) * x i) ^ 2) / ((∑ i, b i) + 1)) := by
    simpa only [norm_one, mul_one, Real.norm_eq_abs, Real.rpow_two, sq_abs,
      integral_const, probReal_univ, smul_eq_mul, one_mul, one_pow, Real.one_rpow,
      integral_dirichletMeasure_affine_sub_mean_sq hb, ← Real.sqrt_eq_rpow,
      Real.sqrt_one, mul_one] using h
  apply h'.trans
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ i, (b i / ∑ j, b j) * x i ^ 2 := sub_le_self _ (sq_nonneg _)
    _ ≤ ∑ i, (b i / ∑ j, b j) * B ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (div_pos (hb i) hc).le
      nlinarith [hx i, abs_nonneg (x i), sq_abs (x i)]
    _ = B ^ 2 := by rw [← Finset.sum_mul, hw, one_mul]

/-- A scalar Lipschitz kernel has a dimension-independent Dirichlet concentration
 bound. The parameter sum, rather than the number of nodes, controls the error. -/
theorem integral_dirichletMeasure_affine_error_le {b x : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) {a A B : ℝ} (hx : ∀ i, x i ∈ Icc a A)
    (hB : ∀ i, |x i| ≤ B) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Icc a A)) :
    |(∫ u, f (∑ i, u i * x i) ∂dirichletMeasure b) -
      f (∑ i, (b i / ∑ j, b j) * x i)| ≤
        K * Real.sqrt (B ^ 2 / ((∑ i, b i) + 1)) := by
  let := isProbabilityMeasure_dirichletMeasure hb
  have hc : 0 < ∑ i, b i := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have hw : ∑ i, b i / ∑ j, b j = 1 := by rw [← Finset.sum_div, div_self hc.ne']
  have hm := dirichlet_affine_mem (convex_Icc a A) hx
    (show (fun i => b i / ∑ j, b j) ∈ Convexity.StdSimplex.coordinateSet ℝ ι from
      ⟨fun i => (div_pos (hb i) hc).le, hw⟩)
  have hi := integrable_dirichletMeasure_comp_affine hb (convex_Icc a A) hx hf.continuousOn
  have hd : Integrable (fun u => |(∑ i, u i * x i) - ∑ i, (b i / ∑ j, b j) * x i|)
      (dirichletMeasure b) := integrable_dirichletMeasure_of_continuousOn hb (by fun_prop)
  have hdiff : (∫ u : ι → ℝ, f (∑ i, u i * x i) -
      f (∑ i, (b i / ∑ j, b j) * x i) ∂dirichletMeasure b) =
      (∫ u, f (∑ i, u i * x i) ∂dirichletMeasure b) -
        f (∑ i, (b i / ∑ j, b j) * x i) := by
    rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [← hdiff]
  calc
    _ ≤ ∫ u : ι → ℝ, |f (∑ i, u i * x i) -
        f (∑ i, (b i / ∑ j, b j) * x i)| ∂dirichletMeasure b :=
      abs_integral_le_integral_abs
    _ ≤ ∫ u : ι → ℝ, (K : ℝ) * |(∑ i, u i * x i) -
        ∑ i, (b i / ∑ j, b j) * x i| ∂dirichletMeasure b := by
      apply integral_mono_ae (hi.sub (integrable_const _)).abs (hd.const_mul (K : ℝ))
      filter_upwards [ae_mem_stdSimplex_dirichletMeasure b] with u hu
      simpa only [Real.dist_eq, Pi.sub_apply] using
        hf.dist_le_mul _ (dirichlet_affine_mem (convex_Icc a A) hx hu) _ hm
    _ = K * ∫ u : ι → ℝ, |(∑ i, u i * x i) -
        ∑ i, (b i / ∑ j, b j) * x i| ∂dirichletMeasure b := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_dirichletMeasure_abs_affine_sub_mean_le hb hB) K.coe_nonneg

/-- Smooth scalar Dirichlet averages converge along arbitrary growing finite
families when the parameter mass diverges and the weighted node means converge. -/
theorem tendsto_integral_dirichletMeasure_affine_varying
    {α : Type*} {l : Filter α} {κ : α → Type*} [∀ n, Fintype (κ n)] [∀ n, Nonempty (κ n)]
    {b x : (n : α) → κ n → ℝ} (hb : ∀ n i, 0 < b n i)
    {a A μ : ℝ} (hx : ∀ n i, x n i ∈ Icc a A)
    (hc : Tendsto (fun n => ∑ i, b n i) l atTop)
    (hm : Tendsto (fun n => ∑ i, (b n i / ∑ j, b n j) * x n i) l (𝓝 μ))
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Icc a A)) (hμ : μ ∈ Icc a A) :
    Tendsto (fun n => ∫ u, f (∑ i, u i * x n i) ∂dirichletMeasure (b n)) l (𝓝 (f μ)) := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by norm_num)
    (convex_Icc a A) isCompact_Icc
  have hB n i : |x n i| ≤ max |a| |A| := by
    exact abs_le_max_abs_abs (hx n i).1 (hx n i).2
  have ht : Tendsto (fun n => (max |a| |A|) ^ 2 / ((∑ i, b n i) + 1)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hc.atTop_add tendsto_const_nhds)
  have hzero : Tendsto (fun n =>
      |(∫ u, f (∑ i, u i * x n i) ∂dirichletMeasure (b n)) -
        f (∑ i, (b n i / ∑ j, b n j) * x n i)|) l (𝓝 0) := by
    apply squeeze_zero (fun n => abs_nonneg _)
      (fun n => integral_dirichletMeasure_affine_error_le (hb n) (hx n) (hB n) hK)
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp ht).const_mul (K : ℝ)
  have hmean : Tendsto (fun n => f (∑ i, (b n i / ∑ j, b n j) * x n i)) l (𝓝 (f μ)) := by
    apply hf.continuousOn.continuousWithinAt hμ |>.tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr ⟨hm, Eventually.of_forall ?_⟩
    intro n
    have hs : 0 < ∑ i, b n i :=
      Finset.sum_pos (fun i _ => hb n i) Finset.univ_nonempty
    apply dirichlet_affine_mem (convex_Icc a A) (hx n)
    exact ⟨fun i => (div_pos (hb n i) hs).le, by rw [← Finset.sum_div, div_self hs.ne']⟩
  have hd : Tendsto (fun n => (∫ u, f (∑ i, u i * x n i)
      ∂dirichletMeasure (b n)) - f (∑ i, (b n i / ∑ j, b n j) * x n i)) l (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (by simpa only [Real.norm_eq_abs] using hzero)
  simpa only [zero_add, sub_add_cancel] using hd.add hmean

end ProbabilityTheory
