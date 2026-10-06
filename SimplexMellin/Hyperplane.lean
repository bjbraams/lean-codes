/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.LogRatio
public import SimplexMellin.PaleyWiener
public import ToMathlib.Analysis.Fourier.PaleyWiener
public import Mathlib.Analysis.Fourier.Inversion
public import SeveralComplexVariables.ParametricIntegral
public import SeveralComplexVariables.RealUniqueness

/-!
# Paley–Wiener on the hyperplanes `∑ b i = s`

In log-ratio coordinates `w` relative to an index `i₀` (`SimplexMellin.LogRatio`) the simplex
Mellin transform restricted to a hyperplane `∑ i, b i = s` is a Fourier–Laplace transform in
`card ι - 1` variables:

`S_g(b) = ∫ e^(⟨b', w⟩) Z(w)^(-s) g(u(w)) dw`,   `b' = (b j)_(j ≠ i₀)`.

Combined with the classical Paley–Wiener theorem (`paleyWiener`) this gives a Paley–Wiener
description of the hyperplane restrictions. Every entire function of `b'` with Paley–Wiener
bounds is the restriction of the simplex Mellin transform of a kernel that is continuous on the
simplex, smooth near it and vanishing near its faces. Conversely, for a smooth kernel vanishing
near the faces the restriction has Paley–Wiener bounds, and the restriction to one hyperplane
determines a continuous kernel vanishing near the faces.

## Main results

* `Dirichlet.analyticOnNhd_integral_cexp_mul`: Laplace transforms of continuous compactly supported
  functions are entire.
* `Dirichlet.integral_monomial_mul_eq_integral_logRatio`: the hyperplane formula.
* `Dirichlet.smoothNearStdSimplex_logRatioKernel`: the constructed kernel is smooth near the
  simplex.
* `Dirichlet.exists_kernel_of_paleyWiener`: **sufficiency**.
* `Dirichlet.integral_hyperplane_eq_fourierLaplace`, `Dirichlet.norm_integral_hyperplane_le`:
  **necessity**.
* `Dirichlet.eqOn_of_integral_hyperplane_eq`: **injectivity** on one hyperplane.
-/

open Complex MeasureTheory Set Filter
open scoped Topology FourierTransform Real ContDiff

@[expose] public noncomputable section

namespace Dirichlet

/-- **Laplace transforms are entire.** For `ψ` continuous with compact support on `m → ℝ`,
`z ↦ ∫ e^(∑ j, z j w j) ψ(w) dw` is entire. -/
theorem analyticOnNhd_integral_cexp_mul {m : Type*} [Fintype m] {ψ : (m → ℝ) → ℂ}
    (hψ : Continuous ψ) (hsupp : HasCompactSupport ψ) :
    AnalyticOnNhd ℂ (fun z : m → ℂ => ∫ w, Complex.exp (∑ j, z j * w j) * ψ w) univ := by
  obtain ⟨R, hR⟩ := hsupp.isCompact.isBounded.subset_closedBall 0
  set L : (m → ℝ) → (m → ℂ) →L[ℂ] ℂ := fun w => ∑ j, (w j : ℂ) • ContinuousLinearMap.proj j
  have hL : ∀ w z, L w z = ∑ j, z j * w j := fun w z => by simp [L, mul_comm]
  refine analyticOnNhd_integral_of_dominated_of_fderiv_le isOpen_univ fun z₀ _ => ?_
  set M : ℝ := Real.exp ((‖z₀‖ + 1) * (Fintype.card m * |R|)) * (Fintype.card m * |R|)
  refine ⟨Metric.ball z₀ 1, fun w => M * ‖ψ w‖,
    fun z w => (Complex.exp (∑ j, z j * w j) * ψ w) • L w,
    Metric.ball_mem_nhds _ one_pos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Eventually.of_forall fun z =>
      (Continuous.mul (by fun_prop) hψ).aestronglyMeasurable
  · exact (Continuous.mul (by fun_prop) hψ).integrable_of_hasCompactSupport (hsupp.mul_left)
  · refine Continuous.aestronglyMeasurable ?_
    refine Continuous.smul (Continuous.mul (by fun_prop) hψ) ?_
    exact continuous_finsetSum _ fun j _ => (continuous_ofReal.comp (continuous_apply j)).smul
      continuous_const
  · refine Eventually.of_forall fun w z hz => ?_
    by_cases hw : w ∈ tsupport ψ
    · have hwR : ‖w‖ ≤ |R| := (mem_closedBall_zero_iff.mp (hR hw)).trans (le_abs_self R)
      have hwj : ∀ j, |w j| ≤ |R| := fun j => (norm_le_pi_norm w j).trans hwR
      have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
        have := norm_le_of_mem_closedBall (Metric.ball_subset_closedBall hz)
        linarith
      rw [norm_smul, norm_mul, Complex.norm_exp]
      have hre : (∑ j, z j * w j).re ≤ (‖z₀‖ + 1) * (Fintype.card m * |R|) := by
        rw [re_sum]
        calc ∑ j, (z j * w j).re ≤ ∑ _j : m, (‖z₀‖ + 1) * |R| := Finset.sum_le_sum fun j _ => by
              simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
              calc (z j).re * w j ≤ |(z j).re * w j| := le_abs_self _
                _ = |(z j).re| * |w j| := abs_mul _ _
                _ ≤ (‖z₀‖ + 1) * |R| := mul_le_mul ((abs_re_le_norm _).trans
                    ((norm_le_pi_norm z j).trans hz')) (hwj j) (abs_nonneg _) (by positivity)
          _ = (‖z₀‖ + 1) * (Fintype.card m * |R|) := by simp; ring
      have hLw : ‖L w‖ ≤ Fintype.card m * |R| := by
        refine (norm_sum_le _ _).trans ?_
        calc ∑ j, ‖(w j : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => ℂ) j‖
            ≤ ∑ _j : m, |R| := Finset.sum_le_sum fun j _ => by
              rw [norm_smul, norm_real, Real.norm_eq_abs]
              calc |w j| * ‖ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => ℂ) j‖
                  ≤ |R| * 1 := mul_le_mul (hwj j) (ContinuousLinearMap.opNorm_le_bound _
                    zero_le_one fun v => by simpa using norm_le_pi_norm v j) (norm_nonneg _)
                    (abs_nonneg _)
                _ = |R| := mul_one _
          _ = Fintype.card m * |R| := by simp
      calc Real.exp (∑ j, z j * w j).re * ‖ψ w‖ * ‖L w‖
          ≤ Real.exp ((‖z₀‖ + 1) * (Fintype.card m * |R|)) * ‖ψ w‖ *
              (Fintype.card m * |R|) := by gcongr
        _ = M * ‖ψ w‖ := by simp only [M]; ring
    · have h0 : ψ w = 0 := image_eq_zero_of_notMem_tsupport hw
      simp [h0]
  · exact hψ.norm.integrable_of_hasCompactSupport hsupp.norm |>.const_mul M
  · refine Eventually.of_forall fun w z _ => ?_
    have h1 : HasFDerivAt (fun z : m → ℂ => ∑ j, z j * w j) (L w) z := by
      have : (fun z : m → ℂ => ∑ j, z j * w j) = L w := funext fun z => (hL w z).symm
      rw [this]
      exact (L w).hasFDerivAt
    have h2 := (h1.cexp).mul_const (ψ w)
    convert h2 using 1
    ext v
    simp only [smul_apply, smul_eq_mul]
    ring

variable {ι : Type*} [Fintype ι]

open scoped Classical

/-- The parameter vector on the hyperplane `∑ i, b i = s` with coordinates `b' j = b j`
(`j ≠ i₀`). -/
def hyperplaneParam (i₀ : ι) (s : ℂ) (b' : {j : ι // j ≠ i₀} → ℂ) : ι → ℂ :=
  fun i => if h : i = i₀ then s - ∑ j, b' j else b' ⟨i, h⟩

/-- The hyperplane parameters sum to `s`. -/
theorem sum_hyperplaneParam (i₀ : ι) (s : ℂ) (b' : {j : ι // j ≠ i₀} → ℂ) :
    ∑ i, hyperplaneParam i₀ s b' i = s := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
  have h : ∀ j : {j : ι // j ≠ i₀}, hyperplaneParam i₀ s b' j = b' j := fun j => by
    simp [hyperplaneParam, j.2]
  simp_rw [h]
  simp only [hyperplaneParam, dite_true, sub_add_cancel]

/-- A kernel vanishing near the faces, multiplied by a complex monomial, stays continuous on the
simplex. -/
theorem continuousOn_monomial_mul_of_vanish {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i)
    (c : ι → ℂ) :
    ContinuousOn (fun u => (∏ i, (u i : ℂ) ^ c i) * g u)
      (Convexity.StdSimplex.coordinateSet ℝ ι) := by
  intro u hu
  by_cases hpos : ∀ i, 0 < u i
  · refine ContinuousAt.continuousWithinAt ?_ |>.mul (hg u hu)
    refine tendsto_finsetProd _ fun i _ => ?_
    exact (ContinuousAt.cpow (continuous_ofReal.comp (continuous_apply i)).continuousAt
      continuousAt_const (ofReal_mem_slitPlane.mpr (hpos i)))
  · push Not at hpos
    obtain ⟨i, hi⟩ := hpos
    have hi0 : u i = 0 := le_antisymm hi (hu.1 i)
    have hnear : ∀ᶠ v in 𝓝[Convexity.StdSimplex.coordinateSet ℝ ι] u,
        (∏ i, (v i : ℂ) ^ c i) * g v = 0 := by
      have hev : ∀ᶠ v in 𝓝 u, v i < δ :=
        (continuous_apply i).continuousAt.eventually
          (gt_mem_nhds (show u i < δ by rw [hi0]; exact hδ))
      filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with v hv hvΔ
      by_cases hgv : g v = 0
      · simp [hgv]
      · exact absurd (hgsupp v hvΔ hgv i) (not_le.mpr hv)
    have hu0 : (∏ i, (u i : ℂ) ^ c i) * g u = 0 := by
      by_cases hgu : g u = 0
      · simp [hgu]
      · exact absurd (hgsupp u hu hgu i) (by rw [hi0]; exact not_le.mpr hδ)
    rw [ContinuousWithinAt, hu0]
    exact tendsto_nhds_of_eventually_eq hnear

/-- The coordinates of the log-ratio point are exponentials. -/
theorem logRatioPoint_eq_exp (i₀ : ι) (w : {j : ι // j ≠ i₀} → ℝ) (i : ι) :
    logRatioPoint i₀ w i = Real.exp (logRatioExt i₀ w i - Real.log (logRatioZ i₀ w)) := by
  rw [Real.exp_sub, Real.exp_log (logRatioZ_pos i₀ w)]
  simp [logRatioPoint, piExp, div_eq_inv_mul]

/-- **The hyperplane formula.** For a kernel continuous on the simplex and vanishing near its
faces, the simplex Mellin transform on the hyperplane `∑ i, b i = s` is the Laplace transform in
log-ratio coordinates of `Z(w)^(-s) g(u(w))`. -/
theorem integral_monomial_mul_eq_integral_logRatio (i₀ : ι) {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i)
    (s : ℂ) (b' : {j : ι // j ≠ i₀} → ℂ) :
    ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι,
        (∏ i, (u i : ℂ) ^ (hyperplaneParam i₀ s b' i - 1)) * g u ∂Measure.stdSimplexMeasure =
      ∫ w : {j : ι // j ≠ i₀} → ℝ, Complex.exp (∑ j, b' j * w j) *
        ((logRatioZ i₀ w : ℂ) ^ (-s) * g (logRatioPoint i₀ w)) := by
  rw [integral_stdSimplex_eq_integral_logRatio i₀
    (continuousOn_monomial_mul_of_vanish hg hδ hgsupp _)]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  set b := hyperplaneParam i₀ s b'
  set Z := logRatioZ i₀ w
  have hZ := logRatioZ_pos i₀ w
  have hu : ∀ i, (logRatioPoint i₀ w i : ℂ) =
      ((Real.exp (logRatioExt i₀ w i - Real.log Z) : ℝ) : ℂ) := fun i => by
    rw [logRatioPoint_eq_exp]
  have hprod : ((∏ i, logRatioPoint i₀ w i : ℝ) : ℂ) *
      ∏ i, (logRatioPoint i₀ w i : ℂ) ^ (b i - 1) =
      Complex.exp (∑ i, b i * (logRatioExt i₀ w i - Real.log Z)) := by
    rw [ofReal_prod, ← Finset.prod_mul_distrib, Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hu i, ofReal_exp_cpow, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only
  rw [← mul_assoc, hprod]
  have hsplit : ∑ i, b i * (logRatioExt i₀ w i - Real.log Z) =
      ∑ j, b' j * w j + (-s) * Real.log Z := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, b, sum_hyperplaneParam]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
    simp only [hyperplaneParam, logRatioExt, dite_true, ofReal_zero, mul_zero, zero_add]
    have : ∀ j : {j : ι // j ≠ i₀}, (if h : (j : ι) = i₀ then s - ∑ j, b' j else b' ⟨j, h⟩) *
        ((if h : (j : ι) = i₀ then (0 : ℝ) else w ⟨j, h⟩ : ℝ) : ℂ) = b' j * w j := fun j => by
      simp [j.2]
    simp_rw [this]
    ring
  rw [hsplit, Complex.exp_add, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hZ.ne'),
    ← ofReal_log hZ.le]
  simp only [Z]
  ring_nf

/-- Log-ratio coordinates of a point of the open orthant relative to `i₀`. -/
def logRatioCoords (i₀ : ι) (x : ι → ℝ) : {j : ι // j ≠ i₀} → ℝ :=
  fun j => Real.log (x j / x i₀)

/-- Log-ratio coordinates invert `logRatioPoint`. -/
theorem logRatioCoords_logRatioPoint (i₀ : ι) (w : {j : ι // j ≠ i₀} → ℝ) :
    logRatioCoords i₀ (logRatioPoint i₀ w) = w := by
  funext j
  simp only [logRatioCoords, logRatioPoint_eq_exp, ← Real.exp_sub, Real.log_exp]
  simp [logRatioExt, j.2]

/-- The kernel attached to a function `ψ` of the log-ratio coordinates and an exponent `s`:
`g(u) = Z(w(u))^s ψ(w(u))` at points with positive coordinates, and `0` elsewhere. -/
def logRatioKernel (i₀ : ι) (s : ℂ) (ψ : ({j : ι // j ≠ i₀} → ℝ) → ℂ) (u : ι → ℝ) : ℂ :=
  if ∀ i, 0 < u i then (logRatioZ i₀ (logRatioCoords i₀ u) : ℂ) ^ s * ψ (logRatioCoords i₀ u)
  else 0

/-- The kernel at a log-ratio point. -/
theorem logRatioKernel_logRatioPoint (i₀ : ι) (s : ℂ) (ψ : ({j : ι // j ≠ i₀} → ℝ) → ℂ)
    (w : {j : ι // j ≠ i₀} → ℝ) :
    logRatioKernel i₀ s ψ (logRatioPoint i₀ w) = (logRatioZ i₀ w : ℂ) ^ s * ψ w := by
  have hpos : ∀ i, 0 < logRatioPoint i₀ w i := fun i => by
    rw [logRatioPoint_eq_exp]; exact Real.exp_pos _
  simp [logRatioKernel, hpos, logRatioCoords_logRatioPoint]

/-- If `ψ` vanishes outside the box `|w j| ≤ ρ j`, the kernel vanishes at the points of the
simplex with a coordinate below `δ = (1 + ∑ e^(ρ j))⁻¹ e^(-∑ ρ j)`. -/
theorem logRatioKernel_vanish (i₀ : ι) (s : ℂ) {ψ : ({j : ι // j ≠ i₀} → ℝ) → ℂ}
    {ρ : {j : ι // j ≠ i₀} → ℝ} (hρ : ∀ j, 0 ≤ ρ j)
    (hψ : ∀ w, ψ w ≠ 0 → ∀ j, |w j| ≤ ρ j) :
    ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, logRatioKernel i₀ s ψ u ≠ 0 →
      ∀ i, (1 + ∑ j, Real.exp (ρ j))⁻¹ * Real.exp (-∑ j, ρ j) ≤ u i := by
  intro u hu hne i
  have hpos : ∀ i, 0 < u i := by
    by_contra h
    exact hne (by simp [logRatioKernel, h])
  have hψu : ψ (logRatioCoords i₀ u) ≠ 0 := by
    intro h
    exact hne (by simp [logRatioKernel, hpos, h])
  have hbox := hψ _ hψu
  -- Each ratio `u j / u i₀` lies in `[e^(-ρ j), e^(ρ j)]`.
  have hratio : ∀ j : {j : ι // j ≠ i₀}, Real.exp (-ρ j) ≤ u j / u i₀ ∧
      u j / u i₀ ≤ Real.exp (ρ j) := by
    intro j
    have h := abs_le.mp (hbox j)
    have hq : 0 < u j / u i₀ := div_pos (hpos j) (hpos i₀)
    simp only [logRatioCoords] at h
    constructor
    · rw [← Real.exp_log hq]; exact Real.exp_le_exp.mpr h.1
    · rw [← Real.exp_log hq]; exact Real.exp_le_exp.mpr h.2
  -- The coordinate `u i₀` is at least `(1 + ∑ e^(ρ j))⁻¹`.
  set D := 1 + ∑ j, Real.exp (ρ j)
  have hD : 0 < D := by positivity
  have hsum : ∑ i, u i = 1 := hu.2
  have hi₀ : D⁻¹ ≤ u i₀ := by
    have h1 : 1 ≤ u i₀ * D := by
      calc 1 = ∑ i, u i := hsum.symm
        _ = u i₀ + ∑ j : {j : ι // j ≠ i₀}, u j := Fintype.sum_eq_add_sum_subtype_ne _ i₀
        _ ≤ u i₀ + ∑ j : {j : ι // j ≠ i₀}, u i₀ * Real.exp (ρ j) := by
            gcongr with j
            have := (hratio j).2
            rw [div_le_iff₀ (hpos i₀)] at this
            linarith
        _ = u i₀ * D := by simp only [D, mul_add, mul_one, Finset.mul_sum]
    rw [inv_le_iff_one_le_mul₀ hD]
    linarith
  have hsumρ : 0 ≤ ∑ j, ρ j := Finset.sum_nonneg fun j _ => hρ j
  have hexp1 : Real.exp (-∑ j, ρ j) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  by_cases hi : i = i₀
  · subst hi
    calc D⁻¹ * Real.exp (-∑ j, ρ j) ≤ D⁻¹ * 1 := by gcongr
      _ ≤ u i := by rw [mul_one]; exact hi₀
  · set j : {j : ι // j ≠ i₀} := ⟨i, hi⟩
    have hj : Real.exp (-∑ j, ρ j) ≤ Real.exp (-ρ j) := by
      apply Real.exp_le_exp.mpr
      have := Finset.single_le_sum (f := ρ) (fun j _ => hρ j) (Finset.mem_univ j)
      linarith
    have hu_j : u i₀ * Real.exp (-ρ j) ≤ u i := by
      have := (hratio j).1
      rw [le_div_iff₀ (hpos i₀)] at this
      linarith
    calc D⁻¹ * Real.exp (-∑ j, ρ j) ≤ u i₀ * Real.exp (-ρ j) :=
          mul_le_mul hi₀ hj (by positivity) (hpos i₀).le
      _ ≤ u i := hu_j

/-- The kernel is continuous on the simplex when `ψ` is continuous and vanishes outside a box. -/
theorem continuousOn_logRatioKernel (i₀ : ι) (s : ℂ) {ψ : ({j : ι // j ≠ i₀} → ℝ) → ℂ}
    (hψc : Continuous ψ) {ρ : {j : ι // j ≠ i₀} → ℝ} (hρ : ∀ j, 0 ≤ ρ j)
    (hψ : ∀ w, ψ w ≠ 0 → ∀ j, |w j| ≤ ρ j) :
    ContinuousOn (logRatioKernel i₀ s ψ) (Convexity.StdSimplex.coordinateSet ℝ ι) := by
  set δ := (1 + ∑ j, Real.exp (ρ j))⁻¹ * Real.exp (-∑ j, ρ j)
  have hδ : 0 < δ := mul_pos (inv_pos.mpr (add_pos_of_pos_of_nonneg one_pos
    (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le))) (Real.exp_pos _)
  have hvan := logRatioKernel_vanish i₀ s hρ hψ
  intro u hu
  by_cases hpos : ∀ i, 0 < u i
  · -- Near a point with positive coordinates the kernel is given by its formula.
    have hopen : IsOpen {x : ι → ℝ | ∀ i, 0 < x i} := by
      simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
    have hcoords : ContinuousAt (logRatioCoords i₀) u := by
      refine continuousAt_pi.mpr fun j => ?_
      exact (ContinuousAt.div (f := fun y : ι → ℝ => y j) (g := fun y : ι → ℝ => y i₀)
        (continuous_apply _).continuousAt (continuous_apply _).continuousAt
        (hpos i₀).ne').log (div_pos (hpos j) (hpos i₀)).ne'
    have hZ : ContinuousAt (fun x => logRatioZ i₀ (logRatioCoords i₀ x)) u := by
      simp only [logRatioZ, piExp]
      refine tendsto_finsetSum _ fun i _ => ?_
      refine Real.continuous_exp.continuousAt.comp ?_
      by_cases hi : i = i₀
      · subst hi; simp [logRatioExt]; exact continuousAt_const
      · simp only [logRatioExt, hi, dite_false]
        exact (continuous_apply _).continuousAt.comp hcoords
    have hformula : ContinuousAt (fun x => (logRatioZ i₀ (logRatioCoords i₀ x) : ℂ) ^ s *
        ψ (logRatioCoords i₀ x)) u :=
      ((continuous_ofReal.continuousAt.comp hZ).cpow continuousAt_const
        (ofReal_mem_slitPlane.mpr (logRatioZ_pos i₀ _))).mul
        (hψc.continuousAt.comp hcoords)
    refine (hformula.congr ?_).continuousWithinAt
    filter_upwards [hopen.mem_nhds hpos] with x hx
    simp [logRatioKernel, hx]
  · push Not at hpos
    obtain ⟨i, hi⟩ := hpos
    have hi0 : u i = 0 := le_antisymm hi (hu.1 i)
    have hnear : ∀ᶠ v in 𝓝[Convexity.StdSimplex.coordinateSet ℝ ι] u,
        logRatioKernel i₀ s ψ v = 0 := by
      have hev : ∀ᶠ v in 𝓝 u, v i < δ :=
        (continuous_apply i).continuousAt.eventually
          (gt_mem_nhds (show u i < δ by rw [hi0]; exact hδ))
      filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with v hv hvΔ
      by_contra hne
      exact absurd (hvan v hvΔ hne i) (not_le.mpr hv)
    have hu0 : logRatioKernel i₀ s ψ u = 0 := by
      by_contra hne
      exact absurd (hvan u hu hne i) (by rw [hi0]; exact not_le.mpr hδ)
    rw [ContinuousWithinAt, hu0]
    exact tendsto_nhds_of_eventually_eq hnear

/-! ### Smoothness of the constructed kernel -/

omit [Fintype ι] in
/-- Log-ratio coordinates are invariant under positive scaling. -/
theorem logRatioCoords_smul (i₀ : ι) {c : ℝ} (hc : 0 < c) (x : ι → ℝ) :
    logRatioCoords i₀ (c • x) = logRatioCoords i₀ x := by
  funext j
  simp only [logRatioCoords, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hc.ne']

/-- The kernel is invariant under positive scaling. -/
theorem logRatioKernel_smul (i₀ : ι) (s : ℂ) (ψ : ({j : ι // j ≠ i₀} → ℝ) → ℂ) {c : ℝ}
    (hc : 0 < c) (x : ι → ℝ) : logRatioKernel i₀ s ψ (c • x) = logRatioKernel i₀ s ψ x := by
  have hpos : (∀ i, 0 < (c • x) i) ↔ ∀ i, 0 < x i := by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact forall_congr' fun i => mul_pos_iff_of_pos_left hc
  simp only [logRatioKernel, hpos, logRatioCoords_smul i₀ hc]

/-- **Smoothness of the constructed kernel.** If `ψ` is smooth and vanishes outside a box, the
kernel `g = Z^s ψ(w(u))` is smooth on a neighborhood of the closed simplex: it is smooth on the
open orthant and vanishes identically near the boundary points of the simplex. -/
theorem smoothNearStdSimplex_logRatioKernel (i₀ : ι) (s : ℂ) {ψ : ({j : ι // j ≠ i₀} → ℝ) → ℂ}
    (hψs : ContDiff ℝ ∞ ψ) {ρ : {j : ι // j ≠ i₀} → ℝ} (hρ : ∀ j, 0 ≤ ρ j)
    (hψ : ∀ w, ψ w ≠ 0 → ∀ j, |w j| ≤ ρ j) :
    SmoothNearStdSimplex (logRatioKernel i₀ s ψ) := by
  have : Nonempty ι := ⟨i₀⟩
  set g := logRatioKernel i₀ s ψ
  set δ := (1 + ∑ j, Real.exp (ρ j))⁻¹ * Real.exp (-∑ j, ρ j)
  have hδ : 0 < δ := mul_pos (inv_pos.mpr (add_pos_of_pos_of_nonneg one_pos
    (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le))) (Real.exp_pos _)
  have hvan := logRatioKernel_vanish i₀ s hρ hψ
  have hopen : IsOpen {x : ι → ℝ | ∀ i, 0 < x i} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  -- Smoothness at every point of the simplex.
  have hat : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, ContDiffAt ℝ ∞ g u := by
    intro u hu
    by_cases hpos : ∀ i, 0 < u i
    · -- The formula is smooth on the open orthant.
      have hcoords : ContDiffAt ℝ ∞ (logRatioCoords i₀) u := by
        refine contDiffAt_pi.mpr fun j => ?_
        exact (ContDiffAt.div (f := fun x : ι → ℝ => x j) (g := fun x : ι → ℝ => x i₀)
          (contDiff_apply ℝ ℝ (j : ι)).contDiffAt (contDiff_apply ℝ ℝ i₀).contDiffAt
          (hpos i₀).ne').log (div_pos (hpos j) (hpos i₀)).ne'
      have hZ : ContDiffAt ℝ ∞ (fun x => logRatioZ i₀ (logRatioCoords i₀ x)) u := by
        simp only [logRatioZ, piExp]
        refine ContDiffAt.sum fun i _ => Real.contDiff_exp.contDiffAt.comp _ ?_
        by_cases hi : i = i₀
        · subst hi; simp only [logRatioExt, dite_true]; exact contDiffAt_const
        · simp only [logRatioExt, hi, dite_false]
          exact (contDiff_apply ℝ ℝ _).contDiffAt.comp _ hcoords
      have hZpos : 0 < logRatioZ i₀ (logRatioCoords i₀ u) := logRatioZ_pos i₀ _
      have hcpow : ContDiffAt ℝ ∞ (fun x => (logRatioZ i₀ (logRatioCoords i₀ x) : ℂ) ^ s) u := by
        have hlog : ContDiffAt ℝ ∞ (fun x => Real.log (logRatioZ i₀ (logRatioCoords i₀ x))) u :=
          hZ.log hZpos.ne'
        have hexp : ContDiffAt ℝ ∞ (fun x => Complex.exp
            (s * (Real.log (logRatioZ i₀ (logRatioCoords i₀ x)) : ℂ))) u :=
          (Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp _
            (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp _ hlog))
        refine hexp.congr_of_eventuallyEq ?_
        filter_upwards [hopen.mem_nhds hpos] with x hx
        have hZx : 0 < logRatioZ i₀ (logRatioCoords i₀ x) := logRatioZ_pos i₀ _
        rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hZx.ne'), ← ofReal_log hZx.le, mul_comm]
      refine (hcpow.mul (hψs.contDiffAt.comp _ hcoords)).congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hpos] with x hx
      simp [g, logRatioKernel, hx]
    · -- Near a boundary point the kernel vanishes identically.
      push Not at hpos
      obtain ⟨i, hi⟩ := hpos
      have hi0 : u i = 0 := le_antisymm hi (hu.1 i)
      have hsum : ∑ k, u k = 1 := hu.2
      have hnorm : ContinuousAt (fun x : ι → ℝ => (∑ k, x k)⁻¹ • x) u :=
        ((continuous_finsetSum _ fun k _ => continuous_apply k).continuousAt.inv₀
          (by rw [hsum]; exact one_ne_zero)).smul continuousAt_id
      have hev : ∀ᶠ x in 𝓝 u, ((∑ k, x k)⁻¹ • x) i < δ := by
        have h := (continuous_apply i).continuousAt.comp hnorm
        refine h.eventually (gt_mem_nhds ?_)
        simp only [Function.comp, Pi.smul_apply, smul_eq_mul, hsum, inv_one, one_mul, hi0]
        exact hδ
      refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with x hx
      by_cases hxpos : ∀ k, 0 < x k
      · have hS : 0 < ∑ k, x k := Finset.sum_pos (fun k _ => hxpos k) Finset.univ_nonempty
        have hmem := inv_sum_smul_mem_coordinateSet (ι := ι) (x := x) fun k _ => hxpos k
        show logRatioKernel i₀ s ψ x = 0
        rw [← logRatioKernel_smul i₀ s ψ (inv_pos.mpr hS) x]
        by_contra hne
        exact absurd (hvan _ hmem hne i) (not_le.mpr hx)
      · simp [g, logRatioKernel, hxpos]
  -- Pass to neighborhoods, one order at a time.
  intro N
  refine ⟨{x | ∀ᶠ y in 𝓝 x, ContDiffAt ℝ N g y}, isOpen_setOfPred_eventually_nhds, fun u hu => ?_,
    fun x hx => (hx.self_of_nhds).contDiffWithinAt⟩
  exact ((hat u hu).of_le (by exact_mod_cast le_top)).eventually (by simp)

/-- **Paley–Wiener on a hyperplane, sufficiency.** Fix `i₀` and `s : ℂ`. Let `P` be an entire
function of `b' : {j // j ≠ i₀} → ℂ` such that `ζ ↦ P(-2πi ζ)` satisfies the Paley–Wiener bounds
`C_N (1 + ‖ζ‖)^(-N) exp (2π ∑ j, ρ j |Im ζ j|)` for every `N`, with `ρ ≥ 0`. Then there is a
kernel `g`, continuous on the simplex, smooth near it and vanishing near its faces, whose simplex
Mellin transform on the hyperplane `∑ i, b i = s` is `P`:
`∫_Δ ∏ u^(b - 1) g = P(b')` for `b = hyperplaneParam i₀ s b'`. -/
theorem exists_kernel_of_paleyWiener (i₀ : ι) (s : ℂ) {P : ({j : ι // j ≠ i₀} → ℂ) → ℂ}
    (hP : Differentiable ℂ P) {ρ : {j : ι // j ≠ i₀} → ℝ} (hρ : ∀ j, 0 ≤ ρ j)
    (hbd : ∀ N : ℕ, ∃ C, ∀ ζ : {j : ι // j ≠ i₀} → ℂ,
      ‖P (fun j => -(2 * π * I) * ζ j)‖ ≤ C * (1 + ‖ζ‖) ^ (-(N : ℝ)) *
        Real.exp (2 * π * ∑ j, ρ j * |(ζ j).im|)) :
    ∃ g : (ι → ℝ) → ℂ, ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι) ∧
      SmoothNearStdSimplex g ∧
      (∃ δ > 0, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i) ∧
      ∀ b' : {j : ι // j ≠ i₀} → ℂ,
        ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι,
          (∏ i, (u i : ℂ) ^ (hyperplaneParam i₀ s b' i - 1)) * g u ∂Measure.stdSimplexMeasure =
          P b' := by
  -- The classical Paley–Wiener theorem in the frequency variable `ζ`, `b' = -2πi ζ`.
  set F : ({j : ι // j ≠ i₀} → ℂ) → ℂ := fun ζ => P (fun j => -(2 * π * I) * ζ j)
  have hF : Differentiable ℂ F := hP.comp (by fun_prop)
  obtain ⟨hsm, hsupp, hcpt, hfour⟩ := paleyWiener hF hρ hbd
  set f := 𝓕⁻ fun ξ => F (realPoint ξ)
  set ψ : ({j : ι // j ≠ i₀} → ℝ) → ℂ := fun w => f (WithLp.toLp 2 w)
  have hψc : Continuous ψ := hsm.continuous.comp (PiLp.continuous_toLp 2 _)
  have hψbox : ∀ w, ψ w ≠ 0 → ∀ j, |w j| ≤ ρ j := by
    intro w hw j
    by_contra h
    exact hw (hsupp (WithLp.toLp 2 w) j (not_le.mp h))
  have hψcpt : HasCompactSupport ψ := by
    refine HasCompactSupport.intro (isCompact_univ_pi fun j => isCompact_Icc (a := -ρ j)
      (b := ρ j)) fun w hw => ?_
    by_contra hne
    exact hw fun j _ => abs_le.mp (hψbox w hne j)
  -- The Laplace transform of `ψ` is `P`.
  set Q : ({j : ι // j ≠ i₀} → ℂ) → ℂ := fun z => ∫ w, Complex.exp (∑ j, z j * w j) * ψ w
  have hQ : AnalyticOnNhd ℂ Q univ := analyticOnNhd_integral_cexp_mul hψc hψcpt
  have hreal : ∀ ξ : {j : ι // j ≠ i₀} → ℝ,
      Q (fun j => -(2 * π * I) * ξ j) = P (fun j => -(2 * π * I) * ξ j) := by
    intro ξ
    have h := congrFun hfour (WithLp.toLp 2 ξ)
    rw [Real.fourier_eq', ← (PiLp.volume_preserving_toLp _).integral_comp
      (MeasurableEquiv.toLp 2 _).measurableEmbedding] at h
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, smul_eq_mul] at h
    show Q _ = F (realPoint (WithLp.toLp 2 ξ))
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [ψ, f]
    congr 1
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hPQ : P = Q := by
    have hP1 : AnalyticOnNhd ℂ (fun z : {j : ι // j ≠ i₀} → ℂ => P (fun j => -(2 * π * I) * z j))
        univ :=
      (hF.differentiableOn).analyticOnNhd_of_finiteDimensional isOpen_univ
    have hQ1 : AnalyticOnNhd ℂ (fun z : {j : ι // j ≠ i₀} → ℂ => Q (fun j => -(2 * π * I) * z j))
        univ := fun z _ =>
      (hQ _ (mem_univ _)).comp_of_eq
        (((-(2 * π * I) : ℂ) • ContinuousLinearMap.id ℂ ({j : ι // j ≠ i₀} → ℂ)).analyticAt z) rfl
    have heq := AnalyticOnNhd.eq_of_eqOn_posReal_pi hP1 hQ1 fun ξ _ => (hreal ξ).symm
    funext b'
    have hb' : b' = fun j => -(2 * π * I) * (b' j / (-(2 * π * I))) := by
      funext j
      have : -(2 * π * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      field_simp
    rw [hb']
    exact congrFun heq _
  -- The kernel.
  set δ : ℝ := (1 + ∑ j, Real.exp (ρ j))⁻¹ * Real.exp (-∑ j, ρ j)
  have hδ : 0 < δ := mul_pos (inv_pos.mpr (add_pos_of_pos_of_nonneg one_pos
    (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le))) (Real.exp_pos _)
  refine ⟨logRatioKernel i₀ s ψ, continuousOn_logRatioKernel i₀ s hψc hρ hψbox,
    smoothNearStdSimplex_logRatioKernel i₀ s (hsm.comp (PiLp.contDiff_toLp (p := 2))) hρ hψbox,
    ⟨δ, hδ, logRatioKernel_vanish i₀ s hρ hψbox⟩, fun b' => ?_⟩
  rw [integral_monomial_mul_eq_integral_logRatio i₀
    (continuousOn_logRatioKernel i₀ s hψc hρ hψbox) hδ
    (logRatioKernel_vanish i₀ s hρ hψbox), hPQ]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  dsimp only
  rw [logRatioKernel_logRatioPoint]
  have hz : (logRatioZ i₀ w : ℂ) ^ (-s) * (logRatioZ i₀ w : ℂ) ^ s = 1 := by
    rw [← cpow_add _ _ (ofReal_ne_zero.mpr (logRatioZ_pos i₀ w).ne'), neg_add_cancel, cpow_zero]
  linear_combination (Complex.exp (∑ j, b' j * w j) * ψ w) * hz

/-! ### Necessity and injectivity on hyperplanes -/

/-- The log-ratio point of the log-ratio coordinates of a point of the open simplex is the point
itself. -/
theorem logRatioPoint_logRatioCoords (i₀ : ι) {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) (hpos : ∀ i, 0 < u i) :
    logRatioPoint i₀ (logRatioCoords i₀ u) = u := by
  have hext : ∀ i, piExp (logRatioExt i₀ (logRatioCoords i₀ u)) i = u i / u i₀ := by
    intro i
    by_cases hi : i = i₀
    · subst hi; simp [piExp, logRatioExt, (hpos i).ne']
    · simp [piExp, logRatioExt, hi, logRatioCoords, Real.exp_log (div_pos (hpos i) (hpos i₀))]
  have hZ : logRatioZ i₀ (logRatioCoords i₀ u) = (u i₀)⁻¹ := by
    simp only [logRatioZ, hext, ← Finset.sum_div, hu.2, one_div]
  funext i
  simp only [logRatioPoint, Pi.smul_apply, smul_eq_mul, hZ, hext, inv_inv]
  field_simp [(hpos i₀).ne']

/-- The exponentiated extended coordinates depend smoothly on the log-ratio coordinates. -/
theorem contDiff_piExp_logRatioExt (i₀ : ι) :
    ContDiff ℝ ∞ (fun w : {j : ι // j ≠ i₀} → ℝ => piExp (logRatioExt i₀ w)) := by
  refine contDiff_pi.mpr fun i => Real.contDiff_exp.comp ?_
  by_cases hi : i = i₀
  · subst hi; simp only [logRatioExt, dite_true]; exact contDiff_const
  · simp only [logRatioExt, hi, dite_false]; exact contDiff_apply ℝ ℝ _

/-- The normalizing sum depends smoothly on the log-ratio coordinates. -/
theorem contDiff_logRatioZ (i₀ : ι) : ContDiff ℝ ∞ (logRatioZ i₀) :=
  ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).comp (contDiff_piExp_logRatioExt i₀)

/-- The log-ratio point depends smoothly on its coordinates. -/
theorem contDiff_logRatioPoint (i₀ : ι) : ContDiff ℝ ∞ (logRatioPoint i₀) :=
  ((contDiff_logRatioZ i₀).inv fun w => (logRatioZ_pos i₀ w).ne').smul
    (contDiff_piExp_logRatioExt i₀)

/-- The power `Z(w)^c` depends smoothly on the log-ratio coordinates. -/
theorem contDiff_logRatioZ_cpow (i₀ : ι) (c : ℂ) :
    ContDiff ℝ ∞ (fun w => (logRatioZ i₀ w : ℂ) ^ c) := by
  have hexp : ContDiff ℝ ∞ (fun w => Complex.exp (c * (Real.log (logRatioZ i₀ w) : ℂ))) :=
    (Complex.contDiff_exp (𝕜 := ℝ)).comp (contDiff_const.mul
      (ofRealCLM.contDiff.comp ((contDiff_logRatioZ i₀).log fun w => (logRatioZ_pos i₀ w).ne')))
  convert hexp using 1
  funext w
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (logRatioZ_pos i₀ w).ne'),
    ← ofReal_log (logRatioZ_pos i₀ w).le, mul_comm]

/-- The function of the log-ratio coordinates whose Fourier–Laplace transform is the simplex
Mellin transform on the hyperplane `∑ b = s`: `ψ(w) = Z(w)^(-s) g(u(w))`. -/
def hyperplaneKernel (i₀ : ι) (s : ℂ) (g : (ι → ℝ) → ℂ) (w : {j : ι // j ≠ i₀} → ℝ) : ℂ :=
  (logRatioZ i₀ w : ℂ) ^ (-s) * g (logRatioPoint i₀ w)

/-- The hyperplane kernel of a kernel continuous on the simplex is continuous. -/
theorem continuous_hyperplaneKernel (i₀ : ι) (s : ℂ) {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    Continuous (hyperplaneKernel i₀ s g) :=
  (contDiff_logRatioZ_cpow i₀ (-s)).continuous.mul
    (hg.comp_continuous (contDiff_logRatioPoint i₀).continuous (logRatioPoint_mem i₀))

/-- On the hyperplane, the simplex Mellin transform at `b' = -2πi ζ` is the Fourier–Laplace
transform of `hyperplaneKernel`. -/
theorem integral_hyperplane_eq_fourierLaplace (i₀ : ι) {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i)
    (s : ℂ) (ζ : {j : ι // j ≠ i₀} → ℂ) :
    ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι,
        (∏ i, (u i : ℂ) ^ (hyperplaneParam i₀ s (fun j => -(2 * π * I) * ζ j) i - 1)) * g u
        ∂Measure.stdSimplexMeasure = fourierLaplace (hyperplaneKernel i₀ s g) ζ := by
  rw [integral_monomial_mul_eq_integral_logRatio i₀ hg hδ hgsupp, fourierLaplace]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [hyperplaneKernel, Finset.mul_sum, mul_assoc]

/-- The hyperplane kernel of a kernel vanishing near the faces vanishes outside the box
`|w j| ≤ |log δ|`. -/
theorem hyperplaneKernel_box (i₀ : ι) (s : ℂ) {g : (ι → ℝ) → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i) :
    ∀ w, hyperplaneKernel i₀ s g w ≠ 0 → ∀ j, |w j| ≤ |Real.log δ| := by
  intro w hw j
  have hgw : g (logRatioPoint i₀ w) ≠ 0 := fun h => hw (by simp [hyperplaneKernel, h])
  have hmem := logRatioPoint_mem i₀ w
  have hδu := hgsupp _ hmem hgw
  have hle1 : ∀ i, logRatioPoint i₀ w i ≤ 1 := fun i =>
    (Convexity.StdSimplex.mem_Icc_of_mem_coordinateSet hmem i).2
  have hpos : ∀ i, 0 < logRatioPoint i₀ w i := fun i => hδ.trans_le (hδu i)
  have hδ1 : δ ≤ 1 := (hδu i₀).trans (hle1 i₀)
  have hw' : w j = Real.log (logRatioPoint i₀ w j / logRatioPoint i₀ w i₀) := by
    have := congrFun (logRatioCoords_logRatioPoint i₀ w) j
    simp only [logRatioCoords] at this
    exact this.symm
  rw [hw', Real.log_div (hpos j).ne' (hpos i₀).ne', abs_of_nonpos (Real.log_nonpos hδ.le hδ1)]
  have h1 := Real.log_le_log hδ (hδu j)
  have h2 := Real.log_le_log hδ (hδu i₀)
  have h3 := Real.log_nonpos (hpos j).le (hle1 j)
  have h4 := Real.log_nonpos (hpos i₀).le (hle1 i₀)
  rw [abs_le]
  constructor <;> linarith

/-- **Paley–Wiener on a hyperplane, necessity.** For a kernel smooth near the simplex and vanishing
at the points of the simplex with a coordinate below `δ > 0`, the simplex Mellin transform on the
hyperplane `∑ b = s`, as a function of `ζ` with `b' = -2πi ζ`, satisfies the Paley–Wiener bounds
for the box `|w j| ≤ |log δ|`. -/
theorem norm_integral_hyperplane_le (i₀ : ι) {g : (ι → ℝ) → ℂ} (hgs : SmoothNearStdSimplex g)
    {δ : ℝ} (hδ : 0 < δ)
    (hgsupp : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g u ≠ 0 → ∀ i, δ ≤ u i)
    (s : ℂ) (N : ℕ) :
    ∃ C, ∀ ζ : {j : ι // j ≠ i₀} → ℂ,
      ‖∫ u in Convexity.StdSimplex.coordinateSet ℝ ι,
          (∏ i, (u i : ℂ) ^ (hyperplaneParam i₀ s (fun j => -(2 * π * I) * ζ j) i - 1)) * g u
          ∂Measure.stdSimplexMeasure‖ ≤
        C * (1 + ‖ζ‖) ^ (-(N : ℝ)) * Real.exp (2 * π * ∑ j, |Real.log δ| * |(ζ j).im|) := by
  have hψ : ContDiff ℝ ∞ (hyperplaneKernel i₀ s g) := by
    refine contDiff_infty.mpr fun n => ?_
    obtain ⟨U, -, hΔU, hgU⟩ := hgs n
    exact (contDiff_logRatioZ_cpow i₀ (-s)).of_le (by exact_mod_cast le_top) |>.mul
      (hgU.comp_contDiff ((contDiff_logRatioPoint i₀).of_le (by exact_mod_cast le_top))
        fun w => hΔU (logRatioPoint_mem i₀ w))
  obtain ⟨C, hC⟩ := norm_fourierLaplace_le_of_contDiff hψ (hyperplaneKernel_box i₀ s hδ hgsupp) N
  refine ⟨C, fun ζ => ?_⟩
  rw [integral_hyperplane_eq_fourierLaplace i₀ hgs.continuousOn hδ hgsupp]
  exact hC ζ

/-- **Injectivity on a hyperplane.** Two kernels continuous on the simplex and vanishing near its
faces whose simplex Mellin transforms agree on one hyperplane `∑ b = s` agree on the simplex. -/
theorem eqOn_of_integral_hyperplane_eq (i₀ : ι) {g₁ g₂ : (ι → ℝ) → ℂ}
    (hg₁ : ContinuousOn g₁ (Convexity.StdSimplex.coordinateSet ℝ ι))
    (hg₂ : ContinuousOn g₂ (Convexity.StdSimplex.coordinateSet ℝ ι)) {δ : ℝ} (hδ : 0 < δ)
    (hv₁ : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g₁ u ≠ 0 → ∀ i, δ ≤ u i)
    (hv₂ : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g₂ u ≠ 0 → ∀ i, δ ≤ u i) (s : ℂ)
    (h : ∀ b' : {j : ι // j ≠ i₀} → ℂ,
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι,
          (∏ i, (u i : ℂ) ^ (hyperplaneParam i₀ s b' i - 1)) * g₁ u ∂Measure.stdSimplexMeasure =
        ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι,
          (∏ i, (u i : ℂ) ^ (hyperplaneParam i₀ s b' i - 1)) * g₂ u ∂Measure.stdSimplexMeasure) :
    EqOn g₁ g₂ (Convexity.StdSimplex.coordinateSet ℝ ι) := by
  have hv : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, g₁ u - g₂ u ≠ 0 → ∀ i, δ ≤ u i := by
    intro u hu hne i
    by_cases h1 : g₁ u = 0
    · exact hv₂ u hu (by intro h2; exact hne (by rw [h1, h2, sub_zero])) i
    · exact hv₁ u hu h1 i
  have hc₁ := continuous_hyperplaneKernel i₀ s hg₁
  have hc₂ := continuous_hyperplaneKernel i₀ s hg₂
  have hcpt₁ := hasCompactSupport_of_box (hyperplaneKernel_box i₀ s hδ hv₁)
  have hcpt₂ := hasCompactSupport_of_box (hyperplaneKernel_box i₀ s hδ hv₂)
  -- The difference of the hyperplane kernels has vanishing Fourier transform.
  have hφ : hyperplaneKernel i₀ s g₁ - hyperplaneKernel i₀ s g₂ = 0 := by
    refine eq_zero_of_fourierLaplace_eq_zero (hc₁.sub hc₂) (hcpt₁.sub hcpt₂) fun ξ => ?_
    have hint : ∀ {φ : ({j : ι // j ≠ i₀} → ℝ) → ℂ}, Continuous φ → HasCompactSupport φ →
        Integrable fun w => Complex.exp (-(2 * π * I) * ∑ j, (ξ j : ℂ) * w j) * φ w :=
      fun hc hcpt => (Continuous.mul (by fun_prop) hc).integrable_of_hasCompactSupport
        hcpt.mul_left
    simp only [fourierLaplace, Pi.sub_apply, mul_sub]
    rw [integral_sub (hint hc₁ hcpt₁) (hint hc₂ hcpt₂), sub_eq_zero]
    have e₁ := integral_hyperplane_eq_fourierLaplace i₀ hg₁ hδ hv₁ s fun j => (ξ j : ℂ)
    have e₂ := integral_hyperplane_eq_fourierLaplace i₀ hg₂ hδ hv₂ s fun j => (ξ j : ℂ)
    rw [fourierLaplace] at e₁ e₂
    rw [← e₁, ← e₂]
    exact h _
  intro u hu
  by_cases hpos : ∀ i, 0 < u i
  · have h0 := congrFun hφ (logRatioCoords i₀ u)
    simp only [Pi.sub_apply, Pi.zero_apply, hyperplaneKernel,
      logRatioPoint_logRatioCoords i₀ hu hpos, ← mul_sub, mul_eq_zero, sub_eq_zero] at h0
    refine h0.resolve_left ?_
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (logRatioZ_pos i₀ _).ne')]
    exact Complex.exp_ne_zero _
  · push Not at hpos
    obtain ⟨i, hi⟩ := hpos
    have hδi : ¬ δ ≤ u i := fun h => absurd (hδ.trans_le h) (not_lt.mpr hi)
    have e₁ : g₁ u = 0 := by by_contra h; exact hδi (hv₁ u hu h i)
    have e₂ : g₂ u = 0 := by by_contra h; exact hδi (hv₂ u hu h i)
    rw [e₁, e₂]

end Dirichlet

end
