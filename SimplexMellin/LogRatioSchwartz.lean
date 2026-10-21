/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.FiniteRegularity
public import SimplexMellin.Hyperplane
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Schwartz weights in intrinsic logarithmic coordinates

Positive Mellin parameters give a Schwartz weight in the `card ι - 1` log-ratio
coordinates, even when the kernel is nonzero on the boundary. The proof pulls back
the double-exponential Schwartz weight along the logarithms of the normalized
exponential coordinates. This map has temperate growth and a continuous linear
left inverse, so Mathlib's Schwartz composition theorem applies.

Multiplication by an angular kernel with `N` derivatives near the closed simplex
then gives the intrinsic Sobolev Fourier criterion `2N > card {j // j ≠ i₀}`.
The positive-parameter change of variables identifies this Fourier transform with
the native Mellin transform on each fixed-sum vertical hyperplane. Consequently one
such hyperplane gives absolute interior inversion at the intrinsic derivative count.
No optimality or endpoint claim is made, and the full-plane inversion threshold is separate.
-/

open Complex MeasureTheory Set
open scoped ContDiff FourierTransform NNReal

@[expose] public noncomputable section

namespace Dirichlet

variable {ι : Type*} [Fintype ι]

/-- The logarithm of the normalizing sum of exponentials. -/
def simplexLogSumExp (y : EuclideanSpace ℝ ι) : ℝ := Real.log (∑ i, Real.exp (y i))

open scoped Classical in
/-- The gradient of log-sum-exp, written as a linear function of simplex coordinates. -/
def simplexLogSumExpGradient (u : ι → ℝ) : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
  ∑ i, u i • PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i

/-- Log-sum-exp differentiates to normalized exponential coordinates. -/
theorem hasFDerivAt_simplexLogSumExp [Nonempty ι] (y : EuclideanSpace ℝ ι) :
    HasFDerivAt simplexLogSumExp (simplexLogSumExpGradient (simplexSoftmax y)) y := by
  classical
  have hp (i : ι) : HasFDerivAt (fun y : EuclideanSpace ℝ ι => Real.exp (y i))
      (Real.exp (y i) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i) y := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (y i)).comp_hasFDerivAt y
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).hasFDerivAt
  have hs : HasFDerivAt (fun y : EuclideanSpace ℝ ι => ∑ i, Real.exp (y i))
      (∑ i, Real.exp (y i) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i) y := by
    simpa only [Finset.sum_fn] using HasFDerivAt.sum (u := Finset.univ) fun i _ => hp i
  have hpos : 0 < ∑ i, Real.exp (y i) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  apply ((Real.hasDerivAt_log hpos.ne').comp_hasFDerivAt y hs).congr_fderiv
  ext v
  simp [simplexLogSumExpGradient, simplexSoftmax, Finset.mul_sum, mul_assoc]

/-- Each normalized exponential coordinate has temperate growth. -/
theorem hasTemperateGrowth_simplexSoftmax_apply [Nonempty ι] (i : ι) :
    (fun y : EuclideanSpace ℝ ι => simplexSoftmax y i).HasTemperateGrowth := by
  have hcoord : ContDiff ℝ ∞ (fun u : ι → ℝ => (u i : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ : ι => ℝ) i)
  have h : SmoothNearStdSimplex (fun u : ι → ℝ => (u i : ℂ)) := fun n =>
    ⟨univ, isOpen_univ, subset_univ _, (hcoord.of_le (by simp)).contDiffOn⟩
  exact Complex.reCLM.hasTemperateGrowth.comp (hasTemperateGrowth_simplexAngle_of_smoothNear h)

/-- Log-sum-exp and all of its derivatives grow at most polynomially. -/
theorem hasTemperateGrowth_simplexLogSumExp [Nonempty ι] :
    (simplexLogSumExp (ι := ι)).HasTemperateGrowth := by
  classical
  have hd : fderiv ℝ (simplexLogSumExp (ι := ι)) =
      simplexLogSumExpGradient ∘ simplexSoftmax :=
    funext fun y => (hasFDerivAt_simplexLogSumExp y).fderiv
  have ht : (fderiv ℝ (simplexLogSumExp (ι := ι))).HasTemperateGrowth := by
    rw [hd]
    unfold simplexLogSumExpGradient
    change (fun y : EuclideanSpace ℝ ι => ∑ i,
      simplexSoftmax y i • PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).HasTemperateGrowth
    apply Function.HasTemperateGrowth.sum
    intro i _
    exact (hasTemperateGrowth_simplexSoftmax_apply i).smul (.const _)
  have hcont : Continuous (simplexLogSumExpGradient (ι := ι)) := by
    unfold simplexLogSumExpGradient
    fun_prop
  obtain ⟨C, hC⟩ := (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι).exists_bound_of_continuousOn
    hcont.continuousOn
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hdiff : Differentiable ℝ (simplexLogSumExp (ι := ι)) :=
    fun y => (hasFDerivAt_simplexLogSumExp y).differentiableAt
  have hLip : LipschitzWith K (simplexLogSumExp (ι := ι)) :=
    lipschitzWith_of_nnnorm_fderiv_le hdiff fun y => by
      change ‖fderiv ℝ simplexLogSumExp y‖ ≤ max C 0
      rw [hd]
      exact (hC _ (simplexSoftmax_mem y)).trans (le_max_left _ _)
  apply Function.HasTemperateGrowth.of_fderiv ht hdiff (k := 1)
    (C := (K : ℝ) + ‖simplexLogSumExp (0 : EuclideanSpace ℝ ι)‖)
  intro y
  have h := hLip.dist_le_mul y 0
  simp only [dist_eq_norm, sub_zero] at h
  calc
    ‖simplexLogSumExp y‖ ≤ ‖simplexLogSumExp y - simplexLogSumExp 0‖ +
        ‖simplexLogSumExp (0 : EuclideanSpace ℝ ι)‖ := norm_le_norm_sub_add _ _
    _ ≤ (K : ℝ) * ‖y‖ + ‖simplexLogSumExp (0 : EuclideanSpace ℝ ι)‖ := by
      simpa only [add_comm] using add_le_add_right h
        ‖simplexLogSumExp (0 : EuclideanSpace ℝ ι)‖
    _ ≤ ((K : ℝ) + ‖simplexLogSumExp (0 : EuclideanSpace ℝ ι)‖) * (1 + ‖y‖) ^ 1 := by
      rw [show ((K : ℝ) + ‖simplexLogSumExp (0 : EuclideanSpace ℝ ι)‖) * (1 + ‖y‖) ^ 1 =
        (K : ℝ) * ‖y‖ + ‖simplexLogSumExp (0 : EuclideanSpace ℝ ι)‖ +
          ((K : ℝ) + ‖simplexLogSumExp (0 : EuclideanSpace ℝ ι)‖ * ‖y‖) by ring]
      exact le_add_of_nonneg_right (add_nonneg K.2 (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

open scoped Classical

variable (i₀ : ι)

/-- Extension by zero as a continuous linear map between Euclidean coordinate spaces. -/
def logRatioExtCLM : EuclideanSpace ℝ {j : ι // j ≠ i₀} →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => if h : i = i₀ then 0 else
      PiLp.proj (𝕜 := ℝ) 2 (fun _ : {j : ι // j ≠ i₀} => ℝ) ⟨i, h⟩)

omit [Fintype ι] in
/-- The linear extension agrees with extension by zero of ordinary coordinate functions. -/
theorem logRatioExtCLM_apply (w : EuclideanSpace ℝ {j : ι // j ≠ i₀}) :
    (logRatioExtCLM i₀ w).ofLp = logRatioExt i₀ w.ofLp := by
  ext i
  by_cases h : i = i₀ <;> simp [logRatioExtCLM, logRatioExt, h]

/-- Logarithms of simplex coordinates, with intrinsic Euclidean log-ratio input. -/
def logRatioLogPoint (w : EuclideanSpace ℝ {j : ι // j ≠ i₀}) : EuclideanSpace ℝ ι :=
  logRatioExtCLM i₀ w - simplexLogSumExp (logRatioExtCLM i₀ w) •
    WithLp.toLp 2 (fun _ => (1 : ℝ))

/-- The logarithmic simplex coordinates are the extended coordinates minus log-sum-exp. -/
theorem logRatioLogPoint_apply (w : EuclideanSpace ℝ {j : ι // j ≠ i₀}) (i : ι) :
    logRatioLogPoint i₀ w i = logRatioExt i₀ w.ofLp i - Real.log (logRatioZ i₀ w.ofLp) := by
  simp [logRatioLogPoint, simplexLogSumExp, logRatioZ, MvMellin.piExp,
    ← logRatioExtCLM_apply]

/-- Logarithmic simplex coordinates have temperate growth. -/
theorem hasTemperateGrowth_logRatioLogPoint : (logRatioLogPoint i₀).HasTemperateGrowth := by
  have : Nonempty ι := ⟨i₀⟩
  exact (logRatioExtCLM i₀).hasTemperateGrowth.sub
    ((hasTemperateGrowth_simplexLogSumExp.comp (logRatioExtCLM i₀).hasTemperateGrowth).smul
      (.const _))

/-- Coordinate differences recover the intrinsic variables from logarithmic simplex coordinates. -/
def logRatioDifferenceCLM : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ {j : ι // j ≠ i₀} :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : {j : ι // j ≠ i₀} => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j =>
      PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) j.1 -
        PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i₀)

/-- The coordinate-difference map is a left inverse, including for singleton simplices. -/
theorem logRatioDifferenceCLM_logRatioLogPoint (w : EuclideanSpace ℝ {j : ι // j ≠ i₀}) :
    logRatioDifferenceCLM i₀ (logRatioLogPoint i₀ w) = w := by
  ext j
  simp [logRatioDifferenceCLM, logRatioLogPoint, logRatioExtCLM, j.2]

/-- Logarithmic simplex coordinates cannot contract distances arbitrarily. -/
theorem antilipschitzWith_logRatioLogPoint :
    AntilipschitzWith ‖logRatioDifferenceCLM i₀‖₊ (logRatioLogPoint i₀) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro w v
  calc
    dist w v = dist (logRatioDifferenceCLM i₀ (logRatioLogPoint i₀ w))
        (logRatioDifferenceCLM i₀ (logRatioLogPoint i₀ v)) := by
      rw [logRatioDifferenceCLM_logRatioLogPoint, logRatioDifferenceCLM_logRatioLogPoint]
    _ ≤ _ := (logRatioDifferenceCLM i₀).lipschitzWith.dist_le_mul _ _

/-- Exponentiating logarithmic simplex coordinates recovers the log-ratio point. -/
theorem exp_logRatioLogPoint (w : EuclideanSpace ℝ {j : ι // j ≠ i₀}) (i : ι) :
    Real.exp (logRatioLogPoint i₀ w i) = logRatioPoint i₀ w.ofLp i := by
  rw [logRatioPoint_eq_exp]
  congr 1
  simp [logRatioLogPoint, simplexLogSumExp, logRatioZ, MvMellin.piExp,
    ← logRatioExtCLM_apply]

/-- The positive Mellin weight in intrinsic coordinates. -/
def logRatioWeight (c : ι → ℝ) (w : EuclideanSpace ℝ {j : ι // j ≠ i₀}) : ℂ :=
  (Real.exp (∑ i, c i * logRatioLogPoint i₀ w i) : ℝ)

/-- Positive Mellin weights are Schwartz in the intrinsic dimension, without face vanishing. -/
theorem exists_schwartzMap_logRatioWeight {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    ∃ S : SchwartzMap (EuclideanSpace ℝ {j : ι // j ≠ i₀}) ℂ, ⇑S = logRatioWeight i₀ c := by
  let S := SchwartzMap.compCLMOfAntilipschitz ℂ (hasTemperateGrowth_logRatioLogPoint i₀)
    (antilipschitzWith_logRatioLogPoint i₀) (expExpSchwartz c hc)
  refine ⟨(Real.exp 1 : ℂ) • S, ?_⟩
  funext w
  change (Real.exp 1 : ℂ) * expExpSchwartz c hc (logRatioLogPoint i₀ w) = _
  rw [expExpSchwartz_apply]
  simp only [← ofReal_mul, ← Real.exp_add, Finset.sum_sub_distrib]
  have hs : ∑ i, Real.exp (logRatioLogPoint i₀ w i) = 1 := by
    simp_rw [exp_logRatioLogPoint]
    exact (logRatioPoint_mem i₀ w.ofLp).2
  rw [hs]
  unfold logRatioWeight
  congr 2
  ring

/-- The complex Mellin weight in intrinsic coordinates. -/
def complexLogRatioWeight (b : ι → ℂ) (w : EuclideanSpace ℝ {j : ι // j ≠ i₀}) : ℂ :=
  Complex.exp (∑ i, b i * logRatioLogPoint i₀ w i)

/-- The intrinsic weight is the product of the complex powers of simplex coordinates. -/
theorem complexLogRatioWeight_eq_prod_cpow (b : ι → ℂ)
    (w : EuclideanSpace ℝ {j : ι // j ≠ i₀}) :
    complexLogRatioWeight i₀ b w = ∏ i, (logRatioPoint i₀ w.ofLp i : ℂ) ^ b i := by
  rw [complexLogRatioWeight, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [← exp_logRatioLogPoint i₀ w i, ofReal_exp_cpow]

/-- A positive real part suffices for the complex Mellin weight to be Schwartz. -/
theorem exists_schwartzMap_complexLogRatioWeight {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    ∃ S : SchwartzMap (EuclideanSpace ℝ {j : ι // j ≠ i₀}) ℂ,
      ⇑S = complexLogRatioWeight i₀ b := by
  obtain ⟨S, hS⟩ := exists_schwartzMap_logRatioWeight i₀ hb
  let phase : EuclideanSpace ℝ {j : ι // j ≠ i₀} → ℝ :=
    fun w => ∑ i, (b i).im * logRatioLogPoint i₀ w i
  have hp : phase.HasTemperateGrowth := by
    apply Function.HasTemperateGrowth.sum
    intro i _
    exact (Function.HasTemperateGrowth.const (b i).im).mul
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).hasTemperateGrowth.comp
      (hasTemperateGrowth_logRatioLogPoint i₀))
  have ht : (fun w => Complex.exp ((phase w : ℂ) * I)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_exp_mul_I.comp hp
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun w => Complex.exp ((phase w : ℂ) * I)) S, ?_⟩
  ext w
  rw [SchwartzMap.smulLeftCLM_apply_apply ht, hS]
  have he : ∑ i, b i * (logRatioLogPoint i₀ w i : ℂ) =
      ((∑ i, (b i).re * logRatioLogPoint i₀ w i : ℝ) : ℂ) + (phase w : ℂ) * I := by
    apply Complex.ext <;> simp [phase, mul_re, mul_im]
  simp only [complexLogRatioWeight, he, Complex.exp_add, logRatioWeight,
    Complex.ofReal_exp, smul_eq_mul]
  ring

/-- The angular kernel expressed in intrinsic Euclidean log-ratio coordinates. -/
def logRatioAngle (g : (ι → ℝ) → ℂ) (w : EuclideanSpace ℝ {j : ι // j ≠ i₀}) : ℂ :=
  g (logRatioPoint i₀ w.ofLp)

/-- Intrinsic angular coordinates are the restriction of the full logarithmic coordinates. -/
theorem logRatioAngle_eq_comp (g : (ι → ℝ) → ℂ) :
    logRatioAngle i₀ g = simplexAngle g ∘ logRatioExtCLM i₀ := by
  funext w
  unfold logRatioAngle simplexAngle logRatioPoint logRatioZ
  simp only [Function.comp_apply]
  rw [logRatioExtCLM_apply]

/-- Finite regularity near the closed simplex passes to intrinsic angular coordinates. -/
theorem contDiff_logRatioAngle_of_contDiffNear {N : ℕ} {g : (ι → ℝ) → ℂ}
    (hg : ContDiffNearStdSimplex N g) : ContDiff ℝ N (logRatioAngle i₀ g) := by
  have : Nonempty ι := ⟨i₀⟩
  rw [logRatioAngle_eq_comp]
  exact (contDiff_simplexAngle_of_contDiffNear hg).comp (logRatioExtCLM i₀).contDiff

/-- Every available intrinsic angular derivative is bounded, with no boundary vanishing. -/
theorem exists_bound_iteratedFDeriv_logRatioAngle {N n : ℕ} {g : (ι → ℝ) → ℂ}
    (hg : ContDiffNearStdSimplex N g) (hn : n ≤ N) :
    ∃ C, ∀ w : EuclideanSpace ℝ {j : ι // j ≠ i₀},
      ‖iteratedFDeriv ℝ n (logRatioAngle i₀ g) w‖ ≤ C := by
  have : Nonempty ι := ⟨i₀⟩
  obtain ⟨C, hC⟩ := exists_bound_iteratedFDeriv_simplexAngle n (hg.of_le hn)
  refine ⟨C * ‖logRatioExtCLM i₀‖ ^ n, fun w => ?_⟩
  rw [logRatioAngle_eq_comp, (logRatioExtCLM i₀).iteratedFDeriv_comp_right
    (contDiff_simplexAngle_of_contDiffNear hg) w (by exact_mod_cast hn)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (simplexAngle g) (logRatioExtCLM i₀ w)‖ *
        ∏ _ : Fin n, ‖logRatioExtCLM i₀‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C * ‖logRatioExtCLM i₀‖ ^ n := by
      simpa using mul_le_mul_of_nonneg_right (hC (logRatioExtCLM i₀ w))
        (show 0 ≤ ‖logRatioExtCLM i₀‖ ^ n by positivity)

/-- The weighted logarithmic boundary kernel in the simplex's intrinsic dimension. -/
def logRatioBoundaryKernel (b : ι → ℂ) (g : (ι → ℝ) → ℂ)
    (w : EuclideanSpace ℝ {j : ι // j ≠ i₀}) : ℂ :=
  logRatioAngle i₀ g w • complexLogRatioWeight i₀ b w

/-- Smooth boundary kernels times positive Mellin weights are Schwartz intrinsically. -/
theorem exists_schwartzMap_logRatioBoundaryKernel {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g) :
    ∃ S : SchwartzMap (EuclideanSpace ℝ {j : ι // j ≠ i₀}) ℂ,
      ⇑S = logRatioBoundaryKernel i₀ b g := by
  have : Nonempty ι := ⟨i₀⟩
  obtain ⟨S, hS⟩ := exists_schwartzMap_complexLogRatioWeight i₀ hb
  have ht : (logRatioAngle i₀ g).HasTemperateGrowth := by
    rw [logRatioAngle_eq_comp]
    exact (hasTemperateGrowth_simplexAngle_of_smoothNear hg).comp
      (logRatioExtCLM i₀).hasTemperateGrowth
  refine ⟨SchwartzMap.smulLeftCLM ℂ (logRatioAngle i₀ g) S, ?_⟩
  ext w
  rw [SchwartzMap.smulLeftCLM_apply_apply ht, hS]
  rfl

/-- Finite regularity is preserved by the intrinsic Mellin weight. -/
theorem contDiff_logRatioBoundaryKernel_of_contDiffNear {N : ℕ} {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g) :
    ContDiff ℝ N (logRatioBoundaryKernel i₀ b g) := by
  obtain ⟨S, hS⟩ := exists_schwartzMap_complexLogRatioWeight i₀ hb
  change ContDiff ℝ N (fun w => logRatioAngle i₀ g w • complexLogRatioWeight i₀ b w)
  rw [← hS]
  exact (contDiff_logRatioAngle_of_contDiffNear i₀ hg).smul (S.smooth N)

/-- Available derivatives of the intrinsic logarithmic kernel are integrable. -/
theorem integrable_iteratedFDeriv_logRatioBoundaryKernel_of_contDiffNear {N n : ℕ}
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) {g : (ι → ℝ) → ℂ}
    (hg : ContDiffNearStdSimplex N g) (hn : n ≤ N) :
    Integrable (iteratedFDeriv ℝ n (logRatioBoundaryKernel i₀ b g)) := by
  obtain ⟨S, hS⟩ := exists_schwartzMap_complexLogRatioWeight i₀ hb
  change Integrable (iteratedFDeriv ℝ n (fun w => logRatioAngle i₀ g w • complexLogRatioWeight i₀ b w))
  rw [← hS]
  exact S.integrable_iteratedFDeriv_smul_of_bounded
    (contDiff_logRatioAngle_of_contDiffNear i₀ hg)
    (fun k hk => exists_bound_iteratedFDeriv_logRatioAngle i₀ hg hk) hn

/-- Available derivatives of the intrinsic logarithmic kernel are square integrable. -/
theorem memLp_iteratedFDeriv_logRatioBoundaryKernel_of_contDiffNear {N n : ℕ}
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) {g : (ι → ℝ) → ℂ}
    (hg : ContDiffNearStdSimplex N g) (hn : n ≤ N) :
    MemLp (iteratedFDeriv ℝ n (logRatioBoundaryKernel i₀ b g)) 2 := by
  obtain ⟨S, hS⟩ := exists_schwartzMap_complexLogRatioWeight i₀ hb
  change MemLp (iteratedFDeriv ℝ n (fun w => logRatioAngle i₀ g w • complexLogRatioWeight i₀ b w)) 2
  rw [← hS]
  exact S.memLp_two_iteratedFDeriv_smul_of_bounded
    (contDiff_logRatioAngle_of_contDiffNear i₀ hg)
    (fun k hk => exists_bound_iteratedFDeriv_logRatioAngle i₀ hg hk) hn

/-- The intrinsic logarithmic kernel is integrable for every finite-regularity boundary kernel. -/
theorem integrable_logRatioBoundaryKernel_of_contDiffNear {N : ℕ} {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g) :
    Integrable (logRatioBoundaryKernel i₀ b g) := by
  apply (integrable_norm_iff
    (contDiff_logRatioBoundaryKernel_of_contDiffNear i₀ hb hg).continuous.aestronglyMeasurable).mp
  simpa only [norm_iteratedFDeriv_zero] using
    (integrable_iteratedFDeriv_logRatioBoundaryKernel_of_contDiffNear i₀ hb hg
      (n := 0) (Nat.zero_le N)).norm

/-- The intrinsic Fourier transform is absolutely integrable with more than half the
intrinsic dimension many derivatives. No boundary vanishing is needed. -/
theorem integrable_fourier_logRatioBoundaryKernel_of_contDiffNear {N : ℕ}
    (hN : Fintype.card {j : ι // j ≠ i₀} < 2 * N) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g) :
    Integrable (𝓕 (logRatioBoundaryKernel i₀ b g)) := by
  exact Real.integrable_fourier_of_memLp_iteratedFDeriv (by simpa using hN)
    (contDiff_logRatioBoundaryKernel_of_contDiffNear i₀ hb hg)
    (integrable_logRatioBoundaryKernel_of_contDiffNear i₀ hb hg)
    (fun n hn => memLp_iteratedFDeriv_logRatioBoundaryKernel_of_contDiffNear i₀ hb hg hn)

/-- Absolute Fourier inversion in intrinsic coordinates for finite-regularity boundary kernels. -/
theorem fourierInv_fourier_logRatioBoundaryKernel_of_contDiffNear {N : ℕ}
    (hN : Fintype.card {j : ι // j ≠ i₀} < 2 * N) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g) :
    𝓕⁻ (𝓕 (logRatioBoundaryKernel i₀ b g)) = logRatioBoundaryKernel i₀ b g := by
  apply (contDiff_logRatioBoundaryKernel_of_contDiffNear i₀ hb hg).continuous.fourierInv_fourier_eq
  · exact integrable_logRatioBoundaryKernel_of_contDiffNear i₀ hb hg
  · exact integrable_fourier_logRatioBoundaryKernel_of_contDiffNear i₀ hN hb hg

/-- Extend intrinsic frequencies by choosing the base coordinate to make their sum zero. -/
def logRatioFrequency (ξ : {j : ι // j ≠ i₀} → ℝ) : ι → ℝ :=
  fun i => if h : i = i₀ then -∑ j, ξ j else ξ ⟨i, h⟩

/-- Intrinsic frequency directions preserve the sum of the Mellin parameters. -/
theorem sum_logRatioFrequency (ξ : {j : ι // j ≠ i₀} → ℝ) :
    ∑ i, logRatioFrequency i₀ ξ i = 0 := by
  have hsub (j : {j : ι // j ≠ i₀}) : logRatioFrequency i₀ ξ j = ξ j := by
    simp [logRatioFrequency, j.2]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
  simp_rw [hsub]
  simp [logRatioFrequency]

/-- The intrinsic frequency pairing cancels the normalizing logarithm. -/
theorem sum_logRatioFrequency_mul_logRatioLogPoint
    (ξ w : EuclideanSpace ℝ {j : ι // j ≠ i₀}) :
    ∑ i, logRatioFrequency i₀ ξ.ofLp i * logRatioLogPoint i₀ w i =
      ∑ j, ξ j * w j := by
  simp_rw [logRatioLogPoint_apply, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, sum_logRatioFrequency, zero_mul, sub_zero]
  have hsub (j : {j : ι // j ≠ i₀}) :
      logRatioFrequency i₀ ξ.ofLp j * logRatioExt i₀ w.ofLp j = ξ j * w j := by
    simp [logRatioFrequency, logRatioExt, j.2]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
  simp_rw [hsub]
  simp [logRatioFrequency, logRatioExt]

/-- The vertical hyperplane through a parameter vector, in intrinsic Fourier normalization. -/
def logRatioVerticalParam (b : ι → ℂ) (ξ : {j : ι // j ≠ i₀} → ℝ) : ι → ℂ :=
  fun i => b i - (2 * Real.pi : ℂ) * logRatioFrequency i₀ ξ i * I

/-- Intrinsic vertical parameters have the same real parts as their base point. -/
theorem logRatioVerticalParam_mem {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (ξ : {j : ι // j ≠ i₀} → ℝ) : logRatioVerticalParam i₀ b ξ ∈ mvBetaConvergent := by
  intro i
  simpa [logRatioVerticalParam, mul_re, mul_im] using hb i

/-- Intrinsic vertical parameters lie on the complex hyperplane through the base point. -/
theorem sum_logRatioVerticalParam (b : ι → ℂ) (ξ : {j : ι // j ≠ i₀} → ℝ) :
    ∑ i, logRatioVerticalParam i₀ b ξ i = ∑ i, b i := by
  simp only [logRatioVerticalParam, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, ← ofReal_sum, sum_logRatioFrequency, ofReal_zero, mul_zero, zero_mul,
    sub_zero]

/-- The native transform on a positive fixed-sum vertical hyperplane is the Fourier
transform of the intrinsic logarithmic kernel, for arbitrary continuous boundary values. -/
theorem fourier_logRatioBoundaryKernel {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    {g : (ι → ℝ) → ℂ} (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι))
    (ξ : EuclideanSpace ℝ {j : ι // j ≠ i₀}) :
    𝓕 (logRatioBoundaryKernel i₀ b g) ξ =
      (∏ i, Gamma (logRatioVerticalParam i₀ b ξ.ofLp i)) *
        regDirichletIntegral (logRatioVerticalParam i₀ b ξ.ofLp) g := by
  rw [prodGamma_regDirichletIntegral_eq_integral_logRatio i₀
    (logRatioVerticalParam_mem i₀ hb ξ.ofLp) hg, Real.fourier_eq',
    ← (PiLp.volume_preserving_toLp {j : ι // j ≠ i₀}).integral_comp
      (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with w
  have hp := sum_logRatioFrequency_mul_logRatioLogPoint i₀ ξ (WithLp.toLp 2 w)
  have he : ∑ i, logRatioVerticalParam i₀ b ξ.ofLp i *
      (logRatioExt i₀ w i - Real.log (logRatioZ i₀ w)) =
      (-(2 * Real.pi * inner ℝ ξ (WithLp.toLp 2 w : EuclideanSpace ℝ {j : ι // j ≠ i₀})) : ℂ) * I +
        ∑ i, b i * logRatioLogPoint i₀ (WithLp.toLp 2 w) i := by
    simp only [← ofReal_sub]
    simp_rw [← logRatioLogPoint_apply i₀ (WithLp.toLp 2 w), logRatioVerticalParam, sub_mul,
      Finset.sum_sub_distrib]
    have hs : ∑ i, (2 * Real.pi : ℂ) * logRatioFrequency i₀ ξ.ofLp i * I *
        logRatioLogPoint i₀ (WithLp.toLp 2 w) i =
        (2 * Real.pi : ℂ) * (∑ j, ξ j * w j : ℝ) * I := by
      calc
        _ = (2 * Real.pi : ℂ) *
            (∑ i, logRatioFrequency i₀ ξ.ofLp i * logRatioLogPoint i₀ (WithLp.toLp 2 w) i : ℝ) * I := by
          push_cast
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [hp]
    rw [hs]
    rw [show inner ℝ ξ (WithLp.toLp 2 w : EuclideanSpace ℝ {j : ι // j ≠ i₀}) =
      ∑ j, ξ j * w j by simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]]
    push_cast
    ring
  simp only [logRatioBoundaryKernel, logRatioAngle, complexLogRatioWeight, smul_eq_mul]
  rw [he, Complex.exp_add]
  rw [real_inner_comm (WithLp.toLp 2 w) ξ]
  push_cast
  ring_nf

/-- Absolute integrability of the native transform on every positive fixed-sum vertical
hyperplane follows from `2N > card ι - 1` derivatives near the closed simplex. -/
theorem integrable_prodGamma_regDirichletIntegral_logRatio_of_contDiffNear {N : ℕ}
    (hN : Fintype.card {j : ι // j ≠ i₀} < 2 * N) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g) :
    Integrable fun ξ : EuclideanSpace ℝ {j : ι // j ≠ i₀} =>
      (∏ i, Gamma (logRatioVerticalParam i₀ b ξ.ofLp i)) *
        regDirichletIntegral (logRatioVerticalParam i₀ b ξ.ofLp) g := by
  exact (integrable_fourier_logRatioBoundaryKernel_of_contDiffNear i₀ hN hb hg).congr
    (Filter.Eventually.of_forall (fourier_logRatioBoundaryKernel i₀ hb hg.continuousOn))

/-- One positive fixed-sum vertical hyperplane recovers every intrinsic kernel value by
absolute inversion with more than half the intrinsic dimension many derivatives. -/
theorem regDirichletIntegral_inversion_logRatio_of_contDiffNear {N : ℕ}
    (hN : Fintype.card {j : ι // j ≠ i₀} < 2 * N) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g)
    (w : EuclideanSpace ℝ {j : ι // j ≠ i₀}) :
    g (logRatioPoint i₀ w.ofLp) = (complexLogRatioWeight i₀ b w)⁻¹ *
      (𝓕⁻ (fun ξ : EuclideanSpace ℝ {j : ι // j ≠ i₀} =>
        (∏ i, Gamma (logRatioVerticalParam i₀ b ξ.ofLp i)) *
          regDirichletIntegral (logRatioVerticalParam i₀ b ξ.ofLp) g)) w := by
  have hinv := congrFun (fourierInv_fourier_logRatioBoundaryKernel_of_contDiffNear i₀ hN hb hg) w
  rw [show (fun ξ : EuclideanSpace ℝ {j : ι // j ≠ i₀} =>
      (∏ i, Gamma (logRatioVerticalParam i₀ b ξ.ofLp i)) *
        regDirichletIntegral (logRatioVerticalParam i₀ b ξ.ofLp) g) =
    𝓕 (logRatioBoundaryKernel i₀ b g) from
      (funext (fourier_logRatioBoundaryKernel i₀ hb hg.continuousOn)).symm, hinv]
  simp only [logRatioBoundaryKernel, logRatioAngle, smul_eq_mul, complexLogRatioWeight]
  field_simp

/-- Smooth boundary kernels give Schwartz restrictions of the native transform to every
positive fixed-sum vertical hyperplane. -/
theorem exists_schwartzMap_prodGamma_regDirichletIntegral_logRatio {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) {g : (ι → ℝ) → ℂ} (hg : SmoothNearStdSimplex g) :
    ∃ S : SchwartzMap (EuclideanSpace ℝ {j : ι // j ≠ i₀}) ℂ,
      ⇑S = fun ξ => (∏ i, Gamma (logRatioVerticalParam i₀ b ξ.ofLp i)) *
        regDirichletIntegral (logRatioVerticalParam i₀ b ξ.ofLp) g := by
  obtain ⟨S, hS⟩ := exists_schwartzMap_logRatioBoundaryKernel i₀ hb hg
  refine ⟨𝓕 S, ?_⟩
  rw [SchwartzMap.fourier_coe, hS]
  exact funext (fourier_logRatioBoundaryKernel i₀ hb hg.continuousOn)

/-- Absolute native inversion at every interior simplex point, using only one positive
fixed-sum vertical hyperplane and the intrinsic sufficient derivative count. -/
theorem regDirichletIntegral_inversion_logRatio_interior_of_contDiffNear {N : ℕ}
    (hN : Fintype.card {j : ι // j ≠ i₀} < 2 * N) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    {g : (ι → ℝ) → ℂ} (hg : ContDiffNearStdSimplex N g)
    {u : ι → ℝ} (hu : u ∈ stdSimplexInterior) :
    g u = (∏ i, (u i : ℂ) ^ (-b i)) *
      ∫ ξ : EuclideanSpace ℝ {j : ι // j ≠ i₀},
        Complex.exp ((2 * Real.pi * inner ℝ ξ
          (WithLp.toLp 2 (logRatioCoords i₀ u) : EuclideanSpace ℝ {j : ι // j ≠ i₀}) : ℝ) * I) •
            ((∏ i, Gamma (logRatioVerticalParam i₀ b ξ.ofLp i)) *
              regDirichletIntegral (logRatioVerticalParam i₀ b ξ.ofLp) g) := by
  have hinv := regDirichletIntegral_inversion_logRatio_of_contDiffNear i₀ hN hb hg
    (WithLp.toLp 2 (logRatioCoords i₀ u))
  rw [complexLogRatioWeight_eq_prod_cpow, logRatioPoint_logRatioCoords i₀ hu.1 hu.2,
    Real.fourierInv_eq'] at hinv
  simpa only [cpow_neg, Finset.prod_inv_distrib] using hinv

end Dirichlet
