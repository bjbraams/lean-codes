/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Fourier.Sobolev
public import ToMathlib.Analysis.Integral.FunSplitAt

/-!
# A Sobolev Fourier criterion with additional diagonal decay

One additional square-integrable frequency weight in the sum of the coordinates
reduces the sufficient Sobolev order to half the transverse dimension. The scalar
dual weight is square integrable by a volume-preserving shear separating the sum
from the remaining coordinates. This is useful when a diagonal derivative falls
on a smooth weight without differentiating a finite-regularity angular multiplier.
-/

open MeasureTheory Set
open scoped ContDiff FourierTransform Classical

@[expose] public noncomputable section

namespace EuclideanSpace

variable {ι : Type*} [Fintype ι] (i₀ : ι)

/-- A shear that adjusts the first coordinate to prescribe the sum of all coordinates. -/
def sumCoordinateShear : ℝ × ({j : ι // j ≠ i₀} → ℝ) ≃ᵐ ℝ × ({j : ι // j ≠ i₀} → ℝ) where
  toFun p := (p.1 - ∑ j, p.2 j, p.2)
  invFun p := (p.1 + ∑ j, p.2 j, p.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := by
    change Measurable (fun p : ℝ × ({j : ι // j ≠ i₀} → ℝ) => (p.1 - ∑ j, p.2 j, p.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : ℝ × ({j : ι // j ≠ i₀} → ℝ) => (p.1 + ∑ j, p.2 j, p.2))
    fun_prop

/-- The sum-coordinate shear preserves product Lebesgue measure. -/
theorem measurePreserving_sumCoordinateShear :
    MeasurePreserving (sumCoordinateShear i₀) ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
  have h := (MeasurePreserving.id (volume : Measure ({j : ι // j ≠ i₀} → ℝ))).skew_product
    (g := fun w t => t + -(∑ j, w j)) (by fun_prop)
    (Filter.Eventually.of_forall fun w => map_add_right_eq_self volume _)
  convert Measure.measurePreserving_swap.comp (h.comp Measure.measurePreserving_swap) using 1
  ext p <;> rfl

/-- Coordinates with first variable equal to the sum, followed by the other coordinates. -/
def sumCoordinateJoin : ℝ × ({j : ι // j ≠ i₀} → ℝ) ≃ᵐ (ι → ℝ) :=
  (sumCoordinateShear i₀).trans (Homeomorph.funSplitAt ℝ i₀).symm.toMeasurableEquiv

/-- The sum-coordinate parametrization preserves Lebesgue measure. -/
theorem measurePreserving_sumCoordinateJoin :
    MeasurePreserving (sumCoordinateJoin i₀) ((volume : Measure ℝ).prod volume) volume :=
  (MeasurePreserving.symm (Homeomorph.funSplitAt ℝ i₀).toMeasurableEquiv
    (volume_preserving_funSplitAt i₀)).comp (measurePreserving_sumCoordinateShear i₀)

/-- The sum of the joined coordinates is the first variable. -/
theorem sum_sumCoordinateJoin (t : ℝ) (w : {j : ι // j ≠ i₀} → ℝ) :
    ∑ i, sumCoordinateJoin i₀ (t, w) i = t := by
  have hsub (j : {j : ι // j ≠ i₀}) : sumCoordinateJoin i₀ (t, w) j = w j := by
    simp [sumCoordinateJoin, sumCoordinateShear, j.2]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
  simp_rw [hsub]
  simp [sumCoordinateJoin, sumCoordinateShear]

/-- The remaining coordinates of the sum-coordinate parametrization are unchanged. -/
theorem sumCoordinateJoin_apply_subtype (t : ℝ) (w : {j : ι // j ≠ i₀} → ℝ)
    (j : {j : ι // j ≠ i₀}) : sumCoordinateJoin i₀ (t, w) j = w j := by
  simp [sumCoordinateJoin, sumCoordinateShear, j.2]

/-- Dropping one Euclidean coordinate does not increase the norm. -/
theorem norm_drop_coordinate_le (ξ : EuclideanSpace ℝ ι) :
    ‖(WithLp.toLp 2 (fun j : {j : ι // j ≠ i₀} => ξ j) :
      EuclideanSpace ℝ {j : ι // j ≠ i₀})‖ ≤ ‖ξ‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), real_norm_sq_eq, real_norm_sq_eq,
    Fintype.sum_eq_add_sum_subtype_ne (fun i => ξ i ^ 2) i₀]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- The dual anisotropic weight, separating the coordinate sum from transverse directions. -/
def diagonalDualWeight (s : ℝ) (ξ : EuclideanSpace ℝ ι) : ℝ :=
  (1 + ‖(WithLp.toLp 2 (fun j : {j : ι // j ≠ i₀} => ξ j) :
    EuclideanSpace ℝ {j : ι // j ≠ i₀})‖ ^ 2) ^ (-s / 2) / (1 + |∑ i, ξ i|)

/-- The dual diagonal weight is square integrable above half the transverse dimension. -/
theorem memLp_diagonalDualWeight {s : ℝ}
    (hs : (Fintype.card {j : ι // j ≠ i₀} : ℝ) < 2 * s) :
    MemLp (diagonalDualWeight i₀ s) 2 := by
  have hm : AEStronglyMeasurable (diagonalDualWeight i₀ s) := by
    apply Continuous.aestronglyMeasurable
    unfold diagonalDualWeight
    have hd : Continuous (fun ξ : EuclideanSpace ℝ ι =>
        (WithLp.toLp 2 (fun j : {j : ι // j ≠ i₀} => ξ j) :
          EuclideanSpace ℝ {j : ι // j ≠ i₀})) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : {j : ι // j ≠ i₀} => ℝ)).symm.continuous.comp
        (continuous_pi fun j => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) j.1).continuous)
    have ha : Continuous (fun ξ : EuclideanSpace ℝ ι => 1 +
        ‖(WithLp.toLp 2 (fun j : {j : ι // j ≠ i₀} => ξ j) :
          EuclideanSpace ℝ {j : ι // j ≠ i₀})‖ ^ 2) := continuous_const.add (hd.norm.pow 2)
    exact (ha.rpow_const (fun _ => Or.inl (by positivity))).div
      (by fun_prop) (fun _ => by positivity)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  rw [← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding,
    ← (measurePreserving_sumCoordinateJoin i₀).integrable_comp_emb
      (sumCoordinateJoin i₀).measurableEmbedding]
  have ht : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  have hw : Integrable (fun w : EuclideanSpace ℝ {j : ι // j ≠ i₀} =>
      (1 + ‖w‖ ^ 2) ^ (-s)) := by
    simpa only [show -(2 * s) / 2 = -s by ring] using
      (integrable_rpow_neg_one_add_norm_sq (E := EuclideanSpace ℝ {j : ι // j ≠ i₀})
        (r := 2 * s) (by simpa using hs))
  have hw' := (PiLp.volume_preserving_toLp {j : ι // j ≠ i₀}).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding |>.mpr hw
  apply (ht.mul_prod hw').congr
  filter_upwards with p
  rcases p with ⟨t, w⟩
  have hd : (fun j : {j : ι // j ≠ i₀} => sumCoordinateJoin i₀ (t, w) j) = w :=
    funext (sumCoordinateJoin_apply_subtype i₀ t w)
  simp only [Function.comp_apply, diagonalDualWeight, sum_sumCoordinateJoin,
    hd, Real.norm_eq_abs, sq_abs, div_pow]
  rw [← Real.rpow_mul_natCast (by positivity)]
  have he : -s / 2 * (2 : ℕ) = -s := by norm_num
  rw [he, Real.rpow_neg (by positivity), Real.rpow_two]
  ring

/-- A square-integrable Sobolev weight and one additional coordinate-sum weight imply
integrability above half the transverse dimension. The target need not be a Hilbert space. -/
theorem integrable_of_memLp_weighted_of_memLp_sum_mul
    {H : Type*} [NormedAddCommGroup H] {s : ℝ}
    (hs : (Fintype.card {j : ι // j ≠ i₀} : ℝ) < 2 * s)
    {f : EuclideanSpace ℝ ι → H} (hf : AEStronglyMeasurable f)
    (h₀ : MemLp (fun ξ => (1 + ‖ξ‖ ^ 2) ^ (s / 2) * ‖f ξ‖) 2)
    (h₁ : MemLp (fun ξ => (∑ i, ξ i) * (1 + ‖ξ‖ ^ 2) ^ (s / 2) * ‖f ξ‖) 2) :
    Integrable f := by
  have hs₀ : 0 ≤ s := by
    have : (0 : ℝ) ≤ Fintype.card {j : ι // j ≠ i₀} := by positivity
    linarith
  have hJ := (memLp_diagonalDualWeight i₀ hs).integrable_mul (h₀.add h₁.norm)
  apply hJ.mono' hf
  filter_upwards with ξ
  change ‖f ξ‖ ≤ diagonalDualWeight i₀ s ξ *
    ((1 + ‖ξ‖ ^ 2) ^ (s / 2) * ‖f ξ‖ +
      ‖(∑ i, ξ i) * (1 + ‖ξ‖ ^ 2) ^ (s / 2) * ‖f ξ‖‖)
  let r : ℝ := 1 + ‖(WithLp.toLp 2 (fun j : {j : ι // j ≠ i₀} => ξ j) :
    EuclideanSpace ℝ {j : ι // j ≠ i₀})‖ ^ 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hW : r ^ (s / 2) ≤ (1 + ‖ξ‖ ^ 2) ^ (s / 2) := by
    apply Real.rpow_le_rpow hr.le _ (by positivity)
    have hd := norm_drop_coordinate_le i₀ ξ
    dsimp [r]
    nlinarith [norm_nonneg ξ, norm_nonneg
      (WithLp.toLp 2 (fun j : {j : ι // j ≠ i₀} => ξ j) : EuclideanSpace ℝ {j : ι // j ≠ i₀})]
  have hprod : 1 ≤ r ^ (-s / 2) * (1 + ‖ξ‖ ^ 2) ^ (s / 2) := by
    calc
      1 = r ^ (-s / 2) * r ^ (s / 2) := by
        rw [← Real.rpow_add hr]
        rw [show -s / 2 + s / 2 = 0 by ring, Real.rpow_zero]
      _ ≤ _ := mul_le_mul_of_nonneg_left hW (by positivity)
  calc
    ‖f ξ‖ ≤ (r ^ (-s / 2) * (1 + ‖ξ‖ ^ 2) ^ (s / 2)) * ‖f ξ‖ := by
      simpa using mul_le_mul_of_nonneg_right hprod (norm_nonneg (f ξ))
    _ = diagonalDualWeight i₀ s ξ *
        ((1 + ‖ξ‖ ^ 2) ^ (s / 2) * ‖f ξ‖ +
          ‖(∑ i, ξ i) * (1 + ‖ξ‖ ^ 2) ^ (s / 2) * ‖f ξ‖‖) := by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg
        (show 0 ≤ (1 + ‖ξ‖ ^ 2) ^ (s / 2) from Real.rpow_nonneg (by positivity) _),
        abs_of_nonneg (norm_nonneg (f ξ)), diagonalDualWeight]
      change _ = r ^ (-s / 2) / (1 + |∑ i, ξ i|) * _
      field_simp

end EuclideanSpace

namespace Real

variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- One additional Sobolev-controlled derivative in the diagonal direction reduces
the sufficient Fourier integrability order to half the transverse dimension. The
derivative is specified by its classical Fourier multiplier, allowing separate regularity. -/
theorem integrable_fourier_of_memSobolev_diagonal (i₀ : ι) {s : ℝ}
    (hs : (Fintype.card {j : ι // j ≠ i₀} : ℝ) < 2 * s)
    {f g : EuclideanSpace ℝ ι → H} (hf₁ : Integrable f) (hf₂ : MemLp f 2)
    (hg₁ : Integrable g) (hg₂ : MemLp g 2)
    (hSf : TemperedDistribution.MemSobolev s 2 (Lp.toTemperedDistribution (hf₂.toLp f)))
    (hSg : TemperedDistribution.MemSobolev s 2 (Lp.toTemperedDistribution (hg₂.toLp g)))
    {a : ℂ} (ha : a ≠ 0)
    (hd : ∀ ξ, 𝓕 g ξ = (a * (∑ i, ξ i : ℝ)) • 𝓕 f ξ) : Integrable (𝓕 f) := by
  have hfW := memLp_weighted_fourier_of_memSobolev hf₁ hf₂ hSf
  have hgW := memLp_weighted_fourier_of_memSobolev hg₁ hg₂ hSg
  have hwabs (ξ : EuclideanSpace ℝ ι) : |(1 + ‖ξ‖ ^ 2) ^ (s / 2)| =
      (1 + ‖ξ‖ ^ 2) ^ (s / 2) := abs_of_nonneg (Real.rpow_nonneg (by positivity) _)
  have h₀ : MemLp (fun ξ => (1 + ‖ξ‖ ^ 2) ^ (s / 2) * ‖𝓕 f ξ‖) 2 := by
    simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, hwabs] using hfW.norm
  have h₁ : MemLp (fun ξ => (∑ i, ξ i) * (1 + ‖ξ‖ ^ 2) ^ (s / 2) * ‖𝓕 f ξ‖) 2 := by
    apply (hgW.norm.const_mul ‖a‖⁻¹).of_le
      (by
        simpa only [mul_assoc] using
          ((show AEStronglyMeasurable (fun ξ : EuclideanSpace ℝ ι => ∑ i, ξ i) by
            apply Continuous.aestronglyMeasurable; fun_prop).fun_mul h₀.aestronglyMeasurable))
    filter_upwards with ξ
    rw [hd]
    simp only [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_norm, abs_abs, hwabs]
    have han : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    field_simp
    ring_nf
    exact le_rfl
  apply EuclideanSpace.integrable_of_memLp_weighted_of_memLp_sum_mul i₀ hs _ h₀ h₁
  exact (memLp_fourier_of_integrable_memLp hf₁ hf₂).aestronglyMeasurable

end Real

namespace SchwartzMap

variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A finite smooth multiplier constant in the diagonal direction has an integrable
Fourier transform after multiplication by any Schwartz weight, at the transverse
Sobolev threshold. No additional derivative of the multiplier is needed. -/
theorem integrable_fourier_smul_of_bounded_of_diagonal_deriv_eq_zero (i₀ : ι) {N : ℕ}
    (hN : Fintype.card {j : ι // j ≠ i₀} < 2 * N)
    (S : SchwartzMap (EuclideanSpace ℝ ι) H) {g : EuclideanSpace ℝ ι → ℂ}
    (hg : ContDiff ℝ N g)
    (hb : ∀ n ≤ N, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C)
    (hd : ∀ x, fderiv ℝ g x (WithLp.toLp 2 (fun _ : ι => (1 : ℝ))) = 0) :
    Integrable (𝓕 (fun x => g x • S x)) := by
  have hN₁ : 1 ≤ N := by omega
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ => 1)
  let T : SchwartzMap (EuclideanSpace ℝ ι) H :=
    (SchwartzMap.evalCLM ℂ (EuclideanSpace ℝ ι) H v) (SchwartzMap.fderivCLM ℂ _ _ S)
  let f : EuclideanSpace ℝ ι → H := fun x => g x • S x
  let D : EuclideanSpace ℝ ι → H := fun x => g x • T x
  have hsm (A : SchwartzMap (EuclideanSpace ℝ ι) H) :
      ContDiff ℝ N (fun x => g x • A x) := hg.smul (A.smooth N)
  have hI (A : SchwartzMap (EuclideanSpace ℝ ι) H) : Integrable (fun x => g x • A x) := by
    apply (integrable_norm_iff (hsm A).continuous.aestronglyMeasurable).mp
    simpa only [norm_iteratedFDeriv_zero] using
      (A.integrable_iteratedFDeriv_smul_of_bounded hg hb (n := 0) (Nat.zero_le N)).norm
  have h₂ (A : SchwartzMap (EuclideanSpace ℝ ι) H) : MemLp (fun x => g x • A x) 2 := by
    apply (A.memLp_two_iteratedFDeriv_smul_of_bounded hg hb (n := 0) (Nat.zero_le N)).of_le
      (hsm A).continuous.aestronglyMeasurable
    filter_upwards with x
    simp only [norm_iteratedFDeriv_zero, le_refl]
  have hSob (A : SchwartzMap (EuclideanSpace ℝ ι) H) :
      TemperedDistribution.MemSobolev N 2
        (Lp.toTemperedDistribution ((h₂ A).toLp (fun x => g x • A x))) :=
    Real.memSobolev_toLp_of_memLp_iteratedFDeriv (hsm A)
      (fun n hn => A.memLp_two_iteratedFDeriv_smul_of_bounded hg hb hn) (h₂ A)
  have hdiff : Differentiable ℝ f :=
    (hsm S).differentiable (by exact_mod_cast (show N ≠ 0 by omega))
  have hIfd : Integrable (fderiv ℝ f) := by
    apply (integrable_norm_iff
      ((hsm S).fderiv_right (m := 0) (by exact_mod_cast hN₁)).continuous.aestronglyMeasurable).mp
    simpa only [norm_iteratedFDeriv_one] using
      (S.integrable_iteratedFDeriv_smul_of_bounded hg hb (n := 1) hN₁).norm
  have hD : D = fun x => fderiv ℝ f x v := by
    funext x
    rw [fderiv_fun_smul (hg.differentiable (by exact_mod_cast (show N ≠ 0 by omega)) x)
      S.differentiableAt]
    change g x • fderiv ℝ S x v = g x • fderiv ℝ S x v + fderiv ℝ g x v • S x
    rw [show fderiv ℝ g x v = 0 from hd x, zero_smul, add_zero]
  apply Real.integrable_fourier_of_memSobolev_diagonal i₀ (by exact_mod_cast hN)
    (hI S) (h₂ S) (hI T) (h₂ T) (hSob S) (hSob T)
    (a := (2 * Real.pi : ℂ) * Complex.I) (by simp [Real.pi_ne_zero])
  intro ξ
  change 𝓕 D ξ = (((2 * Real.pi : ℂ) * Complex.I) * (∑ i, ξ i : ℝ)) • 𝓕 f ξ
  rw [hD, ← Real.fourier_continuousLinearMap_apply hIfd,
    Real.fourier_fderiv (hI S) hdiff hIfd]
  simp only [VectorFourier.fourierSMulRight_apply, neg_apply, neg_smul, smul_neg, neg_neg]
  change (2 * Real.pi * Complex.I) • (inner ℝ ξ v • 𝓕 f ξ) =
    ((2 * Real.pi * Complex.I) * (∑ i, ξ i : ℝ)) • 𝓕 f ξ
  have hv : inner ℝ ξ v = ∑ i, ξ i := by
    simp [v, PiLp.inner_apply, RCLike.inner_apply]
  rw [hv]
  rw [smul_comm, ← smul_assoc, Complex.real_smul, mul_comm]

end SchwartzMap
